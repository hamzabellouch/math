import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCubeMean
import OAI.NumberTheory.CubicMoment.Estimates.RamifiedIdealParts

namespace OAI

/-! Compact support turns the literal completed sum, at every translated
height, into the finite primary cube polynomial used by Montgomery--Vaughan. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimaryPair (du : PrimaryArgument × PrimaryArgument) : Eisenstein × Eisenstein :=
  (du.1.val,du.2.val)

lemma metaplecticPrimaryPair_injective : Function.Injective metaplecticPrimaryPair := by
  intro du ev h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

def metaplecticPrimalSupport (V : ℝ) : Finset (PrimaryArgument × PrimaryArgument) :=
  (((primaryElementBall V).subtype primary).product ((primaryElementBall V).subtype primary)).filter
    (fun du => norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V)

def metaplecticPrimalElementSupport (V : ℝ) : Finset (Eisenstein × Eisenstein) :=
  (metaplecticPrimalSupport V).image metaplecticPrimaryPair

lemma metaplecticPrimalSupport_of_nonzero {r : Eisenstein} (ℓ : ℤ)
    (W : ℝ → ℂ) {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (du : PrimaryArgument × PrimaryArgument)
    (hn : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) ≠ 0) :
    du ∈ metaplecticPrimalSupport V := by
  have hnW : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) ≠ 0 := by
    intro hh
    exact hn (by simp [metaplecticPrimalCoefficient,hh])
  have hsize : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ V := by
    have hb : norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) ≤ B*X := by
      by_contra h
      exact hnW (hW _ ((lt_div_iff₀ hX).mpr (lt_of_not_ge h)))
    exact hb.trans hBV
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    primary_mul du.2.property hcube
  have hd : (du.1:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) :=
    (dvd_pow_self du.1.val (by norm_num : (3:ℕ) ≠ 0)).trans (dvd_mul_left _ _)
  have hu : (du.2:Eisenstein) ∣ metaplecticCubeProduct (metaplecticPrimaryPair du) := dvd_mul_right _ _
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.1.property,(norm_le_of_dvd (primary_ne_zero hp) hd).trans hsize⟩
  · apply Finset.mem_subtype.mpr
    exact mem_primaryElementBall.mpr ⟨du.2.property,(norm_le_of_dvd (primary_ne_zero hp) hu).trans hsize⟩

def metaplecticHeightCompleted (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (X t : ℝ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
      mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du)))

lemma metaplecticHeightCompleted_zero (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) :
    metaplecticHeightCompleted r ℓ W X 0 = metaplecticCompleted r ℓ W X := by
  unfold metaplecticHeightCompleted metaplecticCompleted
  apply tsum_congr
  intro du
  simp [metaplecticPrimalCoefficient,metaplecticPrimaryPair,metaplecticCubeProduct,mellinPhase]

/-- Exact finite support, independent of the height parameter. -/
theorem metaplecticHeightCompleted_finite (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X B V : ℝ} (hX : 0 < X) (hBV : B*X ≤ V)
    (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t =
      ∑ du ∈ metaplecticPrimalElementSupport V,
        metaplecticPrimalCoefficient r ℓ W X du*mellinPhase t (norm (metaplecticCubeProduct du)) := by
  rw [metaplecticHeightCompleted,tsum_eq_sum (s := metaplecticPrimalSupport V) (fun du hdu => ?_)]
  · rw [metaplecticPrimalElementSupport,Finset.sum_image]
    exact fun _ _ _ _ h => metaplecticPrimaryPair_injective h
  · have hc : metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du) = 0 := by
      by_contra hn
      exact hdu (metaplecticPrimalSupport_of_nonzero ℓ W hX hBV hW du hn)
    rw [hc,zero_mul]

/-- Exact norm twist needed to apply the published Voronoi formula at
height t; its outside scalar has modulus one. -/
theorem metaplecticHeightCompleted_twist (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t = mellinPhase t X*
      metaplecticCompleted r ℓ (fun x => W x*mellinPhase t x) X := by
  unfold metaplecticHeightCompleted metaplecticCompleted
  rw [←tsum_mul_left]
  apply tsum_congr
  intro du
  have hcube : primary ((du.1:Eisenstein)^3) := by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul du.1.property du.1.property) du.1.property
  have hn : 0 < norm (metaplecticCubeProduct (metaplecticPrimaryPair du)) :=
    norm_pos_of_ne_zero (primary_ne_zero (primary_mul du.2.property hcube))
  have ht : mellinPhase t X*mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) =
      mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) := by
    rw [←mellinPhase_mul_pos t hX (div_pos hn hX)]
    congr 1
    field_simp
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [metaplecticPrimalCoefficient,metaplecticPrimaryPair,
      hc,ite_true,metaplecticCubeProduct] at ht ⊢
    rw [←ht]
    ring
  · simp only [metaplecticPrimalCoefficient,metaplecticPrimaryPair,
      hc,ite_false,zero_mul,mul_zero]

lemma metaplecticPrimalElementSupport_primary (V : ℝ) :
    ∀ du ∈ metaplecticPrimalElementSupport V, primary du.1 ∧ primary du.2 := by
  intro du hdu
  obtain ⟨ev,_hev,rfl⟩ := Finset.mem_image.mp hdu
  exact ⟨ev.1.property,ev.2.property⟩

lemma metaplecticPrimalElementSupport_size (V : ℝ) :
    ∀ du ∈ metaplecticPrimalElementSupport V, norm (metaplecticCubeProduct du) ≤ V := by
  intro du hdu
  obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp hdu
  exact (Finset.mem_filter.mp hev).2

/-- The mean estimate now applies to the original infinite completed
series, with finiteness and all coefficient bounds discharged. -/
theorem metaplecticHeightCompleted_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X B V M T u : ℝ), 0 < X → B*X ≤ V →
      (∀ x : ℝ, B < x → W x = 0) → (∀ x : ℝ, ‖W x‖ ≤ M) →
      1 ≤ V → 0 ≤ M → 0 < T →
      ((∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T)^2 ≤
        C*K*(1+2*V/T)*V^(1+ε)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := metaplectic_primal_meanAbsolute_sq hε hMV hC
  refine ⟨K,hK,?_⟩
  intro r hr ℓ W X B V M T u hX hBV hcut hW hV hM hT
  simp_rw [metaplecticHeightCompleted_finite r ℓ W hX hBV hcut]
  exact hbound _ (metaplecticPrimalElementSupport_primary V) r hr ℓ W X V M T u hV hM hT
    (metaplecticPrimalElementSupport_size V) (fun du _ => hW _)

end CubicFirstMoment

end

end OAI
