import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCubeEnergy

namespace OAI

/-! Montgomery--Vaughan applied to the actual finite cube-completed
angular Gauss sum. Both the rational norm multiplicity and the original
coefficient energy are supplied by proved arithmetic lemmas. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_cube_polynomial_collect (S : Finset (Eisenstein × Eisenstein))
    (w : Eisenstein × Eisenstein → ℂ) (t : ℝ) :
    (∑ du ∈ S, w du*mellinPhase t (norm (metaplecticCubeProduct du))) =
      eisensteinNormPolynomial (S.image metaplecticCubeProduct) (metaplecticCubeCoefficient S w) t := by
  unfold eisensteinNormPolynomial metaplecticCubeCoefficient
  rw [←Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem metaplecticCubeProduct hdu)
    (fun du => w du*mellinPhase t (norm (metaplecticCubeProduct du)))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro du hdu
  rw [(Finset.mem_filter.mp hdu).2]

lemma metaplectic_cube_output_primary (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) :
    ∀ b ∈ S.image metaplecticCubeProduct, primary b := by
  intro b hb
  obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
  exact primary_mul (hS du hdu).2 (by
    simpa only [pow_succ,pow_zero,one_mul] using
      primary_mul (primary_mul (hS du hdu).1 (hS du hdu).1) (hS du hdu).1)

lemma metaplectic_cube_norm_frequencies (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {V : ℝ}
    (hsize : ∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) :
    ∀ b ∈ S.image metaplecticCubeProduct, normNat b ∈ Finset.Icc 1 ⌈V⌉₊ := by
  intro b hb
  have hp := metaplectic_cube_output_primary S hS b hb
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (show (1:ℝ) ≤ (normNat b:ℝ) by rw [normNat_cast]; exact one_le_norm (primary_ne_zero hp))
  · have hbV : norm b ≤ V := by
      obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
      exact hsize du hdu
    have hh : (normNat b:ℝ) ≤ (⌈V⌉₊:ℝ) := by
      rw [normNat_cast]
      exact hbV.trans (Nat.le_ceil V)
    exact_mod_cast hh

/-- The one-sided height mean for the literal completed angular
coefficients. The only analytic hypothesis is the published ordinary
Montgomery--Vaughan theorem. -/
theorem metaplectic_primal_meanAbsolute_sq {ε C : ℝ} (hε : 0 < ε)
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (r : Eisenstein), primary r → ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X V M T u : ℝ),
      1 ≤ V → 0 ≤ M → 0 < T →
      (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) →
      ((∫ t in T..2*T, ‖∑ du ∈ S, metaplecticPrimalCoefficient r ℓ W X du*
        mellinPhase (t+u) (norm (metaplecticCubeProduct du))‖)/T)^2 ≤
          C*K*(1+2*V/T)*V^(1+ε)*M^2 := by
  let δ := ε/2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨D,hD,hfiber⟩ := primary_norm_fiber_length_bound hδ
  obtain ⟨E,hE,henergy⟩ := metaplectic_primal_energy hδ
  refine ⟨D*E*2^δ,by positivity,?_⟩
  intro S hS r hr ℓ W X V M T u hV hM hT hsize hW
  let A := S.image metaplecticCubeProduct
  let v := metaplecticCubeCoefficient S (metaplecticPrimalCoefficient r ℓ W X)
  have hp := metaplectic_cube_output_primary S hS
  have hz := metaplectic_cube_norm_frequencies S hS hsize
  have he := henergy S hS r hr ℓ W X V M hV hM hsize hW
  have hm := fixedAngular_translated_meanAbsolute_sq hMV hC A v ⌈V⌉₊ (D*(⌈V⌉₊:ℝ)^δ)
    hz (fun b hb => primary_ne_zero (hp b hb)) (hfiber A hp ⌈V⌉₊) 0 u hT
  simp only [theta,zpow_zero,mul_one] at hm
  have hV0 : 0 < V := zero_lt_one.trans_le hV
  have hceil : (⌈V⌉₊:ℝ) ≤ 2*V := by linarith [Nat.ceil_lt_add_one hV0.le]
  have hceilP : (⌈V⌉₊:ℝ)^δ ≤ (2*V)^δ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hceil hδ.le
  have hfactor : 1+(⌈V⌉₊:ℝ)/T ≤ 1+2*V/T := by
    linarith [div_le_div_of_nonneg_right hceil hT.le]
  have hpow : (2*V)^δ*V^(1+δ) = 2^δ*V^(1+ε) := by
    rw [Real.mul_rpow (by norm_num) hV0.le,mul_assoc,←Real.rpow_add hV0]
    congr 2
    dsimp [δ]
    ring
  simp_rw [metaplectic_cube_polynomial_collect] 
  change ((∫ t in T..2*T, ‖eisensteinNormPolynomial A v (t+u)‖)/T)^2 ≤ _
  have hm' : ((∫ t in T..2*T, ‖eisensteinNormPolynomial A v (t+u)‖)/T)^2 ≤
      C*(1+(⌈V⌉₊:ℝ)/T)*(D*(⌈V⌉₊:ℝ)^δ)*(∑ b ∈ A, ‖v b‖^2) := hm
  calc
    _ ≤ C*(1+(⌈V⌉₊:ℝ)/T)*(D*(⌈V⌉₊:ℝ)^δ)*(E*V^(1+δ)*M^2) :=
      hm'.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ C*(1+2*V/T)*(D*(2*V)^δ)*(E*V^(1+δ)*M^2) := by gcongr
    _ = C*(D*E)*(1+2*V/T)*((2*V)^δ*V^(1+δ))*M^2 := by ring
    _ = _ := by rw [hpow]; ring

end CubicFirstMoment

end

end OAI
