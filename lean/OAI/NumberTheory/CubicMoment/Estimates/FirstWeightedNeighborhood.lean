import OAI.NumberTheory.CubicMoment.Estimates.FirstWeightedTuple
import OAI.NumberTheory.CubicMoment.Estimates.FirstTruncatedNeighborhood
import OAI.NumberTheory.CubicMoment.Estimates.NeighborhoodTailPower

namespace OAI

/-! Full weighted short-tuple moments throughout the exceptional conductor
neighborhood, with an explicit thirtieth-moment tail. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_weighted_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein) (Z : ℝ),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) → 0 < Z →
      (∑ a ∈ P, ‖primaryShortTupleSum X A a 1 q η
        (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,ε,hε,T,hcentral⟩ := first_truncated_neighborhood_moment (ι := ι) hpub hGI hGQ hD
  obtain ⟨K,hK,hsize⟩ := smooth_short_product_size (ι := ι) hD
  let J : ℝ := (1/(2*Real.pi))*(∫ τ : ℝ, |τ|^30*‖mellin V ((τ:ℂ)*Complex.I)‖)
  obtain ⟨T₁,hT₁,habsorb⟩ := absorb_short_mellin_bounds hε
    (2*(zeroLineMellinMass V)^2) (2*K^2*J^2) (by positivity) (by positivity)
  refine ⟨κ,hκ,hκhi,min ε (1/3)/2,div_pos (lt_min hε (by norm_num)) (by norm_num),
    max 36 (max T T₁),?_⟩
  intro F Y N X A q η t P Z hY hNlo hNhi hF hA hX hlo hhi hq hη hqY ht hP hZ
  have hY36 : 36 ≤ Y := (le_max_left _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  let f : P → ℝ → ℂ := fun a τ =>
    ∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)
  have hf (a : P) : Continuous (f a) := by
    apply continuous_finsetProd
    intro i _
    exact (continuous_primaryShortSmoothSum (A i) a 1 (q i) (η i) normPartitionWeight
      (by linarith [hX i]) (fun _ hx => normPartitionWeight_high hx)).comp
        (continuous_const.sub continuous_id)
  have hs (a : P) (τ : ℝ) : ‖f a τ‖ ≤ K*Y^2 := by
    exact hsize F Y X A q η (fun _ => normPartitionWeight) (fun i => t i-τ) a 1
      hA hX hq (fun _ => normPartitionWeight_norm)
      (fun _ _ hx => normPartitionWeight_high hx) hhi (hP a a.property).1 (by norm_num [primary])
  have hc := hcentral F Y N X A q η t P V Z hYT hNlo hNhi hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hm := full_mellin_moment_of_central f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) 30
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hZ 30)
    (Real.rpow_pos_of_pos hY0 _) (mul_nonneg hK.le (sq_nonneg Y)) hs hc
  rw [zeroLineMellinWeight_moment V hZ 30] at hm
  have hY1 : 1 ≤ Y := by linarith
  have hN : 1 ≤ N := (Real.one_le_rpow hY1 (by linarith : 0 ≤ 1-κ)).trans hNlo
  have hNY : N ≤ Y^2 := by
    simpa only [Real.rpow_two] using hNhi.trans
      (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : 1+κ ≤ 2))
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    simpa only [Fintype.card_coe] using neighborhood_cubic_card P hY36 hN hNY hP
  have he (a : Eisenstein) : primaryShortTupleSum X A a 1 q η
      (fun _ => normPartitionWeight) t V Z = ∫ τ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) normPartitionWeight (X i/2) (t i-τ) :=
    primaryShortTupleSum_integral X A a 1 q η (fun _ => normPartitionWeight) t
      (fun i => by linarith [hX i]) (fun _ _ hx => normPartitionWeight_high hx) V hV hpos hsm hZ
  apply le_trans _ (habsorb Y hYT₁)
  calc
    _ = ∑ a : P, ‖∫ τ, zeroLineMellinWeight V Z τ*f a τ‖^2 := by
      simp_rw [he]
      symm
      change (∑ a ∈ P.attach, _) = _
      exact Finset.sum_attach P (fun a =>
        ‖∫ τ, zeroLineMellinWeight V Z τ*∏ i,
          primaryShortSmoothSum (A i) a 1 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2)
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*(Fintype.card P:ℝ)*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := hm
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*Y^4*((K*Y^2/(Y^(9/25:ℝ))^30)*J)^2 := by gcongr
    _ ≤ (2*(zeroLineMellinMass V)^2)*Y^(7/3-ε)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      simpa only [mul_assoc] using add_le_add
        (le_refl (2*((zeroLineMellinMass V)^2*Y^(7/3-ε))))
        (neighborhood_mellin_tail_le (K := K) (J := J) hY1)

end CubicFirstMoment

end

end OAI
