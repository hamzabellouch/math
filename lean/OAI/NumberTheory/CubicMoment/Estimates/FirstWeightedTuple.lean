import OAI.NumberTheory.CubicMoment.Estimates.TruncatedProductMoment
import OAI.NumberTheory.CubicMoment.Estimates.ShortProductSize
import OAI.NumberTheory.CubicMoment.Estimates.MellinMomentPowers

namespace OAI

/-! The full first-configuration moment for the actual smooth weighted
short-factor tuple. Mellin separation includes the complementary tails. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primaryShortTupleSum_integral (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ)
    (W : ι → ℝ → ℂ) (t : ι → ℝ)
    (hX : ∀ i, 0 < X i) (hW : ∀ i x, 2 < x → W i x = 0)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) {Z : ℝ} (hZ : 0 < Z) :
    primaryShortTupleSum X A a b q η W t V Z =
      ∫ τ : ℝ, zeroLineMellinWeight V Z τ*
        ∏ i, primaryShortSmoothSum (A i) a b (q i) (η i) (W i) (X i/2) (t i-τ) := by
  rw [primaryShortTupleSum_mellin X A a b q η W t hX hW V hV hpos hsm hZ,
    ← integral_const_mul]
  congr 1
  funext τ
  unfold zeroLineMellinWeight
  ring

theorem first_weighted_tuple_power_saving (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad Y a) → 0 < Z →
      (∑ a ∈ P, ‖primaryShortTupleSum X A a 1 q η
        (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨ε,hε,T,hcentral⟩ := first_truncated_product_moment (ι := ι) hpub hGI hGQ hD
  obtain ⟨K,hK,hsize⟩ := smooth_short_product_size (ι := ι) hD
  let J : ℝ := (1/(2*Real.pi))*(∫ τ : ℝ, |τ|^20*‖mellin V ((τ:ℂ)*Complex.I)‖)
  obtain ⟨T₁,hT₁,habsorb⟩ := absorb_short_mellin_bounds hε
    (2*(zeroLineMellinMass V)^2) (2*K^2*J^2) (by positivity) (by positivity)
  refine ⟨min ε (1/3)/2,div_pos (lt_min hε (by norm_num)) (by norm_num),
    max 36 (max T T₁),?_⟩
  intro F Y X A q η t P Z hY hF hA hX hlo hhi hq hη hqY ht hP hZ
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
  have hc := hcentral F Y X A q η t P V Z hYT hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hm := full_mellin_moment_of_central f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) 20
    (zeroLineMellinWeight_moment_integrable V hV hpos hsm hZ 20)
    (Real.rpow_pos_of_pos hY0 _) (mul_nonneg hK.le (sq_nonneg Y)) hs hc
  rw [zeroLineMellinWeight_moment V hZ 20] at hm
  have hcard : (Fintype.card P:ℝ) ≤ Y^2 := by
    simpa only [Fintype.card_coe] using primary_gram_rows_card_quadratic P hY36 hP
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
        2*(Fintype.card P:ℝ)*((K*Y^2/(Y^(9/25:ℝ))^20)*J)^2 := hm
    _ ≤ 2*((zeroLineMellinMass V)^2*Y^(7/3-ε))+
        2*Y^2*((K*Y^2/(Y^(9/25:ℝ))^20)*J)^2 := by gcongr
    _ = (2*(zeroLineMellinMass V)^2)*Y^(7/3-ε)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      rw [short_mellin_tail_power hY0]
      ring

end CubicFirstMoment

end

end OAI
