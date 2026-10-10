import OAI.NumberTheory.CubicMoment.Estimates.FirstSmoothProduct
import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition
import OAI.NumberTheory.CubicMoment.Estimates.SmoothShortContinuity

namespace OAI

/-! The central Mellin integral inherits the proved exceptional product
moment, with a constant independent of the outer norm scale. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventual_shifted_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(361/1000:ℝ) → |τ| ≤ Y^(9/25:ℝ) → |t-τ| ≤ Y^(37/100:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 9/1000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hYp : 0 < Y := zero_lt_one.trans_le ((le_max_left _ _).trans hY)
  have hτ' : |τ| ≤ Y^(361/1000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le ((le_max_left _ _).trans hY) (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(361/1000:ℝ) := by linarith
    _ ≤ Y^(9/1000:ℝ)*Y^(361/1000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_truncated_product_moment (hpub : PrimitiveResidueHeckeInput)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein)
      (V : ℝ → ℂ) (Z : ℝ),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad Y a) → HasCompactSupport V → tsupport V ⊆ Ioi 0 →
      ContDiff ℝ ∞ V → 0 < Z →
      (∑ a : P, ‖∫ τ in Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ)),
        zeroLineMellinWeight V Z τ*
          ∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i) normPartitionWeight (X i/2) (t i-τ)‖^2) ≤
        (zeroLineMellinMass V)^2*Y^(7/3-ε) := by
  obtain ⟨ε,hε,T,hbound⟩ := first_smooth_product_power_saving hpub
    (fun _ : ι => normPartitionWeight) (fun _ => normPartitionWeight_compact)
    (fun _ => normPartitionWeight_positive_support) (fun _ => normPartitionWeight_smooth)
    (fun _ _ hx => normPartitionWeight_low hx) (fun _ _ hx => normPartitionWeight_high hx)
    (fun _ => normPartitionWeight_norm) hGI hGQ hD
  obtain ⟨T₁,hheight⟩ := eventual_shifted_height_bound
  refine ⟨ε,hε,max 1 (max T T₁),?_⟩
  intro F Y X A q η t P V Z hY hF hA hX hlo hhi hq hη hqY ht hP hV hpos hsm hZ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
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
  have hb (τ : ℝ) (hτ : τ ∈ Icc (-(Y^(9/25:ℝ))) (Y^(9/25:ℝ))) :
      (∑ a : P, ‖f a τ‖^2) ≤ Y^(7/3-ε) := by
    have hτabs : |τ| ≤ Y^(9/25:ℝ) := abs_le.mpr hτ
    have hm := hbound F Y X A q η (fun i => t i-τ) P hYT hF hA hX hlo hhi hq hη hqY
      (fun i => hheight Y hYT₁ (t i) τ (ht i) hτabs) hP
    change (∑ a ∈ P.attach, ‖f a τ‖^2) ≤ _
    dsimp only [f]
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖∏ i, primaryShortSmoothSum (A i) a 1 (q i) (η i)
        normPartitionWeight (X i/2) (t i-τ)‖^2)]
    exact hm
  have hm := finite_interval_integral_moment f hf (zeroLineMellinWeight V Z)
    (zeroLineMellinWeight_integrable V hV hpos hsm hZ) (Y^(9/25:ℝ))
    (Y^(7/3-ε)) (Real.rpow_nonneg (zero_le_one.trans hY1) _) hb
  rwa [zeroLineMellinWeight_mass V hZ] at hm

end CubicFirstMoment

end

end OAI
