import OAI.Geometry.Perimeter.Regularity.NormalCoordinates
import OAI.Geometry.Perimeter.Regularity.FiberCrossing
import OAI.Geometry.Perimeter.Regularity.NormalPhaseMollification

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution InnerProductSpace
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap

theorem phaseMollification_eq_one_of_ae {n : ℕ} {E : Set (Euc n)}
    {k : Euc n → ℝ} (hu : ∫ x, k x = 1) (x : Euc n)
    (he : ∀ᵐ y ∂volume, k (x-y) ≠ 0 → y ∈ E) :
    phaseMollification E k x = 1 := by
  change (∫ y, E.indicator (fun _ ↦ (1:ℝ)) y*k (x-y)) = 1
  calc
    _ = ∫ y, k (x-y) := by
      apply integral_congr_ae
      filter_upwards [he] with y hy
      by_cases hk : k (x-y) = 0
      · simp [hk]
      · simp [hy hk]
    _ = 1 := by rw [integral_sub_left_eq_self,hu]

theorem phaseMollification_eq_zero_of_ae {n : ℕ} {E : Set (Euc n)}
    {k : Euc n → ℝ} (x : Euc n)
    (he : ∀ᵐ y ∂volume, k (x-y) ≠ 0 → y ∉ E) :
    phaseMollification E k x = 0 := by
  change (∫ y, E.indicator (fun _ ↦ (1:ℝ)) y*k (x-y)) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [he] with y hy
  by_cases hk : k (x-y) = 0
  · simp [hk]
  · simp [hy hk]

theorem phaseMollification_lower_cap {n : ℕ} {E : Set (Euc n)} {v : Euc n}
    (hv : ‖v‖ = 1) {k : Euc n → ℝ} (hu : ∫ x, k x = 1)
    {a ε R : ℝ} (ha : 0 ≤ a) (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ y ∂volume, y ∈ Metric.ball 0 R → a < |inner ℝ v y| →
      (y ∈ E ↔ inner ℝ v y < 0))
    (x : Euc n) (hx : ‖x‖+ε ≤ R) (hl : inner ℝ v x < -a-ε) :
    phaseMollification E k x = 1 := by
  apply phaseMollification_eq_one_of_ae hu x
  filter_upwards [hphase] with y hy
  intro hk
  have hxy : ‖x-y‖ < ε := by simpa only [Metric.mem_ball,dist_zero_right] using hs hk
  have hyn : y ∈ Metric.ball (0:Euc n) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have h := norm_sub_le x (x-y)
    rw [sub_sub_cancel] at h
    linarith
  have hiv : |inner ℝ v (x-y)| ≤ ‖x-y‖ := by
    simpa only [hv,one_mul] using abs_real_inner_le_norm v (x-y)
  have hey : inner ℝ v y < -a := by
    rw [inner_sub_right] at hiv
    have he := (neg_le_abs (inner ℝ v x-inner ℝ v y)).trans hiv
    linarith
  exact (hy hyn (by rw [abs_of_neg (by linarith : inner ℝ v y < 0)]; linarith)).mpr
    (by linarith)

theorem phaseMollification_upper_cap {n : ℕ} {E : Set (Euc n)} {v : Euc n}
    (hv : ‖v‖ = 1) {k : Euc n → ℝ}
    {a ε R : ℝ} (ha : 0 ≤ a) (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ y ∂volume, y ∈ Metric.ball 0 R → a < |inner ℝ v y| →
      (y ∈ E ↔ inner ℝ v y < 0))
    (x : Euc n) (hx : ‖x‖+ε ≤ R) (hl : a+ε < inner ℝ v x) :
    phaseMollification E k x = 0 := by
  apply phaseMollification_eq_zero_of_ae x
  filter_upwards [hphase] with y hy
  intro hk
  have hxy : ‖x-y‖ < ε := by simpa only [Metric.mem_ball,dist_zero_right] using hs hk
  have hyn : y ∈ Metric.ball (0:Euc n) R := by
    rw [Metric.mem_ball, dist_zero_right]
    have h := norm_sub_le x (x-y)
    rw [sub_sub_cancel] at h
    linarith
  have hiv : |inner ℝ v (x-y)| ≤ ‖x-y‖ := by
    simpa only [hv,one_mul] using abs_real_inner_le_norm v (x-y)
  have hey : a < inner ℝ v y := by
    rw [inner_sub_right] at hiv
    have he := (le_abs_self (inner ℝ v x-inner ℝ v y)).trans hiv
    linarith
  intro he
  have hn := (hy hyn (by rw [abs_of_pos (by linarith : 0 < inner ℝ v y)]; exact hey)).mp he
  linarith

def mollifiedNormalProfile {n : ℕ} (E : Set (Euc n)) (k : Euc n → ℝ)
    (v : Euc n) (y : normalPlane v) (s : ℝ) : ℝ :=
  phaseMollification E k ((y:Euc n)+s•v)

theorem mollifiedNormalProfile_contDiff {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (v : Euc n) (y : normalPlane v) :
    ContDiff ℝ ∞ (mollifiedNormalProfile E k v y) :=
  (phaseMollification_contDiff hE hk hc).comp (contDiff_const.add (contDiff_id.smul contDiff_const))

theorem mollifiedNormalProfile_deriv {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k)
    (hc : HasCompactSupport k) (v : Euc n) (y : normalPlane v) (s : ℝ) :
    deriv (mollifiedNormalProfile E k v y) s =
      fderiv ℝ (phaseMollification E k) ((y:Euc n)+s•v) v := by
  have hd := ((phaseMollification_contDiff hE hk hc).differentiable (by simp)
    ((y:Euc n)+s•v)).hasFDerivAt.comp_hasDerivAt s
      (HasDerivAt.const_add (y:Euc n) ((hasDerivAt_id s).smul_const v))
  change deriv (fun t ↦ phaseMollification E k ((y:Euc n)+t•v)) s = _
  simpa only [Function.comp_def,id_eq,one_smul] using hd.deriv

theorem mollifiedNormalProfile_flux_defect {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {v : Euc n} (hv : ‖v‖ = 1)
    {k : Euc n → ℝ} (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k)
    (hp : ∀ x, 0 ≤ k x) (hu : ∫ x, k x = 1)
    {a b ε R : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+ε < b)
    (hs : Function.support k ⊆ Metric.ball 0 ε)
    (hphase : ∀ᵐ x ∂volume, x ∈ Metric.ball 0 R → a < |inner ℝ v x| →
      (x ∈ E ↔ inner ℝ v x < 0))
    (y : normalPlane v) (hy : ‖y‖+b+ε ≤ R) :
    let q := mollifiedNormalProfile E k v y
    0 ≤ (∫ s in (-b)..b, s^2*(-deriv q s))-(-b+∫ s in (-b)..b, q s)^2 ∧
    (∫ s in (-b)..b, s^2*(-deriv q s))-(-b+∫ s in (-b)..b, q s)^2 ≤
      4*b*(∫ s in (-b)..b, q s*(1-q s))+
        8*b^2*(∫ s in (-b)..b, max (deriv q s) 0) := by
  dsimp only
  have hself : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq,hv]; norm_num
  have ho : inner ℝ v (y:Euc n) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property
  have hl : mollifiedNormalProfile E k v y (-b) = 1 := by
    apply phaseMollification_lower_cap hv hu ha hs hphase
    · have h := norm_add_le (y:Euc n) ((-b)•v)
      rw [norm_smul,hv,mul_one,Real.norm_eq_abs,abs_neg,abs_of_nonneg hb] at h
      change ‖(y:Euc n)‖+b+ε ≤ R at hy
      linarith
    · rw [inner_add_right,real_inner_smul_right,ho,hself,mul_one,zero_add]
      linarith
  have hr : mollifiedNormalProfile E k v y b = 0 := by
    apply phaseMollification_upper_cap hv ha hs hphase
    · have h := norm_add_le (y:Euc n) (b•v)
      rw [norm_smul,hv,mul_one,Real.norm_eq_abs,abs_of_nonneg hb] at h
      change ‖(y:Euc n)‖+b+ε ≤ R at hy
      linarith
    · rw [inner_add_right,real_inner_smul_right,ho,hself,mul_one,zero_add]
      exact hab
  have he := fiber_flux_height_defect
    ((mollifiedNormalProfile_contDiff hE hk hc v y).of_le (by simp))
    (by linarith : -b ≤ b) hl hr (fun s _ ↦
      phaseMollification_mem_Icc hE (hk.continuous.integrable_of_hasCompactSupport hc) hp hu _)
  simpa only [show 2*(b- -b) = 4*b by ring, show 2*(b- -b)^2 = 8*b^2 by ring] using he

end RPISingularHarnack

end

end OAI
