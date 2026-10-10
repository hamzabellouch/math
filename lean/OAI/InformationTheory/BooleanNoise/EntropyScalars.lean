import OAI.InformationTheory.BooleanNoise.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

theorem ell_lt_one : ell < 1 := by
  have h := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

@[simp] theorem psi_zero : psi 0 = 0 := by norm_num [psi]
@[simp] theorem psi_one : psi 1 = ell := by norm_num [psi, ell]

@[simp] theorem psi_neg (v : ℝ) : psi (-v) = psi v := by
  simp only [psi, sub_eq_add_neg, neg_neg]
  ring

@[simp] theorem psi_neg_one : psi (-1) = ell := by rw [psi_neg, psi_one]

@[simp] theorem entropy_zero : entropy 0 = ell := by simp [entropy]
@[simp] theorem entropy_one : entropy 1 = 0 := by simp [entropy]
@[simp] theorem entropy_neg (v : ℝ) : entropy (-v) = entropy v := by simp [entropy]
@[simp] theorem entropy_neg_one : entropy (-1) = 0 := by simp

theorem entropy_eq_binEntropy (v : ℝ) :
    entropy v = Real.binEntropy ((1 + v) / 2) := by
  have hs (t : ℝ) : Real.negMulLog (t / 2) =
      -(t / 2) * Real.log t + (t / 2) * ell := by
    calc
      _ = (2 : ℝ)⁻¹ * Real.negMulLog t + t * Real.negMulLog ((2 : ℝ)⁻¹) := by
        simpa [div_eq_mul_inv] using Real.negMulLog_mul t ((2 : ℝ)⁻¹)
      _ = _ := by simp [Real.negMulLog, ell, Real.log_inv]; ring
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [show 1 - (1 + v) / 2 = (1 - v) / 2 by ring, hs, hs]
  unfold entropy psi
  ring

theorem continuous_entropy : Continuous entropy := by
  have h : entropy = fun v => Real.binEntropy ((1 + v) / 2) :=
    funext entropy_eq_binEntropy
  rw [h]
  fun_prop

theorem continuous_psi : Continuous psi := by
  have h : psi = fun v => ell - entropy v := by ext v; simp [entropy]
  rw [h]
  exact continuous_const.sub continuous_entropy

theorem psi_nonneg (v : ℝ) : 0 ≤ psi v := by
  have h := Real.binEntropy_le_log_two (p := (1 + v) / 2)
  rw [← entropy_eq_binEntropy] at h
  unfold entropy ell at *
  linarith

theorem entropy_le_ell (v : ℝ) : entropy v ≤ ell := by
  exact sub_le_self _ (psi_nonneg v)

theorem entropy_nonneg {v : ℝ} (hv : v ∈ Icc (-1) 1) : 0 ≤ entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_nonneg (by linarith [hv.1]) (by linarith [hv.2])

theorem entropy_pos {v : ℝ} (hv : v ∈ Ioo (-1) 1) : 0 < entropy v := by
  rw [entropy_eq_binEntropy]
  exact Real.binEntropy_pos (by linarith [hv.1]) (by linarith [hv.2])

theorem psi_le_ell {v : ℝ} (hv : v ∈ Icc (-1) 1) : psi v ≤ ell := by
  have := entropy_nonneg hv
  unfold entropy at this
  linarith

theorem psi_lt_ell {v : ℝ} (hv : v ∈ Ioo (-1) 1) : psi v < ell := by
  have := entropy_pos hv
  unfold entropy at this
  linarith

theorem strictMonoOn_psi : StrictMonoOn psi (Icc 0 1) := by
  intro x hx y hy hxy
  have h := Real.binEntropy_strictAntiOn
    (show (1 + x) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hx.1, hx.2])
    (show (1 + y) / 2 ∈ Icc ((2 : ℝ)⁻¹) 1 by constructor <;> linarith [hy.1, hy.2])
    (show (1 + x) / 2 < (1 + y) / 2 by linarith)
  rw [← entropy_eq_binEntropy, ← entropy_eq_binEntropy] at h
  unfold entropy at h
  linarith

theorem concaveOn_entropy : ConcaveOn ℝ (Icc (-1) 1) entropy := by
  refine ⟨convex_Icc (-1) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (1 + x) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hy' : (1 + y) / 2 ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hy.1, hy.2]
  have h := Real.strictConcave_binEntropy.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at h ⊢
  rw [entropy_eq_binEntropy, entropy_eq_binEntropy, entropy_eq_binEntropy]
  convert h using 1
  congr 1
  nlinarith

theorem convexOn_psi : ConvexOn ℝ (Icc (-1) 1) psi := by
  have h := concaveOn_entropy.neg.add (convexOn_const ell (convex_Icc (-1 : ℝ) 1))
  convert h using 1
  ext v
  simp [entropy]

theorem artanh_eq_log_sub {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    Real.artanh v = (Real.log (1 + v) - Real.log (1 - v)) / 2 := by
  rw [Real.artanh_eq_half_log ⟨hv.1.le, hv.2.le⟩,
    Real.log_div (by linarith [hv.1]) (by linarith [hv.2])]
  ring

theorem hasDerivAt_psi {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt psi (Real.artanh v) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have h1 := ((Real.hasDerivAt_mul_log hp).comp v
    ((hasDerivAt_id v).const_add 1)).div_const 2
  have h2 := ((Real.hasDerivAt_mul_log hm).comp v
    ((hasDerivAt_id v).const_sub 1)).div_const 2
  convert h1.add h2 using 1
  · ext u
    dsimp [psi]
    ring
  · rw [artanh_eq_log_sub hv]
    ring

theorem hasDerivAt_entropy {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt entropy (-Real.artanh v) v := by
  exact (hasDerivAt_psi hv).const_sub ell

theorem hasDerivAt_artanh {v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - v ^ 2)) v := by
  have hp : 1 + v ≠ 0 := by linarith [hv.1]
  have hm : 1 - v ≠ 0 := by linarith [hv.2]
  have hq : 1 - v ^ 2 ≠ 0 := by
    have hp' : 0 < 1 + v := by linarith [hv.1]
    have hm' : 0 < 1 - v := by linarith [hv.2]
    nlinarith [mul_pos hp' hm']
  have h := ((((hasDerivAt_id v).const_add 1).log hp).sub
    (((hasDerivAt_id v).const_sub 1).log hm)).div_const 2
  have he : Real.artanh =ᶠ[𝓝 v]
      (fun u => (Real.log (1 + u) - Real.log (1 - u)) / 2) := by
    filter_upwards [Ioo_mem_nhds hv.1 hv.2] with u hu
    exact artanh_eq_log_sub hu
  apply (h.congr_of_eventuallyEq he).congr_deriv
  change (1 / (1 + v) - -1 / (1 - v)) / 2 = 1 / (1 - v ^ 2)
  field_simp [hp, hm, hq]
  ring

end LeanBlast.CourtadeKumar

end

end OAI
