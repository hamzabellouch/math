import OAI.NumberTheory.JointDickman.Arithmetic.SmoothArithmeticFeatures
import OAI.NumberTheory.JointDickman.Arithmetic.SmoothDyadicPartition
import OAI.NumberTheory.JointDickman.Arithmetic.AmplificationSmoothCutoff

namespace OAI

/-! # The actual amplification weight in normalized geometric-box coordinates -/

namespace JointDickman
open scoped Topology

noncomputable def amplificationSpatialProfile (x y z : ℝ) : ℝ :=
  amplificationBump (x/z)*amplificationBump (y/z)*dyadicPartitionWeight z

noncomputable def amplificationTensorProfile (v : Fin 4 → ℝ) : ℝ :=
  amplificationBump (v 3)*amplificationSpatialProfile (v 0) (v 1) (v 2)

noncomputable def amplificationBoxWeight (B : ℕ) (s x y z : ℝ) : ℝ :=
  amplificationBump (s+Real.log z/B)*amplificationSpatialProfile x y z

theorem amplificationTensorProfile_continuous :
    ContinuousOn amplificationTensorProfile tensorParameterBox := by
  have hv (i : Fin 4) : ContinuousOn (fun v : Fin 4 → ℝ => v i) tensorParameterBox :=
    (continuous_apply i).continuousOn
  have hz : ∀ v ∈ tensorParameterBox, v 2 ≠ 0 := by
    intro v hv
    have hh : (1/4 : ℝ) ≤ v 2 := hv.1 2
    linarith
  exact (amplificationBump.continuous.comp_continuousOn (hv 3)).mul
    (((amplificationBump.continuous.comp_continuousOn ((hv 0).div (hv 2) hz)).mul
      (amplificationBump.continuous.comp_continuousOn ((hv 1).div (hv 2) hz))).mul
      (dyadicPartitionWeight_smooth.continuous.comp_continuousOn (hv 2)))

theorem amplificationSpatialProfile_bounds (x y z : ℝ) :
    0 ≤ amplificationSpatialProfile x y z ∧ amplificationSpatialProfile x y z ≤ 1 := by
  obtain ⟨ha,ha'⟩ := amplificationBump_bounds (x/z)
  obtain ⟨hb,hb'⟩ := amplificationBump_bounds (y/z)
  obtain ⟨hc,hc'⟩ := dyadicPartitionWeight_bounds z
  exact ⟨mul_nonneg (mul_nonneg ha hb) hc,
    (mul_le_mul (mul_le_mul ha' hb' hb zero_le_one) hc' hc (by norm_num)).trans_eq (by ring)⟩

theorem amplificationSpatialProfile_support {x y z : ℝ}
    (h : amplificationSpatialProfile x y z ≠ 0) : x ∈ Set.Icc (1/2 : ℝ) 4 ∧ y ∈ Set.Icc (1/2 : ℝ) 4 ∧
      z ∈ Set.Icc (1/2 : ℝ) 2 := by
  have hprod : amplificationBump (x/z)*amplificationBump (y/z) ≠ 0 :=
    left_ne_zero_of_mul h
  have hx := amplificationBump_support (left_ne_zero_of_mul hprod)
  have hy := amplificationBump_support (right_ne_zero_of_mul hprod)
  have hz : dyadicPartitionWeight z ≠ 0 := right_ne_zero_of_mul h
  have hzlo : (1/2 : ℝ) < z := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inl (le_of_not_gt hn)))
  have hzhi : z ≤ 2 := by
    by_contra hn
    exact hz (dyadicPartitionWeight_zero (Or.inr (lt_of_not_ge hn)))
  have hzpos : 0 < z := by linarith
  have hxb : x ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hx.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hx.2
      nlinarith
  have hyb : y ∈ Set.Icc (1/2 : ℝ) 4 := by
    constructor
    · have he := (lt_div_iff₀ hzpos).mp hy.1
      nlinarith
    · have he := (div_lt_iff₀ hzpos).mp hy.2
      nlinarith
  exact ⟨hxb,hyb,⟨hzlo.le,hzhi⟩⟩

theorem amplificationSpatialProfile_cutoff {x y z : ℝ}
    (h : amplificationSpatialProfile x y z ≠ 0) : tensorCutoff x y z = 1 := by
  obtain ⟨hx,hy,hz⟩ := amplificationSpatialProfile_support h
  rw [tensorCutoff,tensorBoxBump_one hx,tensorBoxBump_one hy,
    tensorBoxBump_one ⟨hz.1,hz.2.trans (by norm_num)⟩]
  norm_num

theorem amplificationTensorProfile_cutoff (s x y z : ℝ) :
    amplificationTensorProfile ![x,y,z,s]*tensorCutoff x y z =
      amplificationTensorProfile ![x,y,z,s] := by
  by_cases h : amplificationSpatialProfile x y z = 0
  · simp [amplificationTensorProfile,h]
  · rw [amplificationSpatialProfile_cutoff h,mul_one]

theorem amplificationBump_lipschitz :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : ℝ, |amplificationBump y-amplificationBump x| ≤ D*|y-x| := by
  let w := amplificationBump_compactSupport.toSchwartzMap amplificationBump_contDiff
  obtain ⟨_,D,_,hD,_,hd,_⟩ := schwartz_value_derivative_bounds w
  refine ⟨D,hD,?_⟩
  intro x y
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := (w : ℝ → ℝ)) (f' := deriv w) (s := Set.univ)
    (fun x _ => (w.hasDerivAt x).hasDerivWithinAt)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hd x)
    convex_univ (Set.mem_univ x) (Set.mem_univ y)
  have heq (z : ℝ) : w z = amplificationBump z := rfl
  rw [heq,heq] at he
  simpa only [Real.norm_eq_abs] using he

theorem amplificationBoxWeight_freezing :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 0 < B → ∀ s x y z : ℝ,
      |amplificationBoxWeight B s x y z-amplificationTensorProfile ![x,y,z,s]| ≤
        (C/B)*tensorCutoff x y z := by
  obtain ⟨D,hD,hlip⟩ := amplificationBump_lipschitz
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨D*Real.log 2,mul_nonneg hD hlog2,?_⟩
  intro B hB s x y z
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  change |amplificationBump (s+Real.log z/B)*amplificationSpatialProfile x y z-
    amplificationBump s*amplificationSpatialProfile x y z| ≤ _
  by_cases h : amplificationSpatialProfile x y z = 0
  · simp only [h,mul_zero,sub_self,abs_zero]
    exact mul_nonneg (div_nonneg (mul_nonneg hD hlog2) hBr.le) (tensorCutoff_nonneg _ _ _)
  · have hcut := amplificationSpatialProfile_cutoff h
    have hz : dyadicPartitionWeight z ≠ 0 := right_ne_zero_of_mul h
    have hzlo : (1/2 : ℝ) < z := by
      by_contra hn
      exact hz (dyadicPartitionWeight_zero (Or.inl (le_of_not_gt hn)))
    have hzhi : z ≤ 2 := by
      by_contra hn
      exact hz (dyadicPartitionWeight_zero (Or.inr (lt_of_not_ge hn)))
    have hzpos : 0 < z := by linarith
    have hlog : |Real.log z| ≤ Real.log 2 := by
      rw [abs_le]
      constructor
      · have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hzlo.le
        rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
        exact hh
      · exact Real.log_le_log hzpos hzhi
    have hdiff := hlip s (s+Real.log z/B)
    rw [add_sub_cancel_left,abs_div,abs_of_pos hBr] at hdiff
    have hmain : |amplificationBump (s+Real.log z/B)-amplificationBump s| ≤ D*Real.log 2/B := by
      exact hdiff.trans (by apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hlog hBr.le) hD).trans_eq; ring)
    have hp := amplificationSpatialProfile_bounds x y z
    rw [← sub_mul,abs_mul,abs_of_nonneg hp.1,hcut,mul_one]
    exact (mul_le_mul hmain hp.2 hp.1 (by positivity)).trans_eq (mul_one _)

end JointDickman

end OAI
