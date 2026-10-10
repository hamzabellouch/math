import OAI.NumberTheory.JointDickman.Amplification.InteriorAmplificationMass
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

namespace OAI

/-! # A fixed smooth cutoff equal to one on the positive interior rectangle -/

namespace JointDickman
open Finset

noncomputable def amplificationBump : ContDiffBump (11/8 : ℝ) where
  rIn := 1/8
  rOut := 1/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem amplificationBump_bounds (x : ℝ) : 0 ≤ amplificationBump x ∧ amplificationBump x ≤ 1 :=
  ⟨amplificationBump.nonneg, amplificationBump.le_one⟩

theorem amplificationBump_one {x : ℝ} (hx : x ∈ Set.Icc (5/4 : ℝ) (3/2)) :
    amplificationBump x = 1 := by
  apply amplificationBump.one_of_mem_closedBall
  change dist x (11/8 : ℝ) ≤ (1/8 : ℝ)
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1,hx.2]

theorem amplificationBump_zero {x : ℝ} (hx : x ≤ 1 ∨ 2 ≤ x) : amplificationBump x = 0 := by
  apply amplificationBump.zero_of_le_dist
  change (1/4 : ℝ) ≤ dist x (11/8 : ℝ)
  rw [Real.dist_eq]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

theorem amplificationBump_support {x : ℝ} (hx : amplificationBump x ≠ 0) : 1 < x ∧ x < 2 := by
  constructor
  · by_contra h
    exact hx (amplificationBump_zero (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hx (amplificationBump_zero (Or.inr (le_of_not_gt h)))

theorem amplificationBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => amplificationBump x) :=
  amplificationBump.contDiff

theorem amplificationBump_compactSupport : HasCompactSupport (fun x => amplificationBump x) :=
  amplificationBump.hasCompactSupport

noncomputable def amplificationSmoothWeight (B T a c : ℕ) : ℝ :=
  amplificationBump (Real.log c / B) * amplificationBump ((a : ℝ) / ((T : ℝ)*c))

theorem amplificationSmoothWeight_bounds (B T a c : ℕ) :
    0 ≤ amplificationSmoothWeight B T a c ∧ amplificationSmoothWeight B T a c ≤ 1 := by
  obtain ⟨h0,h1⟩ := amplificationBump_bounds (Real.log c / B)
  obtain ⟨h0',h1'⟩ := amplificationBump_bounds ((a : ℝ) / ((T : ℝ)*c))
  exact ⟨mul_nonneg h0 h0', (mul_le_mul h1 h1' h0' (by norm_num)).trans_eq (by norm_num)⟩

theorem amplificationSmoothWeight_one {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (hc : c ∈ amplificationInteriorC B) (ha : a ∈ amplificationInteriorA T c) :
    amplificationSmoothWeight B T a c = 1 := by
  obtain ⟨hcl,hcu⟩ := amplificationInteriorC_bounds hc
  have hc0 : (0 : ℝ) < c := (Real.exp_pos _).trans hcl
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 := mul_pos hT0 hc0
  have hlog : Real.log c / B ∈ Set.Icc (5/4 : ℝ) (3/2) := by
    constructor
    · apply (le_div_iff₀ hB0).mpr
      have hh := Real.log_le_log (Real.exp_pos _) hcl.le
      simpa only [Real.log_exp] using hh
    · apply (div_le_iff₀ hB0).mpr
      have hh := Real.log_le_log hc0 hcu
      simpa only [Real.log_exp] using hh
  have hr : (a : ℝ) / ((T : ℝ)*c) ∈ Set.Icc (5/4 : ℝ) (3/2) := by
    obtain ⟨hal,hau⟩ := mem_Ioc.mp ha
    constructor
    · apply (le_div_iff₀ hTC0).mpr
      have hh := (Nat.floor_lt (by positivity : (0 : ℝ) ≤ (5/4 : ℝ)*T*c)).mp hal
      nlinarith only [hh]
    · apply (div_le_iff₀ hTC0).mpr
      have hh := (Nat.le_floor_iff (by positivity : (0 : ℝ) ≤ (3/2 : ℝ)*T*c)).mp hau
      nlinarith only [hh]
  rw [amplificationSmoothWeight, amplificationBump_one hlog, amplificationBump_one hr, one_mul]

theorem amplificationSmoothWeight_one_on_interior {B T a c : ℕ} (hB : 0 < B) (hT : 0 < T)
    (h : (a,c) ∈ amplificationInteriorPairs B T) : amplificationSmoothWeight B T a c = 1 := by
  obtain ⟨d,hd,he⟩ := mem_biUnion.mp h
  obtain ⟨b,hb,he⟩ := mem_image.mp he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact amplificationSmoothWeight_one hB hT hd hb

open Classical in
theorem amplificationSmoothWeight_support {B T : ℕ} (hB : 0 < B) (hT : 0 < T)
    (a c : ℕ) (h : (a,c) ∉ amplificationCoefficientPairs B T) :
    amplificationSmoothWeight B T a c = 0 := by
  by_contra hn
  have hs := mul_ne_zero_iff.mp hn
  obtain ⟨hcl,hcu⟩ := amplificationBump_support hs.1
  obtain ⟨hal,hau⟩ := amplificationBump_support hs.2
  have hc : 0 < c := by
    by_contra hc
    have hz : c = 0 := by omega
    subst c
    norm_num at hcl
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hTC0 := mul_pos hT0 hc0
  apply h
  apply (mem_amplificationCoefficientPairs hB).mpr
  have hcl' : (B : ℝ) < Real.log c := by
    have hh := (lt_div_iff₀ hB0).mp hcl
    simpa only [one_mul] using hh
  have hcu' := (div_lt_iff₀ hB0).mp hcu
  have hal' := (lt_div_iff₀ hTC0).mp hal
  have hau' := (div_lt_iff₀ hTC0).mp hau
  refine ⟨?_,?_,?_,?_⟩
  · exact (Real.exp_le_exp.mpr hcl'.le).trans_eq (Real.exp_log hc0)
  · exact (Real.exp_log hc0).symm.trans_le (Real.exp_le_exp.mpr hcu'.le)
  · exact_mod_cast (by simpa only [one_mul] using hal'.le : (T : ℝ)*c ≤ a)
  · have hh : (a : ℝ) < (2*T*c : ℕ) := by push_cast; nlinarith only [hau']
    exact_mod_cast hh

end JointDickman

end OAI
