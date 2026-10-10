import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakStripScale

namespace OAI

/-! A dyadic cutoff comparable with the square of the height, with the
precise height-to-length margin needed by the phase estimate. -/
namespace TwoPointCorrelations

noncomputable def halaszDyadicCutoffDegree (L : ℝ) : ℕ := ⌈2*L/Real.log 2⌉₊+1

lemma halasz_dyadic_cutoff_bounds {L : ℝ} (hL : 100≤ L) :
    let K := halaszDyadicCutoffDegree L
    1≤2^K-1 ∧ (K:ℝ)*Real.log 2≤(100/49:ℝ)*L ∧
      (K:ℝ)≤4*L+2 ∧
      (Real.exp L)^2≤((2^K-1:ℕ):ℝ) ∧
      ((2^K-1:ℕ):ℝ)≤4*(Real.exp L)^2 := by
  have hL0 : 0<L := by linarith
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hloglo : (1/2:ℝ)≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hloghi : Real.log 2≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  let K := halaszDyadicCutoffDegree L
  have hceil : 2*L/Real.log 2≤(⌈2*L/Real.log 2⌉₊:ℝ) := Nat.le_ceil _
  have hceilhi := Nat.ceil_lt_add_one (show 0≤2*L/Real.log 2 by positivity)
  have hK : (K:ℝ)<2*L/Real.log 2+2 := by dsimp only [K,halaszDyadicCutoffDegree]; push_cast; linarith
  have hKlo : 2*L+Real.log 2≤(K:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_right hceil hlog.le
    have he : 2*L/Real.log 2*Real.log 2=2*L := by field_simp
    rw [he] at hh
    dsimp only [K,halaszDyadicCutoffDegree]
    push_cast
    linarith
  have hKhi : (K:ℝ)*Real.log 2≤2*L+2*Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right hK hlog
    have he : (2*L/Real.log 2+2)*Real.log 2=2*L+2*Real.log 2 := by field_simp
    rw [he] at hh
    exact hh.le
  have hKlinear : (K:ℝ)≤4*L+2 := by
    have hq : 2*L/Real.log 2≤4*L := (div_le_iff₀ hlog).mpr (by nlinarith)
    linarith
  have hpow : ((2^K:ℕ):ℝ)=Real.exp ((K:ℝ)*Real.log 2) := by
    push_cast
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  have hexp (y : ℝ) : Real.exp (2*y)=(Real.exp y)^2 := by
    rw [two_mul,Real.exp_add,pow_two]
  have hpowlo : 2*(Real.exp L)^2≤((2^K:ℕ):ℝ) := by
    rw [hpow]
    have hh := Real.exp_le_exp.mpr hKlo
    have he : Real.exp (2*L+Real.log 2)=2*(Real.exp L)^2 := by
      rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),hexp]
      ring
    rwa [he] at hh
  have hpowhi : ((2^K:ℕ):ℝ)≤4*(Real.exp L)^2 := by
    rw [hpow]
    have hh := Real.exp_le_exp.mpr hKhi
    have he : Real.exp (2*L+2*Real.log 2)=4*(Real.exp L)^2 := by
      rw [Real.exp_add,hexp,hexp,Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring
    rwa [he] at hh
  have hE : 1≤ Real.exp L := Real.one_le_exp_iff.mpr (by linarith)
  have hNcast : ((2^K-1:ℕ):ℝ)=((2^K:ℕ):ℝ)-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow K 2 (by norm_num)),Nat.cast_one]
  have hN : 1≤2^K-1 := by
    have hh : (1:ℝ)≤((2^K-1:ℕ):ℝ) := by rw [hNcast]; nlinarith
    exact_mod_cast hh
  refine ⟨hN,by nlinarith,hKlinear,?_,?_⟩
  · rw [hNcast]
    nlinarith
  · rw [hNcast]
    linarith

end TwoPointCorrelations

end OAI
