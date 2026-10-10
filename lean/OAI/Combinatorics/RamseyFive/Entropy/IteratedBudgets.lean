import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.StageNumerics
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalStageArithmetic
import OAI.Combinatorics.RamseyFive.Geometry.CompressionRecurrence

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

def iterD (σ η : ℝ) : ℕ→ℝ
  | 0 => σ^beta η*(1+10*σ*σ^(-η))
  | n+1 => σ^beta η*(1+iterD σ η n*σ^(-η/3)+
      domainSlackConstant*iterD σ η n*σ^(6*beta η)*σ^(-η))
def iterA (σ η : ℝ) : ℕ→ℝ
  | 0 => 0
  | n+1 => iterD σ η n*σ^(-η/3)
def iterDelta (σ η : ℝ) : ℕ→ℝ
  | 0 => 10*σ
  | n+1 => domainSlackConstant*iterD σ η n*σ^(6*beta η)
lemma iterD_eq (σ η : ℝ) (n : ℕ) :
    iterD σ η n=σ^beta η*(1+iterA σ η n+iterDelta σ η n*σ^(-η)) := by
  cases n  <;> simp [iterD,iterA,iterDelta]
lemma iter_budgets_nonneg {σ η : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    σ^beta η ≤ iterD σ η n ∧ 0 ≤ iterA σ η n ∧ 0 ≤ iterDelta σ η n := by
  have hC:=domainSlackConstant_pos.le
  have hb:=Real.rpow_nonneg hσ (beta η)
  induction n with
  | zero => dsimp [iterD,iterA,iterDelta];constructor
            · have hh : 0 ≤ 10*σ*σ^(-η) := by positivity
              nlinarith
            · constructor  <;> positivity
  | succ n ih =>
    have hd : 0 ≤ iterD σ η n := hb.trans ih.1
    have hA : 0 ≤ iterD σ η n*σ^(-η/3) := by positivity
    have hΔ : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η) := by positivity
    dsimp only [iterD,iterA,iterDelta]
    refine ⟨?_,hA,hΔ⟩
    have hh : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η)*σ^(-η) := by positivity
    nlinarith

theorem eventually_iterD_range {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop,∀n,iterD σ η n ≤ σ^(1-η/2) := by
  have he0 : 0 < η/2-beta η := by unfold beta;linarith
  have he1 : 0 < 1-η/2-2*beta η := by unfold beta;linarith
  have ht0 : Tendsto (fun σ : ℝ=>11*σ^(-(η/2-beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop he0).const_mul 11
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht0.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    (tendsto_rpow_neg_atTop he1).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    (tendsto_rpow_neg_atTop (by linarith : 0 < η/4)).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    eventually_stage_recurrence hη domainSlackConstant domainSlackConstant_pos.le]
    with σ hσ h0 h1 hratio hrec
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hbase : σ^(2*beta η) ≤ (1/2)*σ^(1-η/2) := by
    have hh:=mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid : σ^(-(1-η/2-2*beta η))*σ^(1-η/2)=σ^(2*beta η) := by
      rw [←Real.rpow_add hs];congr 1;ring
    rwa [hid] at hh
  have hr : σ^(-η/4) ≤ (1:ℝ)/2 := by simpa only [neg_div] using hratio.le
  intro n
  induction n with
  | zero =>
    have hpow : 1 ≤ σ^(1-η) := Real.one_le_rpow hσ (by linarith)
    have hid : 10*σ*σ^(-η)=10*σ^(1-η) := by rw [Real.rpow_sub hs,Real.rpow_one,Real.rpow_neg hs.le];ring
    have hinit : iterD σ η 0 ≤ 11*σ^(1-η+beta η) := by
      dsimp [iterD]
      rw [hid]
      calc
        _  ≤  σ^beta η*(11*σ^(1-η)) := by gcongr;nlinarith
        _ = _ := by rw [mul_left_comm,←Real.rpow_add hs];congr 2;ring
    apply hinit.trans
    have hh:=mul_le_mul_of_nonneg_right h0.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid' : (11*σ^(-(η/2-beta η)))*σ^(1-η/2)=11*σ^(1-η+beta η) := by
      rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    simpa only [hid',one_mul] using hh
  | succ n ih =>
    have hd:=(iter_budgets_nonneg (η:=η) hs.le n).1
    have h:=hrec (iterD σ η n) (iterA σ η (n+1)) (iterDelta σ η (n+1))
      ((Real.rpow_nonneg hs.le _).trans hd) le_rfl le_rfl
    rw [←iterD_eq] at h
    calc
      _  ≤  σ^(2*beta η)+iterD σ η n*σ^(-η/4) := h
      _  ≤  (1/2)*σ^(1-η/2)+σ^(1-η/2)*(1/2) := by gcongr
      _ = _ := by ring

theorem eventually_iter_terminal {η : ℝ} (hη : 0 < η) (hη' : η < 1/10)
    (m : ℕ) (hm : 1 ≤ η*(m:ℝ)/4) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,iterA σ η (m+1) ≤ 1 ∧ iterDelta σ η (m+1) ≤ c/9600*σ^η := by
  have ha : 0 < η/3-2*beta η := by unfold beta;linarith
  have hb : 0 < η-8*beta η := by unfold beta;linarith
  have htA : Tendsto (fun σ : ℝ=>2*σ^(-(η/3-2*beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop ha).const_mul 2
  have htB : Tendsto (fun σ : ℝ=>2*domainSlackConstant*σ^(-(η-8*beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop hb).const_mul (2*domainSlackConstant)
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_iterD_range hη hη',
    (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<2) (beta_pos hη))).eventually_ge_atTop 2,
    (tendsto_rpow_neg_atTop (by linarith : 0 < η/4)).eventually_lt_const (by norm_num : (0:ℝ) < 1/3),
    eventually_stage_recurrence hη domainSlackConstant domainSlackConstant_pos.le,
    htA.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    htB.eventually_lt_const (by positivity : (0:ℝ) < c/9600)]
    with σ hσ hrange hpow hratio hrec hA hB
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hinit : iterD σ η 0 ≤ σ := (hrange 0).trans (by
    conv_rhs => rw [←Real.rpow_one σ]
    exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith))
  have hh:=compression_recurrence_terminal σ η (beta η) m (iterD σ η) hσ hη (beta_pos hη).le
    hpow (by simpa only [neg_div] using hratio.le) hm hinit (fun n=>by
      rw [iterD_eq σ η (n+1)]
      exact hrec _ _ _ ((Real.rpow_nonneg hs.le _).trans (iter_budgets_nonneg (η:=η) hs.le n).1) le_rfl le_rfl)
  constructor
  · calc
      iterA σ η (m+1) ≤ (2*σ^(2*beta η))*σ^(-η/3) := by dsimp [iterA];gcongr
      _ = 2*σ^(-(η/3-2*beta η)) := by rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
      _  ≤  1 := hA.le
  · calc
      iterDelta σ η (m+1) ≤ domainSlackConstant*(2*σ^(2*beta η))*σ^(6*beta η) := by
        dsimp [iterDelta];gcongr;exact domainSlackConstant_pos.le
      _ = (2*domainSlackConstant*σ^(-(η-8*beta η)))*σ^η := by
        rw [show domainSlackConstant*(2*σ^(2*beta η))*σ^(6*beta η)=
          2*domainSlackConstant*(σ^(2*beta η)*σ^(6*beta η)) by ring,
          ←Real.rpow_add hs]
        rw [show (2*domainSlackConstant*σ^(-(η-8*beta η)))*σ^η=
          2*domainSlackConstant*(σ^(-(η-8*beta η))*σ^η) by ring,←Real.rpow_add hs]
        congr 2;ring
      _  ≤  c/9600*σ^η := by gcongr
end
end SharpRamseyFive.ParameterHierarchy

end OAI
