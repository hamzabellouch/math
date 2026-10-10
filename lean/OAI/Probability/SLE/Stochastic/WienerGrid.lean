import OAI.Probability.SLE.Stochastic.WienerBridge
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! The uniform grid and its linear interpolation, used only to prove
the finite-window support of the actual Wiener law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def wienerGridTime (n k : ℕ) : ℝ≥0 := (k:ℝ≥0)/(n+1:ℝ≥0)

def wienerGridCell (n : ℕ) (t : unitInterval) : ℕ :=
  ⌊(n+1:ℝ)*(t:ℝ)⌋₊

def wienerGridWeight (n : ℕ) (t : unitInterval) : ℝ :=
  (n+1:ℝ)*(t:ℝ)-wienerGridCell n t

lemma wienerGridCell_le (n : ℕ) (t : unitInterval) :
    wienerGridCell n t ≤ n+1 := by
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [t.2.2]

lemma wienerGridWeight_mem (n : ℕ) (t : unitInterval) :
    wienerGridWeight n t ∈ Ico (0:ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg (by positivity) t.2.1))
  · have h := Nat.lt_floor_add_one ((n+1:ℝ)*(t:ℝ))
    change _ < (wienerGridCell n t:ℝ)+1 at h
    unfold wienerGridWeight
    linarith

lemma wienerGrid_bracket (n : ℕ) (t : unitInterval) :
    (wienerGridTime n (wienerGridCell n t):ℝ) ≤ t ∧
    (t:ℝ) ≤ wienerGridTime n (wienerGridCell n t+1) := by
  have hN : (0:ℝ)<n+1 := by positivity
  change ((wienerGridCell n t:ℝ)/(n+1) ≤ t) ∧
    ((t:ℝ) ≤ ((wienerGridCell n t+1:ℕ):ℝ)/(n+1))
  constructor
  · rw [div_le_iff₀ hN]
    have h := Nat.floor_le (mul_nonneg hN.le t.2.1)
    change (wienerGridCell n t:ℝ) ≤ (n+1:ℝ)*(t:ℝ) at h
    nlinarith
  · rw [le_div_iff₀ hN]
    push_cast
    have h := Nat.lt_floor_add_one ((n+1:ℝ)*(t:ℝ))
    change _ < (wienerGridCell n t:ℝ)+1 at h
    nlinarith

lemma wienerGrid_affine (n : ℕ) (t : unitInterval) :
    (1-wienerGridWeight n t)*(wienerGridTime n (wienerGridCell n t):ℝ)+
      wienerGridWeight n t*(wienerGridTime n (wienerGridCell n t+1):ℝ) = t := by
  change (1-((n+1:ℝ)*(t:ℝ)-wienerGridCell n t))*((wienerGridCell n t:ℝ)/(n+1))+
    ((n+1:ℝ)*(t:ℝ)-wienerGridCell n t)*(((wienerGridCell n t+1:ℕ):ℝ)/(n+1))=t
  push_cast
  field_simp
  ring

lemma wienerGrid_gap (n k : ℕ) :
    (wienerGridTime n (k+1):ℝ)-(wienerGridTime n k:ℝ) = 1/(n+1:ℝ) := by
  change ((k+1:ℕ):ℝ)/(n+1)-(k:ℝ)/(n+1)=1/(n+1:ℝ)
  push_cast
  ring

def wienerGridInterp (n : ℕ) (f : ℝ≥0 → ℝ) (t : unitInterval) : ℝ :=
  (1-wienerGridWeight n t)*f (wienerGridTime n (wienerGridCell n t))+
    wienerGridWeight n t*f (wienerGridTime n (wienerGridCell n t+1))

lemma wienerGridInterp_error (n : ℕ) (f : ℝ≥0 → ℝ) (t : unitInterval)
    {ε : ℝ}
    (ha : |f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t))| ≤ ε)
    (hb : |f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t+1))| ≤ ε) :
    |f ⟨t,t.2.1⟩-wienerGridInterp n f t| ≤ ε := by
  have hw := wienerGridWeight_mem n t
  have he : f ⟨t,t.2.1⟩-wienerGridInterp n f t =
      (1-wienerGridWeight n t)*(f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t)))+
      wienerGridWeight n t*(f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t+1))) := by
    unfold wienerGridInterp
    ring
  rw [he]
  calc
    _ ≤ |(1-wienerGridWeight n t)*(f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t)))|+
        |wienerGridWeight n t*(f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t+1)))| := abs_add_le _ _
    _ = (1-wienerGridWeight n t)*|f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t))|+
        wienerGridWeight n t*|f ⟨t,t.2.1⟩-f (wienerGridTime n (wienerGridCell n t+1))| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hw.2.le),abs_of_nonneg hw.1]
    _ ≤ (1-wienerGridWeight n t)*ε+wienerGridWeight n t*ε :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw.2.le))
        (mul_le_mul_of_nonneg_left hb hw.1)
    _ = ε := by ring

lemma wienerGridTime_mono (n : ℕ) : Monotone (wienerGridTime n) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity)

lemma wienerGridTime_mem (n k : ℕ) (hk : k ≤ n+2) :
    wienerGridTime n k ∈ Icc (0:ℝ≥0) 2 := by
  refine ⟨zero_le,?_⟩
  apply NNReal.coe_le_coe.mp
  change (k:ℝ)/(n+1) ≤ 2
  rw [div_le_iff₀ (by positivity : (0:ℝ)<n+1)]
  have h : (k:ℝ) ≤ (n+2:ℕ) := by exact_mod_cast hk
  push_cast at h
  nlinarith

lemma wienerGrid_dist_left (n : ℕ) (t : unitInterval) :
    dist (⟨t,t.2.1⟩:ℝ≥0) (wienerGridTime n (wienerGridCell n t)) ≤ 1/(n+1:ℝ) := by
  have h := wienerGrid_bracket n t
  change |(t:ℝ)-(wienerGridTime n (wienerGridCell n t):ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  have hg := wienerGrid_gap n (wienerGridCell n t)
  linarith

lemma wienerGrid_dist_right (n : ℕ) (t : unitInterval) :
    dist (⟨t,t.2.1⟩:ℝ≥0) (wienerGridTime n (wienerGridCell n t+1)) ≤ 1/(n+1:ℝ) := by
  have h := wienerGrid_bracket n t
  change |(t:ℝ)-(wienerGridTime n (wienerGridCell n t+1):ℝ)| ≤ _
  rw [abs_of_nonpos (sub_nonpos.mpr h.2)]
  have hg := wienerGrid_gap n (wienerGridCell n t)
  linarith

lemma wienerGridInterp_uniform (f : ℝ≥0 → ℝ)
    (hf : ContinuousOn f (Icc 0 2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : unitInterval,
      |f ⟨t,t.2.1⟩-wienerGridInterp n f t| ≤ ε := by
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) ε hε
  filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hδ)] with n hn t
  have ht : (⟨t,t.2.1⟩:ℝ≥0) ∈ Icc (0:ℝ≥0) 2 := by
    refine ⟨zero_le,?_⟩
    apply NNReal.coe_le_coe.mp
    change (t:ℝ) ≤ 2
    linarith [t.2.2]
  apply wienerGridInterp_error
  · have h := hmod _ ht _ (wienerGridTime_mem n _ ((wienerGridCell_le n t).trans (by omega)))
      ((wienerGrid_dist_left n t).trans_lt hn)
    exact (by simpa only [Real.dist_eq] using h.le)
  · have h := hmod _ ht _ (wienerGridTime_mem n _ (by have := wienerGridCell_le n t; omega))
      ((wienerGrid_dist_right n t).trans_lt hn)
    exact (by simpa only [Real.dist_eq] using h.le)

lemma wienerGridInterp_sub (n : ℕ) (f g : ℝ≥0 → ℝ) (t : unitInterval) :
    wienerGridInterp n f t-wienerGridInterp n g t =
      wienerGridInterp n (fun s => f s-g s) t := by
  unfold wienerGridInterp
  ring

lemma wienerGridInterp_difference (n : ℕ) (f g : ℝ≥0 → ℝ) (t : unitInterval)
    {ε : ℝ}
    (h : ∀ k ≤ n+2, |f (wienerGridTime n k)-g (wienerGridTime n k)| ≤ ε) :
    |wienerGridInterp n f t-wienerGridInterp n g t| ≤ ε := by
  rw [wienerGridInterp_sub]
  have hw := wienerGridWeight_mem n t
  have ha := h (wienerGridCell n t) ((wienerGridCell_le n t).trans (by omega))
  have hb := h (wienerGridCell n t+1) (by have := wienerGridCell_le n t; omega)
  unfold wienerGridInterp
  calc
    _ ≤ |(1-wienerGridWeight n t)*(f (wienerGridTime n (wienerGridCell n t))-g (wienerGridTime n (wienerGridCell n t)))|+
        |wienerGridWeight n t*(f (wienerGridTime n (wienerGridCell n t+1))-g (wienerGridTime n (wienerGridCell n t+1)))| := abs_add_le _ _
    _ = (1-wienerGridWeight n t)*|f (wienerGridTime n (wienerGridCell n t))-g (wienerGridTime n (wienerGridCell n t))|+
        wienerGridWeight n t*|f (wienerGridTime n (wienerGridCell n t+1))-g (wienerGridTime n (wienerGridCell n t+1))| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hw.2.le),abs_of_nonneg hw.1]
    _ ≤ (1-wienerGridWeight n t)*ε+wienerGridWeight n t*ε :=
      add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr hw.2.le))
        (mul_le_mul_of_nonneg_left hb hw.1)
    _ = ε := by ring

end SLEExactGauge

end

end OAI
