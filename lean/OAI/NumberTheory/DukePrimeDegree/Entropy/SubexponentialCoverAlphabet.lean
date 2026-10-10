import OAI.NumberTheory.DukePrimeDegree.Dynamics.TemperedOrbitWindows
import OAI.NumberTheory.DukePrimeDegree.Entropy.ControlledCoverFuture

namespace OAI

/-! # Subexponential coding cost for a height-bounded covering alphabet -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

def coverAlphabet (J : ℕ → ℕ) (M : ℕ) : Finset ℕ :=
  (Finset.range (M+1)).biUnion (fun m => (Finset.range (J m)).image (Nat.pair m))

lemma mem_coverAlphabet {Y : Type*} (Q H : Y → ℕ) (J : ℕ → ℕ)
    (hcode : ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m))
    {M : ℕ} {x : Y} (hx : H x ≤ M) : Q x ∈ coverAlphabet J M := by
  obtain ⟨j,hj,he⟩ := hcode (H x) (mem_image_of_mem Q rfl)
  apply Finset.mem_biUnion.mpr
  refine ⟨H x,Finset.mem_range.mpr (by omega),?_⟩
  exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,he⟩

lemma coverAlphabet_card_le (J : ℕ → ℕ) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hJ : ∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) (M : ℕ) :
    ((coverAlphabet J M).card : ℝ) ≤ ((M:ℝ)+1)*K*Real.exp (C*(M:ℝ)) := by
  have hc : (coverAlphabet J M).card ≤ ∑ m ∈ Finset.range (M+1), J m := by
    apply Finset.card_biUnion_le.trans
    exact Finset.sum_le_sum fun m _ => (Finset.card_image_le.trans_eq (Finset.card_range _))
  have hr : ((coverAlphabet J M).card:ℝ) ≤ ∑ m ∈ Finset.range (M+1), (J m:ℝ) := by
    exact_mod_cast hc
  apply hr.trans
  calc
    (∑ m ∈ Finset.range (M+1), (J m:ℝ)) ≤
        ∑ _m ∈ Finset.range (M+1), K*Real.exp (C*(M:ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply (hJ m).trans
      apply mul_le_mul_of_nonneg_left _ hK.le
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ hC
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,
      Nat.cast_one]; ring

lemma coverAlphabet_log_card_le (J : ℕ → ℕ) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hJ : ∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ))) (M : ℕ)
    (hne : (coverAlphabet J M).Nonempty) :
    Real.log (coverAlphabet J M).card ≤ Real.log (K+1)+(C+1)*M := by
  have hM : 0 < (M:ℝ)+1 := by positivity
  have hcard : 0 < ((coverAlphabet J M).card:ℝ) := by exact_mod_cast hne.card_pos
  have hc := (coverAlphabet_card_le J hK hC hJ M).trans
    (show ((M:ℝ)+1)*K*Real.exp (C*(M:ℝ)) ≤
      ((M:ℝ)+1)*(K+1)*Real.exp (C*(M:ℝ)) by gcongr; linarith)
  have hl := Real.log_le_log hcard hc
  rw [Real.log_mul (mul_ne_zero hM.ne' (by positivity)) (Real.exp_ne_zero _),
    Real.log_mul hM.ne' (by positivity),Real.log_exp] at hl
  have hlog := Real.log_le_sub_one_of_pos hM
  linarith

/-- Encoding one height-bounded label anywhere in the word costs o(N).
The same alphabet covers every time in the window. -/
theorem ae_coverAlphabet_cost_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H Q : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (J : ℕ → ℕ) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hJ : ∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ)))
    (hcode : ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m)) :
    ∀ᵐ x ∂μ,
      (∀ N k, k ≤ N → Q (T^[k] x) ∈ coverAlphabet J (windowHeight T H N x)) ∧
      Tendsto (fun N : ℕ => Real.log (coverAlphabet J (windowHeight T H N x)).card / N)
        atTop (𝓝 0) := by
  filter_upwards [ae_windowHeight_div_tendsto_zero μ hT H hH hstep] with x hx
  have hmem (N k : ℕ) (hk : k ≤ N) :=
    mem_coverAlphabet Q H J hcode (height_le_windowHeight T H hk x)
  refine ⟨hmem,?_⟩
  have hne (N : ℕ) : (coverAlphabet J (windowHeight T H N x)).Nonempty :=
    ⟨Q (T^[0] x),hmem N 0 (Nat.zero_le N)⟩
  have hmajor : Tendsto (fun N : ℕ =>
      (Real.log (K+1)+(C+1)*(windowHeight T H N x:ℝ))/N) atTop (𝓝 0) := by
    have ha : Tendsto (fun N : ℕ => Real.log (K+1)/(N:ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    convert ha.add (hx.const_mul (C+1)) using 1
    · ext N
      ring
    · norm_num
  apply squeeze_zero' _ _ hmajor
  · apply Eventually.of_forall
    intro N
    apply div_nonneg _ (Nat.cast_nonneg N)
    exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (hne N).card_pos)
  · apply Eventually.of_forall
    intro N
    exact div_le_div_of_nonneg_right (coverAlphabet_log_card_le J hK hC hJ _ (hne N))
      (Nat.cast_nonneg N)

end DukePrimeDegree

end

end OAI
