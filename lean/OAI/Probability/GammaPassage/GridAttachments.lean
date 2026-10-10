import OAI.Probability.GammaPassage.CoordinateTails
import OAI.Probability.GammaPassage.GridIndependence
import OAI.Probability.GammaPassage.GridGeometry

namespace OAI

namespace GammaFPP.Grid
open PlanarFPP MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

noncomputable def verticalExponent (shape : ℝ) : ℝ := 50 * shape * (1 - Real.log 2)
noncomputable def attachmentAllowance (shape rate K : ℝ) : ℝ := K + 200 * shape / rate

lemma verticalExponent_pos {shape : ℝ} (hs : 0 < shape) : 0 < verticalExponent shape := by
  have hl : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    norm_num at h
    exact h
  unfold verticalExponent
  positivity

/-- The attachment allowance dominates the geometric bound of fifty. -/
lemma attachmentAllowance_ge_fifty {shape rate K : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (hK : 100 ≤ K) :
    50 ≤ attachmentAllowance shape rate K := by
  unfold attachmentAllowance
  have : 0 < 200 * shape / rate := by positivity
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential cost tail for an edge set of cardinality at most `50*L`. -/
theorem vertical_edgeSet_tail (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (S : Finset Edge) (L : ℝ)
    (hcard : (S.card : ℝ) ≤ 50 * L) :
    P.real {ω | 100 * shape / rate * L < edgeSum S τ ω} ≤
      Real.exp (-verticalExponent shape * L) := by
  let _ := h.probability
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    field_simp [hr.ne']
    ring
  have hb := h.upper_tail_edgeSum hs hr hp hl S (100 * shape / rate * L)
  rw [he] at hb
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * (100 * shape / rate * L))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfinite : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ S.card /
      ENNReal.ofReal (Real.exp ((rate / 2) * (100 * shape / rate * L))) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hreal := ENNReal.toReal_mono hfinite hb
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  change P.real _ ≤ _ at hreal
  have hsub : {ω | 100 * shape / rate * L < edgeSum S τ ω} ⊆
      {ω | 100 * shape / rate * L ≤ edgeSum S τ ω} := by
    intro ω hω
    change 100 * shape / rate * L < edgeSum S τ ω at hω
    change 100 * shape / rate * L ≤ edgeSum S τ ω
    exact hω.le
  refine (measureReal_mono (μ := P) hsub (measure_ne_top P _)).trans (hreal.trans ?_)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
    ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hcard (mul_nonneg hlog hs.le)
  have hc : rate / 2 * (100 * shape / rate * L) = 50 * shape * L := by
    field_simp [hr.ne']
    ring
  rw [hc]
  unfold verticalExponent
  nlinarith

/-- Finite-bin event with crossing trials and two whole attachment edge sets. -/
def binGood {ι : Type*} (trials : Finset ι) (A : ι → Set (Edge → ℝ))
    (S₁ S₂ : Finset Edge) (shape rate L : ℝ) : Set (Edge → ℝ) :=
  {weights | (∃ i ∈ trials, weights ∈ A i) ∧
    (∑ e ∈ S₁, weights e) ≤ 100 * shape / rate * L ∧
    (∑ e ∈ S₂, weights e) ≤ 100 * shape / rate * L}

/-- Failure bound from disjoint crossing trials and Gamma attachment tails. -/
theorem bin_failure_bound (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) {ι : Type*}
    (trials : Finset ι) (A : ι → Set (Edge → ℝ)) (supports : ι → Finset Edge)
    (hA : ∀ i ∈ trials, MeasurableSet (A i))
    (hdep : ∀ i ∈ trials, DependsOnEdges (A i) (supports i))
    (hdis : Set.Pairwise (↑trials : Set ι) (fun i j => Disjoint (supports i) (supports j)))
    (q : ℝ) (hq : ∀ i ∈ trials, q ≤ P.real {ω | (fun e => τ e ω) ∈ A i})
    (S₁ S₂ : Finset Edge) (L : ℝ)
    (hc₁ : (S₁.card : ℝ) ≤ 50 * L) (hc₂ : (S₂.card : ℝ) ≤ 50 * L) :
    P.real {ω | (fun e => τ e ω) ∉ binGood trials A S₁ S₂ shape rate L} ≤
      (1-q)^trials.card + 2 * Real.exp (-verticalExponent shape * L) := by
  let _ := h.probability
  let F := {ω | ∀ i ∈ trials, (fun e => τ e ω) ∉ A i}
  let V₁ := {ω | 100 * shape / rate * L < edgeSum S₁ τ ω}
  let V₂ := {ω | 100 * shape / rate * L < edgeSum S₂ τ ω}
  have hsub : {ω | (fun e => τ e ω) ∉ binGood trials A S₁ S₂ shape rate L} ⊆ F ∪ V₁ ∪ V₂ := by
    intro ω hω
    simp only [binGood, Set.mem_ofPred_eq, not_and_or, not_exists, not_le] at hω
    rcases hω with hf | hv | hv
    · apply Or.inl
      apply Or.inl
      change ∀ i ∈ trials, (fun e => τ e ω) ∉ A i
      intro i hi
      exact (hf i).resolve_left (not_not.mpr hi)
    · exact Or.inl (Or.inr hv)
    · exact Or.inr hv
  have hf := disjoint_trials_failure_bound h trials A supports hA hdep hdis q hq
  have hv₁ := vertical_edgeSet_tail h hs hr S₁ L hc₁
  have hv₂ := vertical_edgeSet_tail h hs hr S₂ L hc₂
  have hh := (measureReal_mono (μ := P) hsub).trans
    ((measureReal_union_le (μ := P) (F ∪ V₁) V₂).trans
      (add_le_add (measureReal_union_le (μ := P) F V₁) le_rfl))
  change P.real F ≤ _ at hf
  change P.real V₁ ≤ _ at hv₁
  change P.real V₂ ≤ _ at hv₂
  linarith

/-- Combined crossing and attachment cost bound. -/
lemma combined_cost {shape rate K m l L a b c : ℝ}
    (ha : a ≤ m*l+K*L) (hb : b ≤ 100*shape/rate*L)
    (hc : c ≤ 100*shape/rate*L) :
    a+b+c ≤ m*l+attachmentAllowance shape rate K*L := by
  calc
    a+b+c ≤ (m*l+K*L)+(100*shape/rate*L)+(100*shape/rate*L) :=
      add_le_add (add_le_add ha hb) hc
    _ = m*l+attachmentAllowance shape rate K*L := by
      unfold attachmentAllowance
      ring

/-- Column interval used for vertical attachments. -/
theorem transverse_interval_tail (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (b : ℝ) (X h w : ℤ) (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w) :
    P.real {ω | 100*shape/rate*(j : ℝ)^2*w <
      edgeSum (transverseIntervalEdges b X (gridIntervalLower h w)
        (gridIntervalUpper j h w)) τ ω} ≤
      Real.exp (-verticalExponent shape*(j : ℝ)^2*w) := by
  have hb := vertical_edgeSet_tail henv hs hr
    (transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w))
    ((j : ℝ)^2*w) (by simpa only [mul_assoc] using grid_interval_card b X h w j hj hw)
  simpa only [mul_assoc] using hb

/-- Failure bound for `j²` separated translated trials and the left and right
vertical attachment intervals. -/
theorem source_bin_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) (b : ℝ) (X h w l : ℤ)
    (j : ℕ) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (A : Fin (j^2) → Set (Edge → ℝ)) (supports : Fin (j^2) → Finset Edge)
    (hA : ∀ i, MeasurableSet (A i))
    (hdep : ∀ i, DependsOnEdges (A i) (supports i))
    (hdis : Pairwise (fun i k => Disjoint (supports i) (supports k)))
    (q : ℝ) (hq : ∀ i, q ≤ P.real {ω | (fun e => τ e ω) ∈ A i}) :
    P.real {ω | (fun e => τ e ω) ∉ binGood Finset.univ A
      (transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w))
      (transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w))
      shape rate ((j : ℝ)^2*w)} ≤
        (1-q)^(j^2)+2*Real.exp (-verticalExponent shape*(j : ℝ)^2*w) := by
  have hb := bin_failure_bound henv hs hr Finset.univ A supports
    (fun i _ => hA i) (fun i _ => hdep i) (fun i _ k _ hik => hdis hik) q
    (fun i _ => hq i)
    (transverseIntervalEdges b X (gridIntervalLower h w) (gridIntervalUpper j h w))
    (transverseIntervalEdges b (X+l) (gridIntervalLower h w) (gridIntervalUpper j h w))
    ((j : ℝ)^2*w)
    (by simpa only [mul_assoc] using grid_interval_card b X h w j hj hw)
    (by simpa only [mul_assoc] using grid_interval_card b (X+l) h w j hj hw)
  simpa only [Finset.card_univ, Fintype.card_fin, mul_assoc] using hb

/-- Simultaneous finite-bin event, with failure controlled without independence
between bins. Only independence of each bin's separated crossing trials is used. -/
theorem finite_bins_failure_bound (henv : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate) {κ : Type*} (bins : Finset κ)
    (j : ℕ) (L : ℝ) (q : ℝ)
    (A : κ → Fin (j^2) → Set (Edge → ℝ))
    (supports : κ → Fin (j^2) → Finset Edge) (S₁ S₂ : κ → Finset Edge)
    (hA : ∀ k ∈ bins, ∀ i, MeasurableSet (A k i))
    (hdep : ∀ k ∈ bins, ∀ i, DependsOnEdges (A k i) (supports k i))
    (hdis : ∀ k ∈ bins, Pairwise (fun i t => Disjoint (supports k i) (supports k t)))
    (hq : ∀ k ∈ bins, ∀ i, q ≤ P.real {ω | (fun e => τ e ω) ∈ A k i})
    (hc₁ : ∀ k ∈ bins, ((S₁ k).card : ℝ) ≤ 50*L)
    (hc₂ : ∀ k ∈ bins, ((S₂ k).card : ℝ) ≤ 50*L) :
    P.real (⋃ k ∈ bins, {ω | (fun e => τ e ω) ∉
      binGood Finset.univ (A k) (S₁ k) (S₂ k) shape rate L}) ≤
      (bins.card : ℝ)*((1-q)^(j^2)+2*Real.exp (-verticalExponent shape*L)) := by
  let _ := henv.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ bins, ((1-q)^(j^2)+2*Real.exp (-verticalExponent shape*L)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hb := bin_failure_bound henv hs hr Finset.univ (A k) (supports k)
        (fun i _ => hA k hk i) (fun i _ => hdep k hk i)
        (fun i _ t _ hit => hdis k hk hit) q (fun i _ => hq k hk i)
        (S₁ k) (S₂ k) L (hc₁ k hk) (hc₂ k hk)
      simpa only [Finset.card_univ, Fintype.card_fin] using hb
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]

end GammaFPP.Grid

end OAI
