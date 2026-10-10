import OAI.Analysis.DiskMaximal.GreenBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

noncomputable section

namespace IntrinsicMarks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def direction (e v : E) : E := by
  classical
  exact if v = 0 then e else ‖v‖⁻¹ • v

lemma norm_direction {e : E} (he : ‖e‖ = 1) (v : E) : ‖direction e v‖ = 1 := by
  by_cases hv : v = 0
  · simp [direction,hv,he]
  · rw [direction,ite_eq_right hv,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

lemma mass_direction (e v : E) : ‖v‖ • direction e v = v := by
  by_cases hv : v = 0
  · simp [hv]
  · simp [direction,hv,smul_smul,norm_ne_zero_iff.mpr hv]

lemma debt_identity {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (v : E) :
    2*(‖v‖-⟪v,n⟫) = ‖v‖*‖direction e v-n‖^2 := by
  have hi : ‖v‖*⟪direction e v,n⟫ = ⟪v,n⟫ := by
    rw [← real_inner_smul_left,mass_direction]
  rw [norm_sub_sq_real,norm_direction he,hn]
  nlinarith

lemma marked_mass_le {e n : E} (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (v : E) {δ : ℝ} (hδ : 0 < δ) (hmark : δ < ‖direction e v-n‖) :
    ‖v‖ ≤ (2/δ^2)*(‖v‖-⟪v,n⟫) := by
  have hs : δ^2 ≤ ‖direction e v-n‖^2 :=
    (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr hmark.le
  have hm := mul_le_mul_of_nonneg_left hs (norm_nonneg v)
  have hid := debt_identity he hn v
  have hd : 0 < δ^2 := sq_pos_of_pos hδ
  rw [div_mul_eq_mul_div,le_div_iff₀ hd]
  nlinarith

/-- Finite uniform branching includes each finite positive-refinement path forest
by padding absent children with zero vectors. No triangle defect is assumed. -/
inductive Tree (ι : Type*) (E : Type*) where
  | leaf : E → Tree ι E
  | branch : (ι → Tree ι E) → Tree ι E

variable {ι : Type*} [Fintype ι]

def vector : Tree ι E → E
  | .leaf v => v
  | .branch t => ∑ i, vector (t i)

def terminalMass : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t => ∑ i, terminalMass (t i)

omit [InnerProductSpace ℝ E] in
lemma norm_vector_le_terminalMass (t : Tree ι E) : ‖vector t‖ ≤ terminalMass t := by
  induction t with
  | leaf v => exact le_rfl
  | branch t ih =>
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ih i)

/-- Only the first crossing from the most recent marked direction is counted;
a crossing resets the anchor before descending further. -/
def markedCost (e : E) (δ : ℝ) : Tree ι E → E → ℝ
  | .leaf v, n => if δ < ‖direction e v-n‖ then ‖v‖ else 0
  | .branch t, n =>
      let v := ∑ i, vector (t i)
      if δ < ‖direction e v-n‖ then
        ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n

theorem markedCost_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) {n : E} (hn : ‖n‖ = 1) :
    markedCost e δ t n ≤ (2/δ^2)*(terminalMass t-⟪vector t,n⟫) := by
  induction t generalizing n with
  | leaf v =>
    dsimp [markedCost,terminalMass,vector]
    split_ifs with hm
    · exact marked_mass_le he hn v hδ hm
    · have hi : ⟪v,n⟫ ≤ ‖v‖ := by simpa only [hn,mul_one] using real_inner_le_norm v n
      exact mul_nonneg (by positivity) (sub_nonneg.mpr hi)
  | branch t ih =>
    let v := ∑ i, vector (t i)
    have hs (u : E) (hu : ‖u‖ = 1) :
        (∑ i, markedCost e δ (t i) u) ≤
          (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,u⟫) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),u⟫) :=
          Finset.sum_le_sum (fun i _ => ih i hu)
        _ = _ := by simp only [Finset.mul_sum,Finset.sum_sub_distrib,sum_inner,v,mul_sub]
    have hv := norm_direction he v
    change (if δ < ‖direction e v-n‖ then
      ‖v‖ + ∑ i, markedCost e δ (t i) (direction e v)
      else ∑ i, markedCost e δ (t i) n) ≤ _
    split_ifs with hm
    · have hms := marked_mass_le he hn v hδ hm
      have hss := hs (direction e v) hv
      have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
        calc
          _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
          _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
      rw [hinner] at hss
      change _ ≤ (2/δ^2)*((∑ i, terminalMass (t i))-⟪v,n⟫)
      nlinarith
    · exact hs n hn

def costWithRoot (e : E) (δ : ℝ) : Tree ι E → ℝ
  | .leaf v => ‖v‖
  | .branch t =>
      let v := ∑ i, vector (t i)
      ‖v‖+∑ i, markedCost e δ (t i) (direction e v)

theorem costWithRoot_le {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) : costWithRoot e δ t ≤ (1+2/δ^2)*terminalMass t := by
  cases t with
  | leaf v =>
    change ‖v‖ ≤ (1+2/δ^2)*‖v‖
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]
  | branch t =>
    let v := ∑ i, vector (t i)
    have hv := norm_direction he v
    have hinner : ⟪v,direction e v⟫ = ‖v‖ := by
      calc
        _ = ⟪‖v‖ • direction e v,direction e v⟫ := congrArg (fun w => ⟪w,direction e v⟫) (mass_direction e v).symm
        _ = _ := by rw [real_inner_smul_left,real_inner_self_eq_norm_sq,hv]; ring
    have hs : (∑ i, markedCost e δ (t i) (direction e v)) ≤
        (2/δ^2)*((∑ i, terminalMass (t i))-‖v‖) := by
      calc
        _ ≤ ∑ i, (2/δ^2)*(terminalMass (t i)-⟪vector (t i),direction e v⟫) :=
          Finset.sum_le_sum (fun i _ => markedCost_le he hδ (t i) hv)
        _ = _ := by rw [← Finset.mul_sum,Finset.sum_sub_distrib,← sum_inner,hinner]
    have hn : ‖v‖ ≤ ∑ i, terminalMass (t i) := norm_vector_le_terminalMass (.branch t)
    change ‖v‖+∑ i, markedCost e δ (t i) (direction e v) ≤
      (1+2/δ^2)*(∑ i, terminalMass (t i))
    nlinarith [mul_nonneg (show 0 ≤ 2/δ^2 by positivity) (norm_nonneg v)]

end IntrinsicMarks

namespace IntrinsicMarks
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

/-- The fraction of the child capacity occupied by particles already alive. -/
def survival (t : ι → Tree ι E) : ℝ :=
  ‖∑ i, vector (t i)‖ / ∑ i, ‖vector (t i)‖

lemma survival_nonneg (t : ι → Tree ι E) : 0 ≤ survival t := by
  unfold survival
  positivity

lemma survival_le_one (t : ι → Tree ι E) : survival t ≤ 1 := by
  unfold survival
  exact div_le_one_of_le₀ (norm_sum_le _ _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

lemma survival_capacity (t : ι → Tree ι E) :
    survival t * (∑ i, ‖vector (t i)‖) = ‖∑ i, vector (t i)‖ := by
  unfold survival
  by_cases h : (∑ i, ‖vector (t i)‖) = 0
  · have hn : ‖∑ i, vector (t i)‖ = 0 := by
      apply le_antisymm _ (norm_nonneg _)
      simpa only [h] using norm_sum_le Finset.univ (fun i => vector (t i))
    simp [h,hn]
  · exact div_mul_cancel₀ _ h

/-- Explicit finite weighted evaluation on terminal paths, for the population
born at the current root. Every branching has its true capacity ratio. -/
def rootEval : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, F => ‖v‖ * F []
  | .branch t, F => survival t * ∑ i, rootEval (t i) (fun p => F (i::p))

/-- Explicit finite evaluation of populations born strictly below this root.
The complete prefix is retained, including the part before birth. -/
def lateEval : Tree ι E → (List ι → ℕ → ℝ) → ℝ
  | .leaf _, _ => 0
  | .branch t, F =>
      (1-survival t) * (∑ i, rootEval (t i) (fun p => F (i::p) 1)) +
        ∑ i, lateEval (t i) (fun p b => F (i::p) (b+1))

def particleEval (t : Tree ι E) (F : List ι → ℕ → ℝ) : ℝ :=
  rootEval t (fun p => F p 0) + lateEval t F

lemma rootEval_nonneg (t : Tree ι E) {F : List ι → ℝ} (hF : ∀ p, 0 ≤ F p) :
    0 ≤ rootEval t F := by
  induction t generalizing F with
  | leaf v => exact mul_nonneg (norm_nonneg _) (hF _)
  | branch t ih =>
    exact mul_nonneg (survival_nonneg t) (Finset.sum_nonneg fun i _ => ih i (fun p => hF (i::p)))

lemma lateEval_nonneg (t : Tree ι E) {F : List ι → ℕ → ℝ} (hF : ∀ p b, 0 ≤ F p b) :
    0 ≤ lateEval t F := by
  induction t generalizing F with
  | leaf v => exact le_rfl
  | branch t ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr (survival_le_one t))
      (Finset.sum_nonneg (fun i _ => rootEval_nonneg (t i) (fun p => hF (i::p) 1))))
      (Finset.sum_nonneg (fun i _ => ih i (fun p b => hF (i::p) (b+1))))

lemma particleEval_nonneg (t : Tree ι E) {F : List ι → ℕ → ℝ} (hF : ∀ p b, 0 ≤ F p b) :
    0 ≤ particleEval t F := add_nonneg (rootEval_nonneg t (fun p => hF p 0)) (lateEval_nonneg t hF)

lemma rootEval_const (t : Tree ι E) (c : ℝ) :
    rootEval t (fun _ => c) = ‖vector t‖*c := by
  induction t with
  | leaf _ => rfl
  | branch t ih =>
    change survival t * (∑ i, rootEval (t i) (fun _ => c)) = _
    simp only [ih,← Finset.sum_mul]
    rw [← mul_assoc,survival_capacity]
    rfl

lemma rootEval_add (t : Tree ι E) (F G : List ι → ℝ) :
    rootEval t (fun p => F p+G p) = rootEval t F+rootEval t G := by
  induction t generalizing F G with
  | leaf _ => exact mul_add _ _ _
  | branch t ih => simp only [rootEval,ih,Finset.sum_add_distrib,mul_add]

lemma rootEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℝ) :
    rootEval t (fun p => c*F p) = c*rootEval t F := by
  induction t generalizing F with
  | leaf _ => dsimp [rootEval]; ring
  | branch t ih => simp only [rootEval,ih,← Finset.mul_sum]; ring

lemma lateEval_const (t : Tree ι E) (c : ℝ) :
    lateEval t (fun _ _ => c) = (terminalMass t-‖vector t‖)*c := by
  induction t with
  | leaf _ => simp [lateEval,terminalMass,vector]
  | branch t ih =>
    change (1-survival t)*(∑ i, rootEval (t i) (fun _ => c)) +
      (∑ i, lateEval (t i) (fun _ _ => c)) = _
    simp only [ih,rootEval_const,← Finset.sum_mul,Finset.sum_sub_distrib]
    rw [sub_mul,one_mul,← mul_assoc,survival_capacity]
    simp only [terminalMass,vector]
    ring

lemma particleEval_const (t : Tree ι E) (c : ℝ) :
    particleEval t (fun _ _ => c) = terminalMass t*c := by
  rw [particleEval,rootEval_const,lateEval_const]
  ring

lemma lateEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    lateEval t (fun p b => F p b+G p b) = lateEval t F+lateEval t G := by
  induction t generalizing F G with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_add,ih,Finset.sum_add_distrib,mul_add]; ring

lemma lateEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    lateEval t (fun p b => c*F p b) = c*lateEval t F := by
  induction t generalizing F with
  | leaf _ => simp [lateEval]
  | branch t ih => simp only [lateEval,rootEval_smul,ih,← Finset.mul_sum]; ring

lemma particleEval_add (t : Tree ι E) (F G : List ι → ℕ → ℝ) :
    particleEval t (fun p b => F p b+G p b) = particleEval t F+particleEval t G := by
  simp only [particleEval,rootEval_add,lateEval_add]
  ring

lemma particleEval_smul (t : Tree ι E) (c : ℝ) (F : List ι → ℕ → ℝ) :
    particleEval t (fun p b => c*F p b) = c*particleEval t F := by
  simp only [particleEval,rootEval_smul,lateEval_smul,mul_add]

lemma particleEval_mono (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (hFG : ∀ p b, F p b ≤ G p b) : particleEval t F ≤ particleEval t G := by
  have hn := particleEval_nonneg t (F := fun p b => G p b-F p b) (fun p b => sub_nonneg.mpr (hFG p b))
  have h := particleEval_add t G (fun p b => -1*F p b)
  simp only [neg_one_mul] at h
  have hn' : particleEval t (fun p b => G p b-F p b) = particleEval t G-particleEval t F := by
    calc
      _ = particleEval t G+particleEval t (fun p b => -1*F p b) := by simpa only [neg_one_mul,sub_eq_add_neg] using h
      _ = _ := by rw [particleEval_smul]; ring
  rw [hn'] at hn
  linarith

/-- Sum a node charge only at and after the particle's birth. -/
def pathCharge (C : List ι → ℝ) : List ι → ℕ → ℝ
  | [], 0 => C []
  | [], _+1 => 0
  | i::p, 0 => C [] + pathCharge (fun q => C (i::q)) p 0
  | i::p, b+1 => pathCharge (fun q => C (i::q)) p b

def nodeCharge : Tree ι E → (List ι → ℝ) → ℝ
  | .leaf v, C => ‖v‖*C []
  | .branch t, C => ‖∑ i, vector (t i)‖*C [] + ∑ i, nodeCharge (t i) (fun p => C (i::p))

/-- Exact occupancy identity for every node charge. This includes all levels,
not only the terminal mass; populations created later are not charged earlier. -/
theorem particle_occupancy (t : Tree ι E) (C : List ι → ℝ) :
    particleEval t (pathCharge C) = nodeCharge t C := by
  induction t generalizing C with
  | leaf v => simp [particleEval,rootEval,lateEval,pathCharge,nodeCharge]
  | branch t ih =>
    simp only [particleEval,rootEval,lateEval,pathCharge,rootEval_add,rootEval_const,
      Finset.sum_add_distrib]
    have hs : (∑ i, particleEval (t i) (pathCharge (fun q => C (i::q)))) =
        ∑ i, nodeCharge (t i) (fun q => C (i::q)) :=
      Finset.sum_congr rfl (fun i _ => ih i _)
    simp only [particleEval,Finset.sum_add_distrib] at hs
    rw [← Finset.sum_mul,mul_add,← mul_assoc,survival_capacity]
    change _ = ‖∑ i, vector (t i)‖*C []+∑ i, nodeCharge (t i) (fun q => C (i::q))
    linarith

end IntrinsicMarks

namespace IntrinsicMarks
open Finset
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def validPath : Tree ι E → List ι → Prop
  | .leaf _, p => p = []
  | .branch _, [] => False
  | .branch t, i::p => validPath (t i) p

omit [InnerProductSpace ℝ E] in
lemma rootEval_mono_on (t : Tree ι E) {F G : List ι → ℝ}
    (h : ∀ p, validPath t p → F p ≤ G p) : rootEval t F ≤ rootEval t G := by
  induction t generalizing F G with
  | leaf v => exact mul_le_mul_of_nonneg_left (h [] rfl) (norm_nonneg _)
  | branch t ih =>
    apply mul_le_mul_of_nonneg_left _ (survival_nonneg t)
    exact sum_le_sum fun i _ => ih i (fun p hp => h (i::p) hp)

omit [InnerProductSpace ℝ E] in
lemma lateEval_mono_on (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, validPath t p → b ≤ p.length → F p b ≤ G p b) :
    lateEval t F ≤ lateEval t G := by
  induction t generalizing F G with
  | leaf v => rfl
  | branch t ih =>
    unfold lateEval
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (survival_le_one t))
      exact sum_le_sum fun i _ => rootEval_mono_on (t i) (fun p hp => h (i::p) 1 hp (by simp))
    · exact sum_le_sum fun i _ => ih i (fun p b hp hb => h (i::p) (b+1) hp (by simpa using Nat.succ_le_succ hb))

omit [InnerProductSpace ℝ E] in
/-- Particle monotonicity requires bounds only on genuine terminal paths and
legal birth times; the explicit construction has no mass elsewhere. -/
theorem particleEval_mono_on (t : Tree ι E) {F G : List ι → ℕ → ℝ}
    (h : ∀ p b, validPath t p → b ≤ p.length → F p b ≤ G p b) :
    particleEval t F ≤ particleEval t G := by
  exact add_le_add (rootEval_mono_on t (fun p hp => h p 0 hp (Nat.zero_le _)))
    (lateEval_mono_on t h)

/-- Intrinsic marks as an actual function on prefixes, with first-crossing
reset. Prefixes outside the tree have zero charge. -/
def markIndicator (e : E) (δ : ℝ) : Tree ι E → E → List ι → ℝ
  | .leaf v, n, [] => if δ < ‖direction e v-n‖ then 1 else 0
  | .leaf _, _, _::_ => 0
  | .branch t, n, [] => if δ < ‖direction e (∑ i, vector (t i))-n‖ then 1 else 0
  | .branch t, n, i::p =>
      let v := ∑ j, vector (t j)
      markIndicator e δ (t i) (if δ < ‖direction e v-n‖ then direction e v else n) p

def rootMarkIndicator (e : E) (δ : ℝ) : Tree ι E → List ι → ℝ
  | _, [] => 1
  | .leaf _, _::_ => 0
  | .branch t, i::p => markIndicator e δ (t i) (direction e (∑ j, vector (t j))) p

lemma marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) (n : E) :
    nodeCharge t (markIndicator e δ t n) = markedCost e δ t n := by
  induction t generalizing n with
  | leaf v => simp only [nodeCharge,markIndicator,markedCost]; split_ifs <;> simp
  | branch t ih =>
    simp only [nodeCharge,markIndicator,markedCost]
    split_ifs with h
    · simp only [mul_one]
      congr 1
      exact sum_congr rfl (fun i _ => ih i _)
    · simp only [mul_zero,zero_add]
      exact sum_congr rfl (fun i _ => ih i _)

lemma root_marked_occupancy (e : E) (δ : ℝ) (t : Tree ι E) :
    nodeCharge t (rootMarkIndicator e δ t) = costWithRoot e δ t := by
  cases t with
  | leaf v => simp [nodeCharge,rootMarkIndicator,costWithRoot]
  | branch t => simp only [nodeCharge,rootMarkIndicator,costWithRoot,mul_one,marked_occupancy]

theorem particle_mark_budget {e : E} (he : ‖e‖ = 1) {δ : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) :
    particleEval t (pathCharge (rootMarkIndicator e δ t)) ≤
      (1+2/δ^2)*terminalMass t := by
  rw [particle_occupancy,root_marked_occupancy]
  exact costWithRoot_le he hδ t

/-- Turning a genuine pathwise switch bound into the global budget uses exact
occupancy, rather than a false assumption that every particle is born at a root. -/
theorem particle_switch_budget {e : E} (he : ‖e‖ = 1) {δ c : ℝ} (hδ : 0 < δ)
    (t : Tree ι E) (energy : List ι → ℝ) (switches : List ι → ℕ → ℝ)
    (hpath : ∀ p b, validPath t p → b ≤ p.length → switches p b ≤
      1+2*pathCharge (rootMarkIndicator e δ t) p b+c*pathCharge energy p b) :
    particleEval t switches ≤ (3+4/δ^2)*terminalMass t+c*nodeCharge t energy := by
  have h := particleEval_mono_on t hpath
  simp only [particleEval_add,particleEval_smul,particleEval_const,particle_occupancy,
    root_marked_occupancy] at h
  have hm := costWithRoot_le he hδ t
  calc
    _ ≤ terminalMass t*1 + 2*((1+2/δ^2)*terminalMass t)+c*nodeCharge t energy :=
      h.trans (by gcongr)
    _ = _ := by ring

end IntrinsicMarks

namespace SignedAssembly
open Finset
open scoped RealInnerProductSpace
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure RowJet (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  law : FiniteLabels.Law ι
  grad : ι → E
  total_grad : ∑ i, grad i = 0

inductive JetTree (ι E : Type*) [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  | leaf : E → JetTree ι E
  | branch : RowJet ι E → E → ℝ → (ι → JetTree ι E) → JetTree ι E

def mean : JetTree ι E → E
  | .leaf v => v
  | .branch row _ _ t => ∑ i, row.law i • mean (t i)

def flux : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ _ t => ∑ i, ⟪row.grad i,mean (t i)⟫ + ∑ i, row.law i*flux (t i)

/-- Product-rule expansion over all terminal label histories. The carried mass
and its derivative are updated by the exact Leibniz rule. -/
def pathFlux : JetTree ι E → ℝ → E → ℝ
  | .leaf v, _, G => ⟪G,v⟫
  | .branch row _ _ t, q, G =>
      ∑ i, pathFlux (t i) (q*row.law i) (q • row.grad i+row.law i • G)

lemma pathFlux_eq (t : JetTree ι E) (q : ℝ) (G : E) :
    pathFlux t q G = ⟪G,mean t⟫+q*flux t := by
  induction t generalizing q G with
  | leaf v => simp [pathFlux,mean,flux]
  | branch row c B t ih =>
    simp only [pathFlux,ih,inner_add_left,real_inner_smul_left,sum_add_distrib,
      ← mul_sum,mean,flux,inner_sum,real_inner_smul_right]
    simp only [mul_assoc, ← mul_sum]
    ring

lemma terminal_flux (t : JetTree ι E) : pathFlux t 1 0 = flux t := by
  rw [pathFlux_eq,inner_zero_left,one_mul,zero_add]

/-- Every terminal continuation is within B of the same closed-prefix value. -/
def TerminalBound : JetTree ι E → E → ℝ → Prop
  | .leaf v, c, B => ‖v-c‖ ≤ B
  | .branch _ _ _ t, c, B => ∀ i, TerminalBound (t i) c B

lemma mean_bound (t : JetTree ι E) (c : E) (B : ℝ) (h : TerminalBound t c B) :
    ‖mean t-c‖ ≤ B := by
  induction t with
  | leaf v => exact h
  | branch row _ _ t ih =>
    have he : mean (.branch row (0:E) 0 t)-c = ∑ i, row.law i • (mean (t i)-c) := by
      simp only [mean,smul_sub,sum_sub_distrib,← sum_smul,row.law.total,one_smul]
    change ‖mean (.branch row (0:E) 0 t)-c‖ ≤ B
    rw [he]
    calc
      _ ≤ ∑ i, ‖row.law i • (mean (t i)-c)‖ := norm_sum_le _ _
      _ = ∑ i, row.law i*‖mean (t i)-c‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (row.law.nonneg _)]
      _ ≤ ∑ i, row.law i*B := sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (ih i (h i)) (row.law.nonneg i)
      _ = B := by rw [← sum_mul,row.law.total,one_mul]

/-- This is the exact zero-row-sum cancellation. No unsigned path-potential
bound is used and the parent prefix may be arbitrarily large. -/
lemma prefix_cancellation (row : RowJet ι E) (v : ι → E) (c : E) :
    (∑ i, ⟪row.grad i,v i⟫) = ∑ i, ⟪row.grad i,v i-c⟫ := by
  simp only [inner_sub_right,sum_sub_distrib,← sum_inner,row.total_grad,inner_zero_left,sub_zero]

lemma row_flux_bound (row : RowJet ι E) (v : ι → E) (c : E) (B : ℝ)
    (h : ∀ i, ‖v i-c‖ ≤ B) :
    |∑ i, ⟪row.grad i,v i⟫| ≤ (∑ i, ‖row.grad i‖)*B := by
  rw [prefix_cancellation row v c]
  calc
    _ ≤ ∑ i, |⟪row.grad i,v i-c⟫| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖row.grad i‖*B := sum_le_sum fun i _ =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
    _ = _ := by rw [← sum_mul]

def Controlled : JetTree ι E → Prop
  | .leaf _ => True
  | .branch _ c B t => (∀ i, TerminalBound (t i) c B) ∧ ∀ i, Controlled (t i)

def cost : JetTree ι E → ℝ
  | .leaf _ => 0
  | .branch row _ B t => (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i)

/-- Full finite-history signed flux estimate, with all stochastic prefix
weights kept. The node bound is the tail oscillation, not the old envelope. -/
theorem signed_flux_bound (t : JetTree ι E) (ht : Controlled t) :
    |pathFlux t 1 0| ≤ cost t := by
  rw [terminal_flux]
  induction t with
  | leaf v => simp [flux,cost]
  | branch row c B t ih =>
    change |(∑ i, ⟪row.grad i,mean (t i)⟫)+∑ i, row.law i*flux (t i)| ≤ _
    calc
      _ ≤ |∑ i, ⟪row.grad i,mean (t i)⟫|+|∑ i, row.law i*flux (t i)| := abs_add_le _ _
      _ ≤ (∑ i, ‖row.grad i‖)*B+∑ i, row.law i*cost (t i) := by
        apply add_le_add (row_flux_bound row (fun i => mean (t i)) c B
          (fun i => mean_bound (t i) c B (ht.1 i)))
        calc
          _ ≤ ∑ i, |row.law i*flux (t i)| := abs_sum_le_sum_abs _ _
          _ = ∑ i, row.law i*|flux (t i)| := by
            simp only [abs_mul,abs_of_nonneg (row.law.nonneg _)]
          _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ih i (ht.2 i)) (row.law.nonneg i)
      _ = _ := rfl

end SignedAssembly

open scoped ContDiff
namespace PlanePotential
lemma potential_norm_lintegral {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b) :
    (∫⁻ y, ‖⟪L y,b y⟫‖ₑ) ≤
      ∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖) := by
  rw [lintegral_withDensity_eq_lintegral_mul₀' hb.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
    hL.norm.ennreal_ofReal.aemeasurable]
  apply lintegral_mono
  intro y
  dsimp only [Pi.mul_apply]
  rw [← ofReal_norm]
  change ENNReal.ofReal ‖⟪L y,b y⟫‖ ≤ ENNReal.ofReal ‖b y‖ * ENNReal.ofReal ‖L y‖
  rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans_eq (mul_comm _ _))

lemma potential_integrable_of_density {L : ℂ → ℂ} (hL : Measurable L) {b : ℂ → ℂ}
    (hb : Integrable b)
    (hfinite : (∫⁻ y, ENNReal.ofReal ‖L y‖ ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)) < ⊤) :
    Integrable (fun y => ⟪L y,b y⟫) := by
  refine ⟨hL.aestronglyMeasurable.inner hb.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (potential_norm_lintegral hL hb).trans_lt hfinite

/-- Finiteness of the genuine singular integrals, obtained from the column
estimate itself. This justifies insertion of the finite vector decomposition. -/
theorem kernel_potential_ae_integrable (μ : Measure ℂ) [SFinite μ]
    {K : ℂ × ℂ → ℂ} (hK : Measurable K) {b : ℂ → ℂ} (hb : Integrable b)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hcol : ∀ᵐ y ∂volume.withDensity (fun y => ENNReal.ofReal ‖b y‖),
      (∫⁻ x, (ENNReal.ofReal ‖K (x,y)‖)^(3/2:ℝ) ∂μ) ≤ C) :
    ∀ᵐ x ∂μ, Integrable (fun y => ⟪K (x,y),b y⟫) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖b y‖)
  have hm : ν univ = ENNReal.ofReal (∫ y, ‖b y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hb.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have hν : ν univ < ⊤ := by rw [hm]; exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := ⟨hν⟩
  have hlp := kernel_column_lp μ ν hK.norm.ennreal_ofReal hcol
  have hfinite : (∫⁻ x, (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν)^(3/2:ℝ) ∂μ) ≠ ⊤ :=
    ne_of_lt (hlp.trans_lt (ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hν.ne)))
  have hae := ae_lt_top (hK.norm.ennreal_ofReal.lintegral_prod_right.pow_const _) hfinite
  filter_upwards [hae] with x hx
  apply potential_integrable_of_density (hK.comp (measurable_const.prodMk measurable_id)) hb
  apply lt_top_iff_ne_top.mpr
  intro htop
  change (∫⁻ y, ENNReal.ofReal ‖K (x,y)‖ ∂ν) = ⊤ at htop
  rw [htop,ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 3/2)] at hx
  exact (lt_irrefl _ hx)

lemma green_root_column {ψ : ℂ → ℝ} (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y) {y : ℂ} (hy : ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal ‖green ψ x y‖)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) := by
  apply kernel_near_three_halves (by positivity) (by positivity : 0 < 2*(X+Y)) y
  · intro x hx
    rw [mem_ball,dist_eq_norm]
    have hn := norm_sub_le x y
    change ‖x‖ ≤ X at hx
    linarith
  · intro x hx
    exact green_size_all hψm hψs hψB hM hB hx

lemma green_ae_integrable {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    ∀ᵐ x ∂volume.restrict {x : ℂ | ‖x‖ ≤ X}, Integrable (fun y => ⟪green ψ x y,β y⟫) := by
  apply kernel_potential_ae_integrable _ (green_measurable ψ hψm) hβ ENNReal.ofReal_lt_top
  rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
  filter_upwards with y hy
  apply green_root_column hψm hψs hψB hM hB hXY
  apply hβs y
  intro hy0
  simp [hy0] at hy

lemma green_root_lp {ψ : ℂ → ℝ} {β : ℂ → ℂ}
    (hψm : Measurable ψ) {R X Y B : ℝ}
    (hψs : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R) (hψB : ∀ z, |ψ z| ≤ B)
    (hM : 0 < R+X) (hB : 0 ≤ B) (hXY : 0 < X+Y)
    (hβ : Integrable β) (hβs : ∀ y, β y ≠ 0 → ‖y‖ ≤ Y) :
    (∫⁻ x in {x : ℂ | ‖x‖ ≤ X}, (ENNReal.ofReal |∫ y, ⟪green ψ x y,β y⟫|)^(3/2:ℝ)) ≤
    ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ))) *
      (ENNReal.ofReal (∫ y, ‖β y‖))^(3/2:ℝ) := by
  let ν := volume.withDensity (fun y => ENNReal.ofReal ‖β y‖)
  have hν : ν univ = ENNReal.ofReal (∫ y, ‖β y‖) := by
    dsimp only [ν]
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hβ.norm
      (ae_of_all _ (fun _ => norm_nonneg _))).symm
  have : IsFiniteMeasure ν := ⟨by rw [hν]; exact ENNReal.ofReal_lt_top⟩
  have hm := green_measurable ψ hψm
  have hcol := kernel_column_lp (volume.restrict {x : ℂ | ‖x‖ ≤ X}) ν hm.norm.ennreal_ofReal
    (C := ENNReal.ofReal ((2*B*(R+X)^2)^(3/2:ℝ)*(4*Real.pi*(2*(X+Y))^(1/2:ℝ)))) (by
      rw [ae_withDensity_iff' hβ.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal]
      filter_upwards with y hy
      apply green_root_column hψm hψs hψB hM hB hXY
      apply hβs y
      intro hy0
      simp [hy0] at hy)
  rw [hν] at hcol
  apply le_trans _ hcol
  apply lintegral_mono
  intro x
  exact ENNReal.rpow_le_rpow (potential_domination
    (hm.comp (measurable_const.prodMk measurable_id)) hβ) (by norm_num)

end PlanePotential

namespace PlanePotential
lemma eLpNorm_three_halves_bound (μ : Measure ℂ) {F : ℂ → ℝ} {K m : ℝ≥0∞}
    (h : (∫⁻ x, (ENNReal.ofReal |F x|)^(3/2:ℝ) ∂μ) ≤ K*m^(3/2:ℝ)) :
    eLpNorm' F (3/2) μ ≤ K^(2/3:ℝ)*m := by
  rw [eLpNorm'_eq_lintegral_enorm]
  norm_num only [one_div_div]
  have hpow := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2/3)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2/3),← ENNReal.rpow_mul] at hpow
  norm_num only [show (3/2:ℝ)*(2/3)=1 by norm_num,ENNReal.rpow_one] at hpow
  simpa only [← ofReal_norm,Real.norm_eq_abs] using hpow

lemma potential_aestronglyMeasurable (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) :
    AEStronglyMeasurable (fun x => ∫ y, ⟪K (x,y),β y⟫) μ := by
  have h : AEStronglyMeasurable (fun z : ℂ × ℂ => @inner ℝ ℂ _ (K z) (β z.2)) (μ.prod volume) :=
    hK.aestronglyMeasurable.inner hβ.aestronglyMeasurable.comp_snd
  exact h.integral_prod_right'

lemma potential_memLp_of_bound (μ : Measure ℂ) {K : ℂ × ℂ → ℂ}
    (hK : Measurable K) {β : ℂ → ℂ} (hβ : Integrable β) {C m : ℝ≥0∞}
    (hC : C < ⊤) (hm : m < ⊤)
    (h : (∫⁻ x, (ENNReal.ofReal |∫ y, ⟪K (x,y),β y⟫|)^(3/2:ℝ) ∂μ) ≤ C*m^(3/2:ℝ)) :
    MemLp (fun x => ∫ y, ⟪K (x,y),β y⟫) (3/2) μ := by
  rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num : (3/2:ℝ≥0∞) ≠ 0)
    (ENNReal.div_ne_top (by norm_num) (by norm_num)) (potential_aestronglyMeasurable μ hK hβ)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_ofNat]
  exact (eLpNorm_three_halves_bound μ h).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne) hm)

/-- A genuine fixed smooth probability cutoff. Its finite size and Lipschitz
constants depend on no input, no dyadic level and no number of scales. -/
theorem exists_kernel_cutoff : ∃ (ψ : ℂ → ℝ) (B L : ℝ),
    0 ≤ B ∧ 0 ≤ L ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
    (∫ x, ψ x) = 1 ∧ (∀ x, ψ x ≠ 0 → ‖x‖ ≤ 1) ∧
    (∀ x, |ψ x| ≤ B) ∧ (∀ x y, |ψ x-ψ y| ≤ L*‖x-y‖) := by
  let φ : ContDiffBump (0:ℂ) := ⟨1/2,1,by norm_num,by norm_num⟩
  let ψ := φ.normed volume
  have hc : HasCompactSupport ψ := φ.hasCompactSupport_normed
  have hd : ContDiff ℝ ∞ ψ := φ.contDiff_normed
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hd.continuous
  obtain ⟨L,hL⟩ := hd.lipschitzWith_of_hasCompactSupport hc (by simp)
  refine ⟨ψ,B,L,le_trans (norm_nonneg (ψ 0)) (hB 0),L.coe_nonneg,hd,hc,
    φ.integral_normed,?_,?_,?_⟩
  · intro x hx
    have hs : x ∈ Function.support ψ := hx
    rw [φ.support_normed_eq] at hs
    exact (show ‖x‖ < 1 by simpa only [mem_ball,dist_zero_right] using hs).le
  · intro x
    simpa only [Real.norm_eq_abs] using hB x
  · intro x y
    simpa only [Real.norm_eq_abs] using hL.norm_sub_le x y

end PlanePotential

open Finset
noncomputable section

end
end

end OAI
