import Mathlib
import OAI.Algebra.GroupRing.StageBlocks
import OAI.Algebra.GroupRing.StageRealization

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageExpectation
open scoped Classical BigOperators
open ChainSubdivision BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
section
local instance : DecidableEq Types.Letter := Classical.decEq _
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)

include hs in
/-- The retained full-block bins bound the actual turn product of the
subdivided graph, not a separate abstract word process. -/
theorem turnProduct_bin (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i)) :
    ChainRealization.turnProduct len w ≤ Real.exp (-∑ i, (d i : ℝ)) := by
  rw [ChainRealization.turnProduct,← ChainWeights.chainProduct_eq len w]
  exact ChainWeights.chain_bin_bound s hs len w d hbin

include hs in
/-- Source equation (entropy-fixed-label-expectation), in its exact finite
form before the uniform asymptotic prescription and marked-vertex errors. -/
theorem fixed_label_bin_bound (outgoing : TV → Finset Types.Letter)
    (pp : V → Option TV) (n p : ℝ) (hp : 0 ≤ p)
    (w : C → ℤ → Letter) (d : Underlying s len → ℤ)
    (hbin : ∀ i, word s len w i ∈ binWords (height s len i) (d i))
    (himm : Function.Injective (fun a =>
      ((graph len first last).origin a, ChainRealization.label len w a)))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u)
    (N D R : ℕ) (hD : 2 ≤ D) (hR : 0 < R)
    (hdegree : ∀ v, Nat.card {a : PatternEmbeddings.Dart outgoing //
      PatternEmbeddings.origin outgoing a = v} ≤ D)
    (hsize : ∀ x : PatternEmbeddings.Dart outgoing,
      R + (∑ c, len c) + 4*D^(2*N+1) ≤
        Nat.card {a : PatternEmbeddings.Dart outgoing //
          PatternEmbeddings.label outgoing a = PatternEmbeddings.label outgoing x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅,
        StageRealization.realizations (graph len first last) (ChainRealization.label len w)
          outgoing (ChainRealization.pin len pp) Types.inverse r : ℕ) : ℝ) /
      (ConditionedMatchings.Matching.conditioned
        (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
        (PatternEmbeddings.origin outgoing) N ∅).card ≤
      (n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1))) / (R : ℝ)^(∑ c, len c) *
        Real.exp (-∑ i, (d i : ℝ)) := by
  have hn0 : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TV)).trans hn
  refine (ChainRealization.fixed_label_bound len first last outgoing pp n p w
    himm hn htable N D R hD hR hdegree hsize hΩ).trans ?_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (turnProduct_bin s hs len w d hbin) (by positivity)

/-- Finite Fubini for the actual permitted-label union. We count only
immersed template labels and do not assume independence of repeated edges. -/
theorem label_union_mean {Ω W : Type*} (sample : Finset Ω) (labels : Finset W)
    (X : W → Ω → ℕ) (B : ℝ)
    (hX : ∀ w ∈ labels, ((∑ r ∈ sample, X w r : ℕ) : ℝ)/sample.card ≤ B) :
    ((∑ r ∈ sample, ∑ w ∈ labels, X w r : ℕ) : ℝ)/sample.card ≤
      (labels.card : ℝ)*B := by
  rw [Finset.sum_comm,Nat.cast_sum,Finset.sum_div]
  calc
    _ ≤ ∑ _w ∈ labels, B := Finset.sum_le_sum hX
    _ = _ := by simp

/-- Finite letters on a chain, extended only to make the integer indexing
convenient. The fallback is never used at an edge of the pattern. -/
def readWord (F : ComparedBlocks.Position len → Letter) (c : C) (q : ℤ) : Letter :=
  if h : q ∈ positions 0 (len c) then F ⟨c,⟨q,h⟩⟩ else default

omit [Fintype C] in
@[simp] theorem readWord_on (F : ComparedBlocks.Position len → Letter) (c : C)
    (q : positions 0 (len c)) : readWord len F c q.val = F ⟨c,q⟩ := by
  simp [readWord,q.property]

omit [Fintype C] in
include hs in
theorem word_position (i : Underlying s len) (k : Fin (height s len i)) :
    (k.val : ℤ)+lower s len i ∈ positions 0 (len i.1) := by
  let q := (wordCoordinate s len i).symm k
  have hv := wordCoordinate_val s len i q
  rw [show (wordCoordinate s len i) q = k from Equiv.apply_symm_apply _ _] at hv
  have he : (k.val : ℤ)+lower s len i = q.val := by omega
  rw [he]
  exact full_subset s hs (len i.1) i.2 q.property

end

section Active
open ChainStageLabels
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev activeLen : ActiveChain m j → ℕ := fun c => len c.val

def activeIndex (i : Underlying s (activeLen len m j)) : Underlying s len := ⟨i.1.val,i.2⟩

/-- The active-block subtype counts exactly the full blocks of the active
chains; no inactive full block is inserted into this stage. -/
def activeBlockEquiv : Underlying s (activeLen len m j) ≃ activeBlocks s len m j where
  toFun i := ⟨activeIndex s len m j i,by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.1.property⟩⟩
  invFun i := ⟨⟨i.val.1,(Finset.mem_filter.mp i.property).2⟩,i.val.2⟩
  left_inv i := by cases i; rfl
  right_inv i := by cases i; rfl

include hs in
/-- A permitted full-stage assignment really has the prescribed bins on
every active chain, under the literal integer coordinates. -/
theorem active_bins (cmp : Comparisons (E := E) (traversalLength len m))
    (d : Underlying s len → ℤ) (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    ∀ i, word s (activeLen len m j) (readWord (activeLen len m j) F) i ∈
      binWords (height s (activeLen len m j) i) (d (activeIndex s len m j i)) := by
  obtain ⟨w,_,_,hb,rfl⟩ := (Finset.mem_filter.mp hF).2
  intro i
  have he : word s (activeLen len m j)
      (readWord (activeLen len m j) (fun x => w x.1.val x.2.val)) i =
      word s len w (activeIndex s len m j i) := by
    funext k
    dsimp only [word,readWord]
    rw [dite_eq_left (word_position s hs (activeLen len m j) i k)]
    rfl
  rw [he]
  exact hb (activeIndex s len m j i)

/-- Equality of the literal active bin sum and the filtered global bin sum. -/
theorem active_bin_sum (d : Underlying s len → ℤ) :
    (∑ i : Underlying s (activeLen len m j), (d (activeIndex s len m j i) : ℝ)) =
      ∑ i ∈ activeBlocks s len m j, (d i : ℝ) := by
  calc
    _ = ∑ i : activeBlocks s len m j, (d i.val : ℝ) :=
      Fintype.sum_equiv (activeBlockEquiv s len m j) _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort (activeBlocks s len m j) (fun i => (d i : ℝ))

end Active
variable {C V TV : Type*} [Fintype C] [Fintype V] [Fintype TV]
variable (s : ℝ) (hs : 0 < s) (len : C → ℕ) (first last : C → V)
local instance : DecidableEq Types.Letter := Classical.decEq _

def immersedWords (X : Finset (ComparedBlocks.Position len → Letter)) :
    Finset (ComparedBlocks.Position len → Letter) :=
  X.filter (fun F => Function.Injective (fun a =>
    ((graph len first last).origin a,ChainRealization.label len (readWord len F) a)))

/-- The stage random variable is a literal sum of feasible injective graph
realizations, restricted to the full-word projection and to immersed labels. -/
def count (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (X : Finset (ComparedBlocks.Position len → Letter))
    (r : ConditionedMatchings.Matching (PatternEmbeddings.label outgoing) Types.inverse) : ℕ :=
  ∑ F ∈ immersedWords len first last X,
    StageRealization.realizations (graph len first last)
      (ChainRealization.label len (readWord len F)) outgoing (ChainRealization.pin len pp)
      Types.inverse r

include hs in
/-- The exact stage expectation, including the full prescribed matching
model and all dependencies among repeated edge occurrences. -/
theorem mean_bound (outgoing : TV → Finset Types.Letter) (pp : V → Option TV)
    (X : Finset (ComparedBlocks.Position len → Letter))
    (n p : ℝ) (hp : 0 ≤ p) (d : Underlying s len → ℤ)
    (hbin : ∀ F ∈ X, ∀ i, word s len (readWord len F) i ∈
      binWords (height s len i) (d i))
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤
        n*p*TypeWeights.jointWeight t u)
    (N D R : ℕ) (hD : 2 ≤ D) (hR : 0 < R)
    (hdegree : ∀ v, Nat.card {a : PatternEmbeddings.Dart outgoing //
      PatternEmbeddings.origin outgoing a = v} ≤ D)
    (hsize : ∀ x : PatternEmbeddings.Dart outgoing,
      R + (∑ c, len c) + 4*D^(2*N+1) ≤
        Nat.card {a : PatternEmbeddings.Dart outgoing //
          PatternEmbeddings.label outgoing a = PatternEmbeddings.label outgoing x})
    (hΩ : (ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ ConditionedMatchings.Matching.conditioned
      (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
      (PatternEmbeddings.origin outgoing) N ∅,
        count len first last outgoing pp X r : ℕ) : ℝ) /
      (ConditionedMatchings.Matching.conditioned
        (label := PatternEmbeddings.label outgoing) (bar := Types.inverse)
        (PatternEmbeddings.origin outgoing) N ∅).card ≤
      (X.card : ℝ)*((n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
        p^(∑ c, (len c-1))) / (R : ℝ)^(∑ c, len c) *
        Real.exp (-∑ i, (d i : ℝ))) := by
  have hn0 : 0 ≤ n := (Nat.cast_nonneg (Fintype.card TV)).trans hn
  refine (label_union_mean _ (immersedWords len first last X) _
    (((n^((Finset.univ.filter fun v => pp v = none).card+∑ c, (len c-1)) *
      p^(∑ c, (len c-1))) / (R : ℝ)^(∑ c, len c)) *
      Real.exp (-∑ i, (d i : ℝ))) ?_).trans ?_
  · intro F hF
    obtain ⟨hx,hi⟩ := (Finset.mem_filter.mp hF)
    exact fixed_label_bin_bound s hs len first last outgoing pp n p hp (readWord len F) d
      (hbin F hx) hi hn htable N D R hD hR hdegree hsize hΩ
  · exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Finset.card_filter_le ..)) (by positivity)

end TorsionFreeZeroDivisors.StageExpectation

/-! Finite Fubini for the product of the separately girth-conditioned sides.
The label set here is global: it is not replaced by the product of its two
projections. This is the independence actually used in entropy.tex 396–435. -/
namespace TorsionFreeZeroDivisors.TwoSideMean
open scoped BigOperators Classical

variable {A B W : Type*}

def mean (Ω : Finset A) (X : A → ℕ) : ℝ := (∑ r ∈ Ω, X r : ℕ) / (Ω.card : ℝ)

theorem mean_nonneg (Ω : Finset A) (X : A → ℕ) : 0 ≤ mean Ω X := by
  unfold mean
  positivity

theorem mean_product (ΩA : Finset A) (ΩB : Finset B) (X : A → ℕ) (Y : B → ℕ) :
    mean (ΩA ×ˢ ΩB) (fun r => X r.1 * Y r.2) = mean ΩA X * mean ΩB Y := by
  unfold mean
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, Finset.card_product, Nat.cast_mul, Nat.cast_mul]
  ring

/-- The product model factors only after a whole global label assignment is
fixed. No assertion that the allowed labels on the two sides are independent. -/
theorem fixed_mean_bound (ΩA : Finset A) (ΩB : Finset B)
    (X : A → ℕ) (Y : B → ℕ) {a b : ℝ}
    (ha : mean ΩA X ≤ a) (hb : mean ΩB Y ≤ b) :
    mean (ΩA ×ˢ ΩB) (fun r => X r.1 * Y r.2) ≤ a*b := by
  rw [mean_product]
  exact mul_le_mul ha hb (mean_nonneg ΩB Y) ((mean_nonneg ΩA X).trans ha)

/-- A finite union bound keeps the exact number of global label assignments,
not a product of the sizes of projection sets (which could lose the entropy). -/
theorem label_union (Ω : Finset A) (labels : Finset W) (X : W → A → ℕ)
    {b : ℝ} (hX : ∀ w ∈ labels, mean Ω (X w) ≤ b) :
    mean Ω (fun r => ∑ w ∈ labels, X w r) ≤ (labels.card : ℝ)*b := by
  unfold mean at *
  rw [Finset.sum_comm, Nat.cast_sum, Finset.sum_div]
  calc
    _ ≤ ∑ _w ∈ labels, b := Finset.sum_le_sum hX
    _ = _ := by simp

theorem global_mean_bound (ΩA : Finset A) (ΩB : Finset B) (labels : Finset W)
    (X : W → A → ℕ) (Y : W → B → ℕ) {a b : ℝ}
    (ha : ∀ w ∈ labels, mean ΩA (X w) ≤ a)
    (hb : ∀ w ∈ labels, mean ΩB (Y w) ≤ b) :
    mean (ΩA ×ˢ ΩB) (fun r => ∑ w ∈ labels, X w r.1 * Y w r.2) ≤
      (labels.card : ℝ)*(a*b) := by
  exact label_union _ _ _ fun w hw => fixed_mean_bound _ _ _ _ (ha w hw) (hb w hw)

/-- Product conditioning is literally a product when the girth restriction
is imposed separately on the disjoint sides. -/
theorem filter_product (ΩA : Finset A) (ΩB : Finset B) (PA : A → Prop) (PB : B → Prop) :
    (ΩA ×ˢ ΩB).filter (fun r => PA r.1 ∧ PB r.2) =
      (ΩA.filter PA) ×ˢ (ΩB.filter PB) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_product]
  tauto

end TorsionFreeZeroDivisors.TwoSideMean

namespace TorsionFreeZeroDivisors.TwoSideStage
open scoped Classical BigOperators
open ChainSubdivision PatternEmbeddings ConditionedMatchings BlockAlignment ComparedBlocks RepeatedBlocks
local instance : DecidableEq Types.Letter := Classical.decEq _

/-- A stage on one prescribed side. Its marked vertices do not include any
isolated vertices of inactive chains. The source number of available vertices
is n on EACH side, not the cardinality 2n of their disjoint union. -/
structure Side where
  C : Type
  V : Type
  TV : Type
  fC : Fintype C
  fV : Fintype V
  fTV : Fintype TV
  len : C → ℕ
  first : C → V
  last : C → V
  outgoing : TV → Finset Types.Letter
  pin : V → Option TV
attribute [instance] Side.fC Side.fV Side.fTV

abbrev Side.Word (S : Side) := ComparedBlocks.Position S.len → WordEstimate.Letter
abbrev Side.Match (S : Side) := Matching (label S.outgoing) Types.inverse

def Side.samples (S : Side) (N : ℕ) : Finset S.Match :=
  Matching.conditioned (label := label S.outgoing) (bar := Types.inverse)
    (origin S.outgoing) N ∅

def Side.immersed (S : Side) (F : S.Word) : Prop :=
  Function.Injective (fun a => ((graph S.len S.first S.last).origin a,
    ChainRealization.label S.len (StageExpectation.readWord S.len F) a))

def Side.realizations (S : Side) (F : S.Word) (r : S.Match) : ℕ :=
  StageRealization.realizations (graph S.len S.first S.last)
    (ChainRealization.label S.len (StageExpectation.readWord S.len F))
    S.outgoing (ChainRealization.pin S.len S.pin) Types.inverse r

def Side.internal (S : Side) : ℕ := ∑ c, (S.len c-1)
def Side.edges (S : Side) : ℕ := ∑ c, S.len c
def Side.freeMarks (S : Side) : ℕ := (Finset.univ.filter fun v => S.pin v = none).card

def Side.cost (S : Side) (n p : ℝ) (R : ℕ) : ℝ :=
  (n^(S.freeMarks+S.internal)*p^S.internal)/(R : ℝ)^S.edges

/-- All probability hypotheses are the literal finite matching conditions.
No expected count or entropy estimate is a field of this certificate. -/
structure Conditions (S : Side) (n p : ℝ) (N D R : ℕ) : Prop where
  nonneg : 0 ≤ p
  vertices : (Fintype.card S.TV : ℝ) ≤ n
  table : ∀ t u, t ≠ u →
    (Fintype.card {x : S.TV // t ∈ S.outgoing x ∧ u ∈ S.outgoing x} : ℝ) ≤
      n*p*TypeWeights.jointWeight t u
  degree_lower : 2 ≤ D
  denominator_pos : 0 < R
  degree : ∀ v, Nat.card {a : PatternEmbeddings.Dart S.outgoing // origin S.outgoing a = v} ≤ D
  room : ∀ x : PatternEmbeddings.Dart S.outgoing,
    R+S.edges+4*D^(2*N+1) ≤
      Nat.card {a : PatternEmbeddings.Dart S.outgoing // label S.outgoing a = label S.outgoing x}
  nonempty : (S.samples N).Nonempty

variable (s : ℝ) (hs : 0 < s)

def Side.bins (S : Side) (d : Underlying s S.len → ℤ) (F : S.Word) : Prop :=
  ∀ i, RepeatedBlocks.word s S.len (StageExpectation.readWord S.len F) i ∈
    WordEstimate.binWords (RepeatedBlocks.height s S.len i) (d i)

include hs in
/-- Exact single-side specialization reused at each fixed GLOBAL label. -/
theorem fixed_mean (S : Side) (n p : ℝ) (N D R : ℕ) (h : Conditions S n p N D R)
    (F : S.Word) (hF : S.immersed F) (d : Underlying s S.len → ℤ)
    (hd : S.bins s d F) :
    TwoSideMean.mean (S.samples N) (S.realizations F) ≤
      S.cost n p R * Real.exp (-∑ i, (d i : ℝ)) := by
  exact StageExpectation.fixed_label_bin_bound s hs S.len S.first S.last S.outgoing S.pin
    n p h.nonneg (StageExpectation.readWord S.len F) d hd hF h.vertices h.table
    N D R h.degree_lower h.denominator_pos h.degree h.room h.nonempty

variable {W : Type*}

/-- Only one filter of the global string set; it does not discard comparisons
between sides or enlarge that set to the product of projections. -/
def immersedLabels (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word) : Finset W :=
  X.filter fun w => A.immersed (WA w) ∧ B.immersed (WB w)

def count (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (r : A.Match × B.Match) : ℕ :=
  ∑ w ∈ immersedLabels A B X WA WB, A.realizations (WA w) r.1 * B.realizations (WB w) r.2

include hs in
/-- Literal two-side stage first moment. Conditioning factors into the product
of the girth restrictions; repeated-edge dependencies stay inside each matching. -/
theorem mean_bound (A B : Side) (X : Finset W) (WA : W → A.Word) (WB : W → B.Word)
    (n p : ℝ) (N D R : ℕ) (hA : Conditions A n p N D R) (hB : Conditions B n p N D R)
    (dA : Underlying s A.len → ℤ) (dB : Underlying s B.len → ℤ)
    (hdA : ∀ w ∈ X, A.bins s dA (WA w)) (hdB : ∀ w ∈ X, B.bins s dB (WB w)) :
    TwoSideMean.mean ((A.samples N) ×ˢ (B.samples N)) (count A B X WA WB) ≤
      (X.card : ℝ)*((A.cost n p R * B.cost n p R) *
        Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ)))) := by
  have hn : 0 ≤ n := (Nat.cast_nonneg (Fintype.card A.TV)).trans hA.vertices
  have hp := hA.nonneg
  have hcost : 0 ≤ (A.cost n p R * B.cost n p R) *
      Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ))) := by
    unfold Side.cost
    positivity
  have he := TwoSideMean.global_mean_bound (A.samples N) (B.samples N)
    (immersedLabels A B X WA WB) (fun w => A.realizations (WA w)) (fun w => B.realizations (WB w))
    (fun w hw => fixed_mean s hs A n p N D R hA (WA w)
      (Finset.mem_filter.mp hw).2.1 dA (hdA w (Finset.mem_filter.mp hw).1))
    (fun w hw => fixed_mean s hs B n p N D R hB (WB w)
      (Finset.mem_filter.mp hw).2.2 dB (hdB w (Finset.mem_filter.mp hw).1))
  have eq : (A.cost n p R * Real.exp (-∑ i, (dA i : ℝ))) *
      (B.cost n p R * Real.exp (-∑ i, (dB i : ℝ))) =
      (A.cost n p R * B.cost n p R)*
        Real.exp (-(∑ i, (dA i : ℝ))-(∑ i, (dB i : ℝ))) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  rw [eq] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (Finset.card_filter_le ..)) hcost)

/-- No entropy factor 2 is introduced when the two sides are combined. -/
theorem cost_product (A B : Side) (n p : ℝ) (R : ℕ) :
    A.cost n p R * B.cost n p R =
      (n^(A.freeMarks+A.internal+B.freeMarks+B.internal) * p^(A.internal+B.internal)) /
        (R : ℝ)^(A.edges+B.edges) := by
  simp only [Side.cost, pow_add]
  ring

end TorsionFreeZeroDivisors.TwoSideStage

end

end OAI
