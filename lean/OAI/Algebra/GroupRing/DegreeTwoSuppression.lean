import Mathlib
import OAI.Algebra.GroupRing.WeightedPortMoore

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.DegreeTwoSuppression
open Function
open scoped Classical
open TorsionFreeZeroDivisors ChainSuppression PortSubdivision
variable {V D : Type*} [Fintype D]

def out (o : D → V) (v : V) : Finset D := Finset.univ.filter (fun d => o d=v)
@[simp] lemma mem_out (o : D → V) (v : V) (d : D) : d∈out o v ↔ o d=v := by
  simp [out]

lemma unique_other (o : D → V) (d : D) (hc : (out o (o d)).card=2) :
    ∃! e : D, o e=o d ∧ e≠d := by
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hc
  have hm (e : D) : o e=o d ↔ e=a ∨ e=b := by
    rw [← mem_out,hs]
    simp
  have hd : d=a ∨ d=b := (hm d).mp rfl
  rcases hd with rfl | rfl
  · refine ⟨b,⟨(hm b).mpr (Or.inr rfl),Ne.symm hab⟩,?_⟩
    intro e he
    exact ((hm e).mp he.1).resolve_left he.2
  · refine ⟨a,⟨(hm a).mpr (Or.inl rfl),hab⟩,?_⟩
    intro e he
    exact ((hm e).mp he.1).resolve_right he.2

variable (o : D → V) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out o v).card=2)

def turn (d : D) : D := if h : mark (o d) then d else
  Classical.choose (unique_other o d (h2 (o d) h)).exists

lemma turn_of_mark (d : D) (hd : mark (o d)) : turn o mark h2 d=d := by
  simp [turn,hd]

lemma turn_of_unmarked (d : D) (hd : ¬mark (o d)) :
    o (turn o mark h2 d)=o d ∧ turn o mark h2 d≠d := by
  simpa only [turn,dite_eq_right hd] using
    Classical.choose_spec (unique_other o d (h2 (o d) hd)).exists

lemma turn_origin (d : D) : o (turn o mark h2 d)=o d := by
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd]
  · exact (turn_of_unmarked o mark h2 d hd).1

lemma turn_fixed_iff (d : D) : turn o mark h2 d=d ↔ mark (o d) := by
  constructor
  · intro he
    by_contra hd
    exact (turn_of_unmarked o mark h2 d hd).2 he
  · exact turn_of_mark o mark h2 d

lemma turn_involutive : Involutive (turn o mark h2) := by
  intro d
  by_cases hd : mark (o d)
  · rw [turn_of_mark o mark h2 d hd,turn_of_mark o mark h2 d hd]
  · have he := turn_of_unmarked o mark h2 d hd
    have hemark : ¬mark (o (turn o mark h2 d)) := he.1 ▸ hd
    have hef := turn_of_unmarked o mark h2 (turn o mark h2 d) hemark
    exact (unique_other o (turn o mark h2 d) (h2 _ hemark)).unique hef
      ⟨he.1.symm,he.2.symm⟩

/-- Darts of the actual suppressed multigraph: all outgoing darts at marked
vertices. The return map pairs them by the unique maximal degree-two chain. -/
def suppressed (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2) :
    PortGraph V {d : D // turn Γ.origin mark h2 d=d} where
  origin d := Γ.origin d.val
  reverse := endpoint Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2)
  reverse_reverse := endpoint_involutive Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2)
  reverse_ne := endpoint_ne Γ.reverse (turn Γ.origin mark h2)
    Γ.reverse_reverse (turn_involutive Γ.origin mark h2) Γ.reverse_ne

/-- Positive integral lengths count exactly the original directed edges along
the chains; the two orientations have the same length. -/
def chainLength (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : ℕ :=
  length Γ.reverse (turn Γ.origin mark h2) Γ.reverse_reverse
    (turn_involutive Γ.origin mark h2) d.val d.property

lemma chainLength_pos (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) : 0 < chainLength Γ mark h2 d :=
  length_pos _ _ _ _ _ _

lemma chainLength_reverse (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (d : {d : D // turn Γ.origin mark h2 d=d}) :
    chainLength Γ mark h2 ((suppressed Γ mark h2).reverse d)=chainLength Γ mark h2 d :=
  length_endpoint _ _ _ _ _

lemma chainLength_total (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2) :
    ∑ d : {d : D // turn Γ.origin mark h2 d=d}, chainLength Γ mark h2 d ≤ Fintype.card D :=
  total_length_le _ _ _ _

lemma suppressed_degree (Γ : PortGraph V D) (mark : V → Prop)
    (h2 : ∀ v, ¬mark v → (out Γ.origin v).card=2)
    (v : V) (hv : mark v) :
    (out (suppressed Γ mark h2).origin v).card = (out Γ.origin v).card := by
  classical
  apply Finset.card_bij (fun d _ => d.val)
  · intro d hd
    exact (mem_out Γ.origin v d.val).mpr ((mem_out _ v d).mp hd)
  · intro d _ e _ he
    exact Subtype.ext he
  · intro d hd
    have ho : Γ.origin d=v := (mem_out _ v d).mp hd
    let e : {d : D // turn Γ.origin mark h2 d=d} :=
      ⟨d,(turn_fixed_iff Γ.origin mark h2 d).mpr (ho ▸ hv)⟩
    exact ⟨e,(mem_out _ v e).mpr ho,rfl⟩

/-- Minimum degree two becomes minimum degree three whenever a component has
some branching. Pure circle components give no darts and are treated separately. -/
lemma suppressed_min_degree (Γ : PortGraph V D)
    (hmin : ∀ d, 2 ≤ (out Γ.origin (Γ.origin d)).card) :
    let mark := fun v => (out Γ.origin v).card≠2
    let h2 := fun v (h : ¬mark v) => Classical.not_not.mp h
    ∀ d, 3 ≤ (out (suppressed Γ mark h2).origin ((suppressed Γ mark h2).origin d)).card := by
  intro mark h2 d
  have hm : mark (Γ.origin d.val) := (turn_fixed_iff Γ.origin mark h2 d.val).mp d.property
  change 3 ≤ (out (suppressed Γ mark h2).origin (Γ.origin d.val)).card
  rw [suppressed_degree Γ mark h2 _ hm]
  have hc := hmin d.val
  dsimp [mark] at hm
  omega

end TorsionFreeZeroDivisors.DegreeTwoSuppression

namespace TorsionFreeZeroDivisors.SuppressedMoore
open Function SimpleGraph
open scoped Classical
open TorsionFreeZeroDivisors PortSubdivision WeightedMoore WeightedPortMoore
variable {V D : Type*} [Fintype D] (Γ : PortGraph V D)
    (mark : V → Prop) (h2 : ∀ v, ¬mark v → (DegreeTwoSuppression.out Γ.origin v).card=2)

local notation "τ" => DegreeTwoSuppression.turn Γ.origin mark h2
local notation "hτ" => DegreeTwoSuppression.turn_involutive Γ.origin mark h2
local notation "F" => ChainSuppression.next Γ.reverse τ
local notation "B" => {d : D // τ d=d}
local notation "Γ'" => DegreeTwoSuppression.suppressed Γ mark h2
local notation "len" => DegreeTwoSuppression.chainLength Γ mark h2

def iterChain (f : D → D) : (n : ℕ) → D → Chain D n
  | 0, x => x
  | n+1, x => (x,iterChain f n (f x))

omit [Fintype D] in
@[simp] lemma head_iterChain (f : D → D) (n : ℕ) (x : D) : head (iterChain f n x)=x := by
  cases n <;> rfl

omit [Fintype D] in
@[simp] lemma last_iterChain (f : D → D) (n : ℕ) (x : D) :
    last (iterChain f n x)=f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change last (iterChain f n (f x))=f^[n+1] x
    rw [ih,iterate_succ_apply]

lemma iterChain_good (n : ℕ) (x : D)
    (hm : ∀ i : ℕ, 0 < i → i ≤ n → τ (F^[i] x) ≠ F^[i] x) :
    Good Γ (iterChain F n x) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,?_⟩
    · change PortWalk.step Γ.origin Γ.reverse x (head (iterChain F n (F x)))
      rw [head_iterChain]
      have hne : F x ≠ Γ.reverse x := by
        intro he
        have h0 : τ (F x)=F x := by
          change τ (τ (Γ.reverse x))=F x
          rw [hτ,he]
        exact hm 1 (by omega) (by omega) (by simpa only [iterate_one] using h0)
      exact ⟨(DegreeTwoSuppression.turn_origin Γ.origin mark h2 (Γ.reverse x)).symm,hne⟩
    · apply ih (F x)
      intro i hi hin
      have his : i+1≤n+1 := by omega
      simpa only [iterate_succ_apply] using hm (i+1) (by omega) his

lemma chain_good (d : B) : Good Γ (iterChain F (len d-1) d.val) := by
  apply iterChain_good
  intro i hi hil
  exact ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse hτ d.val d.property hi
    (by change i < len d; have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d; omega)

lemma chain_last (d : B) : Γ.reverse (last (iterChain F (len d-1) d.val)) = ((Γ').reverse d).val := by
  rw [last_iterChain]
  have hf := ((Γ').reverse d).property
  change τ (F^[len d] d.val)=F^[len d] d.val at hf
  have hk : len d=(len d-1)+1 := by
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    omega
  conv_lhs at hf => rw [hk,iterate_succ_apply']
  change τ (τ (Γ.reverse (F^[len d-1] d.val)))=F^[len d] d.val at hf
  rw [hτ] at hf
  exact hf

/-- Literal expansion of one suppressed edge into the original graph. Its
endpoints are the two marked ports, and every internal vertex is degree two. -/
def chainWalk (d : B) : Γ.subdivision.Walk (.inr d.val) (.inr ((Γ').reverse d).val) :=
  (draw Γ (iterChain F (len d-1) d.val) (chain_good Γ mark h2 d)).copy
    (congrArg Sum.inr (head_iterChain F _ _)) (congrArg Sum.inr (chain_last Γ mark h2 d))

lemma chainWalk_reduced (d : B) : (chainWalk Γ mark h2 d).edges.IsChain (·≠·) := by
  simpa only [chainWalk,Walk.edges_copy] using
    draw_reduced Γ (iterChain F (len d-1) d.val) (chain_good Γ mark h2 d)

omit [Fintype D] in
lemma cost_iterChain_one (f : D → D) (n : ℕ) (d : D) :
    cost (fun _ => (1:ℝ)) (iterChain f n d) = n+1 := by
  induction n generalizing d with
  | zero => simp [cost]
  | succ n ih =>
    change 1+cost (fun _ => (1:ℝ)) (iterChain f n (f d))=(n+1:ℕ)+1
    rw [ih]
    push_cast
    ring

lemma chainWalk_weight (d : B) :
    WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) (chainWalk Γ mark h2 d)=len d := by
  simp only [chainWalk,WeightedCycles.weight,Walk.edges_copy]
  change WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ)))
    (draw Γ (iterChain F (len d-1) d.val) (chain_good Γ mark h2 d))=len d
  rw [draw_weight Γ _ (fun _ => rfl),cost_iterChain_one]
  have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
  norm_cast
  omega

/- The variable-length concatenation keeps all occurrences: no quotient by
cyclic words and no assumption that the original paths are embedded. -/
omit [Fintype D] in
def join : {k : ℕ} → Chain D k → (Σ l, Chain D l) → (Σ l, Chain D l)
  | 0, d, ⟨l,q⟩ => ⟨l+1,(d,q)⟩
  | _+1, p, q => let r := join p.2 q; ⟨r.1+1,(p.1,r.2)⟩

omit [Fintype D] in
lemma join_head {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    head (join p q).2 = head p := by cases k <;> rfl

omit [Fintype D] in
lemma join_last {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    last (join p q).2 = last q.2 := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih p.2

omit [Fintype D] in
lemma join_cost (w : D → ℝ) {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    cost w (join p q).2 = cost w p + cost w q.2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change w p.1+cost w (join p.2 q).2 = (w p.1+cost w p.2)+cost w q.2
    rw [ih]; ring

omit [Fintype D] in
lemma join_good {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l)
    (hp : Good Γ p) (hq : Good Γ q.2)
    (hlink : PortWalk.step Γ.origin Γ.reverse (last p) (head q.2)) :
    Good Γ (join p q).2 := by
  induction k with
  | zero => exact ⟨hlink,hq⟩
  | succ k ih =>
    change PortWalk.step Γ.origin Γ.reverse p.1 (head (join p.2 q).2) ∧ _
    rw [join_head]
    exact ⟨hp.1,ih p.2 hp.2 hlink⟩

omit [Fintype D] in
def outWord : {k : ℕ} → Chain D k → List D
  | 0, d => [d]
  | _+1, p => p.1 :: outWord p.2

omit [Fintype D] in
lemma outWord_injective (k : ℕ) : Injective (@outWord D k) := by
  induction k with
  | zero => intro p q h; exact List.cons.inj h |>.1
  | succ k ih =>
    intro p q h
    exact Prod.ext (List.cons.inj h).1 (ih (List.cons.inj h).2)

omit [Fintype D] in
lemma outWord_join {k : ℕ} (p : Chain D k) (q : Σ l, Chain D l) :
    outWord (join p q).2 = outWord p ++ outWord q.2 := by
  induction k with
  | zero => rfl
  | succ k ih => change p.1 :: outWord (join p.2 q).2 = _; rw [ih]; rfl

omit [Fintype D] in
def pickEven : List D → List D
  | [] => []
  | [d] => [d]
  | d::_::ds => d::pickEven ds

omit [Fintype D] in
lemma pickEven_portWord {k : ℕ} (p : Chain D k) :
    pickEven (portWord Γ p) = outWord p := by
  induction k with
  | zero => rfl
  | succ k ih => change p.1::pickEven (portWord Γ p.2)=_; rw [ih]; rfl

lemma iterChain_no_marks (n : ℕ) (d : D)
    (hn : ∀ i : ℕ, i≤n → τ (F^[i] d) ≠ F^[i] d) :
    (outWord (iterChain F n d)).filter (fun d => τ d=d) = [] := by
  induction n generalizing d with
  | zero => simpa [outWord,iterChain] using hn 0 (by omega)
  | succ n ih =>
    change (d::outWord (iterChain F n (F d))).filter (fun d => τ d=d)=[]
    rw [List.filter_cons_of_neg (by simpa using hn 0 (by omega))]
    apply ih
    intro i hi
    simpa only [iterate_succ_apply] using hn (i+1) (by omega)

lemma chain_one_mark (d : B) :
    (outWord (iterChain F (len d-1) d.val)).filter (fun d => τ d=d) = [d.val] := by
  have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
  have hn (i : ℕ) (hi : 0 < i) (hil : i < len d) : τ (F^[i] d.val)≠F^[i] d.val :=
    ChainSuppression.no_internal_mark Γ.reverse τ Γ.reverse_reverse hτ d.val d.property hi hil
  generalize he : len d-1 = n
  cases n with
  | zero => simp [outWord,iterChain,d.property]
  | succ n =>
    change (d.val::outWord (iterChain F n (F d.val))).filter (fun d => τ d=d)=[d.val]
    rw [List.filter_cons_of_pos (by simpa using d.property)]
    rw [iterChain_no_marks]
    intro i hi
    simpa only [iterate_succ_apply] using hn (i+1) (by omega) (by omega)

/-- Expand every macro-edge, preserving the ordered path occurrence data. -/
def expand : {k : ℕ} → Chain B k → (Σ l, Chain D l)
  | 0, d => ⟨len d-1,iterChain F (len d-1) d.val⟩
  | _+1, p => join (iterChain F (len p.1-1) p.1.val) (expand p.2)

lemma expand_head {k : ℕ} (p : Chain B k) : head (expand Γ mark h2 p).2 = (head p).val := by
  cases k with
  | zero => exact head_iterChain F _ _
  | succ k => change head (join _ _).2 = p.1.val; rw [join_head,head_iterChain]

lemma expand_last {k : ℕ} (p : Chain B k) :
    Γ.reverse (last (expand Γ mark h2 p).2) = ((Γ').reverse (last p)).val := by
  induction k with
  | zero => exact chain_last Γ mark h2 p
  | succ k ih => change Γ.reverse (last (join _ _).2)=_; rw [join_last]; exact ih p.2

lemma expand_good {k : ℕ} (p : Chain B k) (hp : Good (Γ') p) :
    Good Γ (expand Γ mark h2 p).2 := by
  induction k with
  | zero => exact chain_good Γ mark h2 p
  | succ k ih =>
    apply join_good Γ _ _ (chain_good Γ mark h2 p.1) (ih p.2 hp.2)
    unfold PortWalk.step
    rw [chain_last,expand_head]
    exact ⟨hp.1.1,fun he => hp.1.2 (Subtype.ext he)⟩

lemma expand_cost {k : ℕ} (p : Chain B k) :
    cost (fun _ : D => (1:ℝ)) (expand Γ mark h2 p).2 = cost (fun d => (len d : ℝ)) p := by
  have hs (d : B) : cost (fun _ : D => (1:ℝ)) (iterChain F (len d-1) d.val) = len d := by
    rw [cost_iterChain_one]
    have hp := DegreeTwoSuppression.chainLength_pos Γ mark h2 d
    norm_cast
    omega
  induction k with
  | zero => exact hs p
  | succ k ih => change cost _ (join _ _).2 = _; rw [join_cost,hs,ih]; rfl

lemma expand_marks {k : ℕ} (p : Chain B k) :
    (outWord (expand Γ mark h2 p).2).filter (fun d => τ d=d) = (outWord p).map Subtype.val := by
  induction k with
  | zero => exact chain_one_mark Γ mark h2 p
  | succ k ih =>
    change (outWord (join _ _).2).filter _ = _
    rw [outWord_join,List.filter_append,chain_one_mark,ih]
    rfl

/-- The stationary Moore collision in the suppressed graph expands to a
literal original cycle. Girth is imposed only on the original graph. -/
theorem original_short_cycle [Nonempty B]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out (Γ').origin ((Γ').origin d)).card) :
    let k := Nat.log 2 (Fintype.card B) + 2
    ∃ (a : V ⊕ D) (c : Γ.subdivision.Walk a a), c.IsCycle ∧
      WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c ≤
        4*(k+1:ℝ)*(∑ d : B, (len d : ℝ))/Fintype.card B := by
  let T := PortWalk.transition (Γ').origin (Γ').reverse
  have ht : Transition T := PortWalk.transition_law (Γ').origin (Γ').reverse
    (Γ').reverse_reverse hdeg
  have hlpos (d : B) : (0:ℝ) < len d := by
    exact_mod_cast DegreeTwoSuppression.chainLength_pos Γ mark h2 d
  obtain ⟨p,q,hne,hh,hl,hp,hq,hcost⟩ := logarithmic_short_collision ht (fun d => (len d : ℝ)) hlpos
  have hgp : Good (Γ') p := positive_good (Γ') ht p hp
  have hgq : Good (Γ') q := positive_good (Γ') ht q hq
  let ep := expand Γ mark h2 p
  let eq := expand Γ mark h2 q
  have hep : Good Γ ep.2 := expand_good Γ mark h2 p hgp
  have heq : Good Γ eq.2 := expand_good Γ mark h2 q hgq
  have heh : head eq.2 = head ep.2 := by
    change head (expand Γ mark h2 q).2=head (expand Γ mark h2 p).2
    rw [expand_head,expand_head,hh]
  have hel : Γ.reverse (last eq.2) = Γ.reverse (last ep.2) := by
    change Γ.reverse (last (expand Γ mark h2 q).2)=Γ.reverse (last (expand Γ mark h2 p).2)
    rw [expand_last,expand_last,hl]
  let qp : Γ.subdivision.Walk (.inr (head ep.2)) (.inr (Γ.reverse (last ep.2))) :=
    (draw Γ eq.2 heq).copy (congrArg Sum.inr heh) (congrArg Sum.inr hel)
  have hqp : draw Γ ep.2 hep ≠ qp := by
    intro he
    have hr := congrArg (fun r => r.support.filterMap onlyPort) he
    simp only [qp,Walk.support_copy,draw_portWord] at hr
    have ho := congrArg pickEven hr
    simp only [pickEven_portWord] at ho
    have hm := congrArg (fun ds => ds.filter (fun d => τ d=d)) ho
    change (outWord (expand Γ mark h2 p).2).filter _ =
      (outWord (expand Γ mark h2 q).2).filter _ at hm
    rw [expand_marks,expand_marks] at hm
    exact hne (outWord_injective _ ((List.map_inj_right (fun _ _ => Subtype.ext)).mp hm))
  have hqred : qp.edges.IsChain (· ≠ ·) := by
    simpa only [qp,Walk.edges_copy] using draw_reduced Γ eq.2 heq
  have hwp : WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) (draw Γ ep.2 hep) =
      cost (fun d => (len d : ℝ)) p := by
    rw [draw_weight Γ _ (fun _ => rfl)]
    exact expand_cost Γ mark h2 p
  have hwq : WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) qp =
      cost (fun d => (len d : ℝ)) q := by
    simp only [qp,WeightedCycles.weight,Walk.edges_copy]
    change WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) (draw Γ eq.2 heq)=_
    rw [draw_weight Γ _ (fun _ => rfl)]
    exact expand_cost Γ mark h2 q
  obtain ⟨a,c,hc,hwc⟩ := WeightedCycles.distinct_reduced_cycle
    (edgeWeight (fun _ : D => (1:ℝ))) (edgeWeight_nonneg _ (fun _ => by norm_num))
    (draw Γ ep.2 hep) qp hqp (draw_reduced Γ ep.2 hep) hqred
  refine ⟨a,c,hc,?_⟩
  rw [hwp,hwq] at hwc
  exact hwc.trans hcost

/-- Actual branch-port complexity from original edge count and original girth,
without an a priori graph-rank or chain-count hypothesis. -/
theorem original_dart_inequality [Nonempty B]
    (hdeg : ∀ d, 3 ≤ (PortWalk.out (Γ').origin ((Γ').origin d)).card)
    (L C : ℝ) (hL : 0 < L)
    (htotal : (Fintype.card D : ℝ) ≤ 2*C*L)
    (hgirth : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
      L ≤ WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c) :
    (Fintype.card B : ℝ) ≤ 8*C*(Nat.log 2 (Fintype.card B)+3:ℝ) := by
  obtain ⟨a,c,hc,hbound⟩ := original_short_cycle Γ mark h2 hdeg
  have hD : (0:ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  have he := (le_div_iff₀ hD).mp ((hgirth a c hc).trans hbound)
  have hs : (∑ d : B, (len d : ℝ)) ≤ Fintype.card D := by
    exact_mod_cast DegreeTwoSuppression.chainLength_total Γ mark h2
  have hn : (0:ℝ) ≤ 4*((Nat.log 2 (Fintype.card B)+2:ℕ)+1:ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left (hs.trans htotal) hn
  push_cast at he hm
  nlinarith

omit [Fintype D] in
/-- Uniformly many branch ports in an actual finite graph of minimum degree
two with O(L) edges and girth L. Pure circles contribute no branch ports. -/
theorem bounded_branch_ports (C : ℝ) (hC : 0 ≤ C) :
    ∃ R : ℕ, ∀ {V D : Type} [Fintype D] (Γ : PortGraph V D)
      (_ : ∀ d, 2 ≤ (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card)
      (L : ℝ) (_ : 0 < L)
      (_ : (Fintype.card D : ℝ) ≤ 2*C*L)
      (_ : ∀ a (c : Γ.subdivision.Walk a a), c.IsCycle →
          L ≤ WeightedCycles.weight (edgeWeight (fun _ : D => (1:ℝ))) c),
      (Finset.univ.filter (fun d : D =>
        (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card≠2)).card ≤ R := by
  obtain ⟨R,hR⟩ := logarithmic_inequality_bounded (8*C) (by positivity)
  refine ⟨R,?_⟩
  intro V D _ Γ hmin L hL htotal hg
  let mark := fun v => (DegreeTwoSuppression.out Γ.origin v).card≠2
  let h2 := fun v (h : ¬mark v) => Classical.not_not.mp h
  let CoreD := {d : D // DegreeTwoSuppression.turn Γ.origin mark h2 d=d}
  have he : (Finset.univ.filter (fun d : D =>
      (DegreeTwoSuppression.out Γ.origin (Γ.origin d)).card≠2)).card = Fintype.card CoreD := by
    change (Finset.univ.filter (fun d : D => mark (Γ.origin d))).card = _
    simpa only [CoreD,Fintype.card_subtype] using congrArg Finset.card (show
      Finset.univ.filter (fun d : D => mark (Γ.origin d)) =
      Finset.univ.filter (fun d : D => DegreeTwoSuppression.turn Γ.origin mark h2 d=d) by
        ext d; simp [DegreeTwoSuppression.turn_fixed_iff])
  rw [he]
  cases isEmpty_or_nonempty CoreD with
  | inl hi => have := hi; rw [Fintype.card_eq_zero]; exact Nat.zero_le R
  | inr hi =>
    have := hi
    apply hR
    apply original_dart_inequality Γ mark h2 ?_ L C hL htotal hg
    exact DegreeTwoSuppression.suppressed_min_degree Γ hmin

end TorsionFreeZeroDivisors.SuppressedMoore

end

end OAI
