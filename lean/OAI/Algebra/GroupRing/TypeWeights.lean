import Mathlib
import OAI.Algebra.GroupRing.PatternCount
import OAI.Algebra.GroupRing.WordEstimate

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.TypeWeights
open TorsionFreeZeroDivisors.Types

/-- The conditional joint-incidence table in the manuscript, before excluding
cancellation. Arguments here are the two outgoing letters at the vertex. -/
def jointWeight : Letter → Letter → ℝ
  | .inl _, .inl _ => 1/129
  | .inl _, .inr _ => 129/16513
  | .inr _, .inl _ => 129/16513
  | .inr _, .inr _ => 1

def turnWeight (t u : Letter) : ℝ := if u = inverse t then 0 else jointWeight (inverse t) u

/-- The finite geometric incidence table equals the analytic table, without
changing the given inverse pairing or field. -/
theorem jointWeight_signed (t u : Signed) :
    jointWeight (inverse (signedLetter t)) (signedLetter u) = WordEstimate.baseWeight t u := by
  rw [show inverse (signedLetter t) = signedLetter (WordEstimate.inverse t) by
    rcases t with ⟨g,b⟩; exact inverse_signed g b]
  rcases t with ⟨i | i,b⟩ <;> rcases u with ⟨j | j,c⟩ <;>
    cases b <;> cases c <;>
    simp [signedLetter,jointWeight,WordEstimate.baseWeight,
      WordEstimate.inverse,WordEstimate.p]

theorem turnWeight_signed (t u : Signed) :
    turnWeight (signedLetter t) (signedLetter u) = WordEstimate.weight t u := by
  unfold turnWeight
  rw [jointWeight_signed]
  rw [show inverse (signedLetter t) = signedLetter (WordEstimate.inverse t) by
    rcases t with ⟨g,b⟩; exact inverse_signed g b]
  simp only [Equiv.apply_eq_iff_eq]
  rfl

theorem jointWeight_comm (t u : Letter) : jointWeight t u = jointWeight u t := by
  cases t <;> cases u <;> rfl

/-- At an internal chain vertex of side B this is an exact count. -/
theorem joint_countB (rep : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {v : VertexB rep // a ∈ outgoingB v ∧ b ∈ outgoingB v} : ℝ) =
      (Fintype.card (VertexB rep) : ℝ) * (129/16513) * jointWeight a b := by
  rw [card_vertexB]
  rcases a with p | e <;> rcases b with q | f
  · have hpq : p ≠ q := fun h => hab (congrArg Sum.inl h)
    rw [show Fintype.card {v : VertexB rep // Sum.inl p ∈ outgoingB v ∧ Sum.inl q ∈ outgoingB v} =
      33026*rep by simpa [outgoingB,card_slotB] using joint_ordinary extrasB rep p q hpq]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · rw [show Fintype.card {v : VertexB rep // Sum.inl p ∈ outgoingB v ∧ Sum.inr f ∈ outgoingB v} =
      129*258*rep by simpa [outgoingB,slotB_extra_frequency] using joint_mixed extrasB rep p f]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · have he' : Fintype.card {v : VertexB rep // Sum.inr e ∈ outgoingB v ∧ Sum.inl q ∈ outgoingB v} =
        Fintype.card {v : VertexB rep // Sum.inl q ∈ outgoingB v ∧ Sum.inr e ∈ outgoingB v} := by
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
    rw [he',show Fintype.card {v : VertexB rep // Sum.inl q ∈ outgoingB v ∧ Sum.inr e ∈ outgoingB v} =
      129*258*rep by simpa [outgoingB,slotB_extra_frequency] using joint_mixed extrasB rep q e]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring
  · rw [show Fintype.card {v : VertexB rep // Sum.inr e ∈ outgoingB v ∧ Sum.inr f ∈ outgoingB v} =
      16513*258*rep by simpa [outgoingB,slotB_extra_joint] using joint_extras extrasB rep e f]
    simp only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,jointWeight]
    ring

/-- The A-side conditional table is dominated by the B-side table, with the
source's factor 1/2 for distinct extras. -/
theorem joint_countA_le (rep : ℕ) (a b : Letter) (hab : a ≠ b) :
    (Fintype.card {v : VertexA rep // a ∈ outgoingA v ∧ b ∈ outgoingA v} : ℝ) ≤
      (Fintype.card (VertexA rep) : ℝ) * (129/16513) * jointWeight a b := by
  rw [card_vertexA]
  rcases a with p | e <;> rcases b with q | f
  · have hpq : p ≠ q := fun h => hab (congrArg Sum.inl h)
    rw [show Fintype.card {v : VertexA rep // Sum.inl p ∈ outgoingA v ∧ Sum.inl q ∈ outgoingA v} =
      33026*rep by simpa [outgoingA,card_slotA] using joint_ordinary extrasA rep p q hpq]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · rw [show Fintype.card {v : VertexA rep // Sum.inl p ∈ outgoingA v ∧ Sum.inr f ∈ outgoingA v} =
      129*258*rep by simpa [outgoingA,slotA_extra_frequency] using joint_mixed extrasA rep p f]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · rw [show Fintype.card {v : VertexA rep // Sum.inr e ∈ outgoingA v ∧ Sum.inl q ∈ outgoingA v} =
        Fintype.card {v : VertexA rep // Sum.inl q ∈ outgoingA v ∧ Sum.inr e ∈ outgoingA v} by
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))]
    rw [show Fintype.card {v : VertexA rep // Sum.inl q ∈ outgoingA v ∧ Sum.inr e ∈ outgoingA v} =
      129*258*rep by simpa [outgoingA,slotA_extra_frequency] using joint_mixed extrasA rep q e]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]
  · have hef : e ≠ f := fun h => hab (congrArg Sum.inr h)
    rw [show Fintype.card {v : VertexA rep // Sum.inr e ∈ outgoingA v ∧ Sum.inr f ∈ outgoingA v} =
      16513*129*rep by simpa [outgoingA,slotA_extra_joint e f hef] using joint_extras extrasA rep e f]
    push_cast
    simp only [jointWeight]
    nlinarith [Nat.cast_nonneg (α := ℝ) rep]

theorem internal_countB (rep : ℕ) (t u : Letter) (h : u ≠ inverse t) :
    (Fintype.card {v : VertexB rep // inverse t ∈ outgoingB v ∧ u ∈ outgoingB v} : ℝ) =
      (Fintype.card (VertexB rep) : ℝ) * (129/16513) * turnWeight t u := by
  simpa only [turnWeight,ite_eq_right h] using joint_countB rep (inverse t) u h.symm

theorem internal_countA (rep : ℕ) (t u : Letter) (h : u ≠ inverse t) :
    (Fintype.card {v : VertexA rep // inverse t ∈ outgoingA v ∧ u ∈ outgoingA v} : ℝ) ≤
      (Fintype.card (VertexA rep) : ℝ) * (129/16513) * turnWeight t u := by
  simpa only [turnWeight,ite_eq_right h] using joint_countA_le rep (inverse t) u h.symm

end TorsionFreeZeroDivisors.TypeWeights

namespace TorsionFreeZeroDivisors.StageRealization
open scoped Classical BigOperators
open PortSubdivision ConditionedMatchings PatternEmbeddings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

/-- Actual vertex carriers: all outgoing template ports must be available;
`pin` imposes exactly the prescribed images, not extra random conditions. -/
def allowed (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
    (pin : PV → Option TV) (v : PV) : Finset TV :=
  Finset.univ.filter fun x => (∀ d, Γ.origin d = v → plabel d ∈ outgoing x) ∧
    ∀ y, pin v = some y → x = y

omit [Fintype PV] [Fintype T] in
theorem allowed_ports (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) :
    ∀ v x, x ∈ allowed Γ plabel outgoing pin v →
      ∀ d, Γ.origin d = v → plabel d ∈ outgoing x := by
  intro v x hx
  exact (Finset.mem_filter.mp hx).2.1

omit [Fintype PV] [Fintype T] in
theorem allowed_card_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) :
    (allowed Γ plabel outgoing pin v).card ≤ Fintype.card TV :=
  Finset.card_le_univ _

omit [Fintype PV] [Fintype T] in
theorem pinned_card_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) (y : TV)
    (hp : pin v = some y) : (allowed Γ plabel outgoing pin v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact ((Finset.mem_filter.mp ha).2.2 y hp).trans
    ((Finset.mem_filter.mp hb).2.2 y hp).symm

omit [Fintype PV] [Fintype T] in
/-- A turn at an internal chain vertex restricts its image to the *joint*
carrier. This does not assume independence of consecutive turns. -/
theorem allowed_turn_le (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (v : PV) (a b : PD)
    (ha : Γ.origin a = v) (hb : Γ.origin b = v) :
    (allowed Γ plabel outgoing pin v).card ≤
      Fintype.card {x : TV // plabel a ∈ outgoing x ∧ plabel b ∈ outgoing x} := by
  rw [Fintype.card_subtype]
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    allowed_ports Γ plabel outgoing pin v x hx a ha,
    allowed_ports Γ plabel outgoing pin v x hx b hb⟩

/-- Concrete realization count for one fixed immersed labeling. -/
def realizations (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (bar : T → T)
    (r : Matching (label outgoing) bar) : ℕ :=
  (Finset.univ.filter fun f : VertexMap (allowed Γ plabel outgoing pin) =>
    ∀ d, r.val (dartMap Γ plabel outgoing _ (allowed_ports Γ plabel outgoing pin) f d) =
      dartMap Γ plabel outgoing _ (allowed_ports Γ plabel outgoing pin) f (Γ.reverse d)).card

/-- Finite, exact form of the source fixed-label first moment. `cost v` is a
literal upper bound for carrier size; the matching estimate is proved above. -/
theorem fixed_label_bound (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (bar : T → T)
    (hbar : ∀ t, bar t ≠ t) (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : Dart outgoing // origin outgoing e = v} ≤ d)
    (hsize : ∀ x : Dart outgoing,
      R + (edges Γ).card + 4*d^(2*N+1) ≤
        Nat.card {e : Dart outgoing // label outgoing e = label outgoing x})
    (hΩ : (Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅).Nonempty)
    (cost : PV → ℝ) (hcost : ∀ v, ((allowed Γ plabel outgoing pin v).card : ℝ) ≤ cost v) :
    ((∑ r ∈ Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅, realizations Γ plabel outgoing pin bar r : ℕ) : ℝ) /
      (Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅).card ≤
      (∏ v, cost v) / (R : ℝ)^(edges Γ).card := by
  exact (PatternEmbeddings.expectation_bound Γ plabel outgoing
    (allowed Γ plabel outgoing pin) (allowed_ports Γ plabel outgoing pin)
    bar hbar himm N d R h2 hR hd hsize hΩ).trans
      (div_le_div_of_nonneg_right (Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun v _ => hcost v)) (by positivity))

/-- Source internal-turn product, retaining a finite, explicit matching
error denominator instead of hiding it in o(L). -/
def vertexCost (n p : ℝ) (J : Finset PV) (w : T → T → ℝ)
    (a b : PV → T) (pin : PV → Option TV) (v : PV) : ℝ :=
  if pin v = none then (if v ∈ J then n*p*w (a v) (b v) else n) else 1

omit [Fintype TV] [Fintype T] in
theorem product_vertexCost (n p : ℝ) (J : Finset PV) (w : T → T → ℝ)
    (a b : PV → T) (pin : PV → Option TV) (hJ : ∀ v ∈ J, pin v = none) :
    (∏ v, vertexCost n p J w a b pin v) =
      n^((Finset.univ.filter fun v => pin v = none).card) * p^J.card *
        ∏ v ∈ J, w (a v) (b v) := by
  have he (v : PV) : vertexCost n p J w a b pin v =
      (if pin v = none then n else 1) *
        (if v ∈ J then p*w (a v) (b v) else 1) := by
    by_cases hj : v ∈ J
    · simp [vertexCost,hJ v hj,hj,mul_assoc]
    · simp [vertexCost,hj]
  simp_rw [he,Finset.prod_mul_distrib]
  rw [← Finset.prod_filter,← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
    Finset.prod_mul_distrib]
  ring

omit [Fintype PV] [Fintype T] in
/-- Every eligible local carrier is bounded by its actual type-table cost. -/
theorem allowed_cost (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV)
    (J : Finset PV) (a b : PV → PD)
    (ha : ∀ v ∈ J, Γ.origin (a v) = v) (hb : ∀ v ∈ J, Γ.origin (b v) = v)
    (hab : ∀ v ∈ J, a v ≠ b v)
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (n p : ℝ) (w : T → T → ℝ)
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤ n*p*w t u) :
    ∀ v, ((allowed Γ plabel outgoing pin v).card : ℝ) ≤
      vertexCost n p J w (plabel ∘ a) (plabel ∘ b) pin v := by
  intro v
  by_cases hp : pin v = none
  · simp only [vertexCost,hp,ite_true,Function.comp_apply]
    by_cases hj : v ∈ J
    · rw [ite_eq_left hj]
      have hne : plabel (a v) ≠ plabel (b v) := by
        intro he
        exact hab v hj (himm (Prod.ext ((ha v hj).trans (hb v hj).symm) he))
      exact (Nat.cast_le.mpr (allowed_turn_le Γ plabel outgoing pin v (a v) (b v)
        (ha v hj) (hb v hj))).trans (htable _ _ hne)
    · rw [ite_eq_right hj]
      exact (Nat.cast_le.mpr (allowed_card_le Γ plabel outgoing pin v)).trans hn
  · simp only [vertexCost,hp,ite_false]
    cases he : pin v with
    | none => exact False.elim (hp he)
    | some x => exact_mod_cast pinned_card_le Γ plabel outgoing pin v x he

/-- Literal fixed-label bound with actual internal turns and fixed vertices,
before taking logarithms or asymptotics. -/
theorem turn_product_bound (Γ : PortGraph PV PD) (plabel : PD → T)
    (outgoing : TV → Finset T) (pin : PV → Option TV) (bar : T → T)
    (hbar : ∀ t, bar t ≠ t) (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : Dart outgoing // origin outgoing e = v} ≤ d)
    (hsize : ∀ x : Dart outgoing,
      R + (edges Γ).card + 4*d^(2*N+1) ≤
        Nat.card {e : Dart outgoing // label outgoing e = label outgoing x})
    (hΩ : (Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅).Nonempty)
    (J : Finset PV) (a b : PV → PD)
    (ha : ∀ v ∈ J, Γ.origin (a v) = v) (hb : ∀ v ∈ J, Γ.origin (b v) = v)
    (hab : ∀ v ∈ J, a v ≠ b v) (hJ : ∀ v ∈ J, pin v = none)
    (n p : ℝ) (w : T → T → ℝ)
    (hn : (Fintype.card TV : ℝ) ≤ n)
    (htable : ∀ t u, t ≠ u →
      (Fintype.card {x : TV // t ∈ outgoing x ∧ u ∈ outgoing x} : ℝ) ≤ n*p*w t u) :
    ((∑ r ∈ Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅, realizations Γ plabel outgoing pin bar r : ℕ) : ℝ) /
      (Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅).card ≤
      (n^((Finset.univ.filter fun v => pin v = none).card) * p^J.card *
        ∏ v ∈ J, w (plabel (a v)) (plabel (b v))) / (R : ℝ)^(edges Γ).card := by
  have h := fixed_label_bound Γ plabel outgoing pin bar hbar himm N d R h2 hR hd hsize hΩ
    (vertexCost n p J w (plabel ∘ a) (plabel ∘ b) pin)
    (allowed_cost Γ plabel outgoing pin J a b ha hb hab himm n p w hn htable)
  rwa [product_vertexCost n p J w (plabel ∘ a) (plabel ∘ b) pin hJ] at h

section Typed
open TorsionFreeZeroDivisors.Types
variable (rep : ℕ) (Γ : PortGraph PV PD) (plabel : PD → Letter)
  (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
  (J : Finset PV) (a b : PV → PD)
  (ha : ∀ v ∈ J, Γ.origin (a v) = v) (hb : ∀ v ∈ J, Γ.origin (b v) = v)
  (hab : ∀ v ∈ J, a v ≠ b v)

include himm ha hb hab
omit [Fintype PV] [Fintype TV] [Fintype T] in
/-- The exact source A-side empirical counts instantiate the local estimate. -/
theorem allowed_costA (pin : PV → Option (VertexA rep)) :
    ∀ v, ((allowed Γ plabel (@outgoingA rep) pin v).card : ℝ) ≤
      vertexCost (Fintype.card (VertexA rep)) (129/16513) J TypeWeights.jointWeight
        (plabel ∘ a) (plabel ∘ b) pin v :=
  allowed_cost Γ plabel (@outgoingA rep) pin J a b ha hb hab himm _ _ _ le_rfl
    (fun t u h => by simpa only [← Nat.card_eq_fintype_card] using
      TypeWeights.joint_countA_le rep t u h)

omit [Fintype PV] [Fintype TV] [Fintype T] in
/-- The B-side count uses its own types, not independent coordinates. -/
theorem allowed_costB (pin : PV → Option (VertexB rep)) :
    ∀ v, ((allowed Γ plabel (@outgoingB rep) pin v).card : ℝ) ≤
      vertexCost (Fintype.card (VertexB rep)) (129/16513) J TypeWeights.jointWeight
        (plabel ∘ a) (plabel ∘ b) pin v :=
  allowed_cost Γ plabel (@outgoingB rep) pin J a b ha hb hab himm _ _ _ le_rfl
    (fun t u h => by simpa only [← Nat.card_eq_fintype_card] using
      (TypeWeights.joint_countB rep t u h).le)

end Typed

/-- Exact expectation factorization for the two independently chosen side
matchings. No independence of edges *within* either matching is used. -/
theorem mean_product {A B : Type*} (S : Finset A) (U : Finset B)
    (f : A → ℝ) (g : B → ℝ) :
    (∑ x ∈ S, ∑ y ∈ U, f x*g y) / ((S.card : ℝ)*U.card) =
      ((∑ x ∈ S, f x)/S.card) * ((∑ y ∈ U, g y)/U.card) := by
  rw [← Finset.sum_mul_sum, mul_div_mul_comm]

/-- Combining the side bounds correctly counts a mixed-side stage. -/
theorem mean_product_le {A B : Type*} (S : Finset A) (U : Finset B)
    (f : A → ℝ) (g : B → ℝ) (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ y ∈ U, 0 ≤ g y)
    (a b : ℝ) (ha : (∑ x ∈ S, f x)/S.card ≤ a)
    (hb : (∑ y ∈ U, g y)/U.card ≤ b) :
    (∑ x ∈ S, ∑ y ∈ U, f x*g y) / ((S.card : ℝ)*U.card) ≤ a*b := by
  rw [mean_product]
  exact mul_le_mul ha hb (div_nonneg (Finset.sum_nonneg hg) (Nat.cast_nonneg _))
    ((div_nonneg (Finset.sum_nonneg hf) (Nat.cast_nonneg _)).trans ha)

end TorsionFreeZeroDivisors.StageRealization

namespace TorsionFreeZeroDivisors.ChainSubdivision
open scoped Classical BigOperators
variable {C V : Type*} (len : C → ℕ) (first last : C → V)
abbrev Interior := (c : C) × Fin (len c-1)
abbrev Vertex := V ⊕ Interior len
abbrev Edge := (c : C) × Fin (len c)
abbrev Dart := Edge len × Bool

def point (c : C) (k : Fin (len c+1)) : Vertex len (V := V) :=
  if h0 : k.val=0 then .inl (first c) else if h1 : k.val=len c then .inl (last c)
  else .inr ⟨c,⟨k.val-1,by omega⟩⟩

def graph : PortSubdivision.PortGraph (Vertex len (V := V)) (Dart len) where
  origin d := point len first last d.1.1 ⟨d.1.2.val+(if d.2 then 1 else 0),by
    cases d.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
  reverse d := (d.1,!d.2)
  reverse_reverse d := by simp
  reverse_ne d := by
    intro h
    have hh := congrArg Prod.snd h
    cases hb : d.2 <;> simp [hb] at hh

@[simp] theorem reverse (d : Dart len) : (graph len first last).reverse d = (d.1,!d.2) := rfl
@[simp] theorem origin_forward (e : Edge len) :
    (graph len first last).origin (e,false) = point len first last e.1 ⟨e.2.val,by omega⟩ := rfl
@[simp] theorem origin_backward (e : Edge len) :
    (graph len first last).origin (e,true) = point len first last e.1 ⟨e.2.val+1,by omega⟩ := rfl

@[simp] theorem at_zero (c : C) : point len first last c ⟨0,by omega⟩ = .inl (first c) := by
  simp [point]

theorem at_last (hpos : ∀ c, 0 < len c) (c : C) :
    point len first last c ⟨len c,by omega⟩ = .inl (last c) := by
  simp [point,Nat.ne_of_gt (hpos c)]

@[simp] theorem at_interior (c : C) (k : Fin (len c-1)) :
    point len first last c ⟨k.val+1,by omega⟩ = .inr ⟨c,k⟩ := by
  have hk : k.val+1 ≠ len c := by omega
  simp [point,hk]

/-- Outgoing darts at an internal vertex: the preceding edge backwards and
following edge forwards, with no arbitrary choices. -/
def back (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val,by omega⟩⟩,true)
def front (v : Interior len) : Dart len := (⟨v.1,⟨v.2.val+1,by omega⟩⟩,false)

@[simp] theorem back_origin (v : Interior len) :
    (graph len first last).origin (back len v) = .inr v := by
  simpa only [back,origin_backward] using at_interior len first last v.1 v.2
@[simp] theorem front_origin (v : Interior len) :
    (graph len first last).origin (front len v) = .inr v := by
  simpa only [front,origin_forward] using at_interior len first last v.1 v.2

theorem back_ne_front (v : Interior len) : back len v ≠ front len v := by
  intro h
  have hh := congrArg Prod.snd h
  cases hh

theorem at_eq_interior {c : C} {k : Fin (len c+1)} {v : Interior len}
    (hk : point len first last c k = .inr v) :
    c = v.1 ∧ k.val = v.2.val+1 := by
  unfold point at hk
  split_ifs at hk with h0 h1
  have he := Sum.inr.inj hk
  have hc := congrArg Sigma.fst he
  have hh := congrArg (fun v : Interior len => v.2.val) he
  dsimp at hc hh
  exact ⟨hc,by omega⟩

/-- Each internal vertex has precisely the two prescribed outgoing darts. -/
theorem internal_ports (v : Interior len) (d : Dart len) :
    (graph len first last).origin d = .inr v ↔ d = back len v ∨ d = front len v := by
  constructor
  · rcases d with ⟨⟨c,k⟩,b⟩
    cases b
    · intro h
      have hh := at_eq_interior len first last h
      rcases v with ⟨c',l⟩
      dsimp at hh
      obtain ⟨rfl,hk⟩ := hh
      right
      apply congrArg (fun t : Fin (len c) => ((⟨c,t⟩ : Edge len),false))
      exact Fin.ext hk
    · intro h
      simp only [origin_backward] at h
      have hh := at_eq_interior len first last h
      rcases v with ⟨c',l⟩
      dsimp at hh
      obtain ⟨rfl,hk⟩ := hh
      left
      apply congrArg (fun t : Fin (len c) => ((⟨c,t⟩ : Edge len),true))
      apply Fin.ext
      change k.val = l.val
      omega
  · rintro (rfl|rfl)
    · exact back_origin len first last v
    · exact front_origin len first last v

variable [Fintype C] [Fintype V]

@[simp] theorem card_edges : Fintype.card (Edge len) = ∑ c, len c := by
  simp [Edge,Fintype.card_sigma]

@[simp] theorem card_darts : Fintype.card (Dart len) = 2*∑ c, len c := by
  simp [Dart,Fintype.card_prod,Nat.mul_comm]

@[simp] theorem card_interiors : Fintype.card (Interior len) = ∑ c, (len c-1) := by
  simp [Interior,Fintype.card_sigma]

/-- Interior and endpoint counts are kept separate, including loop chains. -/
theorem card_vertices (hpos : ∀ c, 0 < len c) :
    Fintype.card (Vertex len (V := V)) + Fintype.card C = Fintype.card V + ∑ c, len c := by
  simp only [Vertex,Fintype.card_sum,card_interiors]
  have hh : (∑ c, (len c-1)) + Fintype.card C = ∑ c, len c := by
    have hone : Fintype.card C = ∑ _c : C, (1 : ℕ) := by simp
    rw [hone, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    have hc := hpos c
    omega
  omega

/-- The complete set of unmarked internal vertices. -/
def internal : Finset (Vertex len (V := V)) := Finset.univ.image Sum.inr

omit [Fintype V] in
@[simp] theorem mem_internal (v : Vertex len (V := V)) :
    v ∈ internal len (V := V) ↔ ∃ x, v = Sum.inr x := by
  simp [internal,eq_comm]

omit [Fintype V] in
@[simp] theorem card_internal : (internal len (V := V)).card = ∑ c, (len c-1) := by
  rw [internal,Finset.card_image_of_injective _ Sum.inr_injective,Finset.card_univ,card_interiors]

/-- Constant traversal multiplicity on each original marked chain. -/
def multiplicity (m : C → ℕ) (d : Dart len) := m d.1.1
omit [Fintype C] [Fintype V] in
@[simp] theorem multiplicity_reverse (m : C → ℕ) (d : Dart len) :
    multiplicity len m ((graph len first last).reverse d) = multiplicity len m d := rfl

end TorsionFreeZeroDivisors.ChainSubdivision

end

end OAI
