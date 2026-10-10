import OAI.Analysis.TreePotential.CostGeometry

namespace OAI

noncomputable section
open Set
open scoped ENNReal


open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials.Segments

abbrev Node := (n : ℕ) × {s : List ℕ // s.length ≤ n+1}

instance nodeDecidableEq : DecidableEq Node := Classical.decEq Node

def Prefix (s t : Node) : Prop := s.1 = t.1 ∧ s.2.val <+: t.2.val

lemma prefix_refl (s : Node) : Prefix s s := ⟨rfl, List.prefix_refl _⟩
lemma Prefix.trans {s t u : Node} (h : Prefix s t) (h' : Prefix t u) : Prefix s u :=
  ⟨h.1.trans h'.1, h.2.trans h'.2⟩

lemma Prefix.antisymm {s t : Node} (h : Prefix s t) (h' : Prefix t s) : s = t := by
  rcases s with ⟨n,s⟩
  rcases t with ⟨m,t⟩
  obtain ⟨hcomp,hpref⟩ := h
  dsimp only at hcomp
  subst m
  have hv : s = t := Subtype.ext (hpref.eq_of_length (Nat.le_antisymm hpref.length_le h'.2.length_le))
  subst t
  rfl

lemma prefix_chain {s t u : Node} (h : Prefix s u) (h' : Prefix t u) :
    Prefix s t ∨ Prefix t s := by
  have hcomp : s.1 = t.1 := h.1.trans h'.1.symm
  have hl : s.2.val <+: t.2.val ∨ t.2.val <+: s.2.val := by
    rcases le_total s.2.val.length t.2.val.length with hlen | hlen
    · exact Or.inl (List.prefix_of_prefix_length_le h.2 h'.2 hlen)
    · exact Or.inr (List.prefix_of_prefix_length_le h'.2 h.2 hlen)
  exact hl.elim (fun hs => Or.inl ⟨hcomp,hs⟩) (fun hs => Or.inr ⟨hcomp.symm,hs⟩)

def prefixAt (v : Node) (k : Fin (v.2.val.length+1)) : Node :=
  ⟨v.1, ⟨v.2.val.take k, by simpa only [List.length_take] using (Nat.min_le_right (k:ℕ) v.2.val.length).trans v.2.property⟩⟩

def ancestors (v : Node) : Finset Node := Finset.univ.image (prefixAt v)

lemma mem_ancestors (v s : Node) : s ∈ ancestors v ↔ Prefix s v := by
  constructor
  · intro hs
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hs
    exact ⟨rfl, List.take_prefix ..⟩
  · rintro ⟨hcomp,hpref⟩
    refine Finset.mem_image.mpr ⟨⟨s.2.val.length, Nat.lt_succ_of_le hpref.length_le⟩,
      Finset.mem_univ _, ?_⟩
    rcases s with ⟨n,s⟩
    rcases v with ⟨m,v⟩
    dsimp only at hcomp
    subst m
    apply Sigma.mk.inj_iff.mpr
    refine ⟨rfl, ?_⟩
    apply heq_of_eq
    apply Subtype.ext
    exact (List.prefix_iff_eq_take.mp hpref).symm

structure Segment where
  start : Node
  finish : Node
  extends_to : Prefix start finish

namespace Segment

def nodes (S : Segment) : Finset Node := (ancestors S.finish).filter (Prefix S.start)

lemma mem_nodes (S : Segment) (s : Node) : s ∈ S.nodes ↔ Prefix S.start s ∧ Prefix s S.finish := by
  simp only [nodes, Finset.mem_filter, mem_ancestors, and_comm]

@[simp] lemma start_mem (S : Segment) : S.start ∈ S.nodes :=
  (S.mem_nodes _).mpr ⟨prefix_refl _, S.extends_to⟩
@[simp] lemma finish_mem (S : Segment) : S.finish ∈ S.nodes :=
  (S.mem_nodes _).mpr ⟨S.extends_to, prefix_refl _⟩

def singleton (s : Node) : Segment := ⟨s,s,prefix_refl s⟩

@[simp] lemma singleton_nodes (s : Node) : (singleton s).nodes = {s} := by
  ext t
  rw [mem_nodes, Finset.mem_singleton]
  constructor
  · rintro ⟨h,h'⟩
    exact Prefix.antisymm h' h
  · rintro rfl
    exact ⟨prefix_refl _, prefix_refl _⟩

def eval (S : Segment) (g : Node → ℝ) : ℝ := ∑ v ∈ S.nodes, g v

@[simp] lemma eval_zero (S : Segment) : S.eval 0 = 0 := by simp [eval]
@[simp] lemma eval_neg (S : Segment) (g : Node → ℝ) : S.eval (-g) = -S.eval g := by simp [eval]
@[simp] lemma eval_add (S : Segment) (f g : Node → ℝ) : S.eval (f+g) = S.eval f+S.eval g := by
  simp [eval, Finset.sum_add_distrib]
@[simp] lemma eval_smul (S : Segment) (c : ℝ) (g : Node → ℝ) : S.eval (c • g) = c*S.eval g := by
  simp [eval, Finset.mul_sum]
@[simp] lemma eval_singleton (s : Node) (g : Node → ℝ) : (singleton s).eval g = g s := by
  simp [eval]

lemma eval_coordinate (S : Segment) (v : Node) :
    S.eval (fun s => if s=v then (1:ℝ) else 0) = if v ∈ S.nodes then 1 else 0 := by
  simp [eval]

end Segment

/-- Incomparability is of starts, equivalently of every node in different
segments; mere disjointness is not used as a substitute. -/
def Incomparable (F : Finset Segment) : Prop :=
  ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ¬Prefix S.start T.start ∧ ¬Prefix T.start S.start

lemma incomparable_nodes {F : Finset Segment} (hF : Incomparable F)
    {S T : Segment} (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T)
    {s t : Node} (hs : s ∈ S.nodes) (ht : t ∈ T.nodes) :
    ¬Prefix s t ∧ ¬Prefix t s := by
  obtain ⟨hss,hse⟩ := S.mem_nodes s |>.mp hs
  obtain ⟨htt,hte⟩ := T.mem_nodes t |>.mp ht
  obtain ⟨hn,hn'⟩ := hF S hS T hT hne
  constructor
  · intro hh
    exact (prefix_chain (hss.trans hh) htt).elim hn hn'
  · intro hh
    exact (prefix_chain hss (htt.trans hh)).elim hn hn'

lemma incomparable_disjoint {F : Finset Segment} (hF : Incomparable F)
    {S T : Segment} (hS : S ∈ F) (hT : T ∈ F) (hne : S ≠ T) :
    Disjoint S.nodes T.nodes := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact (incomparable_nodes hF hS hT hne hs ht).1 (prefix_refl s)

/-- Closed unit tests for the exact incomparable-segment norm. -/
def IsUnitTest (g : Node → ℝ) : Prop :=
  ∀ F : Finset Segment, Incomparable F → ∑ S ∈ F, (S.eval g)^2 ≤ 1

lemma unit_zero : IsUnitTest 0 := by intro F hF; simp
lemma unit_neg {g : Node → ℝ} (hg : IsUnitTest g) : IsUnitTest (-g) := by
  intro F hF
  simpa only [Segment.eval_neg, neg_sq] using hg F hF

lemma unit_segment {g : Node → ℝ} (hg : IsUnitTest g) (S : Segment) : |S.eval g| ≤ 1 := by
  have hh := hg {S} (by intro U hU V hV hne; simp only [Finset.mem_singleton] at hU hV; subst U; subst V; exact (hne rfl).elim)
  simp only [Finset.sum_singleton] at hh
  rw [abs_le]
  constructor <;> nlinarith

lemma unit_coordinate {g : Node → ℝ} (hg : IsUnitTest g) (s : Node) : |g s| ≤ 1 := by
  simpa only [Segment.eval_singleton] using unit_segment hg (Segment.singleton s)

lemma unit_coordinate_test (v : Node) : IsUnitTest (fun s => if s=v then 1 else 0) := by
  intro F hF
  simp only [Segment.eval_coordinate]
  by_cases he : ∃ S ∈ F, v ∈ S.nodes
  · obtain ⟨S,hS,hv⟩ := he
    have hh : ∀ T ∈ F, T ≠ S → v ∉ T.nodes := by
      intro T hT hne hvT
      exact Finset.disjoint_left.mp (incomparable_disjoint hF hT hS hne) hvT hv
    rw [Finset.sum_eq_single S]
    · simp [hv]
    · intro T hT hne
      simp [hh T hT hne]
    · exact fun hn => (hn hS).elim
  · have hh : ∀ S ∈ F, v ∉ S.nodes := by simpa only [not_exists, not_and] using he
    have hz : ∑ S ∈ F, (if v ∈ S.nodes then (1:ℝ) else 0)^2 = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      simp [hh S hS]
    rw [hz]
    norm_num

structure Atom where
  family : Finset Segment
  incomparable : Incomparable family
  coeff : Segment → ℝ
  budget : ∑ S ∈ family, (coeff S)^2 ≤ 1

namespace Atom

def profile (A : Atom) (v : Node) : ℝ :=
  ∑ S ∈ A.family, A.coeff S * (if v ∈ S.nodes then 1 else 0)

def pairing (A : Atom) (g : Node → ℝ) : ℝ := ∑ S ∈ A.family, A.coeff S*S.eval g

lemma coeff_bound (A : Atom) {S : Segment} (hS : S ∈ A.family) : |A.coeff S| ≤ 1 := by
  have hh := (Finset.single_le_sum (fun T _ => sq_nonneg (A.coeff T)) hS).trans A.budget
  rw [abs_le]
  constructor <;> nlinarith

lemma profile_at (A : Atom) {S : Segment} (hS : S ∈ A.family) {v : Node}
    (hv : v ∈ S.nodes) : A.profile v = A.coeff S := by
  unfold profile
  rw [Finset.sum_eq_single_of_mem S hS]
  · simp [hv]
  · intro T hT hne
    have hnot : v ∉ T.nodes := fun ht =>
      Finset.disjoint_left.mp (incomparable_disjoint A.incomparable hT hS hne) ht hv
    simp [hnot]

lemma profile_missing (A : Atom) {v : Node} (hv : ∀ S ∈ A.family, v ∉ S.nodes) :
    A.profile v = 0 := by
  apply Finset.sum_eq_zero
  intro S hS
  simp [hv S hS]

lemma profile_bound (A : Atom) (v : Node) : |A.profile v| ≤ 1 := by
  by_cases h : ∃ S ∈ A.family, v ∈ S.nodes
  · obtain ⟨S,hS,hv⟩ := h
    rw [A.profile_at hS hv]
    exact A.coeff_bound hS
  · rw [A.profile_missing (by simpa only [not_exists, not_and] using h)]
    norm_num

def zero : Atom := ⟨∅, by intro S hS; simp at hS, 0, by simp⟩
def neg (A : Atom) : Atom := ⟨A.family, A.incomparable, -A.coeff, by simpa using A.budget⟩

def coordinate (v : Node) : Atom where
  family := {Segment.singleton v}
  incomparable := by
    intro S hS T hT hne
    simp only [Finset.mem_singleton] at hS hT
    exact (hne (hS.trans hT.symm)).elim
  coeff := fun _ => 1
  budget := by simp

@[simp] lemma zero_profile : zero.profile = 0 := by funext v; simp [profile, zero]
@[simp] lemma neg_profile (A : Atom) : A.neg.profile = -A.profile := by
  funext v
  change (∑ S ∈ A.family, -A.coeff S*(if v ∈ S.nodes then 1 else 0)) =
    -(∑ S ∈ A.family, A.coeff S*(if v ∈ S.nodes then 1 else 0))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  ring
@[simp] lemma coordinate_profile (v : Node) :
    (coordinate v).profile = fun s => if s=v then 1 else 0 := by
  funext s
  change (∑ S ∈ {Segment.singleton v}, (1:ℝ)*(if s ∈ S.nodes then 1 else 0)) = _
  rw [Finset.sum_singleton]
  simp

lemma pairing_sq_le (A : Atom) {g : Node → ℝ} (hg : IsUnitTest g) : (A.pairing g)^2 ≤ 1 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq A.family A.coeff (fun S => S.eval g)
  have hn1 : 0 ≤ ∑ S ∈ A.family, (A.coeff S)^2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hn2 : 0 ≤ ∑ S ∈ A.family, (S.eval g)^2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  have hb := mul_le_mul A.budget (hg A.family A.incomparable) hn2 zero_le_one
  change (∑ S ∈ A.family, A.coeff S*S.eval g)^2 ≤ 1
  nlinarith

lemma pairing_bound (A : Atom) {g : Node → ℝ} (hg : IsUnitTest g) : |A.pairing g| ≤ 1 := by
  have hh := A.pairing_sq_le hg
  rw [abs_le]
  constructor <;> nlinarith

/-- The coefficient replacement identity, retaining both nonnegative deficits. -/
lemma defect (A : Atom) {g : Node → ℝ} (hg : IsUnitTest g) :
    0 ≤ 1-A.pairing g ∧
    (∑ S ∈ A.family, (A.coeff S-S.eval g)^2) ≤ 2*(1-A.pairing g) ∧
    1-(∑ S ∈ A.family, (S.eval g)^2) ≤ 2*(1-A.pairing g) := by
  have hG := hg A.family A.incomparable
  have hpair := le_abs_self (A.pairing g) |>.trans (A.pairing_bound hg)
  have hid : (∑ S ∈ A.family, (A.coeff S-S.eval g)^2) =
      (∑ S ∈ A.family, (A.coeff S)^2)+(∑ S ∈ A.family, (S.eval g)^2)-2*A.pairing g := by
    unfold pairing
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  have hsq : 0 ≤ ∑ S ∈ A.family, (A.coeff S-S.eval g)^2 := Finset.sum_nonneg fun S _ => sq_nonneg _
  exact ⟨by linarith, by linarith [A.budget], by linarith [A.budget]⟩

end Atom

end BoundedTreePotentials.Segments

end

end OAI
