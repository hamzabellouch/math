import Mathlib
import OAI.Algebra.GroupRing.MatchingGraphs

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PatternCount
open scoped Classical
open ConditionedMatchings
variable {V D T F E A : Type*} [Fintype V] [Fintype D] [Fintype F] [Fintype E]
variable (label : D → T) (bar : T → T)

omit [Fintype D] in
/-- A prescribed undirected edge can be read in either orientation. -/
theorem contains_prescriptions (r : Matching label bar) (ports : E → D × D) :
    r.Contains (Finset.univ.image (fun e => s((ports e).1,(ports e).2))) ↔
      ∀ e, r (ports e).1 = (ports e).2 := by
  classical
  constructor
  · intro h e
    exact h _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  · intro h a b hab
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hab
    rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [← ha,← hb,h]
    · rw [← ha,← hb,← h e,r.reverse_reverse]

omit [Fintype V] in
/-- The expectation numerator counts each vertex realization in each matching
exactly once; prescriptions retain every edge, rather than path occurrences. -/
theorem sum_realizations_eq (origin : D → V) (N : ℕ) (C : F → Finset (Sym2 D)) :
    (∑ r ∈ Matching.conditioned (label := label) (bar := bar) origin N ∅,
      (Finset.univ.filter (fun f : F => r.Contains (C f))).card) =
    ∑ f : F, (Matching.conditioned (label := label) (bar := bar) origin N (C f)).card := by
  classical
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  have hcf (f : F) : Matching.conditioned (label := label) (bar := bar) origin N (C f) =
      Ω.filter (fun r => r.Contains (C f)) := by
    ext r
    simp only [Matching.conditioned,Ω,Finset.mem_filter,Finset.mem_univ,true_and]
    have hemp : r.Contains (∅ : Finset (Sym2 D)) := by intro a b h; simp at h
    tauto
  simp_rw [hcf,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

/-- Finite first-moment bound for a fixed labelled actual-image pattern.
Distinct edges, not occurrences, supply the power of the matching denominator. -/
theorem expectation_bound [DecidableEq D] (origin : D → V) (N : ℕ)
    (hbar : ∀ t, bar t ≠ t) (d : ℕ) (h2 : 2 ≤ d)
    (hd : ∀ v, Nat.card {e : D // origin e = v} ≤ d)
    (C : F → Finset (Sym2 D)) (E R : ℕ) (hcard : ∀ f, (C f).card = E)
    (hR : 0 < R)
    (hsize : ∀ x, R + E + 4*d^(2*N+1) ≤ Nat.card {e : D // label e = label x})
    (hΩ : (Matching.conditioned (label := label) (bar := bar) origin N ∅).Nonempty) :
    ((∑ r ∈ Matching.conditioned (label := label) (bar := bar) origin N ∅,
        (Finset.univ.filter (fun f : F => r.Contains (C f))).card : ℕ) : ℝ) /
      (Matching.conditioned (label := label) (bar := bar) origin N ∅).card ≤
      (Fintype.card F : ℝ) / (R : ℝ)^E := by
  classical
  let Ω := Matching.conditioned (label := label) (bar := bar) origin N ∅
  have hcount (f : F) : (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card * R^E ≤ Ω.card := by
    have h := Matching.prescriptions_count (label := label) (bar := bar)
      origin N hbar d h2 hd R (C f) (by intro x; rw [hcard]; exact hsize x)
    simpa only [hcard] using h
  have hs : (∑ f : F, (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card) * R^E ≤ Fintype.card F * Ω.card := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ _f : F, Ω.card := Finset.sum_le_sum (fun f _ => hcount f)
      _ = _ := by simp
  rw [sum_realizations_eq]
  have hs' : ((∑ f : F, (Matching.conditioned (label := label) (bar := bar)
      origin N (C f)).card : ℕ) : ℝ) * (R : ℝ)^E ≤ (Fintype.card F : ℝ) * Ω.card := by
    exact_mod_cast hs
  have hp : (0 : ℝ) < (R : ℝ)^E := pow_pos (Nat.cast_pos.mpr hR) _
  have ho : (0 : ℝ) < Ω.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hΩ)
  exact (div_le_div_iff₀ ho hp).mpr hs'

/-- Independent vertex carrier restrictions count by an exact product. This
is an upper bound for injective vertex maps, without assuming independence
of sampled edges. -/
theorem vertex_assignments_card [Fintype A]
    (allowed : A → Finset V) :
    Fintype.card {f : A → V // ∀ a, f a ∈ allowed a} =
      ∏ a : A, (allowed a).card := by
  classical
  let e : {f : A → V // ∀ a, f a ∈ allowed a} ≃ ((a : A) → {v : V // v ∈ allowed a}) :=
    { toFun := fun f a => ⟨f.val a,f.property a⟩
      invFun := fun f => ⟨fun a => (f a).val,fun a => (f a).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_pi]
  simp only [Fintype.card_coe]

end TorsionFreeZeroDivisors.PatternCount

namespace TorsionFreeZeroDivisors.PatternEmbeddings
open scoped BigOperators Classical
open PortSubdivision ConditionedMatchings
variable {PV PD TV T : Type*} [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T]

abbrev Dart (outgoing : TV → Finset T) := {x : TV × T // x.2 ∈ outgoing x.1}
def origin (outgoing : TV → Finset T) (e : Dart outgoing) : TV := e.val.1
def label (outgoing : TV → Finset T) (e : Dart outgoing) : T := e.val.2

def edges (Γ : PortGraph PV PD) : Finset (Sym2 PD) :=
  Finset.univ.image (fun d => s(d,Γ.reverse d))

abbrev VertexMap (allowed : PV → Finset TV) :=
  {f : PV → TV // Function.Injective f ∧ ∀ v, f v ∈ allowed v}

variable (Γ : PortGraph PV PD) (plabel : PD → T) (outgoing : TV → Finset T)
  (allowed : PV → Finset TV)
  (hallowed : ∀ v x, x ∈ allowed v → ∀ d, Γ.origin d = v → plabel d ∈ outgoing x)

/-- Every candidate is injective on actual-image vertices; the letters uniquely
specify the target ports before the random matching is chosen. -/
def dartMap (f : VertexMap allowed) (d : PD) : Dart outgoing :=
  ⟨(f.val (Γ.origin d),plabel d),hallowed _ _ (f.property.2 _) d rfl⟩

omit [Fintype PV] [Fintype PD] [Fintype TV] [Fintype T] in
theorem dartMap_injective
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (f : VertexMap allowed) : Function.Injective (dartMap Γ plabel outgoing allowed hallowed f) := by
  intro d e he
  have hp := congrArg Subtype.val he
  have hv : Γ.origin d = Γ.origin e := f.property.1 (congrArg Prod.fst hp)
  have hl : plabel d = plabel e := congrArg Prod.snd hp
  exact himm (Prod.ext hv hl)

/-- Each undirected actual edge is prescribed once, regardless of its number
of occurrences in the paths. This prevents the independence fallacy. -/
def prescriptions (f : VertexMap allowed) : Finset (Sym2 (Dart outgoing)) :=
  (edges Γ).image (Sym2.map (dartMap Γ plabel outgoing allowed hallowed f))

omit [Fintype PV] [Fintype TV] [Fintype T] in
theorem prescriptions_card
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (f : VertexMap allowed) :
    (prescriptions Γ plabel outgoing allowed hallowed f).card = (edges Γ).card := by
  exact Finset.card_image_of_injective _ (Sym2.map.injective
    (dartMap_injective Γ plabel outgoing allowed hallowed himm f))

omit [Fintype PV] [Fintype TV] [Fintype T] in
/-- A matching contains the prescriptions precisely when the vertex map is
an edge-respecting labelled graph embedding. -/
theorem contains_iff (bar : T → T) (f : VertexMap allowed)
    (r : Matching (label outgoing) bar) :
    r.Contains (prescriptions Γ plabel outgoing allowed hallowed f) ↔
      ∀ d, r.val (dartMap Γ plabel outgoing allowed hallowed f d) =
        dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d) := by
  have he : prescriptions Γ plabel outgoing allowed hallowed f =
      Finset.univ.image (fun d => s(dartMap Γ plabel outgoing allowed hallowed f d,
        dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d))) := by
    rw [prescriptions,edges,Finset.image_image]
    rfl
  rw [he]
  convert PatternCount.contains_prescriptions (label outgoing) bar r
    (fun d => (dartMap Γ plabel outgoing allowed hallowed f d,
      dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse d))) using 1
  simp only [Matching.Contains,Finset.mem_image]

omit [Fintype PD] [Fintype T] in
theorem vertexMap_card : Fintype.card (VertexMap allowed) ≤ ∏ v, (allowed v).card := by
  let forget : VertexMap allowed → {f : PV → TV // ∀ v, f v ∈ allowed v} :=
    fun f => ⟨f.val,f.property.2⟩
  calc
    _ ≤ Fintype.card {f : PV → TV // ∀ v, f v ∈ allowed v} :=
      Fintype.card_le_of_injective forget (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {f : PV → TV // ∀ v, f v ∈ allowed v} => z.val) h)
    _ = _ := PatternCount.vertex_assignments_card allowed

/-- Fixed-label stage first moment with all graph-embedding hypotheses
explicit. The only counting input on vertices is their literal carrier sets. -/
theorem expectation_bound (bar : T → T) (hbar : ∀ t, bar t ≠ t)
    (himm : Function.Injective (fun d => (Γ.origin d,plabel d)))
    (N d R : ℕ) (h2 : 2 ≤ d) (hR : 0 < R)
    (hd : ∀ v, Nat.card {e : Dart outgoing // origin outgoing e = v} ≤ d)
    (hsize : ∀ x : Dart outgoing,
      R + (edges Γ).card + 4*d^(2*N+1) ≤
        Nat.card {e : Dart outgoing // label outgoing e = label outgoing x})
    (hΩ : (Matching.conditioned (label := label outgoing) (bar := bar)
      (origin outgoing) N ∅).Nonempty) :
    ((∑ r ∈ Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅,
      (Finset.univ.filter (fun f : VertexMap allowed =>
        ∀ e, r.val (dartMap Γ plabel outgoing allowed hallowed f e) =
          dartMap Γ plabel outgoing allowed hallowed f (Γ.reverse e))).card : ℕ) : ℝ) /
      (Matching.conditioned (label := label outgoing) (bar := bar) (origin outgoing) N ∅).card ≤
        (∏ v, ((allowed v).card : ℝ)) / (R : ℝ) ^ (edges Γ).card := by
  have hc := PatternCount.expectation_bound (label outgoing) bar (origin outgoing) N hbar d h2 hd
    (prescriptions Γ plabel outgoing allowed hallowed) (edges Γ).card R
    (prescriptions_card Γ plabel outgoing allowed hallowed himm) hR hsize hΩ
  simp_rw [contains_iff] at hc
  refine hc.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  exact_mod_cast vertexMap_card allowed

end TorsionFreeZeroDivisors.PatternEmbeddings

/-!
Exact finite geometry and type system over the field with 128 elements.
-/

namespace TorsionFreeZeroDivisors
namespace Types

open scoped LinearAlgebra.Projectivization
open Configuration

abbrev Field128 := GaloisField 2 7

instance : Fintype Field128 := Fintype.ofFinite _
instance : DecidableEq Field128 := Classical.decEq _

abbrev Point := ℙ Field128 (Fin 3 → Field128)
abbrev Line := Point

instance : Fintype Point := Fintype.ofFinite _
instance : DecidableEq Point := Classical.decEq _

instance (p : Point) (l : Line) : Decidable (p ∈ l) := Classical.propDecidable _

theorem field_card : Nat.card Field128 = 128 := by
  simpa using GaloisField.card 2 7 (by decide)

theorem point_card : Fintype.card Point = 16513 := by
  have h := Projectivization.card' Field128 (Fin 3 → Field128)
  rw [Nat.card_fun, Nat.card_fin, field_card] at h
  change 128 ^ 3 = Nat.card Point * (128 - 1) + 1 at h
  norm_num at h
  omega

theorem order_eq : ProjectivePlane.order Point Line = 128 := by
  have h := ProjectivePlane.card_points Point Line
  rw [point_card] at h
  have hi : (16513 : ℤ) = (ProjectivePlane.order Point Line : ℤ) ^ 2 +
      (ProjectivePlane.order Point Line : ℤ) + 1 := by exact_mod_cast h
  have hf : ((ProjectivePlane.order Point Line : ℤ) - 128) *
      ((ProjectivePlane.order Point Line : ℤ) + 129) = 0 := by nlinarith
  rcases mul_eq_zero.mp hf with h1 | h1 <;> omega

/-- Ordinary labels carried by a line type. -/
def pointsOn (l : Line) : Finset Point := Finset.univ.filter (· ∈ l)

def linesOn (p : Point) : Finset Line := Finset.univ.filter (p ∈ ·)

@[simp] theorem mem_pointsOn {p : Point} {l : Line} : p ∈ pointsOn l ↔ p ∈ l := by
  simp [pointsOn]

@[simp] theorem mem_linesOn {p : Point} {l : Line} : l ∈ linesOn p ↔ p ∈ l := by
  simp [linesOn]

theorem pointsOn_card (l : Line) : (pointsOn l).card = 129 := by
  have h := ProjectivePlane.pointCount_eq Point l
  rw [order_eq] at h
  simpa [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, pointsOn] using h

theorem linesOn_card (p : Point) : (linesOn p).card = 129 := by
  have h := ProjectivePlane.lineCount_eq Line p
  rw [order_eq] at h
  simpa [lineCount, Nat.card_eq_fintype_card, Fintype.card_subtype, linesOn] using h

theorem pointsOn_inter_card {l m : Line} (hlm : l ≠ m) :
    (pointsOn l ∩ pointsOn m).card = 1 := by
  obtain ⟨p, hp, hu⟩ := HasPoints.existsUnique_point Point Line l m hlm
  have heq : pointsOn l ∩ pointsOn m = {p} := by
    ext q
    simp only [Finset.mem_inter, mem_pointsOn, Finset.mem_singleton]
    exact ⟨fun hq => hu q hq, fun hq => hq ▸ hp⟩
  rw [heq, Finset.card_singleton]

theorem linesOn_inter_card {p q : Point} (hpq : p ≠ q) :
    (linesOn p ∩ linesOn q).card = 1 := by
  obtain ⟨l, hl, hu⟩ := HasLines.existsUnique_line Point Line p q hpq
  have heq : linesOn p ∩ linesOn q = {l} := by
    ext m
    simp only [Finset.mem_inter, mem_linesOn, Finset.mem_singleton]
    exact ⟨fun hm => hu m hm, fun hm => hm ▸ hl⟩
  rw [heq, Finset.card_singleton]

/-- Counting a predicate depending only on the first coordinate. -/
theorem card_prod_fst {U V : Type*} [Fintype U] [Fintype V]
    (p : U → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.1} = Fintype.card {u : U // p u} * Fintype.card V := by
  let e : {x : U × V // p x.1} ≃ {u : U // p u} × V :=
    { toFun := fun x => (⟨x.val.1, x.property⟩, x.val.2)
      invFun := fun x => ⟨(x.1.val, x.2), x.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

theorem card_prod_snd {U V : Type*} [Fintype U] [Fintype V]
    (p : V → Prop) [DecidablePred p] :
    Fintype.card {x : U × V // p x.2} = Fintype.card U * Fintype.card {v : V // p v} := by
  let e : {x : U × V // p x.2} ≃ U × {v : V // p v} :=
    { toFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
      invFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

/-! The empirical type slots. Each line has exactly 33026 slots on each
side, before the admissible replication parameter is applied. -/
abbrev SlotA := (Fin 3 × Fin 129) ⊕ Fin 32639
abbrev SlotB := Fin 258 ⊕ Fin 32768
abbrev VertexA (N : ℕ) := Line × SlotA × Fin N
abbrev VertexB (N : ℕ) := Line × SlotB × Fin N
abbrev Letter := Point ⊕ Fin 3

def extrasA : SlotA → Finset (Fin 3)
  | .inl (i, _) => Finset.univ.erase i
  | .inr _ => ∅

def extrasB : SlotB → Finset (Fin 3)
  | .inl _ => Finset.univ
  | .inr _ => ∅

def outgoingA {N : ℕ} (x : VertexA N) : Finset Letter :=
  (pointsOn x.1).disjSum (extrasA x.2.1)

def outgoingB {N : ℕ} (y : VertexB N) : Finset Letter :=
  (pointsOn y.1).disjSum (extrasB y.2.1)

theorem card_slotA : Fintype.card SlotA = 33026 := by
  simp [SlotA]

theorem card_slotB : Fintype.card SlotB = 33026 := by
  simp [SlotB]

theorem card_vertexA (N : ℕ) : Fintype.card (VertexA N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotA, Fintype.card_fin, point_card]
  ring

theorem card_vertexB (N : ℕ) : Fintype.card (VertexB N) = 2 * 16513 ^ 2 * N := by
  simp only [Fintype.card_prod, card_slotB, Fintype.card_fin, point_card]
  ring

theorem disjSum_inter {P E : Type*} [DecidableEq P] [DecidableEq E]
    (a b : Finset P) (c d : Finset E) :
    a.disjSum c ∩ b.disjSum d = (a ∩ b).disjSum (c ∩ d) := by
  ext x
  cases x <;> simp

theorem ordinary_inter_odd (l m : Line) : Odd ((pointsOn l ∩ pointsOn m).card) := by
  by_cases h : l = m
  · subst m
    simp only [Finset.inter_self,pointsOn_card]
    decide
  · rw [pointsOn_inter_card h]
    decide

theorem extras_inter_even (a : SlotA) (b : SlotB) :
    Even ((extrasA a ∩ extrasB b).card) := by
  rcases a with ⟨i,j⟩ | k <;> cases b <;>
    simp [extrasA, extrasB, Finset.card_erase_of_mem]

/-- The parity condition holds on every admissible size, independently of
all edge matchings, exactly as in equation odd-intersections. -/
theorem odd_cross_intersections {N : ℕ} (x : VertexA N) (y : VertexB N) :
    Odd ((outgoingA x ∩ outgoingB y).card) := by
  rw [outgoingA, outgoingB, disjSum_inter, Finset.card_disjSum]
  exact (ordinary_inter_odd x.1 y.1).add_even (extras_inter_even x.2.1 y.2.1)

theorem degreeA_bounds {N : ℕ} (x : VertexA N) :
    129 ≤ (outgoingA x).card ∧ (outgoingA x).card ≤ 132 := by
  rw [outgoingA, Finset.card_disjSum, pointsOn_card]
  rcases x.2.1 with ⟨i,j⟩ | k <;> simp [extrasA, Finset.card_erase_of_mem]

theorem degreeB_bounds {N : ℕ} (y : VertexB N) :
    129 ≤ (outgoingB y).card ∧ (outgoingB y).card ≤ 132 := by
  rw [outgoingB, Finset.card_disjSum, pointsOn_card]
  cases y.2.1 <;> simp [extrasB]

theorem slotA_extra_frequency (e : Fin 3) :
    Fintype.card {a : SlotA // e ∈ extrasA a} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ a : Fin 32639, if e ∈ extrasA (.inr a) then 1 else 0) = 0 := by
    simp [extrasA]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 3) :
      (∑ j : Fin 129, if e ∈ extrasA (.inl (i,j)) then 1 else 0) =
        129 * (if e ≠ i then 1 else 0) := by
    by_cases h : e = i <;> simp [extrasA, h]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin 3 => e ≠ i) = Finset.univ.erase e := by ext i; simp [ne_comm]
  rw [hc]
  simp

theorem slotB_extra_frequency (e : Fin 3) :
    Fintype.card {b : SlotB // e ∈ extrasB b} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp [extrasB]

/-- Each of the 16516 letters has exactly np carriers on each side. -/
theorem letter_frequencyA (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexA N // t ∈ outgoingA x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexA N => Sum.inl p ∈ outgoingA x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotA × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotA, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexA N => Sum.inr e ∈ outgoingA x) =
        (fun x => e ∈ extrasA x.2.1) := by funext x; simp [outgoingA]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotA × Fin N => e ∈ extrasA x.1),
      card_prod_fst (V := Fin N) (fun a : SlotA => e ∈ extrasA a),
      point_card, slotA_extra_frequency,
      Fintype.card_fin]
    ring

theorem letter_frequencyB (N : ℕ) (t : Letter) :
    Fintype.card {x : VertexB N // t ∈ outgoingB x} = 4260354 * N := by
  cases t with
  | inl p =>
    have he : (fun x : VertexB N => Sum.inl p ∈ outgoingB x) =
        (fun x => p ∈ x.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_fst (V := SlotB × Fin N) (fun l : Line => p ∈ l), Fintype.card_prod, card_slotB, Fintype.card_fin]
    have hc : Fintype.card {l : Line // p ∈ l} = 129 := by
      rw [Fintype.card_subtype]
      exact linesOn_card p
    rw [hc]
    ring
  | inr e =>
    have he : (fun x : VertexB N => Sum.inr e ∈ outgoingB x) =
        (fun x => e ∈ extrasB x.2.1) := by funext x; simp [outgoingB]
    rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))),
      card_prod_snd (U := Line) (fun x : SlotB × Fin N => e ∈ extrasB x.1),
      card_prod_fst (V := Fin N) (fun b : SlotB => e ∈ extrasB b),
      point_card, slotB_extra_frequency,
      Fintype.card_fin]
    ring

/-! ### The fixed inverse pairing and the actual space of graph matchings -/

abbrev OrdinaryCode := Fin 3 ⊕ (Fin 8255 × Bool)
abbrev Generator := Fin 3 ⊕ Fin 8255
abbrev Signed := Generator × Bool

/-- The arbitrary pairing of the remaining ordinary letters is fixed once,
using a cardinality equivalence; the first three partner the extras. -/
def pointCode : Point ≃ OrdinaryCode := Fintype.equivOfCardEq (by
  rw [point_card]
  simp [OrdinaryCode])

def signedLetter : Signed ≃ Letter where
  toFun
    | (.inl i, true) => .inr i
    | (.inl i, false) => .inl (pointCode.symm (.inl i))
    | (.inr j, b) => .inl (pointCode.symm (.inr (j,b)))
  invFun
    | .inr i => (.inl i, true)
    | .inl p => match pointCode p with
      | .inl i => (.inl i, false)
      | .inr (j,b) => (.inr j, b)
  left_inv := by
    rintro ⟨i | j,b⟩ <;> cases b <;> simp
  right_inv := by
    rintro (p | i)
    · cases hc : pointCode p with
      | inl j =>
        simp only [hc]
        exact congrArg Sum.inl (pointCode.symm_apply_eq.mpr hc.symm)
      | inr jb =>
        simp only [hc]
        exact congrArg Sum.inl (pointCode.symm_apply_eq.mpr hc.symm)
    · rfl

def inverse (t : Letter) : Letter :=
  signedLetter ( (signedLetter.symm t).1, !(signedLetter.symm t).2 )

@[simp] theorem inverse_signed (g : Generator) (b : Bool) :
    inverse (signedLetter (g,b)) = signedLetter (g,!b) := by simp [inverse]

@[simp] theorem inverse_inverse (t : Letter) : inverse (inverse t) = t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  simp

theorem inverse_ne (t : Letter) : inverse t ≠ t := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  intro he
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false] at he <;>
    cases signedLetter.injective he

variable {V : Type*} (outgoing : V → Finset Letter)

/-- Each inverse pair receives a bijection between its two carrier sets. -/
def MatchingTuple := (g : Generator) →
  {x : V // signedLetter (g,true) ∈ outgoing x} ≃
    {x : V // signedLetter (g,false) ∈ outgoing x}

/-- Exact empirical balance ensures the finite matching space is nonempty. -/
theorem matchingTuple_nonempty [Fintype V]
    (hfreq : ∀ t u, Fintype.card {x : V // t ∈ outgoing x} =
      Fintype.card {x : V // u ∈ outgoing x}) : Nonempty (MatchingTuple outgoing) := by
  exact ⟨fun g => Fintype.equivOfCardEq (hfreq _ _)⟩

/-- The direction of a step is given by the signed letter. Non-carrier
values are immaterial and are defined to fix the vertex. -/
def nextSigned (M : MatchingTuple outgoing) (x : V) : Signed → V
  | (g,true) => if hx : signedLetter (g,true) ∈ outgoing x then (M g ⟨x,hx⟩).val else x
  | (g,false) => if hx : signedLetter (g,false) ∈ outgoing x then ((M g).symm ⟨x,hx⟩).val else x

def next (M : MatchingTuple outgoing) (x : V) (t : Letter) : V :=
  nextSigned outgoing M x (signedLetter.symm t)

@[simp] theorem next_signed (M : MatchingTuple outgoing) (x : V) (g : Generator) (b : Bool) :
    next outgoing M x (signedLetter (g,b)) = nextSigned outgoing M x (g,b) := by
  simp [next]

theorem next_reverse_mem (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : inverse t ∈ outgoing (next outgoing M x t) := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simpa [nextSigned, ht] using ((M g).symm ⟨x,ht⟩).property
  · simpa [nextSigned, ht] using (M g ⟨x,ht⟩).property

theorem next_reverse_next (M : MatchingTuple outgoing) (x : V) (t : Letter)
    (ht : t ∈ outgoing x) : next outgoing M (next outgoing M x t) (inverse t) = x := by
  obtain ⟨⟨g,b⟩, rfl⟩ := signedLetter.surjective t
  cases b <;> simp only [inverse_signed, Bool.not_true, Bool.not_false, next_signed]
  · simp only [nextSigned, dite_eq_left ht]
    have hc := ((M g).symm ⟨x,ht⟩).property
    rw [dite_eq_left hc]
    exact congrArg Subtype.val ((M g).apply_symm_apply ⟨x,ht⟩)
  · simp only [nextSigned, dite_eq_left ht]
    have hc := (M g ⟨x,ht⟩).property
    rw [dite_eq_left hc]
    exact congrArg Subtype.val ((M g).symm_apply_apply ⟨x,ht⟩)

/-- In particular both source sides have an actual matching space. This
makes no girth or arrangement claim about a chosen point in that space. -/
theorem matchingA_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingA N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyA N t).trans (letter_frequencyA N u).symm)

theorem matchingB_nonempty (N : ℕ) : Nonempty (MatchingTuple (@outgoingB N)) :=
  matchingTuple_nonempty _ (fun t u => (letter_frequencyB N t).trans (letter_frequencyB N u).symm)

/-! Joint type incidences for internal-chain vertex counts.
These derive the turn weights from the actual prescribed types. -/

theorem card_prod_both {U V : Type*} [Fintype U] [Fintype V]
    (p : U → Prop) (q : V → Prop) [DecidablePred p] [DecidablePred q] :
    Fintype.card {x : U × V // p x.1 ∧ q x.2} =
      Fintype.card {u : U // p u} * Fintype.card {v : V // q v} := by
  let e : {x : U × V // p x.1 ∧ q x.2} ≃ {u : U // p u} × {v : V // q v} :=
    { toFun := fun x => (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩)
      invFun := fun x => ⟨(x.1.val,x.2.val),⟨x.1.property,x.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_prod]

theorem slotA_extra_joint (e f : Fin 3) (hef : e ≠ f) :
    Fintype.card {a : SlotA // e ∈ extrasA a ∧ f ∈ extrasA a} = 129 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  have hz : (∑ a : Fin 32639, if e ∈ extrasA (.inr a) ∧ f ∈ extrasA (.inr a)
      then 1 else 0) = 0 := by simp [extrasA]
  rw [hz, add_zero, Fintype.sum_prod_type]
  have hi (i : Fin 3) :
      (∑ j : Fin 129, if e ∈ extrasA (.inl (i,j)) ∧ f ∈ extrasA (.inl (i,j))
        then 1 else 0) = 129 * (if e ≠ i ∧ f ≠ i then 1 else 0) := by
    by_cases he : e = i <;> by_cases hf : f = i <;> simp [extrasA, he, hf]
  simp_rw [hi]
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc : (Finset.univ.filter fun i : Fin 3 => e ≠ i ∧ f ≠ i).card = 1 := by
    have he : (Finset.univ.filter fun i : Fin 3 => e ≠ i ∧ f ≠ i) =
        (Finset.univ.erase e).erase f := by
      ext i
      simp [and_comm, ne_comm]
    rw [he, Finset.card_erase_of_mem (by simp [hef.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ e)]
    simp
  rw [hc]
  norm_num

theorem slotB_extra_joint (e f : Fin 3) :
    Fintype.card {b : SlotB // e ∈ extrasB b ∧ f ∈ extrasB b} = 258 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_sum_type]
  simp [extrasB]

theorem line_single_card (p : Point) : Fintype.card {l : Line // p ∈ l} = 129 := by
  rw [Fintype.card_subtype]
  exact linesOn_card p

theorem line_joint_card (p q : Point) (hpq : p ≠ q) :
    Fintype.card {l : Line // p ∈ l ∧ q ∈ l} = 1 := by
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter fun l : Line => p ∈ l ∧ q ∈ l) =
      linesOn p ∩ linesOn q := by ext l; simp [linesOn]
  rw [he, linesOn_inter_card hpq]

/-- Counts of joint carriers can be computed in a general independent
line-slot-replica type, so both sides use literally the same geometry. -/
theorem joint_ordinary {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (p q : Point) (hpq : p ≠ q) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inl q ∈ (pointsOn x.1).disjSum (extra x.2.1)} = Fintype.card S * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inl q ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔ (p ∈ x.1 ∧ q ∈ x.1) := by
    simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_fst (V := S × Fin N) (fun l : Line => p ∈ l ∧ q ∈ l),
    line_joint_card p q hpq, Fintype.card_prod, Fintype.card_fin, one_mul]

theorem joint_mixed {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (p : Point) (e : Fin 3) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1)} =
      129 * Fintype.card {s : S // e ∈ extra s} * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inl p ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔
      (p ∈ x.1 ∧ e ∈ extra x.2.1) := by simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_both (fun l : Line => p ∈ l) (fun x : S × Fin N => e ∈ extra x.1),
    card_prod_fst (V := Fin N) (fun s : S => e ∈ extra s), line_single_card p, Fintype.card_fin]
  ring

theorem joint_extras {S : Type*} [Fintype S] (extra : S → Finset (Fin 3))
    (N : ℕ) (e f : Fin 3) :
    Fintype.card {x : Line × S × Fin N //
      Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
      Sum.inr f ∈ (pointsOn x.1).disjSum (extra x.2.1)} =
      16513 * Fintype.card {s : S // e ∈ extra s ∧ f ∈ extra s} * N := by
  have he (x : Line × S × Fin N) :
      (Sum.inr e ∈ (pointsOn x.1).disjSum (extra x.2.1) ∧
       Sum.inr f ∈ (pointsOn x.1).disjSum (extra x.2.1)) ↔
      (e ∈ extra x.2.1 ∧ f ∈ extra x.2.1) := by simp
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he),
    card_prod_snd (U := Line) (fun x : S × Fin N => e ∈ extra x.1 ∧ f ∈ extra x.1),
    card_prod_fst (V := Fin N) (fun s : S => e ∈ extra s ∧ f ∈ extra s), point_card, Fintype.card_fin]
  ring

end Types
end TorsionFreeZeroDivisors

end

end OAI
