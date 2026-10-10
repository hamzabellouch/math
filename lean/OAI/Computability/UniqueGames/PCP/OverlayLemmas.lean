import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.FieldSimp
import OAI.Computability.UniqueGames.PCP.ExpanderTables
import OAI.Computability.UniqueGames.PCP.ExpandersLemmas
import OAI.Computability.UniqueGames.PCP.GraphTables
import OAI.Computability.UniqueGames.PCP.InitialGraphLemmas
import OAI.Computability.UniqueGames.PCP.ZigzagGraphsLemmas

namespace OAI

section

/-!
Overlay a regular constraint graph with an actual regular port graph whose
new constraints always accept. The port sets are disjoint, so all original
rejected darts are retained exactly. The averaging operator is the actual
degree-weighted mixture of the two graph averages.
-/

open scoped BigOperators

namespace UniqueGamesTheorem.Foundations.PCP.Overlay

open PoweringWalks SpectralReturn

variable {V D E A : Type*}

def originalPortGraph (G : ConstraintGraph V (V × D) A) : PortGraph V D where
  rot := G.reverse
  rot_involutive := G.reverse_involutive

def rotate (G : PortGraph V D) (H : PortGraph V E) :
    V × (D ⊕ E) → V × (D ⊕ E)
  | (v, Sum.inl d) => ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2)
  | (v, Sum.inr e) => ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2)

theorem rotate_involutive (G : PortGraph V D) (H : PortGraph V E) :
    Function.Involutive (rotate G H) := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · exact congrArg (fun a : V × D => (a.1, (Sum.inl a.2 : D ⊕ E)))
      (G.rot_involutive (v, d))
  · exact congrArg (fun a : V × E => (a.1, (Sum.inr a.2 : D ⊕ E)))
      (H.rot_involutive (v, e))

def portGraph (G : PortGraph V D) (H : PortGraph V E) : PortGraph V (D ⊕ E) where
  rot :=
    { toFun := rotate G H
      invFun := rotate G H
      left_inv := rotate_involutive G H
      right_inv := rotate_involutive G H }
  rot_involutive := rotate_involutive G H

@[simp] theorem portGraph_rot_inl (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (d : D) :
    (portGraph G H).rot (v, Sum.inl d) =
      ((G.rot (v, d)).1, Sum.inl (G.rot (v, d)).2) := rfl

@[simp] theorem portGraph_rot_inr (G : PortGraph V D) (H : PortGraph V E)
    (v : V) (e : E) :
    (portGraph G H).rot (v, Sum.inr e) =
      ((H.rot (v, e)).1, Sum.inr (H.rot (v, e)).2) := rfl

/-- Keep the original tests and add always-accepting tests on the overlay ports. -/
def constraintGraph (G : ConstraintGraph V (V × D) A) (H : PortGraph V E) :
    ConstraintGraph V (V × (D ⊕ E)) A where
  reverse := (portGraph (originalPortGraph G) H).rot
  reverse_involutive := (portGraph (originalPortGraph G) H).rot_involutive
  tail := Prod.fst
  accepts p a b := match p.2 with
    | Sum.inl d => G.accepts (p.1, d) a b
    | Sum.inr _ => true
  reverse_accepts := by
    rintro ⟨v, p⟩ a b
    rcases p with d | e
    · exact G.reverse_accepts (v, d) a b
    · rfl

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) : (constraintGraph G H).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) :
    originalPortGraph (constraintGraph G H) = portGraph (originalPortGraph G) H := rfl

@[simp] theorem edgeSatisfied_inl (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (htail : G.tail = Prod.fst)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inl d) =
      G.edgeSatisfied labeling (v, d) := by
  change G.accepts (v, d) (labeling v) (labeling (G.reverse (v, d)).1) =
    G.accepts (v, d) (labeling (G.tail (v, d)))
      (labeling (G.tail (G.reverse (v, d))))
  rw [htail]

@[simp] theorem edgeSatisfied_inr (G : ConstraintGraph V (V × D) A)
    (H : PortGraph V E) (labeling : V → A) (v : V) (e : E) :
    (constraintGraph G H).edgeSatisfied labeling (v, Sum.inr e) = true := rfl

theorem complete (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A)
    (h : ∀ a, G.edgeSatisfied labeling a = true) :
    ∀ a, (constraintGraph G H).edgeSatisfied labeling a = true := by
  rintro ⟨v, p⟩
  rcases p with d | e
  · rw [edgeSatisfied_inl G H htail]
    exact h (v, d)
  · rfl

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) :
    (constraintGraph G H).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling, h⟩
    refine ⟨labeling, ?_⟩
    rintro ⟨v, d⟩
    rw [← edgeSatisfied_inl G H htail]
    exact h (v, Sum.inl d)
  · rintro ⟨labeling, h⟩
    exact ⟨labeling, complete G H htail labeling h⟩

/-- Every labeling rejects exactly the same number of darts before and after overlay. -/
theorem rejectionCount_eq [Fintype V] [Fintype D] [Fintype E]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (htail : G.tail = Prod.fst) (labeling : V → A) :
    (constraintGraph G H).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_sum_type]
  simp [edgeSatisfied_inl G H htail]

theorem card_ports [Fintype D] [Fintype E] :
    Fintype.card (D ⊕ E) = Fintype.card D + Fintype.card E := Fintype.card_sum

theorem card_darts [Fintype V] [Fintype D] [Fintype E] :
    Fintype.card (V × (D ⊕ E)) =
      Fintype.card (V × D) + Fintype.card (V × E) := by
  simp only [Fintype.card_prod, Fintype.card_sum, Nat.mul_add]

section Averages

variable [Fintype V] [Fintype D] [Fintype E]

omit [Fintype V] in
/-- The normalized graph average weights the components by their actual port counts. -/
theorem operator_mix [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (f : V → ℝ) (v : V) :
    averagingOperator (portGraph G H) f v =
      (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator G f v +
      (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E) *
        averagingOperator H f v := by
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  change mean (fun p : D ⊕ E => f ((portGraph G H).rot (v, p)).1) = _
  rw [mean_eq_sum_div_card]
  simp only [Fintype.sum_sum_type, Fintype.card_sum, Nat.cast_add,
    portGraph_rot_inl, portGraph_rot_inr]
  unfold averagingOperator
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  field_simp [hd.ne', he.ne', (add_pos hd he).ne']

/-- Convexity of the squared energy, proved pointwise before taking the finite mean. -/
theorem energy_convex_mix (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (f g : V → ℝ) :
    energy (fun v => a * f v + b * g v) ≤ a * energy f + b * energy g := by
  calc
    energy (fun v => a * f v + b * g v) ≤
        mean (fun v => a * (f v) ^ 2 + b * (g v) ^ 2) := by
      apply mean_mono
      intro v
      have hnormalize := congrArg (fun t : ℝ => t * (a * (f v) ^ 2 + b * (g v) ^ 2)) hab
      have hnonneg := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (f v - g v))
      nlinarith
    _ = a * energy f + b * energy g := by
      rw [mean_add, mean_mul_left, mean_mul_left]
      rfl

/-- Actual overlay contraction from the supplied graph's spectral bound and
the proved energy contraction of an arbitrary reversible regular graph. -/
theorem energy_bound [Nonempty V] [Nonempty D] [Nonempty E]
    (G : PortGraph V D) (H : PortGraph V E) (lambda : ℝ)
    (certificate : SpectralCertificate H lambda) (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * lambda ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) * energy f := by
  let a : ℝ := (Fintype.card D : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  let b : ℝ := (Fintype.card E : ℝ) / ((Fintype.card D : ℝ) + Fintype.card E)
  have hd : (0 : ℝ) < Fintype.card D := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card D)
  have he : (0 : ℝ) < Fintype.card E := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := add_pos hd he
  have ha : 0 ≤ a := div_nonneg hd.le hden.le
  have hb : 0 ≤ b := div_nonneg he.le hden.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self hden.ne']
  have hop : averagingOperator (portGraph G H) f =
      fun v => a * averagingOperator G f v + b * averagingOperator H f v := by
    funext v
    exact operator_mix G H f v
  calc
    energy (averagingOperator (portGraph G H) f) ≤
        a * energy (averagingOperator G f) + b * energy (averagingOperator H f) := by
      rw [hop]
      exact energy_convex_mix a b ha hb hab _ _
    _ ≤ a * energy f + b * (lambda ^ 2 * energy f) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (ZigzagSpectral.averaging_energy_le G f) ha)
        (mul_le_mul_of_nonneg_left (certificate.contraction f hf) hb)
    _ = _ := by
      dsimp [a, b]
      ring

/-- With one more original port than overlay ports, a half-spectral overlay
has squared contraction at most three quarters. -/
theorem energy_bound_three_quarters [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ))
    (f : V → ℝ) (hf : mean f = 0) :
    energy (averagingOperator (portGraph G H) f) ≤ (3 / 4 : ℝ) * energy f := by
  let _ : Nonempty E := Fintype.card_pos_iff.mp (lt_of_lt_of_le Nat.zero_lt_one hpositive)
  let _ : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have he : (1 : ℝ) ≤ Fintype.card E := by exact_mod_cast hpositive
  have hd : (Fintype.card D : ℝ) = (Fintype.card E : ℝ) + 1 := by exact_mod_cast hdegree
  have hden : (0 : ℝ) < (Fintype.card D : ℝ) + Fintype.card E := by linarith
  have hcoefficient :
      ((Fintype.card D : ℝ) + (Fintype.card E : ℝ) * (1 / 2 : ℝ) ^ 2) /
        ((Fintype.card D : ℝ) + Fintype.card E) ≤ (3 / 4 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  exact (energy_bound G H (1 / 2) certificate f hf).trans
    (mul_le_mul_of_nonneg_right hcoefficient (energy_nonnegative f))

theorem spectralCertificate_seven_eighths [Nonempty V]
    (G : PortGraph V D) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (portGraph G H) (7 / 8 : ℝ) where
  nonnegative := by norm_num
  lt_one := by norm_num
  contraction := by
    intro f hf
    exact (energy_bound_three_quarters G H hdegree hpositive certificate f hf).trans
      (mul_le_mul_of_nonneg_right (by norm_num : (3 / 4 : ℝ) ≤ (7 / 8 : ℝ) ^ 2)
        (energy_nonnegative f))

/-- The certificate belongs to the exact underlying graph of the overlaid constraints. -/
theorem constraintGraph_spectralCertificate [Nonempty V]
    (G : ConstraintGraph V (V × D) A) (H : PortGraph V E)
    (hdegree : Fintype.card D = Fintype.card E + 1) (hpositive : 1 ≤ Fintype.card E)
    (certificate : SpectralCertificate H (1 / 2 : ℝ)) :
    SpectralCertificate (originalPortGraph (constraintGraph G H)) (7 / 8 : ℝ) := by
  rw [constraintGraph_portGraph]
  exact spectralCertificate_seven_eighths (originalPortGraph G) H
    hdegree hpositive certificate

end Averages

end UniqueGamesTheorem.Foundations.PCP.Overlay

end

section

/-! Lazification of the actual constraint graph. Original ports retain their
tests; the equally many stay-put ports always accept. The reverse is precisely
the existing lazy port-graph rotation used by the spectral and walk lemmas. -/
namespace UniqueGamesTheorem.Foundations.PCP.LazyConstraint

open scoped BigOperators
open PoweringWalks

variable {V D A : Type*}

def constraintGraph (G : ConstraintGraph V (V × D) A) :
    ConstraintGraph V (V × (Bool × D)) A where
  reverse := (lazyGraph (Overlay.originalPortGraph G)).rot
  reverse_involutive := (lazyGraph (Overlay.originalPortGraph G)).rot_involutive
  tail := Prod.fst
  accepts e a b := if e.2.1 then G.accepts (e.1,e.2.2) a b else true
  reverse_accepts := by
    rintro ⟨v,b,d⟩ a c
    cases b with
    | false => rfl
    | true => exact G.reverse_accepts (v,d) a c

@[simp] theorem constraintGraph_tail (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).tail = Prod.fst := rfl

@[simp] theorem constraintGraph_reverse (G : ConstraintGraph V (V × D) A) :
    (constraintGraph G).reverse = (lazyGraph (Overlay.originalPortGraph G)).rot := rfl

@[simp] theorem constraintGraph_portGraph (G : ConstraintGraph V (V × D) A) :
    Overlay.originalPortGraph (constraintGraph G) =
      lazyGraph (Overlay.originalPortGraph G) := rfl

@[simp] theorem edgeSatisfied_false (G : ConstraintGraph V (V × D) A)
    (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(false,d)) = true := rfl

@[simp] theorem edgeSatisfied_true (G : ConstraintGraph V (V × D) A)
    (htail : G.tail = Prod.fst) (labeling : V → A) (v : V) (d : D) :
    (constraintGraph G).edgeSatisfied labeling (v,(true,d)) =
      G.edgeSatisfied labeling (v,d) := by
  change G.accepts (v,d) (labeling v) (labeling (G.reverse (v,d)).1) =
    G.accepts (v,d) (labeling (G.tail (v,d)))
      (labeling (G.tail (G.reverse (v,d))))
  rw [htail]

theorem complete (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) (h : ∀ e, G.edgeSatisfied labeling e = true) :
    ∀ e, (constraintGraph G).edgeSatisfied labeling e = true := by
  rintro ⟨v,b,d⟩
  cases b with
  | false => rfl
  | true =>
    rw [edgeSatisfied_true G htail]
    exact h (v,d)

theorem complete_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (∀ e, (constraintGraph G).edgeSatisfied labeling e = true) ↔
      ∀ e, G.edgeSatisfied labeling e = true := by
  constructor
  · intro h
    rintro ⟨v,d⟩
    rw [← edgeSatisfied_true G htail]
    exact h (v,(true,d))
  · exact complete G htail labeling

theorem satisfiable_iff (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst) :
    (constraintGraph G).Satisfiable ↔ G.Satisfiable := by
  constructor
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, (complete_iff G htail labeling).mp h⟩
  · rintro ⟨labeling,h⟩
    exact ⟨labeling, complete G htail labeling h⟩

/-- The equality holds for every labeling, including nonsatisfying ones. -/
theorem rejectionCount_eq [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    (constraintGraph G).rejectionCount labeling = G.rejectionCount labeling := by
  classical
  simp only [DegreeReplacement.rejectionCount_eq_sum, Fintype.sum_prod_type,
    Fintype.sum_bool]
  simp [edgeSatisfied_true G htail]

theorem card_ports [Fintype D] :
    Fintype.card (Bool × D) = 2 * Fintype.card D := by
  simp

theorem card_darts [Fintype V] [Fintype D] :
    Fintype.card (V × (Bool × D)) = 2 * Fintype.card (V × D) := by
  simp [Fintype.card_prod, Nat.mul_left_comm]

/-- The actual normalized rejection probability is halved. The identity also
holds for empty dart types, using the field's totalized division. -/
theorem rejection_density_eq_half [Fintype V] [Fintype D]
    (G : ConstraintGraph V (V × D) A) (htail : G.tail = Prod.fst)
    (labeling : V → A) :
    ((constraintGraph G).rejectionCount labeling : ℝ) /
        (Fintype.card (V × (Bool × D)) : ℝ) =
      ((G.rejectionCount labeling : ℝ) / (Fintype.card (V × D) : ℝ)) / 2 := by
  rw [rejectionCount_eq G htail, card_darts]
  simp only [Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
  ring

end UniqueGamesTheorem.Foundations.PCP.LazyConstraint

end

section

/-!
# Executable indexing of the actual outgoing-dart clouds

Clouds are enumerated by filtering the input table's increasing dart-index
list. Ranking searches that list, and selection reads its indexed entry.
The same functions work for empty clouds without selecting a default dart.
Padded cloud indices put all old darts first and the dummy indices afterward.
All data functions below are executable; their proofs establish the connection
to the semantic graph's actual tail fibers.
-/

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

/-- An explicit complete list supplies both directions of a finite encoding.
The forward direction searches the list; its inverse performs list indexing. -/
def listEquiv {α : Type*} [BEq α] [LawfulBEq α] (xs : List α)
    (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) : α ≃ Fin xs.length where
  toFun a := ⟨xs.idxOf a, List.idxOf_lt_length_of_mem (complete a)⟩
  invFun i := xs.get i
  left_inv a := List.idxOf_get _
  right_inv i := by
    apply Fin.ext
    exact List.get_idxOf nodup i

@[simp] theorem listEquiv_val {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs) (a : α) :
    (listEquiv xs nodup complete a).val = xs.idxOf a := rfl

@[simp] theorem listEquiv_symm_apply {α : Type*} [BEq α] [LawfulBEq α]
    (xs : List α) (nodup : xs.Nodup) (complete : ∀ a, a ∈ xs)
    (i : Fin xs.length) : (listEquiv xs nodup complete).symm i = xs.get i := rfl

/-- Retain the input dart order and test only the stored tail index. -/
def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

/-- Filtering preserves the original ordering, including repeated row values
at different dart indices. -/
theorem cloudDarts_sublist (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Sublist (List.finRange t.darts) := List.filter_sublist

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

theorem cloudSize_le_darts (t : Table) (v : Fin t.vertices) :
    cloudSize t v ≤ t.darts := by
  simpa only [cloudSize, List.length_finRange] using (cloudDarts_sublist t v).length_le

/-- Read the original dart stored at a valid local cloud index. -/
def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

/-- Find the local index of an original dart belonging to this cloud. -/
def cloudRank (t : Table) (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    Fin (cloudSize t v) :=
  ⟨(cloudDarts t v).idxOf e.val,
    List.idxOf_lt_length_of_mem ((mem_cloudDarts t v e.val).2 e.property)⟩

@[simp] theorem cloudSelect_val (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) :
    (cloudSelect t v i).val = (cloudDarts t v).get i := rfl

@[simp] theorem cloudRank_val (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) :
    (cloudRank t v e).val = (cloudDarts t v).idxOf e.val := rfl

@[simp] theorem cloudSelect_cloudRank (t : Table) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : cloudSelect t v (cloudRank t v e) = e := by
  apply Subtype.ext
  exact List.idxOf_get (cloudRank t v e).isLt

@[simp] theorem cloudRank_cloudSelect (t : Table) (v : Fin t.vertices)
    (i : Fin (cloudSize t v)) : cloudRank t v (cloudSelect t v i) = i := by
  apply Fin.ext
  exact List.get_idxOf (cloudDarts_nodup t v) i

/-- This equivalence contains executable rank and select functions, including
when both its domain and codomain are empty. -/
def cloudEquiv (t : Table) (v : Fin t.vertices) :
    Cloud (semantics t) v ≃ Fin (cloudSize t v) where
  toFun := cloudRank t v
  invFun := cloudSelect t v
  left_inv := cloudSelect_cloudRank t v
  right_inv := cloudRank_cloudSelect t v

theorem cloudSize_eq_card_cloud (t : Table) (v : Fin t.vertices) :
    cloudSize t v = Fintype.card (Cloud (semantics t) v) := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (cloudEquiv t v)).symm

theorem cloudDarts_eq_nil_iff (t : Table) (v : Fin t.vertices) :
    cloudDarts t v = [] ↔ ∀ e : Fin t.darts, t.rows[e].tail ≠ v := by
  simp only [List.eq_nil_iff_forall_not_mem, mem_cloudDarts]

theorem cloudSize_eq_zero_iff (t : Table) (v : Fin t.vertices) :
    cloudSize t v = 0 ↔ ∀ e : Fin t.darts, t.rows[e].tail ≠ v := by
  rw [cloudSize, List.length_eq_zero_iff, cloudDarts_eq_nil_iff]

theorem sum_cloudSize (t : Table) : (∑ v, cloudSize t v) = t.darts := by
  calc
    _ = ∑ v, Fintype.card (Cloud (semantics t) v) := by
      apply Finset.sum_congr rfl
      intro v _
      exact cloudSize_eq_card_cloud t v
    _ = Fintype.card (Fin t.darts) := CloudPadding.sum_card_cloud (semantics t)
    _ = t.darts := Fintype.card_fin t.darts

/-- An original global dart carries its own owner and executable local rank. -/
def oldCloudIndex (t : Table) (e : Fin t.darts) :
    Fin (cloudSize t t.rows[e].tail) := cloudRank t t.rows[e].tail ⟨e, rfl⟩

@[simp] theorem cloudSelect_oldCloudIndex (t : Table) (e : Fin t.darts) :
    (cloudSelect t t.rows[e].tail (oldCloudIndex t e)).val = e :=
  congrArg Subtype.val (cloudSelect_cloudRank t t.rows[e].tail ⟨e, rfl⟩)

/-- Padding counts are supplied as executable natural-valued data, without
choosing enumerations of the semantic clouds by their cardinalities. -/
abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

/-- Local padded order: old cloud indices first, then increasing dummy index. -/
def paddedCloudEquiv (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) : PaddedCloud t padding v ≃ Fin (cloudSize t v + padding v) :=
  (CloudPadding.paddedCloudEquiv (semantics t) (fun u => Fin (padding u)) v).trans
    ((Equiv.sumCongr (cloudEquiv t v) (Equiv.refl (Fin (padding v)))).trans
      finSumFinEquiv)

def paddedCloudRank (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    PaddedCloud t padding v → Fin (cloudSize t v + padding v) :=
  paddedCloudEquiv t padding v

def paddedCloudSelect (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices) :
    Fin (cloudSize t v + padding v) → PaddedCloud t padding v :=
  (paddedCloudEquiv t padding v).symm

@[simp] theorem paddedCloudSelect_rank (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : PaddedCloud t padding v) :
    paddedCloudSelect t padding v (paddedCloudRank t padding v e) = e :=
  (paddedCloudEquiv t padding v).symm_apply_apply e

@[simp] theorem paddedCloudRank_select (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v + padding v)) :
    paddedCloudRank t padding v (paddedCloudSelect t padding v i) = i :=
  (paddedCloudEquiv t padding v).apply_symm_apply i

@[simp] theorem paddedCloudRank_old (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    paddedCloudRank t padding v (paddedOld t padding v e) =
      Fin.castAdd (padding v) (cloudRank t v e) := rfl

@[simp] theorem paddedCloudRank_new (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudRank t padding v (paddedNew t padding v i) =
      Fin.natAdd (cloudSize t v) i := rfl

@[simp] theorem paddedCloudRank_old_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (e : Cloud (semantics t) v) :
    (paddedCloudRank t padding v (paddedOld t padding v e)).val =
      (cloudRank t v e).val := rfl

@[simp] theorem paddedCloudRank_new_val (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    (paddedCloudRank t padding v (paddedNew t padding v i)).val =
      cloudSize t v + i.val := rfl

@[simp] theorem paddedCloudSelect_castAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    paddedCloudSelect t padding v (Fin.castAdd (padding v) i) =
      paddedOld t padding v (cloudSelect t v i) := by
  apply (paddedCloudEquiv t padding v).injective
  change (paddedCloudEquiv t padding v)
      ((paddedCloudEquiv t padding v).symm (Fin.castAdd (padding v) i)) = _
  rw [Equiv.apply_symm_apply]
  change Fin.castAdd (padding v) i =
    Fin.castAdd (padding v) (cloudRank t v (cloudSelect t v i))
  rw [cloudRank_cloudSelect]

@[simp] theorem paddedCloudSelect_natAdd (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) (i : Fin (padding v)) :
    paddedCloudSelect t padding v (Fin.natAdd (cloudSize t v) i) =
      paddedNew t padding v i :=
  (paddedCloudEquiv t padding v).symm_apply_apply (paddedNew t padding v i)

theorem card_paddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :
    Fintype.card (PaddedCloud t padding v) = cloudSize t v + padding v := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (paddedCloudEquiv t padding v)

end UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex

end

section

namespace UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

/-- At most `fuel` continuing iterations can increment the exponent. -/
theorem levelLoop_level_le (g k fuel e s : Nat) :
    (levelLoop g k fuel e s).1 ≤ e + fuel := by
  induction fuel generalizing e s with
  | zero => simp only [levelLoop, Nat.add_zero, le_refl]
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · omega
      · have h := ih (e + 1) (s * g)
        omega

/-- The carried size remains the exact power of the carried exponent. -/
theorem levelLoop_power (g k fuel e : Nat) :
    (levelLoop g k fuel e (g ^ e)).2 =
      g ^ (levelLoop g k fuel e (g ^ e)).1 := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · rfl
      · simpa only [pow_succ] using ih (e + 1)

theorem levelLoop_covers (g k fuel e s : Nat) (hg : 1 < g)
    (hs : 0 < s) (hbudget : k ≤ s + fuel) :
    k ≤ (levelLoop g k fuel e s).2 := by
  induction fuel generalizing e s with
  | zero => simpa only [levelLoop, Nat.add_zero] using hbudget
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · assumption
      · apply ih
        · exact Nat.mul_pos hs (by omega)
        · have htwo : 2 ≤ g := by omega
          have hmul : s * 2 ≤ s * g := Nat.mul_le_mul_left s htwo
          omega

/-- The search never passes an exponent whose power already covers the
request. This remains true even without a sufficient fuel budget. -/
theorem levelLoop_le_of_covering_power (g k fuel e j : Nat)
    (he : e ≤ j) (hj : k ≤ g ^ j) :
    (levelLoop g k fuel e (g ^ e)).1 ≤ j := by
  induction fuel generalizing e with
  | zero => exact he
  | succ fuel ih =>
      simp only [levelLoop]
      split
      · exact he
      · rename_i hnot
        have hne : e ≠ j := by
          intro h
          subst e
          exact hnot hj
        have hnext : e + 1 ≤ j := by omega
        simpa only [pow_succ] using ih (e + 1) hnext

def searchResult (k : Nat) : Nat × Nat :=
  levelLoop ExpanderFamily.growth k k 0 1

/-- An executable exponent, computed with at most `k` multiplications. -/
def boundedLevel (k : Nat) : Nat := (searchResult k).1

/-- The algorithm returns the power it has already computed. -/
def paddedSize (k : Nat) : Nat := (searchResult k).2

@[simp] theorem boundedLevel_zero : boundedLevel 0 = 0 := rfl

@[simp] theorem paddedSize_zero : paddedSize 0 = 1 := rfl

theorem boundedLevel_le_input (k : Nat) : boundedLevel k ≤ k := by
  simpa only [boundedLevel, searchResult, Nat.zero_add] using
    levelLoop_level_le ExpanderFamily.growth k k 0 1

theorem paddedSize_power (k : Nat) :
    paddedSize k = ExpanderFamily.growth ^ boundedLevel k := by
  simpa only [paddedSize, boundedLevel, searchResult, pow_zero] using
    levelLoop_power ExpanderFamily.growth k k 0

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  exact levelLoop_covers ExpanderFamily.growth k k 0 1
    ExpanderFamily.growth_gt_one (by omega) (by omega)

/-- The bounded multiplication loop computes the existing ceiling logarithm. -/
theorem boundedLevel_eq_level (k : Nat) :
    boundedLevel k = ExpanderFamily.level k := by
  apply Nat.le_antisymm
  · simpa only [boundedLevel, searchResult, pow_zero] using
      levelLoop_le_of_covering_power ExpanderFamily.growth k k 0
        (ExpanderFamily.level k) (Nat.zero_le _) (ExpanderFamily.le_size k)
  · apply (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2
    rw [← paddedSize_power]
    exact le_paddedSize k

theorem paddedSize_eq_size (k : Nat) : paddedSize k = ExpanderFamily.size k := by
  rw [paddedSize_power, boundedLevel_eq_level]
  rfl

/-- The returned exponent is the least exponent whose power covers `k`. -/
theorem boundedLevel_le_of_le_power {k j : Nat}
    (h : k ≤ ExpanderFamily.growth ^ j) : boundedLevel k ≤ j := by
  rw [boundedLevel_eq_level]
  exact (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2 h

theorem paddedSize_positive (k : Nat) : 0 < paddedSize k := by
  rw [paddedSize_power]
  exact Nat.pow_pos (by have h := ExpanderFamily.growth_gt_one; omega)

/-- Positive cloud sizes and positive whole-graph vertex counts increase by
at most the single fixed growth factor. -/
theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

/-- Empty clouds remain empty; nonempty clouds use the geometric family. -/
def cloudPaddedSize (k : Nat) : Nat := if k = 0 then 0 else paddedSize k

@[simp] theorem cloudPaddedSize_zero : cloudPaddedSize 0 = 0 := rfl

theorem cloudPaddedSize_of_pos {k : Nat} (hk : 0 < k) :
    cloudPaddedSize k = paddedSize k := by
  simp only [cloudPaddedSize, Nat.ne_of_gt hk, ite_false]

theorem cloudPaddedSize_bounds (k : Nat) :
    k ≤ cloudPaddedSize k ∧ cloudPaddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp only [cloudPaddedSize_zero, Nat.mul_zero, le_refl, and_self]
  · rw [cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
    exact paddedSize_bounds (Nat.pos_of_ne_zero hk)

/-- The executable table family has exactly the size returned by the loop. -/
theorem table_vertexCount_eq_paddedSize (k : Nat) :
    ExpanderTables.vertexCount (Expanders.baseDegree * Expanders.baseDegree)
        (boundedLevel k) = paddedSize k := by
  rw [ExpanderTables.vertexCount_eq]
  have hg : (Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree) = ExpanderFamily.growth := by
    unfold ExpanderFamily.growth
    ring
  rw [hg]
  exact (paddedSize_power k).symm

theorem family_row_count_at_size
    (H : ExpanderTables.Table
      ((Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree)
    (k : Nat) :
    (ExpanderTables.family H (boundedLevel k)).rows.toList.length =
      paddedSize k * (Expanders.baseDegree * Expanders.baseDegree) := by
  rw [ExpanderTables.row_count, table_vertexCount_eq_paddedSize]

end UniqueGamesTheorem.Foundations.PCP.PreprocessingLevels

end

end OAI
