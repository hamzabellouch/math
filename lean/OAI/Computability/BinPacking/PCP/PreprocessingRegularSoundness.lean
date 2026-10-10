import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import OAI.Computability.BinPacking.Expanders.ExpanderTableEnumeration
import OAI.Computability.BinPacking.PCP.RawInitialPredicate

namespace OAI

namespace BinPackingGames.Foundations.PCP.CloudPadding

open scoped BigOperators
open DegreeReplacement

variable {V E A : Type*}

def paddedSize (k : Nat) : Nat := if k = 0 then 0 else ExpanderFamily.size k

@[simp] theorem paddedSize_zero : paddedSize 0 = 0 := rfl

theorem paddedSize_of_pos {k : Nat} (hk : 0 < k) :
    paddedSize k = ExpanderFamily.size k := by
  simp only [paddedSize, ite_eq_right (Nat.ne_of_gt hk)]

theorem le_paddedSize (k : Nat) : k ≤ paddedSize k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.le_size k

theorem paddedSize_le_mul (k : Nat) : paddedSize k ≤ ExpanderFamily.growth * k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [paddedSize, ite_eq_right hk]
    exact ExpanderFamily.size_le_mul (Nat.pos_of_ne_zero hk)

def paddedCloudEquiv (G : ConstraintGraph V E A) (dummy : V → Type*) (v : V) :
    Cloud (paddedGraph G dummy) v ≃ Cloud G v ⊕ dummy v where
  toFun := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · exact Sum.inl ⟨e, he⟩
    · change w = v at he
      cases he
      exact Sum.inr d
  invFun := fun z => match z with
    | Sum.inl e => ⟨Sum.inl e.val, e.property⟩
    | Sum.inr d => ⟨Sum.inr ⟨v, d⟩, rfl⟩
  left_inv := by
    rintro ⟨e, he⟩
    rcases e with e | ⟨w, d⟩
    · rfl
    · change w = v at he
      cases he
      rfl
  right_inv := by
    intro z
    cases z <;> rfl

def dartCloudEquiv (G : ConstraintGraph V E A) : E ≃ Σ v : V, Cloud G v where
  toFun e := ⟨G.tail e, ⟨e, rfl⟩⟩
  invFun z := z.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, ⟨e, he⟩⟩
    cases he
    rfl

variable [Fintype V] [DecidableEq V] [Fintype E]

theorem sum_card_cloud (G : ConstraintGraph V E A) :
    (∑ v, Fintype.card (Cloud G v)) = Fintype.card E := by
  simpa only [Fintype.card_sigma] using (Fintype.card_congr (dartCloudEquiv G)).symm

theorem card_padded_cloud (G : ConstraintGraph V E A) (dummy : V → Type*)
    [∀ v, Fintype (dummy v)] (v : V) :
    Fintype.card (Cloud (paddedGraph G dummy) v) =
      Fintype.card (Cloud G v) + Fintype.card (dummy v) := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (paddedCloudEquiv G dummy v)

abbrev dummy (G : ConstraintGraph V E A) (v : V) :=
  Fin (paddedSize (Fintype.card (Cloud G v)) - Fintype.card (Cloud G v))

theorem card_cloud (G : ConstraintGraph V E A) (v : V) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      paddedSize (Fintype.card (Cloud G v)) := by
  rw [card_padded_cloud]
  simp only [dummy, Fintype.card_fin]
  exact Nat.add_sub_of_le (le_paddedSize _)

omit [Fintype V] in
theorem card_dummy_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) : Fintype.card (dummy G v) = 0 := by
  simp [dummy, hk]

theorem card_cloud_of_empty (G : ConstraintGraph V E A) (v : V)
    (hk : Fintype.card (Cloud G v) = 0) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) = 0 := by
  rw [card_cloud, hk, paddedSize_zero]

theorem card_cloud_eq_family (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    Fintype.card (Cloud (paddedGraph G (dummy G)) v) =
      Fintype.card (ExpanderFamily.Vertex
        (ExpanderFamily.level (Fintype.card (Cloud G v)))) := by
  rw [card_cloud, paddedSize_of_pos hk, ExpanderFamily.card_vertex]
  rfl

theorem card_paddedDart_eq_sum (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) =
      ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
  calc
    Fintype.card (PaddedDart G (dummy G)) =
        ∑ v, Fintype.card (Cloud (paddedGraph G (dummy G)) v) :=
      (sum_card_cloud (paddedGraph G (dummy G))).symm
    _ = ∑ v, paddedSize (Fintype.card (Cloud G v)) := by
      apply Finset.sum_congr rfl
      intro v _
      exact card_cloud G v

theorem card_paddedDart_le (G : ConstraintGraph V E A) :
    Fintype.card (PaddedDart G (dummy G)) ≤ ExpanderFamily.growth * Fintype.card E := by
  rw [card_paddedDart_eq_sum]
  calc
    (∑ v, paddedSize (Fintype.card (Cloud G v))) ≤
        ∑ v, ExpanderFamily.growth * Fintype.card (Cloud G v) := by
      apply Finset.sum_le_sum
      intro v _
      exact paddedSize_le_mul _
    _ = ExpanderFamily.growth * Fintype.card E := by
      rw [← Finset.mul_sum, sum_card_cloud]

end BinPackingGames.Foundations.PCP.CloudPadding

namespace BinPackingGames.Foundations.PCP.PreprocessingCloudIndex

open scoped BigOperators
open GraphTables DegreeReplacement

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

def cloudDarts (t : Table) (v : Fin t.vertices) : List (Fin t.darts) :=
  (List.finRange t.darts).filter (fun e => decide (t.rows[e].tail = v))

@[simp] theorem mem_cloudDarts (t : Table) (v : Fin t.vertices) (e : Fin t.darts) :
    e ∈ cloudDarts t v ↔ t.rows[e].tail = v := by
  simp [cloudDarts]

theorem cloudDarts_nodup (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange t.darts)

theorem cloudDarts_sublist (t : Table) (v : Fin t.vertices) :
    (cloudDarts t v).Sublist (List.finRange t.darts) := List.filter_sublist

def cloudSize (t : Table) (v : Fin t.vertices) : Nat := (cloudDarts t v).length

theorem cloudSize_le_darts (t : Table) (v : Fin t.vertices) :
    cloudSize t v ≤ t.darts := by
  simpa only [cloudSize, List.length_finRange] using (cloudDarts_sublist t v).length_le

def cloudSelect (t : Table) (v : Fin t.vertices) (i : Fin (cloudSize t v)) :
    Cloud (semantics t) v :=
  ⟨(cloudDarts t v).get i,
    (mem_cloudDarts t v _).1 (List.get_mem (cloudDarts t v) i)⟩

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

def oldCloudIndex (t : Table) (e : Fin t.darts) :
    Fin (cloudSize t t.rows[e].tail) := cloudRank t t.rows[e].tail ⟨e, rfl⟩

@[simp] theorem cloudSelect_oldCloudIndex (t : Table) (e : Fin t.darts) :
    (cloudSelect t t.rows[e].tail (oldCloudIndex t e)).val = e :=
  congrArg Subtype.val (cloudSelect_cloudRank t t.rows[e].tail ⟨e, rfl⟩)

abbrev PaddedCloud (t : Table) (padding : Fin t.vertices → Nat)
    (v : Fin t.vertices) :=
  Cloud (paddedGraph (semantics t) (fun u => Fin (padding u))) v

def paddedOld (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (e : Cloud (semantics t) v) : PaddedCloud t padding v :=
  ⟨Sum.inl e.val, e.property⟩

def paddedNew (t : Table) (padding : Fin t.vertices → Nat) (v : Fin t.vertices)
    (i : Fin (padding v)) : PaddedCloud t padding v :=
  ⟨Sum.inr ⟨v, i⟩, rfl⟩

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

end BinPackingGames.Foundations.PCP.PreprocessingCloudIndex

noncomputable section

namespace BinPackingGames.Foundations.PCP.Regularization

open PoweringWalks DegreeReplacement

variable {V E A : Type*} [Fintype V] [Fintype E] [Fintype A]
variable [DecidableEq V] [DecidableEq E] [DecidableEq A]

abbrev Vertex (G : ConstraintGraph V E A) := PaddedDart G (CloudPadding.dummy G)
abbrev Port := ExpanderFamily.Port ⊕ Unit

def degree : Nat := Fintype.card Port

theorem degree_eq : degree = Fintype.card ExpanderFamily.Port + 1 := by
  simp [degree, Port]

theorem degree_positive : 0 < degree := by rw [degree_eq]; omega

def cloudEquiv (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    ExpanderFamily.Vertex (ExpanderFamily.level (Fintype.card (Cloud G v))) ≃
      Cloud (paddedGraph G (CloudPadding.dummy G)) v :=
  Fintype.equivOfCardEq (CloudPadding.card_cloud_eq_family G v hk).symm

def cloudGraph (G : ConstraintGraph V E A) (v : V) :
    PortGraph (Cloud (paddedGraph G (CloudPadding.dummy G)) v) ExpanderFamily.Port :=
  if hk : Fintype.card (Cloud G v) = 0 then
    { rot := Equiv.refl _
      rot_involutive := fun _ => rfl }
  else
    GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v (Nat.pos_of_ne_zero hk)) (Equiv.refl _)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    cloudGraph G v = GraphTransport.reindex
      (ExpanderFamily.family (ExpanderFamily.level (Fintype.card (Cloud G v))))
      (cloudEquiv G v hk) (Equiv.refl _) := by
  simp only [cloudGraph, dite_eq_right (Nat.ne_of_gt hk)]

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem cloudGraph_certificate_of_pos (G : ConstraintGraph V E A) (v : V)
    (hk : 0 < Fintype.card (Cloud G v)) :
    SpectralReturn.SpectralCertificate (cloudGraph G v) (1 / 2 : ℝ) := by
  rw [cloudGraph_of_pos G v hk]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (ExpanderFamily.family_certificate _)

omit [Fintype A] [DecidableEq A] in
theorem cloud_expansion (G : ConstraintGraph V E A) (v : V)
    (S : Finset (Cloud (paddedGraph G (CloudPadding.dummy G)) v))
    (hsmall : S.card ≤
      Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) / 2) :
    2 * S.card ≤
      (CloudRounding.directedCut (fun ed => ((cloudGraph G v).rot ed).1) S).card := by
  by_cases hk : Fintype.card (Cloud G v) = 0
  · have hzero : Fintype.card (Cloud (paddedGraph G (CloudPadding.dummy G)) v) = 0 := by
      rw [CloudPadding.card_cloud, hk, CloudPadding.paddedSize_zero]
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice (cloudGraph G v)
      (cloudGraph_certificate_of_pos G v (Nat.pos_of_ne_zero hk))
      ExpanderFamily.port_degree_ge_eight S (by omega)

def portGraph (G : ConstraintGraph V E A) : PortGraph (Vertex G) Port :=
  paddedReplacementPortGraph G (CloudPadding.dummy G) (cloudGraph G)

def graph (G : ConstraintGraph V E A) :
    ConstraintGraph (Vertex G) (Vertex G × Port) A :=
  paddedReplacementGraph G (CloudPadding.dummy G) (cloudGraph G)

omit [Fintype A] [DecidableEq E] in
@[simp] theorem graph_tail (G : ConstraintGraph V E A) (e : Vertex G × Port) :
    (graph G).tail e = e.1 := rfl

omit [Fintype A] [DecidableEq E] in
theorem graph_reverse (G : ConstraintGraph V E A) :
    (graph G).reverse = (portGraph G).rot := rfl

def degreeEquiv (G : ConstraintGraph V E A) (v : Vertex G) :
    Cloud (graph G) v ≃ Port where
  toFun e := e.val.2
  invFun d := ⟨(v, d), rfl⟩
  left_inv := by
    rintro ⟨⟨w, d⟩, hw⟩
    change w = v at hw
    cases hw
    rfl
  right_inv _ := rfl

omit [Fintype A] in
theorem fixed_degree (G : ConstraintGraph V E A) (v : Vertex G) :
    Fintype.card (Cloud (graph G) v) = degree :=
  Fintype.card_congr (degreeEquiv G v)

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem vertex_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G) ≤ ExpanderFamily.growth * Fintype.card E :=
  CloudPadding.card_paddedDart_le G

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) = Fintype.card (Vertex G) * degree :=
  Fintype.card_prod _ _

omit [Fintype A] [DecidableEq E] [DecidableEq A] in
theorem dart_count_le (G : ConstraintGraph V E A) :
    Fintype.card (Vertex G × Port) ≤
      (ExpanderFamily.growth * degree) * Fintype.card E := by
  rw [dart_count]
  calc
    Fintype.card (Vertex G) * degree ≤
        (ExpanderFamily.growth * Fintype.card E) * degree :=
      Nat.mul_le_mul_right degree (vertex_count_le G)
    _ = (ExpanderFamily.growth * degree) * Fintype.card E := Nat.mul_right_comm _ _ _

def liftLabel (G : ConstraintGraph V E A) (labeling : V → A) : Vertex G → A :=
  DegreeReplacement.liftLabel (paddedGraph G (CloudPadding.dummy G)) labeling

omit [Fintype A] [DecidableEq E] in
theorem lift_rejectionCount (G : ConstraintGraph V E A) (labeling : V → A) :
    (graph G).rejectionCount (liftLabel G labeling) = G.rejectionCount labeling :=
  paddedReplacement_rejectionCount G (CloudPadding.dummy G) (cloudGraph G) labeling

omit [Fintype A] [DecidableEq E] in
theorem completeness (G : ConstraintGraph V E A) (h : G.Satisfiable) :
    (graph G).Satisfiable :=
  replacement_satisfiable (paddedGraph G (CloudPadding.dummy G)) (cloudGraph G)
    (padded_satisfiable G (CloudPadding.dummy G) h)

def roundLabels [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) : V → A :=
  CloudRounding.roundLabels (paddedGraph G (CloudPadding.dummy G)) ell

theorem soundness [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    G.rejectionCount (roundLabels G ell) ≤ (graph G).rejectionCount ell :=
  CloudRounding.padded_replacement_soundness G (CloudPadding.dummy G)
    (cloudGraph G) (cloud_expansion G) ell

theorem exists_rounding [Nonempty A] (G : ConstraintGraph V E A) (ell : Vertex G → A) :
    ∃ labeling : V → A, G.rejectionCount labeling ≤ (graph G).rejectionCount ell :=
  ⟨roundLabels G ell, soundness G ell⟩

theorem soundness_of_uniform_lower_bound [Nonempty A] (G : ConstraintGraph V E A)
    (k : Nat) (lower : ∀ labeling : V → A, k ≤ G.rejectionCount labeling)
    (ell : Vertex G → A) : k ≤ (graph G).rejectionCount ell :=
  (lower (roundLabels G ell)).trans (soundness G ell)

end BinPackingGames.Foundations.PCP.Regularization

end

namespace BinPackingGames.Foundations.PCP.PreprocessingLevels

def levelLoop (g k : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, e, s => (e, s)
  | fuel + 1, e, s =>
      if k ≤ s then (e, s)
      else levelLoop g k fuel (e + 1) (s * g)

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

def boundedLevel (k : Nat) : Nat := (searchResult k).1

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

theorem boundedLevel_le_of_le_power {k j : Nat}
    (h : k ≤ ExpanderFamily.growth ^ j) : boundedLevel k ≤ j := by
  rw [boundedLevel_eq_level]
  exact (Nat.clog_le_iff_le_pow ExpanderFamily.growth_gt_one).2 h

theorem paddedSize_positive (k : Nat) : 0 < paddedSize k := by
  rw [paddedSize_power]
  exact Nat.pow_pos (by have h := ExpanderFamily.growth_gt_one; omega)

theorem paddedSize_bounds {k : Nat} (hk : 0 < k) :
    k ≤ paddedSize k ∧ paddedSize k ≤ ExpanderFamily.growth * k := by
  rw [paddedSize_eq_size]
  exact ⟨ExpanderFamily.le_size k, ExpanderFamily.size_le_mul hk⟩

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

end BinPackingGames.Foundations.PCP.PreprocessingLevels

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularTables

open scoped BigOperators
open PoweringWalks DegreeReplacement

def paddingList {n : Nat} (padding : Fin n → Nat) :
    List (Σ v : Fin n, Fin (padding v)) :=
  (List.finRange n).sigma (fun v => List.finRange (padding v))

theorem paddingList_nodup {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).Nodup :=
  (List.nodup_finRange n).sigma (fun v => List.nodup_finRange (padding v))

theorem mem_paddingList {n : Nat} (padding : Fin n → Nat)
    (z : Σ v : Fin n, Fin (padding v)) : z ∈ paddingList padding := by
  rcases z with ⟨v, k⟩
  simp only [paddingList, List.mem_sigma, List.mem_finRange, and_self]

def paddingListOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (paddingList padding).length :=
  PreprocessingCloudIndex.listEquiv (paddingList padding)
    (paddingList_nodup padding) (mem_paddingList padding)

theorem paddingList_length {n : Nat} (padding : Fin n → Nat) :
    (paddingList padding).length = ∑ v, padding v := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using
    (Fintype.card_congr (paddingListOrder padding)).symm

def paddingOrder {n : Nat} (padding : Fin n → Nat) :
    (Σ v : Fin n, Fin (padding v)) ≃ Fin (∑ v, padding v) :=
  (paddingListOrder padding).trans (finCongr (paddingList_length padding))

abbrev Vertex (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :=
  PaddedDart (GraphTables.semantics t) (fun v => Fin (padding v))

def vertexCount (t : GraphTables.Table) (padding : Fin t.vertices → Nat) : Nat :=
  t.darts + ∑ v, padding v

def vertexOrder (t : GraphTables.Table) (padding : Fin t.vertices → Nat) :
    Vertex t padding ≃ Fin (vertexCount t padding) :=
  (Equiv.sumCongr (Equiv.refl _) (paddingOrder padding)).trans finSumFinEquiv

@[simp] theorem vertexOrder_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (e : Fin t.darts) :
    (vertexOrder t padding (Sum.inl e)).val = e.val := rfl

@[simp] theorem vertexOrder_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) (z : Σ v, Fin (padding v)) :
    (vertexOrder t padding (Sum.inr z)).val =
      t.darts + (paddingOrder padding z).val := rfl

def unitOrder : Unit ≃ Fin 1 where
  toFun _ := ⟨0, Nat.zero_lt_one⟩
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv k := Subsingleton.elim _ _

def portOrder (q : Nat) : (Fin q ⊕ Unit) ≃ Fin (q + 1) :=
  (Equiv.sumCongr (Equiv.refl _) unitOrder).trans finSumFinEquiv

@[simp] theorem portOrder_internal (q : Nat) (p : Fin q) :
    (portOrder q (Sum.inl p)).val = p.val := rfl

@[simp] theorem portOrder_inherited (q : Nat) :
    (portOrder q (Sum.inr ())).val = q := rfl

def cloudGraphs (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) (v : Fin t.vertices) :
    PortGraph (Cloud (paddedGraph (GraphTables.semantics t)
      (fun w => Fin (padding w))) v) (Fin q) :=
  GraphTransport.reindex (ExpanderTables.graph (tables v))
    (PreprocessingCloudIndex.paddedCloudEquiv t padding v).symm (Equiv.refl _)

def sourcePortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Vertex t padding) (Fin q ⊕ Unit) :=
  paddedReplacementPortGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def sourceGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    ConstraintGraph (Vertex t padding) (Vertex t padding × (Fin q ⊕ Unit))
      GraphTables.Label :=
  paddedReplacementGraph (GraphTables.semantics t) (fun v => Fin (padding v))
    (cloudGraphs t padding tables)

def numberedPortGraph (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortGraph (Fin (vertexCount t padding)) (Fin (q + 1)) :=
  GraphTransport.reindex (sourcePortGraph t padding tables)
    (vertexOrder t padding) (portOrder q)

def numberedAccepts (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1))
    (a b : GraphTables.Label) : Bool :=
  (sourceGraph t padding tables).accepts
    ((vertexOrder t padding).symm e.1, (portOrder q).symm e.2) a b

theorem numberedAccepts_transpose (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin (vertexCount t padding) × Fin (q + 1)) (a b : GraphTables.Label) :
    numberedAccepts t padding tables ((numberedPortGraph t padding tables).rot e) b a =
      numberedAccepts t padding tables e a b := by
  obtain ⟨z, rfl⟩ := (Equiv.prodCongr (vertexOrder t padding) (portOrder q)).surjective e
  rcases z with ⟨v, p⟩
  simp only [numberedPortGraph, Equiv.prodCongr_apply, Prod.map_apply,
    GraphTransport.reindex_rot, numberedAccepts, Equiv.symm_apply_apply]
  exact (sourceGraph t padding tables).reverse_accepts (v, p) a b

def ofCloudTables (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    {q : Nat} (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q) :
    PortTables.Table (vertexCount t padding) (q + 1) :=
  PortTables.ofPortGraph (numberedPortGraph t padding tables)
    (numberedAccepts t padding tables) (numberedAccepts_transpose t padding tables)

@[simp] theorem rotation_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    PortTables.rotation (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) =
      (vertexOrder t padding ((sourcePortGraph t padding tables).rot (v, p)).1,
        portOrder q ((sourcePortGraph t padding tables).rot (v, p)).2) := by
  rw [ofCloudTables, PortTables.rotation_ofPortGraph]
  exact GraphTransport.reindex_rot _ _ _ _ _

@[simp] theorem accepts_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q p) a b =
      (sourceGraph t padding tables).accepts (v, p) a b := by
  simp only [ofCloudTables, PortTables.accepts_ofPortGraph,
    numberedAccepts, Equiv.symm_apply_apply]

@[simp] theorem accepts_internal (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (v : Vertex t padding) (p : Fin q) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding v, portOrder q (Sum.inl p)) a b = decide (a = b) := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_original (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (e : Fin t.darts) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inl e), portOrder q (Sum.inr ())) a b =
      GraphTables.acceptsAt t.rows e a b := by
  rw [accepts_ofCloudTables]
  rfl

@[simp] theorem accepts_dummy (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (z : Σ v, Fin (padding v)) (a b : GraphTables.Label) :
    PortTables.accepts (ofCloudTables t padding tables)
        (vertexOrder t padding (Sum.inr z), portOrder q (Sum.inr ())) a b = true := by
  rw [accepts_ofCloudTables]
  rfl

theorem edgeSatisfied_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label)
    (v : Vertex t padding) (p : Fin q ⊕ Unit) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).edgeSatisfied labels
        (vertexOrder t padding v, portOrder q p) =
      (sourceGraph t padding tables).edgeSatisfied
        (fun z => labels (vertexOrder t padding z)) (v, p) := by
  change PortTables.accepts (ofCloudTables t padding tables)
    (vertexOrder t padding v, portOrder q p) (labels (vertexOrder t padding v))
    (labels (PortTables.rotation (ofCloudTables t padding tables)
      (vertexOrder t padding v, portOrder q p)).1) = _
  rw [rotation_ofCloudTables, accepts_ofCloudTables]
  rfl

theorem rejectionCount_ofCloudTables (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin (vertexCount t padding) → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount labels =
      (sourceGraph t padding tables).rejectionCount
        (fun z => labels (vertexOrder t padding z)) := by
  classical
  unfold ConstraintGraph.rejectionCount
  symm
  apply Finset.card_equiv (Equiv.prodCongr (vertexOrder t padding) (portOrder q))
  rintro ⟨v, p⟩
  simp only [ConstraintGraph.mem_rejectedDarts, Equiv.prodCongr_apply,
    Prod.map_apply, edgeSatisfied_ofCloudTables]

def liftedLabel (t : GraphTables.Table) (padding : Fin t.vertices → Nat)
    (labels : Fin t.vertices → GraphTables.Label) :
    Fin (vertexCount t padding) → GraphTables.Label :=
  fun z => labels (paddedOwner (GraphTables.semantics t) (fun v => Fin (padding v))
    ((vertexOrder t padding).symm z))

theorem rejectionCount_liftedLabel (t : GraphTables.Table)
    (padding : Fin t.vertices → Nat) {q : Nat}
    (tables : ∀ v, ExpanderTables.Table
      (PreprocessingCloudIndex.cloudSize t v + padding v) q)
    (labels : Fin t.vertices → GraphTables.Label) :
    (PortTables.baseGraph (ofCloudTables t padding tables)).rejectionCount
        (liftedLabel t padding labels) = (GraphTables.semantics t).rejectionCount labels := by
  rw [rejectionCount_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  convert paddedReplacement_rejectionCount (GraphTables.semantics t)
    (fun v => Fin (padding v)) (cloudGraphs t padding tables) labels using 1; rfl

def emptyTable (q : Nat) : ExpanderTables.Table 0 q :=
  ExpanderTables.ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

def resizeTable {n m q : Nat} (h : n = m) (table : ExpanderTables.Table n q) :
    ExpanderTables.Table m q := h ▸ table

abbrev BaseTable := ExpanderTables.Table
  ((Expanders.baseDegree * Expanders.baseDegree) *
    (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree

def internalDegree : Nat := Expanders.baseDegree * Expanders.baseDegree

def padding (t : GraphTables.Table) (v : Fin t.vertices) : Nat :=
  PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) -
    PreprocessingCloudIndex.cloudSize t v

theorem cloudSize_add_padding (t : GraphTables.Table) (v : Fin t.vertices) :
    PreprocessingCloudIndex.cloudSize t v + padding t v =
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) :=
  Nat.add_sub_of_le (PreprocessingLevels.cloudPaddedSize_bounds _).1

theorem vertexCount_eq_sum_cloudPaddedSize (t : GraphTables.Table) :
    vertexCount t (padding t) = ∑ v,
      PreprocessingLevels.cloudPaddedSize (PreprocessingCloudIndex.cloudSize t v) := by
  unfold vertexCount
  rw [← PreprocessingCloudIndex.sum_cloudSize t, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun v _ => cloudSize_add_padding t v)

theorem vertexCount_le (t : GraphTables.Table) :
    vertexCount t (padding t) ≤ ExpanderFamily.growth * t.darts := by
  rw [vertexCount_eq_sum_cloudPaddedSize, ← PreprocessingCloudIndex.sum_cloudSize t,
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun v _ => (PreprocessingLevels.cloudPaddedSize_bounds _).2)

theorem vertexCount_eq_zero_of_no_darts (t : GraphTables.Table) (h : t.darts = 0) :
    vertexCount t (padding t) = 0 := by
  have hle := vertexCount_le t
  rw [h, Nat.mul_zero] at hle
  exact Nat.eq_zero_of_le_zero hle

def familyCloudTable (H : BaseTable) (t : GraphTables.Table) (v : Fin t.vertices) :
    ExpanderTables.Table (PreprocessingCloudIndex.cloudSize t v + padding t v)
      internalDegree :=
  if hk : PreprocessingCloudIndex.cloudSize t v = 0 then
    resizeTable (by rw [cloudSize_add_padding, hk]; rfl) (emptyTable internalDegree)
  else
    resizeTable (by
      rw [cloudSize_add_padding,
        PreprocessingLevels.cloudPaddedSize_of_pos (Nat.pos_of_ne_zero hk)]
      exact PreprocessingLevels.table_vertexCount_eq_paddedSize _)
      (ExpanderTables.family H
        (PreprocessingLevels.boundedLevel (PreprocessingCloudIndex.cloudSize t v)))

def regularize (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Table (vertexCount t (padding t)) (internalDegree + 1) :=
  ofCloudTables t (padding t) (familyCloudTable H t)

def regularizeInput (H : BaseTable) (t : GraphTables.Table) :
    PortTables.Input (internalDegree + 1) :=
  ⟨vertexCount t (padding t), regularize H t⟩

end BinPackingGames.Foundations.PCP.PreprocessingRegularTables

namespace BinPackingGames.Foundations.PCP.PreprocessingRegularSoundness

open PoweringWalks DegreeReplacement SpectralReturn PreprocessingRegularTables

theorem internalDegree_ge_eight : 8 ≤ internalDegree := by
  simpa only [ExpanderFamily.card_port, internalDegree, pow_two] using
    ExpanderFamily.port_degree_ge_eight

theorem baseDegree_ne_zero : Expanders.baseDegree ≠ 0 := by
  intro h
  have hdegree := internalDegree_ge_eight
  simp only [internalDegree, h, Nat.zero_mul] at hdegree
  omega

theorem resizeTable_certificate {n m q : Nat} (h : n = m)
    (table : ExpanderTables.Table n q) (lambda : ℝ)
    (certificate : SpectralCertificate (ExpanderTables.graph table) lambda) :
    SpectralCertificate (ExpanderTables.graph (resizeTable h table)) lambda := by
  cases h
  exact certificate

theorem familyCloudTable_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (ExpanderTables.graph (familyCloudTable H t v)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨baseDegree_ne_zero⟩
  unfold familyCloudTable
  rw [dite_eq_right (Nat.ne_of_gt hk)]
  apply resizeTable_certificate
  exact ExpanderTables.family_certificate H certificate _

theorem cloudGraphs_certificate_of_pos (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (hk : 0 < PreprocessingCloudIndex.cloudSize t v) :
    SpectralCertificate (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (1 / 2 : ℝ) := by
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (familyCloudTable_certificate_of_pos H certificate t v hk)

theorem cloud_expansion (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (v : Fin t.vertices)
    (S : Finset (PreprocessingCloudIndex.PaddedCloud t (padding t) v))
    (hsmall : S.card ≤
      Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) / 2) :
    2 * S.card ≤ (CloudRounding.directedCut
      (fun ed => ((cloudGraphs t (padding t) (familyCloudTable H t) v).rot ed).1) S).card := by
  by_cases hk : PreprocessingCloudIndex.cloudSize t v = 0
  · have hzero : Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v) = 0 := by
      rw [PreprocessingCloudIndex.card_paddedCloud, cloudSize_add_padding, hk]
      rfl
    have hs : S.card = 0 := by omega
    simp only [hs, mul_zero, Nat.zero_le]
  · exact SpectralCut.cut_card_ge_twice
      (cloudGraphs t (padding t) (familyCloudTable H t) v)
      (cloudGraphs_certificate_of_pos H certificate t v (Nat.pos_of_ne_zero hk))
      (by simpa only [Fintype.card_fin] using internalDegree_ge_eight) S (by
        change 2 * S.card ≤
          Fintype.card (PreprocessingCloudIndex.PaddedCloud t (padding t) v)
        omega)

noncomputable def roundLabels (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    Fin t.vertices → GraphTables.Label :=
  CloudRounding.roundLabels
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (fun z => labels (vertexOrder t (padding t) z))

theorem soundness (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    (GraphTables.semantics t).rejectionCount (roundLabels t labels) ≤
      (PortTables.baseGraph (regularize H t)).rejectionCount labels := by
  rw [regularize, rejectionCount_ofCloudTables]
  exact CloudRounding.padded_replacement_soundness (GraphTables.semantics t)
    (fun v => Fin (padding t v)) (cloudGraphs t (padding t) (familyCloudTable H t))
    (cloud_expansion H certificate t) (fun z => labels (vertexOrder t (padding t) z))

theorem exists_rounding (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    ∃ original : Fin t.vertices → GraphTables.Label,
      (GraphTables.semantics t).rejectionCount original ≤
        (PortTables.baseGraph (regularize H t)).rejectionCount labels :=
  ⟨roundLabels t labels, soundness H certificate t labels⟩

theorem lift_rejectionCount (H : BaseTable) (t : GraphTables.Table)
    (labels : Fin t.vertices → GraphTables.Label) :
    (PortTables.baseGraph (regularize H t)).rejectionCount
        (liftedLabel t (padding t) labels) = (GraphTables.semantics t).rejectionCount labels :=
  rejectionCount_liftedLabel t (padding t) (familyCloudTable H t) labels

theorem completeness (H : BaseTable) (t : GraphTables.Table)
    (h : (GraphTables.semantics t).Satisfiable) :
    (PortTables.baseGraph (regularize H t)).Satisfiable := by
  obtain ⟨labels, hlabels⟩ := h
  refine ⟨liftedLabel t (padding t) labels, ?_⟩
  intro e
  obtain ⟨z, rfl⟩ :=
    (Equiv.prodCongr (vertexOrder t (padding t)) (portOrder internalDegree)).surjective e
  rcases z with ⟨v, p⟩
  change (PortTables.baseGraph (regularize H t)).edgeSatisfied
    (liftedLabel t (padding t) labels)
    (vertexOrder t (padding t) v, portOrder internalDegree p) = true
  rw [regularize, edgeSatisfied_ofCloudTables]
  simp only [liftedLabel, Equiv.symm_apply_apply]
  have hcomplete := replacement_complete
    (paddedGraph (GraphTables.semantics t) (fun v => Fin (padding t v)))
    (cloudGraphs t (padding t) (familyCloudTable H t)) labels
    (padded_complete (GraphTables.semantics t) (fun v => Fin (padding t v)) labels hlabels)
    (v, p)
  convert hcomplete using 1
  rfl

theorem soundness_of_uniform_lower_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (k : Nat)
    (lower : ∀ original : Fin t.vertices → GraphTables.Label,
      k ≤ (GraphTables.semantics t).rejectionCount original)
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    k ≤ (PortTables.baseGraph (regularize H t)).rejectionCount labels :=
  (lower (roundLabels t labels)).trans (soundness H certificate t labels)

theorem soundness_of_uniform_real_lower_bound (H : BaseTable)
    (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (t : GraphTables.Table) (k : ℝ)
    (lower : ∀ original : Fin t.vertices → GraphTables.Label,
      k ≤ ((GraphTables.semantics t).rejectionCount original : ℝ))
    (labels : Fin (vertexCount t (padding t)) → GraphTables.Label) :
    k ≤ ((PortTables.baseGraph (regularize H t)).rejectionCount labels : ℝ) :=
  (lower (roundLabels t labels)).trans (Nat.cast_le.mpr (soundness H certificate t labels))

end BinPackingGames.Foundations.PCP.PreprocessingRegularSoundness

end OAI
