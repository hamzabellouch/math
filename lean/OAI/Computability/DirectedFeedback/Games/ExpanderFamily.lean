import Mathlib
import OAI.Computability.DirectedFeedback.Games.CayleySpectral

namespace OAI


namespace DFVSGames.Foundations.PCP.ExpanderFamily

open PoweringWalks SpectralReturn Expanders

abbrev Port := BasePort × BasePort
abbrev CloudPort := Port × Port
def growth : Nat := baseDegree ^ 4

theorem card_port : Fintype.card Port = baseDegree ^ 2 := by
  change Fintype.card (BasePort × BasePort) = baseDegree ^ 2
  rw [Fintype.card_prod, card_basePort, pow_two]

theorem card_cloudPort : Fintype.card CloudPort = growth := by
  change Fintype.card (Port × Port) = growth
  rw [Fintype.card_prod, card_port]
  unfold growth
  ring

theorem growth_gt_one : 1 < growth := by
  norm_num [growth, baseDegree, initialDegree, basePower]

theorem port_degree_ge_eight : 8 ≤ Fintype.card Port := by
  rw [card_port]
  norm_num [baseDegree, initialDegree, basePower]

noncomputable def baseVertexEquiv : BaseVertex ≃ CloudPort :=
  Fintype.equivOfCardEq (card_baseVertex.trans card_cloudPort.symm)

noncomputable def baseOnCloud : PortGraph CloudPort BasePort :=
  GraphTransport.reindex (Classical.choose exists_baseGraph) baseVertexEquiv (Equiv.refl _)

theorem baseOnCloud_certificate : SpectralCertificate baseOnCloud (1 / 100 : ℝ) :=
  GraphTransport.reindex_spectralCertificate _ _ _ _ (Classical.choose_spec exists_baseGraph)

def Vertex : Nat → Type
  | 0 => Unit
  | n + 1 => Vertex n × CloudPort

instance vertexFintype (n : Nat) : Fintype (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Vertex n) := ih
    change Fintype (Vertex n × CloudPort)
    infer_instance

instance basePortNonempty : Nonempty BasePort :=
  ⟨fun _ => ⟨0, by norm_num [initialQuarterDegree]⟩⟩

instance vertexNonempty (n : Nat) : Nonempty (Vertex n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih =>
    let : Nonempty (Vertex n) := ih
    change Nonempty (Vertex n × CloudPort)
    infer_instance

def graph (H : PortGraph CloudPort BasePort) : (n : Nat) → PortGraph (Vertex n) Port
  | 0 => { rot := Equiv.refl _, rot_involutive := fun _ => rfl }
  | n + 1 => ZigzagGraphs.zigzag (ZigzagGraphs.square (graph H n)) H

theorem graph_certificate (H : PortGraph CloudPort BasePort)
    (hH : SpectralCertificate H (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph H n) (1 / 2 : ℝ) := by
  induction n with
  | zero =>
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro f hf
    have hm : mean f = f () := by
      change mean (fun x : Unit => f x) = f ()
      have hfun : (fun x : Unit => f x) = fun _ : Unit => f () := by
        funext x
        cases x
        rfl
      rw [hfun, mean_const]
    have hz : f = fun _ => 0 := by
      funext x
      cases x
      exact hm.symm.trans hf
    rw [hz]
    simp [energy, mean, averagingOperator]
  | succ n ih =>
    exact ZigzagSpectral.square_zigzag_halfCertificate (graph H n) H ih hH

noncomputable def family (n : Nat) : PortGraph (Vertex n) Port := graph baseOnCloud n

theorem family_certificate (n : Nat) : SpectralCertificate (family n) (1 / 2 : ℝ) :=
  graph_certificate baseOnCloud baseOnCloud_certificate n

theorem card_vertex (n : Nat) : Fintype.card (Vertex n) = growth ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Vertex n × CloudPort) = growth ^ (n + 1)
    rw [Fintype.card_prod, ih, card_cloudPort, pow_succ]

def level (k : Nat) : Nat := Nat.clog growth k

def size (k : Nat) : Nat := growth ^ level k

theorem le_size (k : Nat) : k ≤ size k := Nat.le_pow_clog growth_gt_one k

theorem size_le_mul {k : Nat} (hk : 0 < k) : size k ≤ growth * k := by
  by_cases hk1 : k = 1
  · subst k
    simpa [size, level] using growth_gt_one.le
  · have hk2 : 1 < k := by omega
    have hl : 0 < level k := Nat.clog_pos growth_gt_one hk2
    have hp : growth ^ (level k).pred < k :=
      Nat.pow_pred_clog_lt_self growth_gt_one hk2
    have he : (level k).pred + 1 = level k := Nat.succ_pred_eq_of_pos hl
    calc
      size k = growth ^ ((level k).pred + 1) := by rw [he]; rfl
      _ = growth * growth ^ (level k).pred := by rw [pow_succ, Nat.mul_comm]
      _ ≤ growth * k := Nat.mul_le_mul_left growth hp.le

theorem padded_family_size {k : Nat} (hk : 0 < k) :
    k ≤ Fintype.card (Vertex (level k)) ∧
      Fintype.card (Vertex (level k)) ≤ growth * k := by
  rw [card_vertex]
  exact ⟨le_size k, size_le_mul hk⟩

end DFVSGames.Foundations.PCP.ExpanderFamily


namespace DFVSGames.Foundations.PCP.CloudPadding

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


end DFVSGames.Foundations.PCP.CloudPadding


namespace DFVSGames.Foundations.PCP.PreprocessingCloudIndex

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

end DFVSGames.Foundations.PCP.PreprocessingCloudIndex


namespace DFVSGames.Foundations.PCP.ExpanderTables

open PoweringWalks SpectralReturn

def rowIndex (v d : Nat) : Fin v × Fin d ≃ Fin (v * d) := finProdFinEquiv

theorem rowIndex_val (v d : Nat) (x : Fin v × Fin d) :
    (rowIndex v d x).val = x.2.val + d * x.1.val := rfl

structure Table (v d : Nat) where
  rows : Vector (Fin (v * d)) (v * d)
  involutive : Function.Involutive (fun i : Fin (v * d) => rows[i])

def reverseIndex {v d : Nat} (table : Table v d) (i : Fin (v * d)) : Fin (v * d) :=
  table.rows[i]

def lookup {v d : Nat} (table : Table v d) (x : Fin v × Fin d) : Fin v × Fin d :=
  (rowIndex v d).symm (reverseIndex table (rowIndex v d x))

theorem lookup_involutive {v d : Nat} (table : Table v d) :
    Function.Involutive (lookup table) := by
  intro x
  simp only [lookup, Equiv.apply_symm_apply]
  exact (congrArg (rowIndex v d).symm (table.involutive (rowIndex v d x))).trans
    ((rowIndex v d).symm_apply_apply x)

def graph {v d : Nat} (table : Table v d) : PortGraph (Fin v) (Fin d) where
  rot := ZigzagGraphs.involutionEquiv (lookup table) (lookup_involutive table)
  rot_involutive := lookup_involutive table

@[simp] theorem graph_rot {v d : Nat} (table : Table v d) (x : Fin v × Fin d) :
    (graph table).rot x = lookup table x := rfl

def ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) : Table v d where
  rows := Vector.ofFn (fun i => rowIndex v d (G.rot ((rowIndex v d).symm i)))
  involutive := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
    exact (congrArg (rowIndex v d) (G.rot_involutive ((rowIndex v d).symm i))).trans
      ((rowIndex v d).apply_symm_apply i)

@[simp] theorem lookup_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d))
    (x : Fin v × Fin d) : lookup (ofGraph G) x = G.rot x := by
  simp only [lookup, reverseIndex, ofGraph, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta,
    Equiv.symm_apply_apply]

private theorem graph_ext_inline_ExpanderTables {V D : Type*} {G H : PortGraph V D}
    (h : ∀ x, G.rot x = H.rot x) : G = H := by
  have hr : G.rot = H.rot := Equiv.ext h
  cases G
  cases H
  cases hr
  rfl

@[simp] theorem graph_ofGraph {v d : Nat} (G : PortGraph (Fin v) (Fin d)) :
    graph (ofGraph G) = G := graph_ext_inline_ExpanderTables (lookup_ofGraph G)

theorem row_count {v d : Nat} (table : Table v d) : table.rows.toList.length = v * d := by
  simp

def vertexIndex (v q : Nat) : Fin v × (Fin q × Fin q) ≃ Fin (v * (q * q)) :=
  (Equiv.prodCongr (Equiv.refl _) (rowIndex q q)).trans (rowIndex v (q * q))

def stepGraph {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    PortGraph (Fin (v * ((d * d) * (d * d)))) (Fin (d * d)) :=
  GraphTransport.reindex
    (ZigzagGraphs.zigzag (ZigzagGraphs.square (graph G))
      (GraphTransport.reindex (graph H) (rowIndex (d * d) (d * d)).symm (Equiv.refl _)))
    (vertexIndex v (d * d)) (rowIndex d d)

def step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d) :
    Table (v * ((d * d) * (d * d))) (d * d) := ofGraph (stepGraph G H)

def stepLookup {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    Fin (v * ((d * d) * (d * d))) × Fin (d * d) :=
  let vc := (rowIndex v ((d * d) * (d * d))).symm x.1
  let ports := (rowIndex d d).symm x.2
  let first := lookup H (vc.2, ports.1)
  let squarePorts := (rowIndex (d * d) (d * d)).symm first.1
  let outerFirst := lookup G (vc.1, squarePorts.1)
  let outerSecond := lookup G (outerFirst.1, squarePorts.2)
  let last := lookup H (rowIndex (d * d) (d * d) (outerSecond.2, outerFirst.2), ports.2)
  (rowIndex v ((d * d) * (d * d)) (outerSecond.1, last.1),
    rowIndex d d (last.2, first.2))

theorem lookup_step {v d : Nat} (G : Table v (d * d))
    (H : Table ((d * d) * (d * d)) d)
    (x : Fin (v * ((d * d) * (d * d))) × Fin (d * d)) :
    lookup (step G H) x = stepLookup G H x := by
  simp [step, stepGraph, GraphTransport.reindex,
    Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.prodCongr_symm, Equiv.refl_apply, vertexIndex, Equiv.apply_symm_apply,
    ZigzagGraphs.zigzag, ZigzagGraphs.square, ZigzagGraphs.involutionEquiv,
    ZigzagGraphs.cloudFirst, ZigzagGraphs.crossCloud,
    graph_rot,
    stepLookup, Prod.map, Equiv.symm_symm]
  all_goals repeat' constructor

theorem step_certificate {v d : Nat} [NeZero v] [NeZero d]
    (G : Table v (d * d)) (H : Table ((d * d) * (d * d)) d)
    (hG : SpectralCertificate (graph G) (1 / 2 : ℝ))
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) :
    SpectralCertificate (graph (step G H)) (1 / 2 : ℝ) := by
  rw [step, graph_ofGraph]
  apply GraphTransport.reindex_spectralCertificate
  apply ZigzagSpectral.square_zigzag_halfCertificate
  · exact hG
  · exact GraphTransport.reindex_spectralCertificate _ _ _ _ hH

def initial (d : Nat) : Table 1 (d * d) :=
  ofGraph { rot := Equiv.refl _, rot_involutive := fun _ => rfl }

theorem initial_certificate (d : Nat) :
    SpectralCertificate (graph (initial d)) (1 / 2 : ℝ) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro f hf
  have hfun : f = fun _ => f 0 := funext (fun x => congrArg f (Subsingleton.elim x 0))
  have hm : mean f = f 0 := (congrArg mean hfun).trans (mean_const _)
  have hz : f 0 = 0 := hm.symm.trans hf
  rw [hfun, hz]
  simp [energy, mean, averagingOperator]

def vertexCount (q : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => vertexCount q n * (q * q)

theorem vertexCount_eq (q n : Nat) : vertexCount q n = (q * q) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [vertexCount, ih, pow_succ]

theorem vertexCount_positive {q : Nat} (hq : 0 < q) (n : Nat) :
    0 < vertexCount q n := by
  rw [vertexCount_eq]
  exact Nat.pow_pos (Nat.mul_pos hq hq)

def family {d : Nat} (H : Table ((d * d) * (d * d)) d) :
    (n : Nat) → Table (vertexCount (d * d) n) (d * d)
  | 0 => initial d
  | n + 1 => step (family H n) H

theorem family_certificate {d : Nat} [NeZero d]
    (H : Table ((d * d) * (d * d)) d)
    (hH : SpectralCertificate (graph H) (1 / 100 : ℝ)) (n : Nat) :
    SpectralCertificate (graph (family H n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact initial_certificate d
  | succ n ih =>
    let : NeZero (vertexCount (d * d) n) :=
      ⟨Nat.ne_of_gt (vertexCount_positive (Nat.mul_pos (NeZero.pos d) (NeZero.pos d)) n)⟩
    exact step_certificate _ _ ih hH

theorem family_row_count {d : Nat} (H : Table ((d * d) * (d * d)) d) (n : Nat) :
    (family H n).rows.toList.length = ((d * d) * (d * d)) ^ n * (d * d) := by
  rw [row_count, vertexCount_eq]

theorem exists_base_table : ∃ H : Table
    ((Expanders.baseDegree * Expanders.baseDegree) *
      (Expanders.baseDegree * Expanders.baseDegree)) Expanders.baseDegree,
    SpectralCertificate (graph H) (1 / 100 : ℝ) := by
  classical
  have hv : Fintype.card ExpanderFamily.CloudPort =
      (Expanders.baseDegree * Expanders.baseDegree) *
        (Expanders.baseDegree * Expanders.baseDegree) := by
    rw [ExpanderFamily.card_cloudPort]
    unfold ExpanderFamily.growth
    ring
  let vertices := Fintype.equivFinOfCardEq hv
  let ports := Fintype.equivFinOfCardEq Expanders.card_basePort
  let G := GraphTransport.reindex ExpanderFamily.baseOnCloud vertices ports
  refine ⟨ofGraph G, ?_⟩
  rw [graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    ExpanderFamily.baseOnCloud_certificate

end DFVSGames.Foundations.PCP.ExpanderTables


namespace DFVSGames.Foundations.PCP.PreprocessingLevels

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

end DFVSGames.Foundations.PCP.PreprocessingLevels

end OAI
