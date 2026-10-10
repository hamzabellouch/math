import OAI.Combinatorics.CycleDecomposition.UniformLayers

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma assigned_union_edges (L : List (AssignedPiece V)) :
    (⋃ i : Fin L.length, (L.get i).graph.edgeSet) = (graphUnion (L.map AssignedPiece.graph)).edgeSet := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [Set.mem_iUnion,SimpleGraph.mem_edgeSet]

    rw [graphUnion_adj]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨_,List.mem_map.mpr ⟨_,L.get_mem i,rfl⟩,hi⟩
    · rintro ⟨G,hG,hxy⟩
      obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hG
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
      exact ⟨i,hxy⟩

lemma box_coupled_partition {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph) := by
  apply graphPartition_of_le_one
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
  split_ifs at hb hr <;> omega

theorem uniform_local_box_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ wmin : ℝ,
    ErdosGallai.MainScaleReady wmin D →
    ∀ (V : Type) [Fintype V] (L A : List (AssignedPiece V)) (Y : Finset V),
    GraphPartition (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph))
      (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph) →
    A.Pairwise (fun R S => Disjoint R.vertices S.vertices) →
    (∀ R ∈ A, R.vertices ⊆ Y) →
    (∀ Q ∈ L, Q.vertices ⊆ Y) →
    (∀ v ∈ Y, ∃ Q ∈ L, v ∈ Q.vertices) →
    (∀ Q ∈ L, Q.vertices.Nonempty ∧ (Q.vertices.card:ℝ) ≤ D^(1/1000:ℝ) ∧
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ D^(1/1000:ℝ)) →
    (∀ R ∈ A, D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
      CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) →
    (Y.card:ℝ) ≤ D^(51/50:ℝ) → vertexMass L ≤ 2*Y.card →
    ∀ (n : ℕ) (C t : ℝ), 0 ≤ C → 0 ≤ t → Y.card ≤ n → D^(3/10:ℝ) < n →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (ErdosGallai.decompositionCost H:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (Batch.decompositionCost H:ℝ) ≤ t*Fintype.card Q) →
    (decompositionCost (graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph)):ℝ) ≤
      (9+C*ErdosGallai.mainEta)*vertexMass A + (t+8)*vertexMass L +
      (8-t/3)*vertexMass A + ((2/3)*t/logb 2 D-8)*Y.card := by
  obtain ⟨D₀,hD₀,hbox⟩ := ErdosGallai.uniform_box_cost
  refine ⟨D₀,hD₀,?_⟩
  intro D hD wmin hready V _ L A Y hpart hAd hAY hLY hcover hL hA hY hmass
    n C t hC ht hYn hsmall ih ihq
  let F := graphUnion (L.map AssignedPiece.graph)
  let G := graphUnion (L.map AssignedPiece.graph ++ A.map AssignedPiece.graph)
  let R (r : Fin A.length) := (A.get r).graph
  let U (r : Fin A.length) := (A.get r).vertices
  have hp := List.pairwise_append.mp (graphPartition_pairwise hpart)
  have hLL := list_pairwise_get (List.pairwise_map.mp hp.1) (fun _ _ h => h.symm)
  have hRR : Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) :=
    list_pairwise_get (List.pairwise_map.mp hp.2.1) (fun _ _ h => h.symm)
  have hUU : Pairwise (fun r s => Disjoint (U r) (U s)) :=
    list_pairwise_get hAd (fun _ _ h => h.symm)
  have hFR (r) : Disjoint F.edgeSet (R r).edgeSet := by
    rw [← assigned_union_edges]
    exact Set.disjoint_iUnion_left.mpr (fun i => hp.2.2 _ (List.mem_map.mpr ⟨_,L.get_mem i,rfl⟩)
      _ (List.mem_map.mpr ⟨_,A.get_mem r,rfl⟩))
  have hFG : F ≤ G := graphUnion_sublist (List.sublist_append_left _ _)
  have hRG (r) : R r ≤ G := by
    intro x y hxy
    exact (graphUnion_adj _ _ _).mpr ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨_,A.get_mem r,rfl⟩),hxy⟩
  have hcov : F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet := by
    change F.edgeSet ∪ (⋃ r : Fin A.length, (A.get r).graph.edgeSet) = _
    rw [assigned_union_edges]
    ext e
    induction e using Sym2.ind with
    | _ x y => simp only [Set.mem_union,SimpleGraph.mem_edgeSet,G,graphUnion_append,SimpleGraph.sup_adj,F]
  have hB : 0 < D^(3/10:ℝ) := Real.rpow_pos_of_pos (by linarith [hready.gt_one]) _
  obtain ⟨b⟩ := Indexing.materialize_batches F Y (fun i : Fin L.length => (L.get i).graph)
    (fun i => (L.get i).vertices) hLL (assigned_union_edges L)
    (fun i x y hxy => (L.get i).supported hxy) (fun i => hLY _ (L.get_mem i))
    (by
      intro v hv
      obtain ⟨Q,hQ,hvQ⟩ := hcover v hv
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hQ
      exact Finset.mem_biUnion.mpr ⟨i,mem_univ _,hvQ⟩)
    (D^(3/10:ℝ)) hB (fun i => ((hL _ (L.get_mem i)).2.1).trans hready.batch_power)
  have hsum : (∑ i : Fin L.length, ((L.get i).vertices.card:ℝ)) = vertexMass L := list_sum_get L (fun Q => (Q.vertices.card:ℝ))
  have hAsum : (∑ i : Fin A.length, ((U i).card:ℝ)) = vertexMass A := list_sum_get A (fun Q => (Q.vertices.card:ℝ))
  have hF : 2*(F.edgeFinset.card:ℝ) ≤ 2*Y.card*D^(1/1000:ℝ) := by
    have hh := (Nat.cast_le.mpr (edgeCount_union_le (L.map AssignedPiece.graph)) : (_:ℝ) ≤ _)
    have hdeg : (L.map (fun Q => 2*(edgeCount Q.graph:ℝ))).sum ≤ vertexMass L * D^(1/1000:ℝ) := by
      unfold vertexMass
      rw [← List.sum_map_mul_right]
      apply List.sum_le_sum
      intro Q hQ
      have hc : (0:ℝ) < Q.vertices.card := by exact_mod_cast Finset.card_pos.mpr (hL Q hQ).1
      simpa only [mul_comm] using (div_le_iff₀ hc).mp (hL Q hQ).2.2
    simp only [Nat.cast_list_sum,List.map_map,Function.comp_def] at hh
    rw [List.sum_map_mul_left] at hdeg
    have hx := mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg (show (0:ℝ) ≤ D by linarith [hready.gt_one]) (1/1000:ℝ))
    change 2*(edgeCount F:ℝ) ≤ _
    linarith
  have hcost := hbox D hD wmin hready V (Fin A.length) G F R U Y hFG hRG hRR hUU
    (fun r => hAY _ (A.get_mem r)) (fun r x y hxy => (A.get r).supported hxy) hFR hcov
    (fun r => (hA _ (A.get_mem r)).2.2)
    (fun r => ⟨(hA _ (A.get_mem r)).1,(hA _ (A.get_mem r)).2.1⟩)
    hY hF (∑ i : Fin L.length, ((L.get i).vertices.card:ℝ)) (by simpa only [hsum] using hmass)
    b n C t hC ht hYn hsmall ih ihq
  rw [hsum,hAsum] at hcost
  change (decompositionCost G:ℝ) ≤ _
  convert hcost using 1 <;> first | rfl | ring

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pastPieces_mem (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V))
    {R : AssignedPiece V} (hR : R ∈ pastPieces s j k L) :
    ∃ l < k, R ∈ levelPieces s (j+l) (advance s j l L) := by
  induction k with
  | zero => simp [pastPieces] at hR
  | succ k ih =>
    rcases List.mem_append.mp hR with h | h
    · obtain ⟨l,hl,hR⟩ := ih h
      exact ⟨l,by omega,hR⟩
    · exact ⟨k,by omega,h⟩

theorem uniform_committed_piece_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V) (H : Layers P Dstar),
    ∀ (C : ℝ), 0 ≤ C →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    ∀ k ≤ H.count, ∀ R ∈ pastPieces H.system 0 k [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card := by
  obtain ⟨D₀,hD₀,hpc⟩ := ErdosGallai.uniform_piece_cost_on 1 ErdosGallai.mainEta (by norm_num) ErdosGallai.mainEta_pos
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ _ P H C hC ih k hk R hR
  obtain ⟨j,hjk,hR⟩ := pastPieces_mem H.system 0 k [P] hR
  simp only [Nat.zero_add] at hR
  obtain ⟨Q,hQ,B,hB,hR⟩ := (by simpa [levelPieces,List.mem_flatMap] using hR :
    ∃ Q ∈ H.frontier j, ∃ B ∈ (H.system j Q).boxes, R ∈ (H.system j Q).pieces B)
  have hj : j < H.count := by omega
  have hb := (H.bounded j hj Q hQ).2.2.2.1 B hB R hR
  have hsub := ((H.system j Q).piece_subset B hB R hR).trans (H.box_subset j hQ hB)
  exact hpc (H.scale j) (hD.trans (H.cutoff j hj)) P.vertices.card C hC ih V R.graph R.graph R.vertices
    le_rfl (Finset.card_le_card hsub) R.supported hb.1 hb.2.1 (by
      simpa only [one_mul,ErdosGallai.CutExpansionOn,CutExpansionOn,cutCount,Layers.scale] using hb.2.2)

theorem uniform_gap_prefix_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] (P : AssignedPiece V) (H : Layers P Dstar),
    1 < (P.vertices.card:ℝ) →
    (∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) →
    ∀ i, i+200 < H.count → ∀ C t : ℝ, 0 ≤ C → 0 ≤ t →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (Fintype.card Q:ℝ) ≤ (H.scale i)^(3/10:ℝ) →
      (Batch.decompositionCost G:ℝ) ≤ t*Fintype.card Q) →
    (∀ R ∈ pastPieces H.system 0 (i+201) [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card) →
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles H.system 0 (i+201) [P]).length:ℝ) +
      (9+C*ErdosGallai.mainEta)*vertexMass (pastPieces H.system 0 (i+201) [P]) +
      (t+8)*H.mass (i+201) + (8-t/3)*H.pieceMass i +
      ((2/3)*t/logb 2 (H.scale i)-8)*H.mass (i+1) := by
  obtain ⟨D₀,hD₀,hlocal⟩ := uniform_local_box_cost
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ P H hn hready i hik C t hC ht ih ihq hp
  have hi : i < H.count := by omega
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hsmall : (H.scale i)^(3/10:ℝ) < (P.vertices.card:ℝ) := by
    apply lt_of_lt_of_le _ (inductionScale_le P.vertices.card hn.le i)
    have hd := inductionScale_gt_one P.vertices.card hn i
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hd (by norm_num : (3/10:ℝ) < 1)
  apply selected_prefix_cost H.system i 200 P (9+C*ErdosGallai.mainEta)
    (t+8) (8-t/3) ((2/3)*t/logb 2 (H.scale i)-8) hp
  intro Q hQ B hB
  have hQne := advance_nonempty H.system 0 i [P] (by simpa using hne) Q hQ
  have hBne := (H.system i Q).box_nonempty hQne B hB
  have hrest : ((H.system i Q).rest B).vertices.Nonempty := by simpa only [StageSplit.rest_vertices] using hBne
  exact hlocal (H.scale i) (hD.trans (H.cutoff i hi)) 80 (hready i hi) V
    (advance H.system (i+1) 200 [(H.system i Q).rest B]) ((H.system i Q).pieces B) B.vertices
    (box_coupled_partition _ (by simpa only [StageSplit.rest_graph _ hB] using (H.system i Q).box_partition B hB) _ _ _)
    ((H.system i Q).piece_disjoint B hB) ((H.system i Q).piece_subset B hB)
    (advance_subset H.system (i+1) 200 [(H.system i Q).rest B] B.vertices (by simp))
    (fun v hv => advance_cover H.system (i+1) 200 [(H.system i Q).rest B] ((H.system i Q).rest B) (by simp) v (by simpa only [StageSplit.rest_vertices] using hv))
    (fun R hR => ⟨advance_nonempty H.system (i+1) 200 [(H.system i Q).rest B] (by simpa using hrest) R hR,
      H.gap_order hn i hik hQ hB hR⟩)
    ((H.bounded i hi Q hQ).2.2.2.1 B hB) ((H.bounded i hi Q hQ).2.2.1 B hB)
    (H.local_mass_two hn (fun j hj => (hready j hj).log_large) i 200 hik hQ hB)
    P.vertices.card C t hC ht (Finset.card_le_card (H.box_subset i hQ hB)) hsmall ih ihq

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real

lemma main_gap_scalar (q n S M L Nt Ni C t w : ℝ)
    (hn : 0 ≤ n) (hS : 0 ≤ S) (hC : 0 ≤ C) (ht : 0 ≤ t) (hw : 0 < w)
    (hM : M ≤ mainP*S) (hL : L ≤ mainH*n/w)
    (hNt : Nt ≤ n+mainH*n/w) (hNilo : n ≤ Ni) (hNihi : Ni ≤ 2*n)
    (hq : q ≤ L+(9+C*mainEta)*M+(t+8)*Nt+(8-t/3)*S+((2/3)*t/w-8)*Ni) :
    q ≤ mainA₂*(S+n/w)+(C/100)*S+t*(n-S/3+mainA₁*n/w) := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hT := mul_le_mul_of_nonneg_left hNt (by linarith : 0 ≤ t+8)
  have hI := mul_le_mul_of_nonneg_left hNihi (by positivity : 0 ≤ (2/3)*t/w)
  have hI' : -8*Ni ≤ -8*n := by linarith
  have hA := mul_le_mul_of_nonneg_right (le_max_left (9*mainP+8) (9*mainH)) hS
  have hB := mul_le_mul_of_nonneg_right (le_max_right (9*mainP+8) (9*mainH)) (div_nonneg hn hw.le)
  change (9*mainP+8)*S ≤ mainA₂*S at hA
  change 9*mainH*(n/w) ≤ mainA₂*(n/w) at hB
  simp only [mainEta,mainP,mainA₁,div_eq_mul_inv] at hc hT hI hI' hA hB hq hL ⊢
  nlinarith only [hc,hT,hI,hI',hA,hB,hq,hL]

lemma main_terminal_scalar (q n M C Dstar : ℝ) (hn : 0 ≤ n) (hC : 0 ≤ C)
    (hCbig : 4*(20+Dstar+18*mainP) ≤ C) (hM : M ≤ 2*mainP*n)
    (hq : q ≤ (20+Dstar)*n+(9+C*mainEta)*M) :
    q ≤ C*Batch.inductionPhi n*n := by
  have hη := mainEta_pos
  have hc := mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ 9+C*mainEta)
  have hbig := mul_le_mul_of_nonneg_right hCbig hn
  have hphi := mul_le_mul_of_nonneg_left (Batch.inductionPhi_bounds n).1 (mul_nonneg hC hn)
  have hCn : 0 ≤ C*n := mul_nonneg hC hn
  simp only [mainEta,mainP] at hc hbig hq
  nlinarith only [hq,hc,hbig,hphi,hCn]

end
end ErdosGallai

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.gap_log (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i) :
    logb 2 (H.scale (i+200)) = scaleTheta^200 * logb 2 (H.scale i) := by
  dsimp only [Layers.scale]
  rw [inductionScale_add _ (by positivity)]
  exact Real.logb_rpow_eq_mul_logb_of_pos (inductionScale_pos _ (by linarith) _)

lemma Layers.gap_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    H.mass (i+201) ≤ (P.vertices.card:ℝ) + ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.mass_upper hn (fun j hj => (hready j hj).log_large) (i+200) hik
  rw [H.gap_log hn] at hh
  convert hh using 1 ; try omega
  unfold ErdosGallai.mainH
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma Layers.gap_cycles (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (i)
    (hik : i+200 < H.count) :
    ((pastCycles H.system 0 (i+201) [P]).length:ℝ) ≤
      ErdosGallai.mainH*P.vertices.card/logb 2 (H.scale i) := by
  have hh := H.cycles_bound hn hready (i+200) hik
  rw [H.gap_log hn] at hh
  have hw : 0 < logb 2 (H.scale i) := inductionScale_log_pos _ hn i
  calc
    _ ≤ 20*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) := hh
    _ ≤ 80*P.vertices.card/(scaleTheta^200*logb 2 (H.scale i)) :=
      div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]) (by positivity)
    _ = _ := by unfold ErdosGallai.mainH; simp only [div_eq_mul_inv,mul_inv_rev]; ring

lemma Layers.boundary_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) :
    costMass (H.frontier H.count) ≤ Dstar*P.vertices.card := by
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  have hD : 0 ≤ Dstar := by
    have hh := H.last_lt
    have hd := inductionScale_pos P.vertices.card (by linarith) H.count
    linarith
  have hcost : ∀ Q ∈ H.frontier H.count, (decompositionCost Q.graph:ℝ) ≤ (Dstar/2)*Q.vertices.card := by
    intro Q hQ
    have hQne := advance_nonempty H.system 0 H.count [P] (by simpa using hne) Q hQ
    have hc : (0:ℝ) < Q.vertices.card := by exact_mod_cast Finset.card_pos.mpr hQne
    have hg := (div_le_iff₀ hc).mp (H.degree H.count le_rfl Q hQ)
    have hh := mul_le_mul_of_nonneg_right H.last_lt.le hc.le
    have he := (Nat.cast_le.mpr (decompositionCost_edgeCount Q.graph) : (_:ℝ) ≤ _)
    nlinarith only [hg,hh,he]
  have hh := piece_list_cost (H.frontier H.count) (Dstar/2) hcost
  have hm := mul_le_mul_of_nonneg_left (H.mass_two hn (fun j hj => (hready j hj).log_large) H.count le_rfl)
    (div_nonneg hD (by norm_num : (0:ℝ) ≤ 2))
  change costMass (H.frontier H.count) ≤ (Dstar/2)*H.mass H.count at hh
  nlinarith only [hh,hm]

lemma Layers.terminal_cost (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (c : ℝ)
    (hp : ∀ R ∈ pastPieces H.system 0 H.count [P], (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ (20+Dstar)*P.vertices.card + c*vertexMass (pastPieces H.system 0 H.count [P]) := by
  have hcost := past_cost H.system 0 H.count P c hp
  have he := H.boundary_cost hn hready
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt H.positive)
  have hcy := H.cycles_bound hn hready j (by omega)
  have hw := (hready j (by omega)).log_large
  have hdiv : 20*(P.vertices.card:ℝ)/logb 2 (H.scale j) ≤ 20*P.vertices.card :=
    div_le_self (by positivity) (by linarith)
  rw [hj] at hcost he ⊢
  nlinarith only [hcost,he,hcy,hdiv]

end
end ErdosGallai.Scale

end
end
end

end OAI
