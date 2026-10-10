import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateMatrixChunks
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastCertificateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastLayoutGraph

namespace OAI

namespace CycleClique.Construction.Certificates

def k6t3p0 : LayoutCertificate 3 where
  chains := [[0], [1], [2]]
  clique := {0, 1, 2}
  templates := [⟨0, 1, [], [], [], 1, 5⟩,
    ⟨0, 2, [], [], [], 1, 5⟩,
    ⟨1, 2, [], [], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2)}⟩


private def k6t3p0_state_0 : ForbiddenMatrix 3 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p0_initial_eq_row_0 : ∀ j : Fin 3, (k6t3p0.initialMatrix 6) 0 j = k6t3p0_state_0 0 j := by decide

private theorem k6t3p0_initial_eq_row_1 : ∀ j : Fin 3, (k6t3p0.initialMatrix 6) 1 j = k6t3p0_state_0 1 j := by decide

private theorem k6t3p0_initial_eq_row_2 : ∀ j : Fin 3, (k6t3p0.initialMatrix 6) 2 j = k6t3p0_state_0 2 j := by decide

private theorem k6t3p0_initial_eq : (k6t3p0.initialMatrix 6) = k6t3p0_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p0_initial_eq_row_0 j

  · exact k6t3p0_initial_eq_row_1 j

  · exact k6t3p0_initial_eq_row_2 j

private theorem k6t3p0_closure_0 : ClosureCheck k6t3p0.graph k6t3p0_state_0 6 3 [] := by trivial

private theorem k6t3p0_matrix_eq : k6t3p0.matrix 6 = k6t3p0_state_0 := by
  change closureMatrix (k6t3p0.initialMatrix 6) _ = _
  rw [k6t3p0_initial_eq]
  change closureMatrix k6t3p0_state_0 [] = _
  rfl

private theorem k6t3p0_part_0 : k6t3p0.chains.flatten = List.finRange _ := by decide

private theorem k6t3p0_part_1 : k6t3p0.chains.map List.length = ([[], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p0_part_2 : k6t3p0.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p0.clique))) = ([[], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 5⟩ : TemplateData (Fin 3)).Check k6t3p0.graph k6t3p0.clique 6 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 3)).Check k6t3p0.graph k6t3p0.clique 6 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p0_templates_item_2 : (⟨1, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 3)).Check k6t3p0.graph k6t3p0.clique 6 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p0_part_3 : ∀ T ∈ k6t3p0.templates, T.Check k6t3p0.graph k6t3p0.clique 6 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p0_templates_item_0, k6t3p0_templates_item_1, k6t3p0_templates_item_2⟩

private theorem k6t3p0_part_4 : ∀ p ∈ k6t3p0.required, p.Check k6t3p0.graph 6 := by decide

private theorem k6t3p0_part_5 : ClosureCheck k6t3p0.graph (k6t3p0.initialMatrix 6) 6 3 k6t3p0.closure := by
  rw [k6t3p0_initial_eq]
  exact k6t3p0_closure_0

private theorem k6t3p0_part_6 : k6t3p0.bad.Check k6t3p0.graph (k6t3p0.matrix 6) 6 3 := by
  rw [k6t3p0_matrix_eq]
  decide

theorem k6t3p0_check : k6t3p0.Check 6 3 [[], [], []] :=
  ⟨k6t3p0_part_0, k6t3p0_part_1, k6t3p0_part_2, k6t3p0_part_3, k6t3p0_part_4, k6t3p0_part_5, k6t3p0_part_6⟩
def k6t3p1 : LayoutCertificate 4 where
  chains := [[0], [1, 2, 3]]
  clique := {0, 1, 3}
  templates := [⟨0, 1, [], [], [], 2, 5⟩,
    ⟨0, 1, [], [], [2, 3], 1, 3⟩,
    ⟨0, 2, [], [], [1], 1, 4⟩,
    ⟨0, 3, [], [], [2, 1], 1, 3⟩,
    ⟨1, 2, [], [], [3], 1, 4⟩,
    ⟨2, 3, [], [1], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (2, 2), (1, 2)}⟩


private def k6t3p1_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[{1, 2, 3}, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p1_initial_eq_row_0 : ∀ j : Fin 4, (k6t3p1.initialMatrix 6) 0 j = k6t3p1_state_0 0 j := by decide

private theorem k6t3p1_initial_eq_row_1 : ∀ j : Fin 4, (k6t3p1.initialMatrix 6) 1 j = k6t3p1_state_0 1 j := by decide

private theorem k6t3p1_initial_eq_row_2 : ∀ j : Fin 4, (k6t3p1.initialMatrix 6) 2 j = k6t3p1_state_0 2 j := by decide

private theorem k6t3p1_initial_eq_row_3 : ∀ j : Fin 4, (k6t3p1.initialMatrix 6) 3 j = k6t3p1_state_0 3 j := by decide

private theorem k6t3p1_initial_eq : (k6t3p1.initialMatrix 6) = k6t3p1_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p1_initial_eq_row_0 j

  · exact k6t3p1_initial_eq_row_1 j

  · exact k6t3p1_initial_eq_row_2 j

  · exact k6t3p1_initial_eq_row_3 j

private theorem k6t3p1_closure_0 : ClosureCheck k6t3p1.graph k6t3p1_state_0 6 3 [] := by trivial

private theorem k6t3p1_matrix_eq : k6t3p1.matrix 6 = k6t3p1_state_0 := by
  change closureMatrix (k6t3p1.initialMatrix 6) _ = _
  rw [k6t3p1_initial_eq]
  change closureMatrix k6t3p1_state_0 [] = _
  rfl

private theorem k6t3p1_part_0 : k6t3p1.chains.flatten = List.finRange _ := by decide

private theorem k6t3p1_part_1 : k6t3p1.chains.map List.length = ([[], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p1_part_2 : k6t3p1.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p1.clique))) = ([[], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 5⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_templates_item_1 : (⟨0, 1, [], [], [2, 3], 1, 3⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_templates_item_2 : (⟨0, 2, [], [], [1], 1, 4⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_templates_item_3 : (⟨0, 3, [], [], [2, 1], 1, 3⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_templates_item_4 : (⟨1, 2, [], [], [3], 1, 4⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_templates_item_5 : (⟨2, 3, [], [1], [], 1, 4⟩ : TemplateData (Fin 4)).Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p1_part_3 : ∀ T ∈ k6t3p1.templates, T.Check k6t3p1.graph k6t3p1.clique 6 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p1_templates_item_0, k6t3p1_templates_item_1, k6t3p1_templates_item_2, k6t3p1_templates_item_3, k6t3p1_templates_item_4, k6t3p1_templates_item_5⟩

private theorem k6t3p1_part_4 : ∀ p ∈ k6t3p1.required, p.Check k6t3p1.graph 6 := by decide

private theorem k6t3p1_part_5 : ClosureCheck k6t3p1.graph (k6t3p1.initialMatrix 6) 6 3 k6t3p1.closure := by
  rw [k6t3p1_initial_eq]
  exact k6t3p1_closure_0

private theorem k6t3p1_part_6 : k6t3p1.bad.Check k6t3p1.graph (k6t3p1.matrix 6) 6 3 := by
  rw [k6t3p1_matrix_eq]
  decide

theorem k6t3p1_check : k6t3p1.Check 6 3 [[], [1]] :=
  ⟨k6t3p1_part_0, k6t3p1_part_1, k6t3p1_part_2, k6t3p1_part_3, k6t3p1_part_4, k6t3p1_part_5, k6t3p1_part_6⟩
private def k6t3p2_step_0_data : EdgeAttachmentData 5 := ⟨2, 0, [⟨2, 1, [0]⟩], ⟨none, {(0, 2), (2, 2), (1, 3)}⟩⟩

private def k6t3p2_step_0 : ClosureStep 5 := .edge k6t3p2_step_0_data

private def k6t3p2_step_1_data : EdgeAttachmentData 5 := ⟨3, 0, [⟨3, 4, [0]⟩], ⟨none, {(0, 2), (3, 2), (4, 3)}⟩⟩

private def k6t3p2_step_1 : ClosureStep 5 := .edge k6t3p2_step_1_data

private def k6t3p2_step_2_data : EdgeAttachmentData 5 := ⟨3, 1, [⟨2, 1, [3]⟩], ⟨none, {(0, 2), (2, 2), (1, 3)}⟩⟩

private def k6t3p2_step_2 : ClosureStep 5 := .edge k6t3p2_step_2_data

private def k6t3p2_step_3_data : EdgeAttachmentData 5 := ⟨4, 2, [⟨2, 1, [4]⟩], ⟨none, {(0, 2), (2, 2), (1, 3)}⟩⟩

private def k6t3p2_step_3 : ClosureStep 5 := .edge k6t3p2_step_3_data

private def k6t3p2_step_4_data : FreshAttachmentData 5 := ⟨4, 2, [⟨1, 0, [2, 3, 4, 5]⟩, ⟨2, 0, [1, 5, 4, 3]⟩, ⟨2, 4, [1, 5, 0, 3]⟩, ⟨4, 0, [3, 2, 1, 5]⟩, ⟨4, 2, [3, 0, 5, 1]⟩], ⟨none, {(1, 2), (2, 2), (4, 2), (3, 0)}⟩⟩

private def k6t3p2_step_4 : ClosureStep 5 := .fresh k6t3p2_step_4_data

def k6t3p2 : LayoutCertificate 5 where
  chains := [[0], [1, 2, 3, 4]]
  clique := {0, 1, 4}
  templates := [⟨0, 1, [], [], [], 3, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4], 1, 2⟩,
    ⟨0, 2, [], [], [1], 2, 4⟩,
    ⟨0, 2, [], [], [3, 4], 1, 3⟩,
    ⟨0, 3, [], [], [2, 1], 1, 3⟩,
    ⟨0, 3, [], [], [4], 2, 4⟩,
    ⟨0, 4, [], [], [], 3, 5⟩,
    ⟨0, 4, [], [], [3, 2, 1], 1, 2⟩,
    ⟨1, 2, [], [], [3, 4], 1, 3⟩,
    ⟨1, 3, [], [], [4], 2, 4⟩,
    ⟨2, 3, [], [1], [4], 1, 3⟩,
    ⟨3, 4, [], [1, 2], [], 1, 3⟩]
  required := [⟨1, 2, []⟩,
    ⟨3, 4, []⟩]
  closure := [k6t3p2_step_0, k6t3p2_step_1, k6t3p2_step_2, k6t3p2_step_3, k6t3p2_step_4]
  bad := ⟨none, {(0, 2), (2, 2), (3, 1)}⟩


private def k6t3p2_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {2, 3, 4}, ∅],
    #[Finset.Icc 1 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_initial_eq_row_0 : ∀ j : Fin 5, (k6t3p2.initialMatrix 6) 0 j = k6t3p2_state_0 0 j := by decide

private theorem k6t3p2_initial_eq_row_1 : ∀ j : Fin 5, (k6t3p2.initialMatrix 6) 1 j = k6t3p2_state_0 1 j := by decide

private theorem k6t3p2_initial_eq_row_2 : ∀ j : Fin 5, (k6t3p2.initialMatrix 6) 2 j = k6t3p2_state_0 2 j := by decide

private theorem k6t3p2_initial_eq_row_3 : ∀ j : Fin 5, (k6t3p2.initialMatrix 6) 3 j = k6t3p2_state_0 3 j := by decide

private theorem k6t3p2_initial_eq_row_4 : ∀ j : Fin 5, (k6t3p2.initialMatrix 6) 4 j = k6t3p2_state_0 4 j := by decide

private theorem k6t3p2_initial_eq : (k6t3p2.initialMatrix 6) = k6t3p2_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p2_initial_eq_row_0 j

  · exact k6t3p2_initial_eq_row_1 j

  · exact k6t3p2_initial_eq_row_2 j

  · exact k6t3p2_initial_eq_row_3 j

  · exact k6t3p2_initial_eq_row_4 j

private def k6t3p2_state_1 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p2_local_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, {2, 3, 4}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_local_0_eq_row_0 : ∀ j : Fin 5, (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) 0 j = k6t3p2_local_0 0 j := by decide

private theorem k6t3p2_local_0_eq_row_1 : ∀ j : Fin 5, (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) 1 j = k6t3p2_local_0 1 j := by decide

private theorem k6t3p2_local_0_eq_row_2 : ∀ j : Fin 5, (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) 2 j = k6t3p2_local_0 2 j := by decide

private theorem k6t3p2_local_0_eq_row_3 : ∀ j : Fin 5, (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) 3 j = k6t3p2_local_0 3 j := by decide

private theorem k6t3p2_local_0_eq_row_4 : ∀ j : Fin 5, (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) 4 j = k6t3p2_local_0 4 j := by decide

private theorem k6t3p2_local_0_eq : (fun a b => k6t3p2_state_0 a b ∪ requiredMatrix 6 k6t3p2_step_0_data.required a b) = k6t3p2_local_0 := by
  funext i j
  fin_cases i

  · exact k6t3p2_local_0_eq_row_0 j

  · exact k6t3p2_local_0_eq_row_1 j

  · exact k6t3p2_local_0_eq_row_2 j

  · exact k6t3p2_local_0_eq_row_3 j

  · exact k6t3p2_local_0_eq_row_4 j

private theorem k6t3p2_local_0_paths : ∀ p ∈ k6t3p2_step_0_data.required, p.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_0_data.i k6t3p2_step_0_data.j) 6 := by decide

private theorem k6t3p2_local_0_bad : k6t3p2_step_0_data.bad.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_0_data.i k6t3p2_step_0_data.j) k6t3p2_local_0 6 3 := by decide

private theorem k6t3p2_step_0_check : k6t3p2_step_0.Check k6t3p2.graph k6t3p2_state_0 6 3 := by
  change k6t3p2_step_0_data.Check k6t3p2.graph k6t3p2_state_0 6 3
  refine ⟨k6t3p2_local_0_paths, ?_⟩
  rw [k6t3p2_local_0_eq]
  exact k6t3p2_local_0_bad

private theorem k6t3p2_update_0 : k6t3p2_step_0.apply k6t3p2_state_0 = k6t3p2_state_1 := by
  have h : ∀ i j : Fin 5, k6t3p2_step_0.apply k6t3p2_state_0 i j = k6t3p2_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p2_state_2 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p2_local_1 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, ∅, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_local_1_eq_row_0 : ∀ j : Fin 5, (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) 0 j = k6t3p2_local_1 0 j := by decide

private theorem k6t3p2_local_1_eq_row_1 : ∀ j : Fin 5, (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) 1 j = k6t3p2_local_1 1 j := by decide

private theorem k6t3p2_local_1_eq_row_2 : ∀ j : Fin 5, (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) 2 j = k6t3p2_local_1 2 j := by decide

private theorem k6t3p2_local_1_eq_row_3 : ∀ j : Fin 5, (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) 3 j = k6t3p2_local_1 3 j := by decide

private theorem k6t3p2_local_1_eq_row_4 : ∀ j : Fin 5, (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) 4 j = k6t3p2_local_1 4 j := by decide

private theorem k6t3p2_local_1_eq : (fun a b => k6t3p2_state_1 a b ∪ requiredMatrix 6 k6t3p2_step_1_data.required a b) = k6t3p2_local_1 := by
  funext i j
  fin_cases i

  · exact k6t3p2_local_1_eq_row_0 j

  · exact k6t3p2_local_1_eq_row_1 j

  · exact k6t3p2_local_1_eq_row_2 j

  · exact k6t3p2_local_1_eq_row_3 j

  · exact k6t3p2_local_1_eq_row_4 j

private theorem k6t3p2_local_1_paths : ∀ p ∈ k6t3p2_step_1_data.required, p.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_1_data.i k6t3p2_step_1_data.j) 6 := by decide

private theorem k6t3p2_local_1_bad : k6t3p2_step_1_data.bad.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_1_data.i k6t3p2_step_1_data.j) k6t3p2_local_1 6 3 := by decide

private theorem k6t3p2_step_1_check : k6t3p2_step_1.Check k6t3p2.graph k6t3p2_state_1 6 3 := by
  change k6t3p2_step_1_data.Check k6t3p2.graph k6t3p2_state_1 6 3
  refine ⟨k6t3p2_local_1_paths, ?_⟩
  rw [k6t3p2_local_1_eq]
  exact k6t3p2_local_1_bad

private theorem k6t3p2_update_1 : k6t3p2_step_1.apply k6t3p2_state_1 = k6t3p2_state_2 := by
  have h : ∀ i j : Fin 5, k6t3p2_step_1.apply k6t3p2_state_1 i j = k6t3p2_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p2_state_3 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {0, 2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p2_local_2 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, {2, 3, 4}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 1 5, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_local_2_eq_row_0 : ∀ j : Fin 5, (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) 0 j = k6t3p2_local_2 0 j := by decide

private theorem k6t3p2_local_2_eq_row_1 : ∀ j : Fin 5, (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) 1 j = k6t3p2_local_2 1 j := by decide

private theorem k6t3p2_local_2_eq_row_2 : ∀ j : Fin 5, (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) 2 j = k6t3p2_local_2 2 j := by decide

private theorem k6t3p2_local_2_eq_row_3 : ∀ j : Fin 5, (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) 3 j = k6t3p2_local_2 3 j := by decide

private theorem k6t3p2_local_2_eq_row_4 : ∀ j : Fin 5, (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) 4 j = k6t3p2_local_2 4 j := by decide

private theorem k6t3p2_local_2_eq : (fun a b => k6t3p2_state_2 a b ∪ requiredMatrix 6 k6t3p2_step_2_data.required a b) = k6t3p2_local_2 := by
  funext i j
  fin_cases i

  · exact k6t3p2_local_2_eq_row_0 j

  · exact k6t3p2_local_2_eq_row_1 j

  · exact k6t3p2_local_2_eq_row_2 j

  · exact k6t3p2_local_2_eq_row_3 j

  · exact k6t3p2_local_2_eq_row_4 j

private theorem k6t3p2_local_2_paths : ∀ p ∈ k6t3p2_step_2_data.required, p.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_2_data.i k6t3p2_step_2_data.j) 6 := by decide

private theorem k6t3p2_local_2_bad : k6t3p2_step_2_data.bad.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_2_data.i k6t3p2_step_2_data.j) k6t3p2_local_2 6 3 := by decide

private theorem k6t3p2_step_2_check : k6t3p2_step_2.Check k6t3p2.graph k6t3p2_state_2 6 3 := by
  change k6t3p2_step_2_data.Check k6t3p2.graph k6t3p2_state_2 6 3
  refine ⟨k6t3p2_local_2_paths, ?_⟩
  rw [k6t3p2_local_2_eq]
  exact k6t3p2_local_2_bad

private theorem k6t3p2_update_2 : k6t3p2_step_2.apply k6t3p2_state_2 = k6t3p2_state_3 := by
  have h : ∀ i j : Fin 5, k6t3p2_step_2.apply k6t3p2_state_2 i j = k6t3p2_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p2_state_4 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {0, 2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, {0}],
    #[Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, {0}, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p2_local_3 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, {0, 2, 3, 4}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 1 5, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, ∅, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_local_3_eq_row_0 : ∀ j : Fin 5, (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) 0 j = k6t3p2_local_3 0 j := by decide

private theorem k6t3p2_local_3_eq_row_1 : ∀ j : Fin 5, (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) 1 j = k6t3p2_local_3 1 j := by decide

private theorem k6t3p2_local_3_eq_row_2 : ∀ j : Fin 5, (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) 2 j = k6t3p2_local_3 2 j := by decide

private theorem k6t3p2_local_3_eq_row_3 : ∀ j : Fin 5, (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) 3 j = k6t3p2_local_3 3 j := by decide

private theorem k6t3p2_local_3_eq_row_4 : ∀ j : Fin 5, (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) 4 j = k6t3p2_local_3 4 j := by decide

private theorem k6t3p2_local_3_eq : (fun a b => k6t3p2_state_3 a b ∪ requiredMatrix 6 k6t3p2_step_3_data.required a b) = k6t3p2_local_3 := by
  funext i j
  fin_cases i

  · exact k6t3p2_local_3_eq_row_0 j

  · exact k6t3p2_local_3_eq_row_1 j

  · exact k6t3p2_local_3_eq_row_2 j

  · exact k6t3p2_local_3_eq_row_3 j

  · exact k6t3p2_local_3_eq_row_4 j

private theorem k6t3p2_local_3_paths : ∀ p ∈ k6t3p2_step_3_data.required, p.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_3_data.i k6t3p2_step_3_data.j) 6 := by decide

private theorem k6t3p2_local_3_bad : k6t3p2_step_3_data.bad.Check (addedEdgeGraph k6t3p2.graph k6t3p2_step_3_data.i k6t3p2_step_3_data.j) k6t3p2_local_3 6 3 := by decide

private theorem k6t3p2_step_3_check : k6t3p2_step_3.Check k6t3p2.graph k6t3p2_state_3 6 3 := by
  change k6t3p2_step_3_data.Check k6t3p2.graph k6t3p2_state_3 6 3
  refine ⟨k6t3p2_local_3_paths, ?_⟩
  rw [k6t3p2_local_3_eq]
  exact k6t3p2_local_3_bad

private theorem k6t3p2_update_3 : k6t3p2_step_3.apply k6t3p2_state_3 = k6t3p2_state_4 := by
  have h : ∀ i j : Fin 5, k6t3p2_step_3.apply k6t3p2_state_3 i j = k6t3p2_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p2_state_5 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 5}, {0, 2, 3, 4}, ∅],
    #[Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, {0, 1}],
    #[Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[Finset.Icc 1 5, ∅, {0, 1}, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p2_local_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1}, {1}, ∅, {1}, ∅],
    #[{1}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1}, Finset.Icc 1 5, ∅, {1, 2, 3, 5}, Finset.Icc 0 4, ∅],
    #[∅, Finset.Icc 0 4, {1, 2, 3, 5}, ∅, {1, 2, 3}, {0}],
    #[{1}, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3, 5}],
    #[∅, Finset.Icc 1 5, ∅, {0}, {1, 2, 3, 5}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p2_local_4_eq_row_0 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 0 j = k6t3p2_local_4 0 j := by decide

private theorem k6t3p2_local_4_eq_row_1 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 1 j = k6t3p2_local_4 1 j := by decide

private theorem k6t3p2_local_4_eq_row_2 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 2 j = k6t3p2_local_4 2 j := by decide

private theorem k6t3p2_local_4_eq_row_3 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 3 j = k6t3p2_local_4 3 j := by decide

private theorem k6t3p2_local_4_eq_row_4 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 4 j = k6t3p2_local_4 4 j := by decide

private theorem k6t3p2_local_4_eq_row_5 : ∀ j : Fin 6, (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) 5 j = k6t3p2_local_4 5 j := by decide

private theorem k6t3p2_local_4_eq : (fun a b => freshMatrix k6t3p2_state_4 a b ∪ requiredMatrix 6 k6t3p2_step_4_data.required a b) = k6t3p2_local_4 := by
  funext i j
  fin_cases i

  · exact k6t3p2_local_4_eq_row_0 j

  · exact k6t3p2_local_4_eq_row_1 j

  · exact k6t3p2_local_4_eq_row_2 j

  · exact k6t3p2_local_4_eq_row_3 j

  · exact k6t3p2_local_4_eq_row_4 j

  · exact k6t3p2_local_4_eq_row_5 j

private theorem k6t3p2_local_4_paths : ∀ p ∈ k6t3p2_step_4_data.required, p.Check (freshGraph k6t3p2.graph k6t3p2_step_4_data.i k6t3p2_step_4_data.j) 6 := by decide

private theorem k6t3p2_local_4_bad : k6t3p2_step_4_data.bad.Check (freshGraph k6t3p2.graph k6t3p2_step_4_data.i k6t3p2_step_4_data.j) k6t3p2_local_4 6 3 := by decide

private theorem k6t3p2_step_4_check : k6t3p2_step_4.Check k6t3p2.graph k6t3p2_state_4 6 3 := by
  change k6t3p2_step_4_data.Check k6t3p2.graph k6t3p2_state_4 6 3
  refine ⟨by decide, k6t3p2_local_4_paths, ?_⟩
  rw [k6t3p2_local_4_eq]
  exact k6t3p2_local_4_bad

private theorem k6t3p2_update_4 : k6t3p2_step_4.apply k6t3p2_state_4 = k6t3p2_state_5 := by
  have h : ∀ i j : Fin 5, k6t3p2_step_4.apply k6t3p2_state_4 i j = k6t3p2_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k6t3p2_closure_5 : ClosureCheck k6t3p2.graph k6t3p2_state_5 6 3 [] := by trivial

private theorem k6t3p2_closure_4 : ClosureCheck k6t3p2.graph k6t3p2_state_4 6 3 [k6t3p2_step_4] := by
  constructor
  · exact k6t3p2_step_4_check
  · rw [k6t3p2_update_4]
    exact k6t3p2_closure_5

private theorem k6t3p2_closure_3 : ClosureCheck k6t3p2.graph k6t3p2_state_3 6 3 [k6t3p2_step_3, k6t3p2_step_4] := by
  constructor
  · exact k6t3p2_step_3_check
  · rw [k6t3p2_update_3]
    exact k6t3p2_closure_4

private theorem k6t3p2_closure_2 : ClosureCheck k6t3p2.graph k6t3p2_state_2 6 3 [k6t3p2_step_2, k6t3p2_step_3, k6t3p2_step_4] := by
  constructor
  · exact k6t3p2_step_2_check
  · rw [k6t3p2_update_2]
    exact k6t3p2_closure_3

private theorem k6t3p2_closure_1 : ClosureCheck k6t3p2.graph k6t3p2_state_1 6 3 [k6t3p2_step_1, k6t3p2_step_2, k6t3p2_step_3, k6t3p2_step_4] := by
  constructor
  · exact k6t3p2_step_1_check
  · rw [k6t3p2_update_1]
    exact k6t3p2_closure_2

private theorem k6t3p2_closure_0 : ClosureCheck k6t3p2.graph k6t3p2_state_0 6 3 [k6t3p2_step_0, k6t3p2_step_1, k6t3p2_step_2, k6t3p2_step_3, k6t3p2_step_4] := by
  constructor
  · exact k6t3p2_step_0_check
  · rw [k6t3p2_update_0]
    exact k6t3p2_closure_1

private theorem k6t3p2_matrix_eq : k6t3p2.matrix 6 = k6t3p2_state_5 := by
  change closureMatrix (k6t3p2.initialMatrix 6) _ = _
  rw [k6t3p2_initial_eq]
  change closureMatrix k6t3p2_state_0 [k6t3p2_step_0, k6t3p2_step_1, k6t3p2_step_2, k6t3p2_step_3, k6t3p2_step_4] = _
  simp only [closureMatrix]
  rw [k6t3p2_update_0, k6t3p2_update_1, k6t3p2_update_2, k6t3p2_update_3, k6t3p2_update_4]

private theorem k6t3p2_part_0 : k6t3p2.chains.flatten = List.finRange _ := by decide

private theorem k6t3p2_part_1 : k6t3p2.chains.map List.length = ([[], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p2_part_2 : k6t3p2.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p2.clique))) = ([[], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p2_templates_item_0 : (⟨0, 1, [], [], [], 3, 5⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4], 1, 2⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_2 : (⟨0, 2, [], [], [1], 2, 4⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_3 : (⟨0, 2, [], [], [3, 4], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_4 : (⟨0, 3, [], [], [2, 1], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_5 : (⟨0, 3, [], [], [4], 2, 4⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_6 : (⟨0, 4, [], [], [], 3, 5⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_7 : (⟨0, 4, [], [], [3, 2, 1], 1, 2⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_8 : (⟨1, 2, [], [], [3, 4], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_9 : (⟨1, 3, [], [], [4], 2, 4⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_10 : (⟨2, 3, [], [1], [4], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_templates_item_11 : (⟨3, 4, [], [1, 2], [], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p2_part_3 : ∀ T ∈ k6t3p2.templates, T.Check k6t3p2.graph k6t3p2.clique 6 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p2_templates_item_0, k6t3p2_templates_item_1, k6t3p2_templates_item_2, k6t3p2_templates_item_3, k6t3p2_templates_item_4, k6t3p2_templates_item_5, k6t3p2_templates_item_6, k6t3p2_templates_item_7, k6t3p2_templates_item_8, k6t3p2_templates_item_9, k6t3p2_templates_item_10, k6t3p2_templates_item_11⟩

private theorem k6t3p2_required_item_0 : (⟨1, 2, []⟩ : RequiredPathData (Fin 5)).Check k6t3p2.graph 6 := by decide

private theorem k6t3p2_required_item_1 : (⟨3, 4, []⟩ : RequiredPathData (Fin 5)).Check k6t3p2.graph 6 := by decide

private theorem k6t3p2_part_4 : ∀ p ∈ k6t3p2.required, p.Check k6t3p2.graph 6 := by
  simp only [k6t3p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p2_required_item_0, k6t3p2_required_item_1⟩

private theorem k6t3p2_part_5 : ClosureCheck k6t3p2.graph (k6t3p2.initialMatrix 6) 6 3 k6t3p2.closure := by
  rw [k6t3p2_initial_eq]
  exact k6t3p2_closure_0

private theorem k6t3p2_part_6 : k6t3p2.bad.Check k6t3p2.graph (k6t3p2.matrix 6) 6 3 := by
  rw [k6t3p2_matrix_eq]
  decide

theorem k6t3p2_check : k6t3p2.Check 6 3 [[], [2]] :=
  ⟨k6t3p2_part_0, k6t3p2_part_1, k6t3p2_part_2, k6t3p2_part_3, k6t3p2_part_4, k6t3p2_part_5, k6t3p2_part_6⟩
private def k6t3p3_step_0_data : EdgeAttachmentData 6 := ⟨3, 0, [⟨0, 1, [3, 4, 5]⟩, ⟨2, 5, [1, 0, 3, 4]⟩, ⟨2, 4, [1, 5, 0, 3]⟩, ⟨4, 1, [3, 0, 5]⟩, ⟨4, 2, [3, 0, 5, 1]⟩, ⟨4, 1, [5, 0, 3, 2]⟩], ⟨none, {(0, 2), (2, 2), (4, 2), (1, 0)}⟩⟩

private def k6t3p3_step_0 : ClosureStep 6 := .edge k6t3p3_step_0_data

private def k6t3p3_step_1_data : FreshAttachmentData 6 := ⟨3, 0, [⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 0, [2, 1]⟩, ⟨3, 5, [2, 1, 0, 4]⟩, ⟨3, 6, [2, 1, 0, 4, 5]⟩, ⟨3, 0, [2, 6, 1]⟩, ⟨3, 5, [2, 6, 1, 0, 4]⟩, ⟨3, 0, [2, 6, 5, 4]⟩, ⟨3, 1, [2, 6, 5, 4, 0]⟩, ⟨3, 0, [4]⟩, ⟨3, 6, [4, 0, 1, 2]⟩, ⟨5, 0, [4, 3, 2, 1]⟩, ⟨5, 0, [4, 3, 2, 6, 1]⟩, ⟨5, 0, [4]⟩, ⟨5, 3, [4, 0, 1, 2]⟩, ⟨5, 2, [4, 0, 1, 6]⟩, ⟨5, 3, [4, 0, 1, 6, 2]⟩, ⟨5, 0, [6, 1]⟩, ⟨5, 2, [6, 1, 0, 4, 3]⟩, ⟨5, 0, [6, 2, 1]⟩, ⟨5, 1, [6, 2, 3, 4, 0]⟩, ⟨0, 5, [1, 2, 3, 4]⟩, ⟨0, 6, [1, 2, 3, 4, 5]⟩, ⟨0, 4, [1, 2, 6, 5]⟩, ⟨0, 3, [1, 2, 6, 5, 4]⟩, ⟨0, 5, [1, 6, 2, 3, 4]⟩, ⟨0, 3, [1, 6, 5, 4]⟩, ⟨0, 2, [1, 6, 5, 4, 3]⟩, ⟨0, 6, [4, 3, 2, 1]⟩, ⟨0, 1, [4, 3, 2, 6]⟩, ⟨0, 2, [4, 5, 6, 1]⟩], ⟨none, {(3, 2), (5, 2), (0, 2)}⟩⟩

private def k6t3p3_step_1 : ClosureStep 6 := .fresh k6t3p3_step_1_data

private def k6t3p3_step_2_data : FreshAttachmentData 6 := ⟨3, 1, [⟨1, 0, [2, 3, 4]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨1, 0, [6, 5, 4, 3, 2]⟩, ⟨1, 3, [6, 5, 4, 0, 2]⟩, ⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 0, [2, 6, 5, 4]⟩, ⟨3, 1, [2, 0, 4, 5, 6]⟩, ⟨3, 5, [4, 0, 2, 1, 6]⟩, ⟨3, 5, [4, 0, 2, 6]⟩, ⟨5, 0, [4, 3, 2]⟩, ⟨5, 0, [6, 1, 2, 3, 4]⟩, ⟨5, 3, [6, 1, 2, 0, 4]⟩, ⟨5, 0, [6, 2, 3, 4]⟩, ⟨5, 3, [6, 2, 0, 4]⟩], ⟨none, {(3, 1), (5, 2), (1, 2), (0, 0)}⟩⟩

private def k6t3p3_step_2 : ClosureStep 6 := .fresh k6t3p3_step_2_data

private def k6t3p3_step_3_data : FreshAttachmentData 6 := ⟨4, 1, [⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 0, [2, 6, 5]⟩, ⟨1, 0, [2]⟩, ⟨1, 0, [6, 2, 3, 4, 5]⟩, ⟨1, 0, [6, 2]⟩, ⟨1, 4, [6, 2, 0, 5]⟩, ⟨1, 3, [6, 2, 0, 5, 4]⟩, ⟨1, 4, [6, 5, 0, 2, 3]⟩, ⟨3, 0, [2, 1, 6, 5]⟩, ⟨3, 0, [2, 6, 5]⟩, ⟨3, 0, [2]⟩, ⟨3, 0, [4, 5, 6, 1, 2]⟩, ⟨3, 0, [4, 5]⟩, ⟨3, 6, [4, 5, 0, 2, 1]⟩, ⟨3, 6, [4, 5, 0, 2]⟩, ⟨3, 1, [4, 5, 0, 2, 6]⟩, ⟨0, 4, [2, 1, 6, 5]⟩, ⟨0, 3, [2, 1, 6, 5, 4]⟩, ⟨0, 6, [2, 3, 4, 5]⟩, ⟨0, 1, [2, 3, 4, 5, 6]⟩, ⟨0, 3, [2, 6, 5, 4]⟩, ⟨0, 1, [5, 4, 3, 2]⟩, ⟨0, 6, [5, 4, 3, 2, 1]⟩, ⟨0, 4, [5, 6, 1, 2, 3]⟩], ⟨none, {(3, 2), (1, 2), (0, 2)}⟩⟩

private def k6t3p3_step_3 : ClosureStep 6 := .fresh k6t3p3_step_3_data

private def k6t3p3_step_4_data : FreshAttachmentData 6 := ⟨5, 2, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 0, [2, 3]⟩, ⟨1, 4, [2, 3, 0, 6, 5]⟩, ⟨1, 4, [2, 6, 0, 3]⟩, ⟨1, 5, [2, 6, 0, 3, 4]⟩, ⟨1, 0, [6, 2, 3]⟩, ⟨1, 0, [6, 5, 4, 3]⟩, ⟨1, 0, [6]⟩, ⟨5, 0, [4, 3, 2, 1, 6]⟩, ⟨5, 0, [4, 3, 2, 6]⟩, ⟨5, 0, [4, 3]⟩, ⟨5, 2, [4, 3, 0, 6, 1]⟩, ⟨5, 2, [4, 3, 0, 6]⟩, ⟨5, 1, [4, 3, 0, 6, 2]⟩, ⟨5, 0, [6, 2, 3]⟩, ⟨5, 0, [6]⟩, ⟨0, 5, [3, 2, 1, 6]⟩, ⟨0, 4, [3, 2, 1, 6, 5]⟩, ⟨0, 4, [3, 2, 6, 5]⟩, ⟨0, 1, [3, 4, 5, 6]⟩, ⟨0, 2, [3, 4, 5, 6, 1]⟩, ⟨0, 2, [3, 4, 5, 6]⟩, ⟨0, 1, [3, 4, 5, 6, 2]⟩, ⟨0, 5, [6, 1, 2, 3, 4]⟩], ⟨none, {(5, 2), (1, 2), (0, 2)}⟩⟩

private def k6t3p3_step_4 : ClosureStep 6 := .fresh k6t3p3_step_4_data

private def k6t3p3_step_5_data : FreshAttachmentData 6 := ⟨5, 3, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 0, [2, 3, 4]⟩, ⟨1, 5, [2, 3, 4, 0, 6]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 0, [2, 1, 6]⟩, ⟨3, 5, [2, 1, 6, 0, 4]⟩, ⟨3, 0, [2, 6, 5, 4]⟩, ⟨3, 5, [2, 6, 0, 4]⟩, ⟨5, 0, [4, 3, 2, 1, 6]⟩, ⟨5, 0, [4, 3, 2, 6]⟩, ⟨5, 3, [4, 0, 6, 1, 2]⟩, ⟨5, 1, [6, 0, 4, 3, 2]⟩], ⟨none, {(3, 2), (5, 1), (1, 2), (0, 0)}⟩⟩

private def k6t3p3_step_5 : ClosureStep 6 := .fresh k6t3p3_step_5_data

private def k6t3p3_step_6_data : EdgeAttachmentData 6 := ⟨2, 0, [⟨0, 5, [2, 1]⟩, ⟨0, 3, [2]⟩, ⟨0, 5, [2, 3, 4]⟩, ⟨5, 1, [4, 3, 2, 0]⟩], ⟨none, {(0, 2), (5, 2), (3, 2), (4, 0)}⟩⟩

private def k6t3p3_step_6 : ClosureStep 6 := .edge k6t3p3_step_6_data

private def k6t3p3_step_7_data : EdgeAttachmentData 6 := ⟨3, 1, [⟨2, 4, [3, 1, 0, 5]⟩, ⟨4, 2, [5, 0, 1, 3]⟩], ⟨none, {(0, 2), (2, 2), (3, 0), (4, 2)}⟩⟩

private def k6t3p3_step_7 : ClosureStep 6 := .edge k6t3p3_step_7_data

private def k6t3p3_step_8_data : EdgeAttachmentData 6 := ⟨4, 0, [⟨0, 3, [4]⟩, ⟨0, 1, [4, 3, 2]⟩, ⟨0, 1, [4, 5]⟩, ⟨1, 5, [2, 3, 4, 0]⟩], ⟨none, {(0, 2), (1, 2), (3, 2), (2, 0)}⟩⟩

private def k6t3p3_step_8 : ClosureStep 6 := .edge k6t3p3_step_8_data

private def k6t3p3_step_9_data : EdgeAttachmentData 6 := ⟨5, 3, [⟨2, 4, [1, 0, 5, 3]⟩, ⟨4, 2, [3, 5, 0, 1]⟩], ⟨none, {(0, 2), (3, 0), (4, 2), (2, 2)}⟩⟩

private def k6t3p3_step_9 : ClosureStep 6 := .edge k6t3p3_step_9_data

private def k6t3p3_step_10_data : EdgeAttachmentData 6 := ⟨4, 2, [⟨0, 1, [5, 4, 2]⟩], ⟨none, {(0, 1), (3, 2), (2, 0), (1, 1)}⟩⟩

private def k6t3p3_step_10 : ClosureStep 6 := .edge k6t3p3_step_10_data

def k6t3p3 : LayoutCertificate 6 where
  chains := [[0], [1, 2, 3, 4, 5]]
  clique := {0, 1, 5}
  templates := [⟨0, 1, [], [], [], 4, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩,
    ⟨0, 2, [], [], [1], 3, 4⟩,
    ⟨0, 2, [], [], [3, 4, 5], 1, 2⟩,
    ⟨0, 3, [], [], [2, 1], 2, 3⟩,
    ⟨0, 4, [], [], [3, 2, 1], 1, 2⟩,
    ⟨0, 4, [], [], [5], 3, 4⟩,
    ⟨0, 5, [], [], [], 4, 5⟩,
    ⟨0, 5, [], [], [4, 3, 2, 1], 1, 1⟩,
    ⟨1, 2, [], [], [3, 4, 5], 1, 2⟩,
    ⟨1, 3, [], [], [4, 5], 2, 3⟩,
    ⟨2, 3, [], [1], [4, 5], 1, 2⟩,
    ⟨2, 4, [], [1], [5], 2, 3⟩,
    ⟨3, 4, [], [1, 2], [5], 1, 2⟩,
    ⟨3, 5, [], [1, 2], [], 2, 3⟩,
    ⟨4, 5, [], [1, 2, 3], [], 1, 2⟩]
  required := [⟨1, 3, [2]⟩,
    ⟨2, 4, [3]⟩,
    ⟨3, 5, [4]⟩]
  closure := [k6t3p3_step_0, k6t3p3_step_1, k6t3p3_step_2, k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10]
  bad := ⟨none, {(3, 2), (0, 1), (2, 0), (4, 0)}⟩


private def k6t3p3_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, {2, 3}, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[{2, 3}, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, ∅, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_initial_eq_row_0 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 0 j = k6t3p3_state_0 0 j := by decide

private theorem k6t3p3_initial_eq_row_1 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 1 j = k6t3p3_state_0 1 j := by decide

private theorem k6t3p3_initial_eq_row_2 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 2 j = k6t3p3_state_0 2 j := by decide

private theorem k6t3p3_initial_eq_row_3 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 3 j = k6t3p3_state_0 3 j := by decide

private theorem k6t3p3_initial_eq_row_4 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 4 j = k6t3p3_state_0 4 j := by decide

private theorem k6t3p3_initial_eq_row_5 : ∀ j : Fin 6, (k6t3p3.initialMatrix 6) 5 j = k6t3p3_state_0 5 j := by decide

private theorem k6t3p3_initial_eq : (k6t3p3.initialMatrix 6) = k6t3p3_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p3_initial_eq_row_0 j

  · exact k6t3p3_initial_eq_row_1 j

  · exact k6t3p3_initial_eq_row_2 j

  · exact k6t3p3_initial_eq_row_3 j

  · exact k6t3p3_initial_eq_row_4 j

  · exact k6t3p3_initial_eq_row_5 j

private def k6t3p3_state_1 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, {0, 2, 3}, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[{0, 2, 3}, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, ∅, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5}, Finset.Icc 1 4, {2, 3}, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 2, 4, 5}, ∅, {1, 2}, {2, 3, 4}, {1, 2}, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4, {1}],
    #[{2, 3}, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, {1, 2}, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_0_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 0 j = k6t3p3_local_0 0 j := by decide

private theorem k6t3p3_local_0_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 1 j = k6t3p3_local_0 1 j := by decide

private theorem k6t3p3_local_0_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 2 j = k6t3p3_local_0 2 j := by decide

private theorem k6t3p3_local_0_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 3 j = k6t3p3_local_0 3 j := by decide

private theorem k6t3p3_local_0_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 4 j = k6t3p3_local_0 4 j := by decide

private theorem k6t3p3_local_0_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) 5 j = k6t3p3_local_0 5 j := by decide

private theorem k6t3p3_local_0_eq : (fun a b => k6t3p3_state_0 a b ∪ requiredMatrix 6 k6t3p3_step_0_data.required a b) = k6t3p3_local_0 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_0_eq_row_0 j

  · exact k6t3p3_local_0_eq_row_1 j

  · exact k6t3p3_local_0_eq_row_2 j

  · exact k6t3p3_local_0_eq_row_3 j

  · exact k6t3p3_local_0_eq_row_4 j

  · exact k6t3p3_local_0_eq_row_5 j

private theorem k6t3p3_local_0_paths : ∀ p ∈ k6t3p3_step_0_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_0_data.i k6t3p3_step_0_data.j) 6 := by decide

private theorem k6t3p3_local_0_bad : k6t3p3_step_0_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_0_data.i k6t3p3_step_0_data.j) k6t3p3_local_0 6 3 := by decide

private theorem k6t3p3_step_0_check : k6t3p3_step_0.Check k6t3p3.graph k6t3p3_state_0 6 3 := by
  change k6t3p3_step_0_data.Check k6t3p3.graph k6t3p3_state_0 6 3
  refine ⟨k6t3p3_local_0_paths, ?_⟩
  rw [k6t3p3_local_0_eq]
  exact k6t3p3_local_0_bad

private theorem k6t3p3_update_0 : k6t3p3_step_0.apply k6t3p3_state_0 = k6t3p3_state_1 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_0.apply k6t3p3_state_0 i j = k6t3p3_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_2 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 3, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, ∅, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {0, 1}, Finset.Icc 0 4, {1}, Finset.Icc 0 4, {0, 1}],
    #[{1}, ∅, {1, 4, 5}, Finset.Icc 0 4, {0, 2, 3}, Finset.Icc 0 4, {1, 4, 5}],
    #[{0, 1}, {1, 4, 5}, ∅, {1, 2}, {2, 3, 4}, {0, 1}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4, {0, 1}],
    #[{1}, {0, 2, 3}, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {0, 1}, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}],
    #[{0, 1}, {1, 4, 5}, ∅, {0, 1}, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_1_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 0 j = k6t3p3_local_1 0 j := by decide

private theorem k6t3p3_local_1_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 1 j = k6t3p3_local_1 1 j := by decide

private theorem k6t3p3_local_1_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 2 j = k6t3p3_local_1 2 j := by decide

private theorem k6t3p3_local_1_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 3 j = k6t3p3_local_1 3 j := by decide

private theorem k6t3p3_local_1_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 4 j = k6t3p3_local_1 4 j := by decide

private theorem k6t3p3_local_1_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 5 j = k6t3p3_local_1 5 j := by decide

private theorem k6t3p3_local_1_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) 6 j = k6t3p3_local_1 6 j := by decide

private theorem k6t3p3_local_1_eq : (fun a b => freshMatrix k6t3p3_state_1 a b ∪ requiredMatrix 6 k6t3p3_step_1_data.required a b) = k6t3p3_local_1 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_1_eq_row_0 j

  · exact k6t3p3_local_1_eq_row_1 j

  · exact k6t3p3_local_1_eq_row_2 j

  · exact k6t3p3_local_1_eq_row_3 j

  · exact k6t3p3_local_1_eq_row_4 j

  · exact k6t3p3_local_1_eq_row_5 j

  · exact k6t3p3_local_1_eq_row_6 j

private theorem k6t3p3_local_1_paths : ∀ p ∈ k6t3p3_step_1_data.required, p.Check (freshGraph k6t3p3.graph k6t3p3_step_1_data.i k6t3p3_step_1_data.j) 6 := by decide

private theorem k6t3p3_local_1_bad : k6t3p3_step_1_data.bad.Check (freshGraph k6t3p3.graph k6t3p3_step_1_data.i k6t3p3_step_1_data.j) k6t3p3_local_1 6 3 := by decide

private theorem k6t3p3_step_1_check : k6t3p3_step_1.Check k6t3p3.graph k6t3p3_state_1 6 3 := by
  change k6t3p3_step_1_data.Check k6t3p3.graph k6t3p3_state_1 6 3
  refine ⟨by decide, k6t3p3_local_1_paths, ?_⟩
  rw [k6t3p3_local_1_eq]
  exact k6t3p3_local_1_bad

private theorem k6t3p3_update_1 : k6t3p3_step_1.apply k6t3p3_state_1 = k6t3p3_state_2 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_1.apply k6t3p3_state_1 i j = k6t3p3_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_3 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, ∅, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {0, 1, 2}, ∅, {0, 1}, ∅, {0, 1, 2}, ∅],
    #[{0, 1, 2}, ∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[∅, {1, 4, 5}, ∅, {1, 2}, {2, 3, 4}, ∅, ∅],
    #[{0, 1}, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4, ∅],
    #[∅, Finset.Icc 0 3, {2, 3, 4}, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[{0, 1, 2}, Finset.Icc 1 4, ∅, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}],
    #[∅, {1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_2_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 0 j = k6t3p3_local_2 0 j := by decide

private theorem k6t3p3_local_2_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 1 j = k6t3p3_local_2 1 j := by decide

private theorem k6t3p3_local_2_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 2 j = k6t3p3_local_2 2 j := by decide

private theorem k6t3p3_local_2_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 3 j = k6t3p3_local_2 3 j := by decide

private theorem k6t3p3_local_2_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 4 j = k6t3p3_local_2 4 j := by decide

private theorem k6t3p3_local_2_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 5 j = k6t3p3_local_2 5 j := by decide

private theorem k6t3p3_local_2_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) 6 j = k6t3p3_local_2 6 j := by decide

private theorem k6t3p3_local_2_eq : (fun a b => freshMatrix k6t3p3_state_2 a b ∪ requiredMatrix 6 k6t3p3_step_2_data.required a b) = k6t3p3_local_2 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_2_eq_row_0 j

  · exact k6t3p3_local_2_eq_row_1 j

  · exact k6t3p3_local_2_eq_row_2 j

  · exact k6t3p3_local_2_eq_row_3 j

  · exact k6t3p3_local_2_eq_row_4 j

  · exact k6t3p3_local_2_eq_row_5 j

  · exact k6t3p3_local_2_eq_row_6 j

private theorem k6t3p3_local_2_paths : ∀ p ∈ k6t3p3_step_2_data.required, p.Check (freshGraph k6t3p3.graph k6t3p3_step_2_data.i k6t3p3_step_2_data.j) 6 := by decide

private theorem k6t3p3_local_2_bad : k6t3p3_step_2_data.bad.Check (freshGraph k6t3p3.graph k6t3p3_step_2_data.i k6t3p3_step_2_data.j) k6t3p3_local_2 6 3 := by decide

private theorem k6t3p3_step_2_check : k6t3p3_step_2.Check k6t3p3.graph k6t3p3_state_2 6 3 := by
  change k6t3p3_step_2_data.Check k6t3p3.graph k6t3p3_state_2 6 3
  refine ⟨by decide, k6t3p3_local_2_paths, ?_⟩
  rw [k6t3p3_local_2_eq]
  exact k6t3p3_local_2_bad

private theorem k6t3p3_update_2 : k6t3p3_step_2.apply k6t3p3_state_2 = k6t3p3_state_3 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_2.apply k6t3p3_state_2 i j = k6t3p3_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 0 4, ∅, Finset.Icc 0 4, {0, 1}, ∅, {0, 1}],
    #[Finset.Icc 0 4, ∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[∅, {1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {0, 1}],
    #[{0, 1}, Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[∅, Finset.Icc 1 4, ∅, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{0, 1}, {1, 4, 5}, ∅, {0, 1}, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_3_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 0 j = k6t3p3_local_3 0 j := by decide

private theorem k6t3p3_local_3_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 1 j = k6t3p3_local_3 1 j := by decide

private theorem k6t3p3_local_3_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 2 j = k6t3p3_local_3 2 j := by decide

private theorem k6t3p3_local_3_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 3 j = k6t3p3_local_3 3 j := by decide

private theorem k6t3p3_local_3_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 4 j = k6t3p3_local_3 4 j := by decide

private theorem k6t3p3_local_3_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 5 j = k6t3p3_local_3 5 j := by decide

private theorem k6t3p3_local_3_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) 6 j = k6t3p3_local_3 6 j := by decide

private theorem k6t3p3_local_3_eq : (fun a b => freshMatrix k6t3p3_state_3 a b ∪ requiredMatrix 6 k6t3p3_step_3_data.required a b) = k6t3p3_local_3 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_3_eq_row_0 j

  · exact k6t3p3_local_3_eq_row_1 j

  · exact k6t3p3_local_3_eq_row_2 j

  · exact k6t3p3_local_3_eq_row_3 j

  · exact k6t3p3_local_3_eq_row_4 j

  · exact k6t3p3_local_3_eq_row_5 j

  · exact k6t3p3_local_3_eq_row_6 j

private theorem k6t3p3_local_3_paths : ∀ p ∈ k6t3p3_step_3_data.required, p.Check (freshGraph k6t3p3.graph k6t3p3_step_3_data.i k6t3p3_step_3_data.j) 6 := by decide

private theorem k6t3p3_local_3_bad : k6t3p3_step_3_data.bad.Check (freshGraph k6t3p3.graph k6t3p3_step_3_data.i k6t3p3_step_3_data.j) k6t3p3_local_3 6 3 := by decide

private theorem k6t3p3_step_3_check : k6t3p3_step_3.Check k6t3p3.graph k6t3p3_state_3 6 3 := by
  change k6t3p3_step_3_data.Check k6t3p3.graph k6t3p3_state_3 6 3
  refine ⟨by decide, k6t3p3_local_3_paths, ?_⟩
  rw [k6t3p3_local_3_eq]
  exact k6t3p3_local_3_bad

private theorem k6t3p3_update_3 : k6t3p3_step_3.apply k6t3p3_state_3 = k6t3p3_state_4 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_3.apply k6t3p3_state_3 i j = k6t3p3_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_5 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 0 4, {0, 1}, ∅, {0, 1}, Finset.Icc 0 4, ∅],
    #[Finset.Icc 0 4, ∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{0, 1}, {1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {0, 1}, ∅],
    #[∅, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, ∅],
    #[{0, 1}, Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {0, 1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[∅, {1, 4, 5}, ∅, ∅, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_4_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 0 j = k6t3p3_local_4 0 j := by decide

private theorem k6t3p3_local_4_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 1 j = k6t3p3_local_4 1 j := by decide

private theorem k6t3p3_local_4_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 2 j = k6t3p3_local_4 2 j := by decide

private theorem k6t3p3_local_4_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 3 j = k6t3p3_local_4 3 j := by decide

private theorem k6t3p3_local_4_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 4 j = k6t3p3_local_4 4 j := by decide

private theorem k6t3p3_local_4_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 5 j = k6t3p3_local_4 5 j := by decide

private theorem k6t3p3_local_4_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) 6 j = k6t3p3_local_4 6 j := by decide

private theorem k6t3p3_local_4_eq : (fun a b => freshMatrix k6t3p3_state_4 a b ∪ requiredMatrix 6 k6t3p3_step_4_data.required a b) = k6t3p3_local_4 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_4_eq_row_0 j

  · exact k6t3p3_local_4_eq_row_1 j

  · exact k6t3p3_local_4_eq_row_2 j

  · exact k6t3p3_local_4_eq_row_3 j

  · exact k6t3p3_local_4_eq_row_4 j

  · exact k6t3p3_local_4_eq_row_5 j

  · exact k6t3p3_local_4_eq_row_6 j

private theorem k6t3p3_local_4_paths : ∀ p ∈ k6t3p3_step_4_data.required, p.Check (freshGraph k6t3p3.graph k6t3p3_step_4_data.i k6t3p3_step_4_data.j) 6 := by decide

private theorem k6t3p3_local_4_bad : k6t3p3_step_4_data.bad.Check (freshGraph k6t3p3.graph k6t3p3_step_4_data.i k6t3p3_step_4_data.j) k6t3p3_local_4 6 3 := by decide

private theorem k6t3p3_step_4_check : k6t3p3_step_4.Check k6t3p3.graph k6t3p3_state_4 6 3 := by
  change k6t3p3_step_4_data.Check k6t3p3.graph k6t3p3_state_4 6 3
  refine ⟨by decide, k6t3p3_local_4_paths, ?_⟩
  rw [k6t3p3_local_4_eq]
  exact k6t3p3_local_4_bad

private theorem k6t3p3_update_4 : k6t3p3_step_4.apply k6t3p3_state_4 = k6t3p3_state_5 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_4.apply k6t3p3_state_4 i j = k6t3p3_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_6 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {0, 1, 2}, ∅, {0, 1, 2}, ∅, {0, 1}, ∅],
    #[{0, 1, 2}, ∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[∅, {1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[{0, 1, 2}, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4, {1}],
    #[∅, Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}],
    #[{0, 1}, Finset.Icc 0 4, {1}, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}],
    #[∅, {1, 4, 5}, ∅, {1}, {2, 3, 4}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_5_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 0 j = k6t3p3_local_5 0 j := by decide

private theorem k6t3p3_local_5_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 1 j = k6t3p3_local_5 1 j := by decide

private theorem k6t3p3_local_5_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 2 j = k6t3p3_local_5 2 j := by decide

private theorem k6t3p3_local_5_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 3 j = k6t3p3_local_5 3 j := by decide

private theorem k6t3p3_local_5_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 4 j = k6t3p3_local_5 4 j := by decide

private theorem k6t3p3_local_5_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 5 j = k6t3p3_local_5 5 j := by decide

private theorem k6t3p3_local_5_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) 6 j = k6t3p3_local_5 6 j := by decide

private theorem k6t3p3_local_5_eq : (fun a b => freshMatrix k6t3p3_state_5 a b ∪ requiredMatrix 6 k6t3p3_step_5_data.required a b) = k6t3p3_local_5 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_5_eq_row_0 j

  · exact k6t3p3_local_5_eq_row_1 j

  · exact k6t3p3_local_5_eq_row_2 j

  · exact k6t3p3_local_5_eq_row_3 j

  · exact k6t3p3_local_5_eq_row_4 j

  · exact k6t3p3_local_5_eq_row_5 j

  · exact k6t3p3_local_5_eq_row_6 j

private theorem k6t3p3_local_5_paths : ∀ p ∈ k6t3p3_step_5_data.required, p.Check (freshGraph k6t3p3.graph k6t3p3_step_5_data.i k6t3p3_step_5_data.j) 6 := by decide

private theorem k6t3p3_local_5_bad : k6t3p3_step_5_data.bad.Check (freshGraph k6t3p3.graph k6t3p3_step_5_data.i k6t3p3_step_5_data.j) k6t3p3_local_5 6 3 := by decide

private theorem k6t3p3_step_5_check : k6t3p3_step_5.Check k6t3p3.graph k6t3p3_state_5 6 3 := by
  change k6t3p3_step_5_data.Check k6t3p3.graph k6t3p3_state_5 6 3
  refine ⟨by decide, k6t3p3_local_5_paths, ?_⟩
  rw [k6t3p3_local_5_eq]
  exact k6t3p3_local_5_bad

private theorem k6t3p3_update_5 : k6t3p3_step_5.apply k6t3p3_state_5 = k6t3p3_state_6 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_5.apply k6t3p3_state_5 i j = k6t3p3_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_6 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, {1}],
    #[Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[Finset.Icc 1 5, {1}, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_6_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 0 j = k6t3p3_local_6 0 j := by decide

private theorem k6t3p3_local_6_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 1 j = k6t3p3_local_6 1 j := by decide

private theorem k6t3p3_local_6_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 2 j = k6t3p3_local_6 2 j := by decide

private theorem k6t3p3_local_6_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 3 j = k6t3p3_local_6 3 j := by decide

private theorem k6t3p3_local_6_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 4 j = k6t3p3_local_6 4 j := by decide

private theorem k6t3p3_local_6_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) 5 j = k6t3p3_local_6 5 j := by decide

private theorem k6t3p3_local_6_eq : (fun a b => k6t3p3_state_6 a b ∪ requiredMatrix 6 k6t3p3_step_6_data.required a b) = k6t3p3_local_6 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_6_eq_row_0 j

  · exact k6t3p3_local_6_eq_row_1 j

  · exact k6t3p3_local_6_eq_row_2 j

  · exact k6t3p3_local_6_eq_row_3 j

  · exact k6t3p3_local_6_eq_row_4 j

  · exact k6t3p3_local_6_eq_row_5 j

private theorem k6t3p3_local_6_paths : ∀ p ∈ k6t3p3_step_6_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_6_data.i k6t3p3_step_6_data.j) 6 := by decide

private theorem k6t3p3_local_6_bad : k6t3p3_step_6_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_6_data.i k6t3p3_step_6_data.j) k6t3p3_local_6 6 3 := by decide

private theorem k6t3p3_step_6_check : k6t3p3_step_6.Check k6t3p3.graph k6t3p3_state_6 6 3 := by
  change k6t3p3_step_6_data.Check k6t3p3.graph k6t3p3_state_6 6 3
  refine ⟨k6t3p3_local_6_paths, ?_⟩
  rw [k6t3p3_local_6_eq]
  exact k6t3p3_local_6_bad

private theorem k6t3p3_update_6 : k6t3p3_step_6.apply k6t3p3_state_6 = k6t3p3_state_7 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_6.apply k6t3p3_state_6 i j = k6t3p3_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_8 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 1 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 1 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4, {1}],
    #[Finset.Icc 0 3, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_7_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 0 j = k6t3p3_local_7 0 j := by decide

private theorem k6t3p3_local_7_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 1 j = k6t3p3_local_7 1 j := by decide

private theorem k6t3p3_local_7_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 2 j = k6t3p3_local_7 2 j := by decide

private theorem k6t3p3_local_7_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 3 j = k6t3p3_local_7 3 j := by decide

private theorem k6t3p3_local_7_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 4 j = k6t3p3_local_7 4 j := by decide

private theorem k6t3p3_local_7_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) 5 j = k6t3p3_local_7 5 j := by decide

private theorem k6t3p3_local_7_eq : (fun a b => k6t3p3_state_7 a b ∪ requiredMatrix 6 k6t3p3_step_7_data.required a b) = k6t3p3_local_7 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_7_eq_row_0 j

  · exact k6t3p3_local_7_eq_row_1 j

  · exact k6t3p3_local_7_eq_row_2 j

  · exact k6t3p3_local_7_eq_row_3 j

  · exact k6t3p3_local_7_eq_row_4 j

  · exact k6t3p3_local_7_eq_row_5 j

private theorem k6t3p3_local_7_paths : ∀ p ∈ k6t3p3_step_7_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_7_data.i k6t3p3_step_7_data.j) 6 := by decide

private theorem k6t3p3_local_7_bad : k6t3p3_step_7_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_7_data.i k6t3p3_step_7_data.j) k6t3p3_local_7 6 3 := by decide

private theorem k6t3p3_step_7_check : k6t3p3_step_7.Check k6t3p3.graph k6t3p3_state_7 6 3 := by
  change k6t3p3_step_7_data.Check k6t3p3.graph k6t3p3_state_7 6 3
  refine ⟨k6t3p3_local_7_paths, ?_⟩
  rw [k6t3p3_local_7_eq]
  exact k6t3p3_local_7_bad

private theorem k6t3p3_update_7 : k6t3p3_step_7.apply k6t3p3_state_7 = k6t3p3_state_8 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_7.apply k6t3p3_state_7 i j = k6t3p3_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_9 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 0 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_8 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 4, {1, 4, 5}],
    #[Finset.Icc 1 5, ∅, {1, 2}, Finset.Icc 0 4, {1}, {1}],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, {1}, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_8_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 0 j = k6t3p3_local_8 0 j := by decide

private theorem k6t3p3_local_8_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 1 j = k6t3p3_local_8 1 j := by decide

private theorem k6t3p3_local_8_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 2 j = k6t3p3_local_8 2 j := by decide

private theorem k6t3p3_local_8_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 3 j = k6t3p3_local_8 3 j := by decide

private theorem k6t3p3_local_8_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 4 j = k6t3p3_local_8 4 j := by decide

private theorem k6t3p3_local_8_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) 5 j = k6t3p3_local_8 5 j := by decide

private theorem k6t3p3_local_8_eq : (fun a b => k6t3p3_state_8 a b ∪ requiredMatrix 6 k6t3p3_step_8_data.required a b) = k6t3p3_local_8 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_8_eq_row_0 j

  · exact k6t3p3_local_8_eq_row_1 j

  · exact k6t3p3_local_8_eq_row_2 j

  · exact k6t3p3_local_8_eq_row_3 j

  · exact k6t3p3_local_8_eq_row_4 j

  · exact k6t3p3_local_8_eq_row_5 j

private theorem k6t3p3_local_8_paths : ∀ p ∈ k6t3p3_step_8_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_8_data.i k6t3p3_step_8_data.j) 6 := by decide

private theorem k6t3p3_local_8_bad : k6t3p3_step_8_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_8_data.i k6t3p3_step_8_data.j) k6t3p3_local_8 6 3 := by decide

private theorem k6t3p3_step_8_check : k6t3p3_step_8.Check k6t3p3.graph k6t3p3_state_8 6 3 := by
  change k6t3p3_step_8_data.Check k6t3p3.graph k6t3p3_state_8 6 3
  refine ⟨k6t3p3_local_8_paths, ?_⟩
  rw [k6t3p3_local_8_eq]
  exact k6t3p3_local_8_bad

private theorem k6t3p3_update_8 : k6t3p3_step_8.apply k6t3p3_state_8 = k6t3p3_state_9 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_8.apply k6t3p3_state_8 i j = k6t3p3_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_10 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4],
    #[Finset.Icc 0 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 0 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_9 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 1 4],
    #[Finset.Icc 0 4, {1}, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 1 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_9_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 0 j = k6t3p3_local_9 0 j := by decide

private theorem k6t3p3_local_9_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 1 j = k6t3p3_local_9 1 j := by decide

private theorem k6t3p3_local_9_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 2 j = k6t3p3_local_9 2 j := by decide

private theorem k6t3p3_local_9_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 3 j = k6t3p3_local_9 3 j := by decide

private theorem k6t3p3_local_9_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 4 j = k6t3p3_local_9 4 j := by decide

private theorem k6t3p3_local_9_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) 5 j = k6t3p3_local_9 5 j := by decide

private theorem k6t3p3_local_9_eq : (fun a b => k6t3p3_state_9 a b ∪ requiredMatrix 6 k6t3p3_step_9_data.required a b) = k6t3p3_local_9 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_9_eq_row_0 j

  · exact k6t3p3_local_9_eq_row_1 j

  · exact k6t3p3_local_9_eq_row_2 j

  · exact k6t3p3_local_9_eq_row_3 j

  · exact k6t3p3_local_9_eq_row_4 j

  · exact k6t3p3_local_9_eq_row_5 j

private theorem k6t3p3_local_9_paths : ∀ p ∈ k6t3p3_step_9_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_9_data.i k6t3p3_step_9_data.j) 6 := by decide

private theorem k6t3p3_local_9_bad : k6t3p3_step_9_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_9_data.i k6t3p3_step_9_data.j) k6t3p3_local_9 6 3 := by decide

private theorem k6t3p3_step_9_check : k6t3p3_step_9.Check k6t3p3.graph k6t3p3_state_9 6 3 := by
  change k6t3p3_step_9_data.Check k6t3p3.graph k6t3p3_state_9 6 3
  refine ⟨k6t3p3_local_9_paths, ?_⟩
  rw [k6t3p3_local_9_eq]
  exact k6t3p3_local_9_bad

private theorem k6t3p3_update_9 : k6t3p3_step_9.apply k6t3p3_state_9 = k6t3p3_state_10 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_9.apply k6t3p3_state_9 i j = k6t3p3_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t3p3_state_11 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{1, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {0, 2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4],
    #[Finset.Icc 0 4, {1}, {0, 2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 0 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t3p3_local_10 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 3, Finset.Icc 0 4, {1, 4, 5}],
    #[{1, 2, 4, 5}, ∅, {1, 2}, Finset.Icc 0 4, {1}, ∅],
    #[Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, {1, 2}, ∅, {1, 2}, Finset.Icc 0 4],
    #[Finset.Icc 0 4, {1}, {2, 3, 4}, {1, 2}, ∅, {1, 2}],
    #[{1, 4, 5}, ∅, {1}, Finset.Icc 0 4, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p3_local_10_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 0 j = k6t3p3_local_10 0 j := by decide

private theorem k6t3p3_local_10_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 1 j = k6t3p3_local_10 1 j := by decide

private theorem k6t3p3_local_10_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 2 j = k6t3p3_local_10 2 j := by decide

private theorem k6t3p3_local_10_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 3 j = k6t3p3_local_10 3 j := by decide

private theorem k6t3p3_local_10_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 4 j = k6t3p3_local_10 4 j := by decide

private theorem k6t3p3_local_10_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) 5 j = k6t3p3_local_10 5 j := by decide

private theorem k6t3p3_local_10_eq : (fun a b => k6t3p3_state_10 a b ∪ requiredMatrix 6 k6t3p3_step_10_data.required a b) = k6t3p3_local_10 := by
  funext i j
  fin_cases i

  · exact k6t3p3_local_10_eq_row_0 j

  · exact k6t3p3_local_10_eq_row_1 j

  · exact k6t3p3_local_10_eq_row_2 j

  · exact k6t3p3_local_10_eq_row_3 j

  · exact k6t3p3_local_10_eq_row_4 j

  · exact k6t3p3_local_10_eq_row_5 j

private theorem k6t3p3_local_10_paths : ∀ p ∈ k6t3p3_step_10_data.required, p.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_10_data.i k6t3p3_step_10_data.j) 6 := by decide

private theorem k6t3p3_local_10_bad : k6t3p3_step_10_data.bad.Check (addedEdgeGraph k6t3p3.graph k6t3p3_step_10_data.i k6t3p3_step_10_data.j) k6t3p3_local_10 6 3 := by decide

private theorem k6t3p3_step_10_check : k6t3p3_step_10.Check k6t3p3.graph k6t3p3_state_10 6 3 := by
  change k6t3p3_step_10_data.Check k6t3p3.graph k6t3p3_state_10 6 3
  refine ⟨k6t3p3_local_10_paths, ?_⟩
  rw [k6t3p3_local_10_eq]
  exact k6t3p3_local_10_bad

private theorem k6t3p3_update_10 : k6t3p3_step_10.apply k6t3p3_state_10 = k6t3p3_state_11 := by
  have h : ∀ i j : Fin 6, k6t3p3_step_10.apply k6t3p3_state_10 i j = k6t3p3_state_11 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k6t3p3_closure_11 : ClosureCheck k6t3p3.graph k6t3p3_state_11 6 3 [] := by trivial

private theorem k6t3p3_closure_10 : ClosureCheck k6t3p3.graph k6t3p3_state_10 6 3 [k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_10_check
  · rw [k6t3p3_update_10]
    exact k6t3p3_closure_11

private theorem k6t3p3_closure_9 : ClosureCheck k6t3p3.graph k6t3p3_state_9 6 3 [k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_9_check
  · rw [k6t3p3_update_9]
    exact k6t3p3_closure_10

private theorem k6t3p3_closure_8 : ClosureCheck k6t3p3.graph k6t3p3_state_8 6 3 [k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_8_check
  · rw [k6t3p3_update_8]
    exact k6t3p3_closure_9

private theorem k6t3p3_closure_7 : ClosureCheck k6t3p3.graph k6t3p3_state_7 6 3 [k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_7_check
  · rw [k6t3p3_update_7]
    exact k6t3p3_closure_8

private theorem k6t3p3_closure_6 : ClosureCheck k6t3p3.graph k6t3p3_state_6 6 3 [k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_6_check
  · rw [k6t3p3_update_6]
    exact k6t3p3_closure_7

private theorem k6t3p3_closure_5 : ClosureCheck k6t3p3.graph k6t3p3_state_5 6 3 [k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_5_check
  · rw [k6t3p3_update_5]
    exact k6t3p3_closure_6

private theorem k6t3p3_closure_4 : ClosureCheck k6t3p3.graph k6t3p3_state_4 6 3 [k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_4_check
  · rw [k6t3p3_update_4]
    exact k6t3p3_closure_5

private theorem k6t3p3_closure_3 : ClosureCheck k6t3p3.graph k6t3p3_state_3 6 3 [k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_3_check
  · rw [k6t3p3_update_3]
    exact k6t3p3_closure_4

private theorem k6t3p3_closure_2 : ClosureCheck k6t3p3.graph k6t3p3_state_2 6 3 [k6t3p3_step_2, k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_2_check
  · rw [k6t3p3_update_2]
    exact k6t3p3_closure_3

private theorem k6t3p3_closure_1 : ClosureCheck k6t3p3.graph k6t3p3_state_1 6 3 [k6t3p3_step_1, k6t3p3_step_2, k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_1_check
  · rw [k6t3p3_update_1]
    exact k6t3p3_closure_2

private theorem k6t3p3_closure_0 : ClosureCheck k6t3p3.graph k6t3p3_state_0 6 3 [k6t3p3_step_0, k6t3p3_step_1, k6t3p3_step_2, k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] := by
  constructor
  · exact k6t3p3_step_0_check
  · rw [k6t3p3_update_0]
    exact k6t3p3_closure_1

private theorem k6t3p3_matrix_eq : k6t3p3.matrix 6 = k6t3p3_state_11 := by
  change closureMatrix (k6t3p3.initialMatrix 6) _ = _
  rw [k6t3p3_initial_eq]
  change closureMatrix k6t3p3_state_0 [k6t3p3_step_0, k6t3p3_step_1, k6t3p3_step_2, k6t3p3_step_3, k6t3p3_step_4, k6t3p3_step_5, k6t3p3_step_6, k6t3p3_step_7, k6t3p3_step_8, k6t3p3_step_9, k6t3p3_step_10] = _
  simp only [closureMatrix]
  rw [k6t3p3_update_0, k6t3p3_update_1, k6t3p3_update_2, k6t3p3_update_3, k6t3p3_update_4, k6t3p3_update_5, k6t3p3_update_6, k6t3p3_update_7, k6t3p3_update_8, k6t3p3_update_9, k6t3p3_update_10]

private theorem k6t3p3_part_0 : k6t3p3.chains.flatten = List.finRange _ := by decide

private theorem k6t3p3_part_1 : k6t3p3.chains.map List.length = ([[], [3]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p3_part_2 : k6t3p3.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p3.clique))) = ([[], [3]] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p3_templates_item_0 : (⟨0, 1, [], [], [], 4, 5⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_2 : (⟨0, 2, [], [], [1], 3, 4⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_4 : (⟨0, 3, [], [], [2, 1], 2, 3⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_5 : (⟨0, 4, [], [], [3, 2, 1], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_6 : (⟨0, 4, [], [], [5], 3, 4⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_7 : (⟨0, 5, [], [], [], 4, 5⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_8 : (⟨0, 5, [], [], [4, 3, 2, 1], 1, 1⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_9 : (⟨1, 2, [], [], [3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_10 : (⟨1, 3, [], [], [4, 5], 2, 3⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_11 : (⟨2, 3, [], [1], [4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_12 : (⟨2, 4, [], [1], [5], 2, 3⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_13 : (⟨3, 4, [], [1, 2], [5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_14 : (⟨3, 5, [], [1, 2], [], 2, 3⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_templates_item_15 : (⟨4, 5, [], [1, 2, 3], [], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p3_part_3 : ∀ T ∈ k6t3p3.templates, T.Check k6t3p3.graph k6t3p3.clique 6 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p3_templates_item_0, k6t3p3_templates_item_1, k6t3p3_templates_item_2, k6t3p3_templates_item_3, k6t3p3_templates_item_4, k6t3p3_templates_item_5, k6t3p3_templates_item_6, k6t3p3_templates_item_7, k6t3p3_templates_item_8, k6t3p3_templates_item_9, k6t3p3_templates_item_10, k6t3p3_templates_item_11, k6t3p3_templates_item_12, k6t3p3_templates_item_13, k6t3p3_templates_item_14, k6t3p3_templates_item_15⟩

private theorem k6t3p3_required_item_0 : (⟨1, 3, [2]⟩ : RequiredPathData (Fin 6)).Check k6t3p3.graph 6 := by decide

private theorem k6t3p3_required_item_1 : (⟨2, 4, [3]⟩ : RequiredPathData (Fin 6)).Check k6t3p3.graph 6 := by decide

private theorem k6t3p3_required_item_2 : (⟨3, 5, [4]⟩ : RequiredPathData (Fin 6)).Check k6t3p3.graph 6 := by decide

private theorem k6t3p3_part_4 : ∀ p ∈ k6t3p3.required, p.Check k6t3p3.graph 6 := by
  simp only [k6t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p3_required_item_0, k6t3p3_required_item_1, k6t3p3_required_item_2⟩

private theorem k6t3p3_part_5 : ClosureCheck k6t3p3.graph (k6t3p3.initialMatrix 6) 6 3 k6t3p3.closure := by
  rw [k6t3p3_initial_eq]
  exact k6t3p3_closure_0

private theorem k6t3p3_part_6 : k6t3p3.bad.Check k6t3p3.graph (k6t3p3.matrix 6) 6 3 := by
  rw [k6t3p3_matrix_eq]
  decide

theorem k6t3p3_check : k6t3p3.Check 6 3 [[], [3]] :=
  ⟨k6t3p3_part_0, k6t3p3_part_1, k6t3p3_part_2, k6t3p3_part_3, k6t3p3_part_4, k6t3p3_part_5, k6t3p3_part_6⟩
def k6t3p4 : LayoutCertificate 5 where
  chains := [[0, 1, 2, 3, 4]]
  clique := {0, 2, 4}
  templates := [⟨0, 1, [], [], [2], 1, 4⟩,
    ⟨0, 3, [], [], [2], 1, 4⟩,
    ⟨1, 2, [], [0], [], 1, 4⟩,
    ⟨1, 3, [], [0], [2], 1, 3⟩,
    ⟨1, 4, [], [0], [], 1, 4⟩,
    ⟨2, 3, [], [], [4], 1, 4⟩,
    ⟨3, 4, [], [2], [], 1, 4⟩]
  required := [⟨1, 2, []⟩,
    ⟨1, 3, [2]⟩,
    ⟨2, 3, []⟩]
  closure := []
  bad := ⟨none, {(1, 2), (3, 2), (2, 3)}⟩


private def k6t3p4_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4],
    #[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, ∅, Finset.Icc 1 4],
    #[∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p4_initial_eq_row_0 : ∀ j : Fin 5, (k6t3p4.initialMatrix 6) 0 j = k6t3p4_state_0 0 j := by decide

private theorem k6t3p4_initial_eq_row_1 : ∀ j : Fin 5, (k6t3p4.initialMatrix 6) 1 j = k6t3p4_state_0 1 j := by decide

private theorem k6t3p4_initial_eq_row_2 : ∀ j : Fin 5, (k6t3p4.initialMatrix 6) 2 j = k6t3p4_state_0 2 j := by decide

private theorem k6t3p4_initial_eq_row_3 : ∀ j : Fin 5, (k6t3p4.initialMatrix 6) 3 j = k6t3p4_state_0 3 j := by decide

private theorem k6t3p4_initial_eq_row_4 : ∀ j : Fin 5, (k6t3p4.initialMatrix 6) 4 j = k6t3p4_state_0 4 j := by decide

private theorem k6t3p4_initial_eq : (k6t3p4.initialMatrix 6) = k6t3p4_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p4_initial_eq_row_0 j

  · exact k6t3p4_initial_eq_row_1 j

  · exact k6t3p4_initial_eq_row_2 j

  · exact k6t3p4_initial_eq_row_3 j

  · exact k6t3p4_initial_eq_row_4 j

private theorem k6t3p4_closure_0 : ClosureCheck k6t3p4.graph k6t3p4_state_0 6 3 [] := by trivial

private theorem k6t3p4_matrix_eq : k6t3p4.matrix 6 = k6t3p4_state_0 := by
  change closureMatrix (k6t3p4.initialMatrix 6) _ = _
  rw [k6t3p4_initial_eq]
  change closureMatrix k6t3p4_state_0 [] = _
  rfl

private theorem k6t3p4_part_0 : k6t3p4.chains.flatten = List.finRange _ := by decide

private theorem k6t3p4_part_1 : k6t3p4.chains.map List.length = ([[1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p4_part_2 : k6t3p4.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p4.clique))) = ([[1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p4_templates_item_0 : (⟨0, 1, [], [], [2], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_1 : (⟨0, 3, [], [], [2], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_2 : (⟨1, 2, [], [0], [], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_3 : (⟨1, 3, [], [0], [2], 1, 3⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_4 : (⟨1, 4, [], [0], [], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_5 : (⟨2, 3, [], [], [4], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_templates_item_6 : (⟨3, 4, [], [2], [], 1, 4⟩ : TemplateData (Fin 5)).Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p4_part_3 : ∀ T ∈ k6t3p4.templates, T.Check k6t3p4.graph k6t3p4.clique 6 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p4_templates_item_0, k6t3p4_templates_item_1, k6t3p4_templates_item_2, k6t3p4_templates_item_3, k6t3p4_templates_item_4, k6t3p4_templates_item_5, k6t3p4_templates_item_6⟩

private theorem k6t3p4_required_item_0 : (⟨1, 2, []⟩ : RequiredPathData (Fin 5)).Check k6t3p4.graph 6 := by decide

private theorem k6t3p4_required_item_1 : (⟨1, 3, [2]⟩ : RequiredPathData (Fin 5)).Check k6t3p4.graph 6 := by decide

private theorem k6t3p4_required_item_2 : (⟨2, 3, []⟩ : RequiredPathData (Fin 5)).Check k6t3p4.graph 6 := by decide

private theorem k6t3p4_part_4 : ∀ p ∈ k6t3p4.required, p.Check k6t3p4.graph 6 := by
  simp only [k6t3p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p4_required_item_0, k6t3p4_required_item_1, k6t3p4_required_item_2⟩

private theorem k6t3p4_part_5 : ClosureCheck k6t3p4.graph (k6t3p4.initialMatrix 6) 6 3 k6t3p4.closure := by
  rw [k6t3p4_initial_eq]
  exact k6t3p4_closure_0

private theorem k6t3p4_part_6 : k6t3p4.bad.Check k6t3p4.graph (k6t3p4.matrix 6) 6 3 := by
  rw [k6t3p4_matrix_eq]
  decide

theorem k6t3p4_check : k6t3p4.Check 6 3 [[1, 1]] :=
  ⟨k6t3p4_part_0, k6t3p4_part_1, k6t3p4_part_2, k6t3p4_part_3, k6t3p4_part_4, k6t3p4_part_5, k6t3p4_part_6⟩
def k6t3p5 : LayoutCertificate 6 where
  chains := [[0, 1, 2, 3, 4, 5]]
  clique := {0, 2, 5}
  templates := [⟨0, 1, [], [], [2], 2, 4⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩,
    ⟨0, 3, [], [], [4, 5], 1, 3⟩,
    ⟨0, 4, [], [], [3, 2], 1, 3⟩,
    ⟨0, 5, [], [], [], 3, 5⟩,
    ⟨0, 5, [], [], [4, 3, 2], 2, 2⟩,
    ⟨1, 2, [], [0], [3, 4, 5], 1, 1⟩,
    ⟨1, 3, [], [0], [2], 1, 3⟩,
    ⟨1, 4, [], [0], [3, 2], 1, 2⟩,
    ⟨1, 5, [], [0], [], 2, 4⟩,
    ⟨1, 5, [], [0], [4, 3, 2], 1, 1⟩,
    ⟨4, 5, [], [2, 3], [], 1, 3⟩]
  required := [⟨0, 5, [1, 2, 3, 4]⟩]
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (5, 2), (4, 0)}⟩


private def k6t3p5_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, ∅, {1, 2, 3}, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 4, ∅, {1}, {1, 2, 3}, {1, 2}, Finset.Icc 1 4],
    #[∅, {1}, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2, 3}, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2}, ∅, ∅, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 4, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t3p5_initial_eq_row_0 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 0 j = k6t3p5_state_0 0 j := by decide

private theorem k6t3p5_initial_eq_row_1 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 1 j = k6t3p5_state_0 1 j := by decide

private theorem k6t3p5_initial_eq_row_2 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 2 j = k6t3p5_state_0 2 j := by decide

private theorem k6t3p5_initial_eq_row_3 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 3 j = k6t3p5_state_0 3 j := by decide

private theorem k6t3p5_initial_eq_row_4 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 4 j = k6t3p5_state_0 4 j := by decide

private theorem k6t3p5_initial_eq_row_5 : ∀ j : Fin 6, (k6t3p5.initialMatrix 6) 5 j = k6t3p5_state_0 5 j := by decide

private theorem k6t3p5_initial_eq : (k6t3p5.initialMatrix 6) = k6t3p5_state_0 := by
  funext i j
  fin_cases i

  · exact k6t3p5_initial_eq_row_0 j

  · exact k6t3p5_initial_eq_row_1 j

  · exact k6t3p5_initial_eq_row_2 j

  · exact k6t3p5_initial_eq_row_3 j

  · exact k6t3p5_initial_eq_row_4 j

  · exact k6t3p5_initial_eq_row_5 j

private theorem k6t3p5_closure_0 : ClosureCheck k6t3p5.graph k6t3p5_state_0 6 3 [] := by trivial

private theorem k6t3p5_matrix_eq : k6t3p5.matrix 6 = k6t3p5_state_0 := by
  change closureMatrix (k6t3p5.initialMatrix 6) _ = _
  rw [k6t3p5_initial_eq]
  change closureMatrix k6t3p5_state_0 [] = _
  rfl

private theorem k6t3p5_part_0 : k6t3p5.chains.flatten = List.finRange _ := by decide

private theorem k6t3p5_part_1 : k6t3p5.chains.map List.length = ([[1, 2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t3p5_part_2 : k6t3p5.chains.map (fun l => l.map (fun i => decide (i ∈ k6t3p5.clique))) = ([[1, 2]] : List (List ℕ)).map profileMask := by decide

private theorem k6t3p5_templates_item_0 : (⟨0, 1, [], [], [2], 2, 4⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_2 : (⟨0, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_3 : (⟨0, 4, [], [], [3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_4 : (⟨0, 5, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_5 : (⟨0, 5, [], [], [4, 3, 2], 2, 2⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_6 : (⟨1, 2, [], [0], [3, 4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_7 : (⟨1, 3, [], [0], [2], 1, 3⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_8 : (⟨1, 4, [], [0], [3, 2], 1, 2⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_9 : (⟨1, 5, [], [0], [], 2, 4⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_10 : (⟨1, 5, [], [0], [4, 3, 2], 1, 1⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_templates_item_11 : (⟨4, 5, [], [2, 3], [], 1, 3⟩ : TemplateData (Fin 6)).Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t3p5_part_3 : ∀ T ∈ k6t3p5.templates, T.Check k6t3p5.graph k6t3p5.clique 6 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t3p5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t3p5_templates_item_0, k6t3p5_templates_item_1, k6t3p5_templates_item_2, k6t3p5_templates_item_3, k6t3p5_templates_item_4, k6t3p5_templates_item_5, k6t3p5_templates_item_6, k6t3p5_templates_item_7, k6t3p5_templates_item_8, k6t3p5_templates_item_9, k6t3p5_templates_item_10, k6t3p5_templates_item_11⟩

private theorem k6t3p5_required_item_0 : (⟨0, 5, [1, 2, 3, 4]⟩ : RequiredPathData (Fin 6)).Check k6t3p5.graph 6 := by decide

private theorem k6t3p5_part_4 : ∀ p ∈ k6t3p5.required, p.Check k6t3p5.graph 6 := by
  simp only [k6t3p5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact k6t3p5_required_item_0

private theorem k6t3p5_part_5 : ClosureCheck k6t3p5.graph (k6t3p5.initialMatrix 6) 6 3 k6t3p5.closure := by
  rw [k6t3p5_initial_eq]
  exact k6t3p5_closure_0

private theorem k6t3p5_part_6 : k6t3p5.bad.Check k6t3p5.graph (k6t3p5.matrix 6) 6 3 := by
  rw [k6t3p5_matrix_eq]
  decide

theorem k6t3p5_check : k6t3p5.Check 6 3 [[1, 2]] :=
  ⟨k6t3p5_part_0, k6t3p5_part_1, k6t3p5_part_2, k6t3p5_part_3, k6t3p5_part_4, k6t3p5_part_5, k6t3p5_part_6⟩
def k6t4p0 : LayoutCertificate 4 where
  chains := [[0], [1], [2], [3]]
  clique := {0, 1, 2, 3}
  templates := [⟨0, 1, [], [], [], 1, 5⟩,
    ⟨0, 2, [], [], [], 1, 5⟩,
    ⟨0, 3, [], [], [], 1, 5⟩,
    ⟨1, 2, [], [], [], 1, 5⟩,
    ⟨1, 3, [], [], [], 1, 5⟩,
    ⟨2, 3, [], [], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2), (3, 2)}⟩


private def k6t4p0_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p0_initial_eq_row_0 : ∀ j : Fin 4, (k6t4p0.initialMatrix 6) 0 j = k6t4p0_state_0 0 j := by decide

private theorem k6t4p0_initial_eq_row_1 : ∀ j : Fin 4, (k6t4p0.initialMatrix 6) 1 j = k6t4p0_state_0 1 j := by decide

private theorem k6t4p0_initial_eq_row_2 : ∀ j : Fin 4, (k6t4p0.initialMatrix 6) 2 j = k6t4p0_state_0 2 j := by decide

private theorem k6t4p0_initial_eq_row_3 : ∀ j : Fin 4, (k6t4p0.initialMatrix 6) 3 j = k6t4p0_state_0 3 j := by decide

private theorem k6t4p0_initial_eq : (k6t4p0.initialMatrix 6) = k6t4p0_state_0 := by
  funext i j
  fin_cases i

  · exact k6t4p0_initial_eq_row_0 j

  · exact k6t4p0_initial_eq_row_1 j

  · exact k6t4p0_initial_eq_row_2 j

  · exact k6t4p0_initial_eq_row_3 j

private theorem k6t4p0_closure_0 : ClosureCheck k6t4p0.graph k6t4p0_state_0 6 4 [] := by trivial

private theorem k6t4p0_matrix_eq : k6t4p0.matrix 6 = k6t4p0_state_0 := by
  change closureMatrix (k6t4p0.initialMatrix 6) _ = _
  rw [k6t4p0_initial_eq]
  change closureMatrix k6t4p0_state_0 [] = _
  rfl

private theorem k6t4p0_part_0 : k6t4p0.chains.flatten = List.finRange _ := by decide

private theorem k6t4p0_part_1 : k6t4p0.chains.map List.length = ([[], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t4p0_part_2 : k6t4p0.chains.map (fun l => l.map (fun i => decide (i ∈ k6t4p0.clique))) = ([[], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k6t4p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_templates_item_3 : (⟨1, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_templates_item_4 : (⟨1, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_templates_item_5 : (⟨2, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 4)).Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p0_part_3 : ∀ T ∈ k6t4p0.templates, T.Check k6t4p0.graph k6t4p0.clique 6 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k6t4p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t4p0_templates_item_0, k6t4p0_templates_item_1, k6t4p0_templates_item_2, k6t4p0_templates_item_3, k6t4p0_templates_item_4, k6t4p0_templates_item_5⟩

private theorem k6t4p0_part_4 : ∀ p ∈ k6t4p0.required, p.Check k6t4p0.graph 6 := by decide

private theorem k6t4p0_part_5 : ClosureCheck k6t4p0.graph (k6t4p0.initialMatrix 6) 6 4 k6t4p0.closure := by
  rw [k6t4p0_initial_eq]
  exact k6t4p0_closure_0

private theorem k6t4p0_part_6 : k6t4p0.bad.Check k6t4p0.graph (k6t4p0.matrix 6) 6 4 := by
  rw [k6t4p0_matrix_eq]
  decide

theorem k6t4p0_check : k6t4p0.Check 6 4 [[], [], [], []] :=
  ⟨k6t4p0_part_0, k6t4p0_part_1, k6t4p0_part_2, k6t4p0_part_3, k6t4p0_part_4, k6t4p0_part_5, k6t4p0_part_6⟩
def k6t4p1 : LayoutCertificate 5 where
  chains := [[0], [1], [2, 3, 4]]
  clique := {0, 1, 2, 4}
  templates := [⟨0, 1, [], [], [], 2, 5⟩,
    ⟨0, 1, [[2, 3, 4]], [], [], 1, 2⟩,
    ⟨0, 2, [], [], [], 2, 5⟩,
    ⟨0, 2, [], [], [3, 4], 1, 3⟩,
    ⟨0, 3, [], [], [2], 1, 4⟩,
    ⟨0, 4, [], [], [3, 2], 1, 3⟩,
    ⟨1, 2, [], [], [], 2, 5⟩,
    ⟨1, 2, [], [], [3, 4], 1, 3⟩,
    ⟨1, 3, [], [], [2], 1, 4⟩,
    ⟨1, 4, [], [], [3, 2], 1, 3⟩,
    ⟨2, 3, [], [], [4], 1, 4⟩,
    ⟨3, 4, [], [2], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2), (3, 2)}⟩


private def k6t4p1_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[{1, 2, 3}, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p1_initial_eq_row_0 : ∀ j : Fin 5, (k6t4p1.initialMatrix 6) 0 j = k6t4p1_state_0 0 j := by decide

private theorem k6t4p1_initial_eq_row_1 : ∀ j : Fin 5, (k6t4p1.initialMatrix 6) 1 j = k6t4p1_state_0 1 j := by decide

private theorem k6t4p1_initial_eq_row_2 : ∀ j : Fin 5, (k6t4p1.initialMatrix 6) 2 j = k6t4p1_state_0 2 j := by decide

private theorem k6t4p1_initial_eq_row_3 : ∀ j : Fin 5, (k6t4p1.initialMatrix 6) 3 j = k6t4p1_state_0 3 j := by decide

private theorem k6t4p1_initial_eq_row_4 : ∀ j : Fin 5, (k6t4p1.initialMatrix 6) 4 j = k6t4p1_state_0 4 j := by decide

private theorem k6t4p1_initial_eq : (k6t4p1.initialMatrix 6) = k6t4p1_state_0 := by
  funext i j
  fin_cases i

  · exact k6t4p1_initial_eq_row_0 j

  · exact k6t4p1_initial_eq_row_1 j

  · exact k6t4p1_initial_eq_row_2 j

  · exact k6t4p1_initial_eq_row_3 j

  · exact k6t4p1_initial_eq_row_4 j

private theorem k6t4p1_closure_0 : ClosureCheck k6t4p1.graph k6t4p1_state_0 6 4 [] := by trivial

private theorem k6t4p1_matrix_eq : k6t4p1.matrix 6 = k6t4p1_state_0 := by
  change closureMatrix (k6t4p1.initialMatrix 6) _ = _
  rw [k6t4p1_initial_eq]
  change closureMatrix k6t4p1_state_0 [] = _
  rfl

private theorem k6t4p1_part_0 : k6t4p1.chains.flatten = List.finRange _ := by decide

private theorem k6t4p1_part_1 : k6t4p1.chains.map List.length = ([[], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t4p1_part_2 : k6t4p1.chains.map (fun l => l.map (fun i => decide (i ∈ k6t4p1.clique))) = ([[], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t4p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 5⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_1 : (⟨0, 1, [[2, 3, 4]], [], [], 1, 2⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 5⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_3 : (⟨0, 2, [], [], [3, 4], 1, 3⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_4 : (⟨0, 3, [], [], [2], 1, 4⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_5 : (⟨0, 4, [], [], [3, 2], 1, 3⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_6 : (⟨1, 2, [], [], [], 2, 5⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_7 : (⟨1, 2, [], [], [3, 4], 1, 3⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_8 : (⟨1, 3, [], [], [2], 1, 4⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_9 : (⟨1, 4, [], [], [3, 2], 1, 3⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_10 : (⟨2, 3, [], [], [4], 1, 4⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_templates_item_11 : (⟨3, 4, [], [2], [], 1, 4⟩ : TemplateData (Fin 5)).Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p1_part_3 : ∀ T ∈ k6t4p1.templates, T.Check k6t4p1.graph k6t4p1.clique 6 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t4p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t4p1_templates_item_0, k6t4p1_templates_item_1, k6t4p1_templates_item_2, k6t4p1_templates_item_3, k6t4p1_templates_item_4, k6t4p1_templates_item_5, k6t4p1_templates_item_6, k6t4p1_templates_item_7, k6t4p1_templates_item_8, k6t4p1_templates_item_9, k6t4p1_templates_item_10, k6t4p1_templates_item_11⟩

private theorem k6t4p1_part_4 : ∀ p ∈ k6t4p1.required, p.Check k6t4p1.graph 6 := by decide

private theorem k6t4p1_part_5 : ClosureCheck k6t4p1.graph (k6t4p1.initialMatrix 6) 6 4 k6t4p1.closure := by
  rw [k6t4p1_initial_eq]
  exact k6t4p1_closure_0

private theorem k6t4p1_part_6 : k6t4p1.bad.Check k6t4p1.graph (k6t4p1.matrix 6) 6 4 := by
  rw [k6t4p1_matrix_eq]
  decide

theorem k6t4p1_check : k6t4p1.Check 6 4 [[], [], [1]] :=
  ⟨k6t4p1_part_0, k6t4p1_part_1, k6t4p1_part_2, k6t4p1_part_3, k6t4p1_part_4, k6t4p1_part_5, k6t4p1_part_6⟩
private def k6t4p2_step_0_data : EdgeAttachmentData 6 := ⟨3, 0, [⟨0, 1, [3, 2, 5]⟩, ⟨2, 5, [0, 3, 4]⟩, ⟨2, 5, [1, 0, 3, 4]⟩, ⟨2, 4, [1, 5, 0, 3]⟩, ⟨5, 2, [4, 3, 0, 1]⟩], ⟨none, {(0, 2), (2, 2), (1, 2), (5, 2)}⟩⟩

private def k6t4p2_step_0 : ClosureStep 6 := .edge k6t4p2_step_0_data

private def k6t4p2_step_1_data : EdgeAttachmentData 6 := ⟨3, 1, [⟨1, 0, [3, 2, 5]⟩, ⟨2, 5, [0, 1, 3, 4]⟩, ⟨2, 4, [0, 5, 1, 3]⟩, ⟨2, 5, [1, 3, 4]⟩, ⟨5, 2, [4, 3, 1, 0]⟩], ⟨none, {(1, 2), (2, 2), (0, 2), (5, 2)}⟩⟩

private def k6t4p2_step_1 : ClosureStep 6 := .edge k6t4p2_step_1_data

private def k6t4p2_step_2_data : EdgeAttachmentData 6 := ⟨4, 0, [⟨0, 1, [4, 3, 2]⟩, ⟨2, 5, [3, 4, 0, 1]⟩, ⟨5, 2, [0, 4, 3]⟩, ⟨5, 2, [1, 0, 4, 3]⟩, ⟨5, 3, [1, 2, 0, 4]⟩], ⟨none, {(0, 2), (5, 2), (1, 2), (2, 2)}⟩⟩

private def k6t4p2_step_2 : ClosureStep 6 := .edge k6t4p2_step_2_data

private def k6t4p2_step_3_data : EdgeAttachmentData 6 := ⟨4, 1, [⟨1, 0, [4, 3, 2]⟩, ⟨2, 5, [3, 4, 1, 0]⟩, ⟨5, 2, [0, 1, 4, 3]⟩, ⟨5, 3, [0, 2, 1, 4]⟩, ⟨5, 2, [1, 4, 3]⟩], ⟨none, {(1, 2), (5, 2), (0, 2), (2, 2)}⟩⟩

private def k6t4p2_step_3 : ClosureStep 6 := .edge k6t4p2_step_3_data

private def k6t4p2_step_4_data : EdgeAttachmentData 6 := ⟨4, 2, [⟨0, 1, [2, 4, 5]⟩, ⟨3, 5, [4, 2, 0, 1]⟩, ⟨5, 3, [0, 1, 2, 4]⟩], ⟨none, {(0, 2), (1, 2), (5, 2), (3, 2)}⟩⟩

private def k6t4p2_step_4 : ClosureStep 6 := .edge k6t4p2_step_4_data

private def k6t4p2_step_5_data : FreshAttachmentData 6 := ⟨4, 2, [⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 0, [2, 6, 3, 4, 5]⟩, ⟨1, 4, [2, 6, 3, 0, 5]⟩, ⟨4, 0, [3, 1, 2, 6, 5]⟩, ⟨4, 0, [3, 1, 6, 5]⟩, ⟨4, 0, [3, 6, 5]⟩, ⟨4, 2, [3, 0, 5, 6, 1]⟩, ⟨4, 1, [3, 0, 5, 6, 2]⟩, ⟨4, 6, [5, 0, 3, 1, 2]⟩, ⟨6, 0, [1, 2, 3, 4, 5]⟩, ⟨6, 0, [1, 2, 3]⟩, ⟨6, 4, [1, 2, 3, 0, 5]⟩, ⟨6, 0, [1, 3, 4, 5]⟩, ⟨6, 0, [1, 3]⟩, ⟨6, 4, [1, 3, 0, 5]⟩, ⟨0, 4, [3, 1, 2, 6, 5]⟩, ⟨0, 1, [3, 2]⟩, ⟨0, 1, [3, 2, 6]⟩, ⟨0, 1, [3, 4, 5, 6]⟩, ⟨0, 2, [3, 4, 5, 6, 1]⟩, ⟨0, 1, [3, 4, 5, 6, 2]⟩, ⟨0, 6, [5, 4, 3, 1, 2]⟩], ⟨none, {(6, 2), (4, 1), (0, 1), (1, 2)}⟩⟩

private def k6t4p2_step_5 : ClosureStep 6 := .fresh k6t4p2_step_5_data

private def k6t4p2_step_6_data : FreshAttachmentData 6 := ⟨5, 2, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 4, [2, 3, 0, 6, 5]⟩, ⟨1, 5, [2, 6, 0, 3, 4]⟩, ⟨1, 0, [3, 4, 5, 6]⟩, ⟨1, 2, [3, 0, 6]⟩, ⟨2, 0, [1, 3, 4, 5, 6]⟩, ⟨2, 4, [1, 3, 0, 6, 5]⟩, ⟨2, 5, [1, 6, 0, 3, 4]⟩, ⟨2, 0, [3, 4, 5, 6]⟩, ⟨4, 0, [3, 1, 2, 6]⟩, ⟨4, 0, [5, 6, 1, 2, 3]⟩, ⟨4, 2, [5, 6, 0, 3, 1]⟩, ⟨4, 1, [5, 6, 0, 3, 2]⟩, ⟨0, 2, [3, 1]⟩, ⟨0, 4, [3, 1, 2, 6, 5]⟩, ⟨0, 2, [3, 1, 6]⟩, ⟨0, 4, [3, 1, 6, 5]⟩, ⟨0, 1, [3, 2]⟩, ⟨0, 1, [3, 2, 6]⟩, ⟨0, 1, [3, 4, 5, 6]⟩, ⟨0, 2, [3, 4, 5, 6, 1]⟩, ⟨0, 2, [3, 4, 5, 6]⟩, ⟨0, 1, [3, 4, 5, 6, 2]⟩, ⟨0, 4, [3, 6, 5]⟩, ⟨0, 5, [6, 1, 2, 3, 4]⟩, ⟨0, 4, [6, 3]⟩], ⟨none, {(0, 1), (1, 2), (2, 2), (4, 2)}⟩⟩

private def k6t4p2_step_6 : ClosureStep 6 := .fresh k6t4p2_step_6_data

private def k6t4p2_step_7_data : EdgeAttachmentData 6 := ⟨5, 3, [⟨0, 1, [2, 3, 5]⟩, ⟨2, 4, [0, 1, 5, 3]⟩, ⟨4, 2, [3, 5, 0, 1]⟩], ⟨none, {(0, 2), (1, 2), (2, 2), (4, 2)}⟩⟩

private def k6t4p2_step_7 : ClosureStep 6 := .edge k6t4p2_step_7_data

def k6t4p2 : LayoutCertificate 6 where
  chains := [[0], [1], [2, 3, 4, 5]]
  clique := {0, 1, 2, 5}
  templates := [⟨0, 1, [], [], [], 3, 5⟩,
    ⟨0, 1, [[2, 3, 4, 5]], [], [], 1, 1⟩,
    ⟨0, 2, [], [], [], 3, 5⟩,
    ⟨0, 2, [], [], [3, 4, 5], 1, 2⟩,
    ⟨0, 3, [], [], [2], 2, 4⟩,
    ⟨0, 3, [], [], [4, 5], 1, 3⟩,
    ⟨0, 4, [], [], [3, 2], 1, 3⟩,
    ⟨0, 4, [], [], [5], 2, 4⟩,
    ⟨0, 5, [], [], [], 3, 5⟩,
    ⟨0, 5, [], [], [4, 3, 2], 1, 2⟩,
    ⟨1, 2, [], [], [], 3, 5⟩,
    ⟨1, 2, [], [], [3, 4, 5], 1, 2⟩,
    ⟨1, 3, [], [], [2], 2, 4⟩,
    ⟨1, 3, [], [], [4, 5], 1, 3⟩,
    ⟨1, 4, [], [], [3, 2], 1, 3⟩,
    ⟨1, 4, [], [], [5], 2, 4⟩,
    ⟨1, 5, [], [], [], 3, 5⟩,
    ⟨1, 5, [], [], [4, 3, 2], 1, 2⟩,
    ⟨2, 3, [], [], [4, 5], 1, 3⟩,
    ⟨2, 4, [], [], [5], 2, 4⟩,
    ⟨2, 5, [], [], [], 3, 5⟩,
    ⟨3, 4, [], [2], [5], 1, 3⟩,
    ⟨3, 5, [], [2], [], 2, 4⟩,
    ⟨4, 5, [], [2, 3], [], 1, 3⟩]
  required := []
  closure := [k6t4p2_step_0, k6t4p2_step_1, k6t4p2_step_2, k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7]
  bad := ⟨none, {(3, 1), (4, 1), (0, 2), (2, 2)}⟩


private def k6t4p2_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_initial_eq_row_0 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 0 j = k6t4p2_state_0 0 j := by decide

private theorem k6t4p2_initial_eq_row_1 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 1 j = k6t4p2_state_0 1 j := by decide

private theorem k6t4p2_initial_eq_row_2 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 2 j = k6t4p2_state_0 2 j := by decide

private theorem k6t4p2_initial_eq_row_3 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 3 j = k6t4p2_state_0 3 j := by decide

private theorem k6t4p2_initial_eq_row_4 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 4 j = k6t4p2_state_0 4 j := by decide

private theorem k6t4p2_initial_eq_row_5 : ∀ j : Fin 6, (k6t4p2.initialMatrix 6) 5 j = k6t4p2_state_0 5 j := by decide

private theorem k6t4p2_initial_eq : (k6t4p2.initialMatrix 6) = k6t4p2_state_0 := by
  funext i j
  fin_cases i

  · exact k6t4p2_initial_eq_row_0 j

  · exact k6t4p2_initial_eq_row_1 j

  · exact k6t4p2_initial_eq_row_2 j

  · exact k6t4p2_initial_eq_row_3 j

  · exact k6t4p2_initial_eq_row_4 j

  · exact k6t4p2_initial_eq_row_5 j

private def k6t4p2_state_1 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_0_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 0 j = k6t4p2_local_0 0 j := by decide

private theorem k6t4p2_local_0_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 1 j = k6t4p2_local_0 1 j := by decide

private theorem k6t4p2_local_0_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 2 j = k6t4p2_local_0 2 j := by decide

private theorem k6t4p2_local_0_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 3 j = k6t4p2_local_0 3 j := by decide

private theorem k6t4p2_local_0_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 4 j = k6t4p2_local_0 4 j := by decide

private theorem k6t4p2_local_0_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) 5 j = k6t4p2_local_0 5 j := by decide

private theorem k6t4p2_local_0_eq : (fun a b => k6t4p2_state_0 a b ∪ requiredMatrix 6 k6t4p2_step_0_data.required a b) = k6t4p2_local_0 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_0_eq_row_0 j

  · exact k6t4p2_local_0_eq_row_1 j

  · exact k6t4p2_local_0_eq_row_2 j

  · exact k6t4p2_local_0_eq_row_3 j

  · exact k6t4p2_local_0_eq_row_4 j

  · exact k6t4p2_local_0_eq_row_5 j

private theorem k6t4p2_local_0_paths : ∀ p ∈ k6t4p2_step_0_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_0_data.i k6t4p2_step_0_data.j) 6 := by decide

private theorem k6t4p2_local_0_bad : k6t4p2_step_0_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_0_data.i k6t4p2_step_0_data.j) k6t4p2_local_0 6 4 := by decide

private theorem k6t4p2_step_0_check : k6t4p2_step_0.Check k6t4p2.graph k6t4p2_state_0 6 4 := by
  change k6t4p2_step_0_data.Check k6t4p2.graph k6t4p2_state_0 6 4
  refine ⟨k6t4p2_local_0_paths, ?_⟩
  rw [k6t4p2_local_0_eq]
  exact k6t4p2_local_0_bad

private theorem k6t4p2_update_0 : k6t4p2_step_0.apply k6t4p2_state_0 = k6t4p2_state_1 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_0.apply k6t4p2_state_0 i j = k6t4p2_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_2 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_1 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_1_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 0 j = k6t4p2_local_1 0 j := by decide

private theorem k6t4p2_local_1_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 1 j = k6t4p2_local_1 1 j := by decide

private theorem k6t4p2_local_1_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 2 j = k6t4p2_local_1 2 j := by decide

private theorem k6t4p2_local_1_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 3 j = k6t4p2_local_1 3 j := by decide

private theorem k6t4p2_local_1_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 4 j = k6t4p2_local_1 4 j := by decide

private theorem k6t4p2_local_1_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) 5 j = k6t4p2_local_1 5 j := by decide

private theorem k6t4p2_local_1_eq : (fun a b => k6t4p2_state_1 a b ∪ requiredMatrix 6 k6t4p2_step_1_data.required a b) = k6t4p2_local_1 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_1_eq_row_0 j

  · exact k6t4p2_local_1_eq_row_1 j

  · exact k6t4p2_local_1_eq_row_2 j

  · exact k6t4p2_local_1_eq_row_3 j

  · exact k6t4p2_local_1_eq_row_4 j

  · exact k6t4p2_local_1_eq_row_5 j

private theorem k6t4p2_local_1_paths : ∀ p ∈ k6t4p2_step_1_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_1_data.i k6t4p2_step_1_data.j) 6 := by decide

private theorem k6t4p2_local_1_bad : k6t4p2_step_1_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_1_data.i k6t4p2_step_1_data.j) k6t4p2_local_1 6 4 := by decide

private theorem k6t4p2_step_1_check : k6t4p2_step_1.Check k6t4p2.graph k6t4p2_state_1 6 4 := by
  change k6t4p2_step_1_data.Check k6t4p2.graph k6t4p2_state_1 6 4
  refine ⟨k6t4p2_local_1_paths, ?_⟩
  rw [k6t4p2_local_1_eq]
  exact k6t4p2_local_1_bad

private theorem k6t4p2_update_1 : k6t4p2_step_1.apply k6t4p2_state_1 = k6t4p2_state_2 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_1.apply k6t4p2_state_1 i j = k6t4p2_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_3 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_2 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, Finset.Icc 1 5],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_2_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 0 j = k6t4p2_local_2 0 j := by decide

private theorem k6t4p2_local_2_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 1 j = k6t4p2_local_2 1 j := by decide

private theorem k6t4p2_local_2_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 2 j = k6t4p2_local_2 2 j := by decide

private theorem k6t4p2_local_2_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 3 j = k6t4p2_local_2 3 j := by decide

private theorem k6t4p2_local_2_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 4 j = k6t4p2_local_2 4 j := by decide

private theorem k6t4p2_local_2_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) 5 j = k6t4p2_local_2 5 j := by decide

private theorem k6t4p2_local_2_eq : (fun a b => k6t4p2_state_2 a b ∪ requiredMatrix 6 k6t4p2_step_2_data.required a b) = k6t4p2_local_2 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_2_eq_row_0 j

  · exact k6t4p2_local_2_eq_row_1 j

  · exact k6t4p2_local_2_eq_row_2 j

  · exact k6t4p2_local_2_eq_row_3 j

  · exact k6t4p2_local_2_eq_row_4 j

  · exact k6t4p2_local_2_eq_row_5 j

private theorem k6t4p2_local_2_paths : ∀ p ∈ k6t4p2_step_2_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_2_data.i k6t4p2_step_2_data.j) 6 := by decide

private theorem k6t4p2_local_2_bad : k6t4p2_step_2_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_2_data.i k6t4p2_step_2_data.j) k6t4p2_local_2 6 4 := by decide

private theorem k6t4p2_step_2_check : k6t4p2_step_2.Check k6t4p2.graph k6t4p2_state_2 6 4 := by
  change k6t4p2_step_2_data.Check k6t4p2.graph k6t4p2_state_2 6 4
  refine ⟨k6t4p2_local_2_paths, ?_⟩
  rw [k6t4p2_local_2_eq]
  exact k6t4p2_local_2_bad

private theorem k6t4p2_update_2 : k6t4p2_step_2.apply k6t4p2_state_2 = k6t4p2_state_3 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_2.apply k6t4p2_state_2 i j = k6t4p2_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_3 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, Finset.Icc 1 5],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_3_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 0 j = k6t4p2_local_3 0 j := by decide

private theorem k6t4p2_local_3_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 1 j = k6t4p2_local_3 1 j := by decide

private theorem k6t4p2_local_3_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 2 j = k6t4p2_local_3 2 j := by decide

private theorem k6t4p2_local_3_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 3 j = k6t4p2_local_3 3 j := by decide

private theorem k6t4p2_local_3_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 4 j = k6t4p2_local_3 4 j := by decide

private theorem k6t4p2_local_3_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) 5 j = k6t4p2_local_3 5 j := by decide

private theorem k6t4p2_local_3_eq : (fun a b => k6t4p2_state_3 a b ∪ requiredMatrix 6 k6t4p2_step_3_data.required a b) = k6t4p2_local_3 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_3_eq_row_0 j

  · exact k6t4p2_local_3_eq_row_1 j

  · exact k6t4p2_local_3_eq_row_2 j

  · exact k6t4p2_local_3_eq_row_3 j

  · exact k6t4p2_local_3_eq_row_4 j

  · exact k6t4p2_local_3_eq_row_5 j

private theorem k6t4p2_local_3_paths : ∀ p ∈ k6t4p2_step_3_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_3_data.i k6t4p2_step_3_data.j) 6 := by decide

private theorem k6t4p2_local_3_bad : k6t4p2_step_3_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_3_data.i k6t4p2_step_3_data.j) k6t4p2_local_3 6 4 := by decide

private theorem k6t4p2_step_3_check : k6t4p2_step_3.Check k6t4p2.graph k6t4p2_state_3 6 4 := by
  change k6t4p2_step_3_data.Check k6t4p2.graph k6t4p2_state_3 6 4
  refine ⟨k6t4p2_local_3_paths, ?_⟩
  rw [k6t4p2_local_3_eq]
  exact k6t4p2_local_3_bad

private theorem k6t4p2_update_3 : k6t4p2_step_3.apply k6t4p2_state_3 = k6t4p2_state_4 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_3.apply k6t4p2_state_3 i j = k6t4p2_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_5 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {0, 2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, Finset.Icc 1 4, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_4_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 0 j = k6t4p2_local_4 0 j := by decide

private theorem k6t4p2_local_4_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 1 j = k6t4p2_local_4 1 j := by decide

private theorem k6t4p2_local_4_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 2 j = k6t4p2_local_4 2 j := by decide

private theorem k6t4p2_local_4_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 3 j = k6t4p2_local_4 3 j := by decide

private theorem k6t4p2_local_4_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 4 j = k6t4p2_local_4 4 j := by decide

private theorem k6t4p2_local_4_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) 5 j = k6t4p2_local_4 5 j := by decide

private theorem k6t4p2_local_4_eq : (fun a b => k6t4p2_state_4 a b ∪ requiredMatrix 6 k6t4p2_step_4_data.required a b) = k6t4p2_local_4 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_4_eq_row_0 j

  · exact k6t4p2_local_4_eq_row_1 j

  · exact k6t4p2_local_4_eq_row_2 j

  · exact k6t4p2_local_4_eq_row_3 j

  · exact k6t4p2_local_4_eq_row_4 j

  · exact k6t4p2_local_4_eq_row_5 j

private theorem k6t4p2_local_4_paths : ∀ p ∈ k6t4p2_step_4_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_4_data.i k6t4p2_step_4_data.j) 6 := by decide

private theorem k6t4p2_local_4_bad : k6t4p2_step_4_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_4_data.i k6t4p2_step_4_data.j) k6t4p2_local_4 6 4 := by decide

private theorem k6t4p2_step_4_check : k6t4p2_step_4.Check k6t4p2.graph k6t4p2_state_4 6 4 := by
  change k6t4p2_step_4_data.Check k6t4p2.graph k6t4p2_state_4 6 4
  refine ⟨k6t4p2_local_4_paths, ?_⟩
  rw [k6t4p2_local_4_eq]
  exact k6t4p2_local_4_bad

private theorem k6t4p2_update_4 : k6t4p2_step_4.apply k6t4p2_state_4 = k6t4p2_state_5 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_4.apply k6t4p2_state_4 i j = k6t4p2_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_6 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 0 3, {0}, ∅, {0, 1, 2}, ∅, Finset.Icc 0 3],
    #[Finset.Icc 0 3, ∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{0}, {1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, {0, 2, 3, 4}, {3, 4, 5}],
    #[{0, 1, 2}, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 4],
    #[∅, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 0 3, Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, Finset.Icc 0 4, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_5_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 0 j = k6t4p2_local_5 0 j := by decide

private theorem k6t4p2_local_5_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 1 j = k6t4p2_local_5 1 j := by decide

private theorem k6t4p2_local_5_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 2 j = k6t4p2_local_5 2 j := by decide

private theorem k6t4p2_local_5_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 3 j = k6t4p2_local_5 3 j := by decide

private theorem k6t4p2_local_5_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 4 j = k6t4p2_local_5 4 j := by decide

private theorem k6t4p2_local_5_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 5 j = k6t4p2_local_5 5 j := by decide

private theorem k6t4p2_local_5_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) 6 j = k6t4p2_local_5 6 j := by decide

private theorem k6t4p2_local_5_eq : (fun a b => freshMatrix k6t4p2_state_5 a b ∪ requiredMatrix 6 k6t4p2_step_5_data.required a b) = k6t4p2_local_5 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_5_eq_row_0 j

  · exact k6t4p2_local_5_eq_row_1 j

  · exact k6t4p2_local_5_eq_row_2 j

  · exact k6t4p2_local_5_eq_row_3 j

  · exact k6t4p2_local_5_eq_row_4 j

  · exact k6t4p2_local_5_eq_row_5 j

  · exact k6t4p2_local_5_eq_row_6 j

private theorem k6t4p2_local_5_paths : ∀ p ∈ k6t4p2_step_5_data.required, p.Check (freshGraph k6t4p2.graph k6t4p2_step_5_data.i k6t4p2_step_5_data.j) 6 := by decide

private theorem k6t4p2_local_5_bad : k6t4p2_step_5_data.bad.Check (freshGraph k6t4p2.graph k6t4p2_step_5_data.i k6t4p2_step_5_data.j) k6t4p2_local_5 6 4 := by decide

private theorem k6t4p2_step_5_check : k6t4p2_step_5.Check k6t4p2.graph k6t4p2_state_5 6 4 := by
  change k6t4p2_step_5_data.Check k6t4p2.graph k6t4p2_state_5 6 4
  refine ⟨by decide, k6t4p2_local_5_paths, ?_⟩
  rw [k6t4p2_local_5_eq]
  exact k6t4p2_local_5_bad

private theorem k6t4p2_update_5 : k6t4p2_step_5.apply k6t4p2_state_5 = k6t4p2_state_6 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_5.apply k6t4p2_state_5 i j = k6t4p2_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 0 4, {1, 3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 0 3, Finset.Icc 0 3, ∅, Finset.Icc 0 3, {0}, ∅],
    #[Finset.Icc 0 3, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 0 3, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}],
    #[Finset.Icc 0 3, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[{0}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, Finset.Icc 1 5, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_6_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 0 j = k6t4p2_local_6 0 j := by decide

private theorem k6t4p2_local_6_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 1 j = k6t4p2_local_6 1 j := by decide

private theorem k6t4p2_local_6_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 2 j = k6t4p2_local_6 2 j := by decide

private theorem k6t4p2_local_6_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 3 j = k6t4p2_local_6 3 j := by decide

private theorem k6t4p2_local_6_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 4 j = k6t4p2_local_6 4 j := by decide

private theorem k6t4p2_local_6_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 5 j = k6t4p2_local_6 5 j := by decide

private theorem k6t4p2_local_6_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) 6 j = k6t4p2_local_6 6 j := by decide

private theorem k6t4p2_local_6_eq : (fun a b => freshMatrix k6t4p2_state_6 a b ∪ requiredMatrix 6 k6t4p2_step_6_data.required a b) = k6t4p2_local_6 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_6_eq_row_0 j

  · exact k6t4p2_local_6_eq_row_1 j

  · exact k6t4p2_local_6_eq_row_2 j

  · exact k6t4p2_local_6_eq_row_3 j

  · exact k6t4p2_local_6_eq_row_4 j

  · exact k6t4p2_local_6_eq_row_5 j

  · exact k6t4p2_local_6_eq_row_6 j

private theorem k6t4p2_local_6_paths : ∀ p ∈ k6t4p2_step_6_data.required, p.Check (freshGraph k6t4p2.graph k6t4p2_step_6_data.i k6t4p2_step_6_data.j) 6 := by decide

private theorem k6t4p2_local_6_bad : k6t4p2_step_6_data.bad.Check (freshGraph k6t4p2.graph k6t4p2_step_6_data.i k6t4p2_step_6_data.j) k6t4p2_local_6 6 4 := by decide

private theorem k6t4p2_step_6_check : k6t4p2_step_6.Check k6t4p2.graph k6t4p2_state_6 6 4 := by
  change k6t4p2_step_6_data.Check k6t4p2.graph k6t4p2_state_6 6 4
  refine ⟨by decide, k6t4p2_local_6_paths, ?_⟩
  rw [k6t4p2_local_6_eq]
  exact k6t4p2_local_6_bad

private theorem k6t4p2_update_6 : k6t4p2_step_6.apply k6t4p2_state_6 = k6t4p2_state_7 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_6.apply k6t4p2_state_6 i j = k6t4p2_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k6t4p2_state_8 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5}, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 0 4, {1, 3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 3, 4, 5}, {0, 2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k6t4p2_local_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 0 4, {1, 3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p2_local_7_eq_row_0 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 0 j = k6t4p2_local_7 0 j := by decide

private theorem k6t4p2_local_7_eq_row_1 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 1 j = k6t4p2_local_7 1 j := by decide

private theorem k6t4p2_local_7_eq_row_2 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 2 j = k6t4p2_local_7 2 j := by decide

private theorem k6t4p2_local_7_eq_row_3 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 3 j = k6t4p2_local_7 3 j := by decide

private theorem k6t4p2_local_7_eq_row_4 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 4 j = k6t4p2_local_7 4 j := by decide

private theorem k6t4p2_local_7_eq_row_5 : ∀ j : Fin 6, (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) 5 j = k6t4p2_local_7 5 j := by decide

private theorem k6t4p2_local_7_eq : (fun a b => k6t4p2_state_7 a b ∪ requiredMatrix 6 k6t4p2_step_7_data.required a b) = k6t4p2_local_7 := by
  funext i j
  fin_cases i

  · exact k6t4p2_local_7_eq_row_0 j

  · exact k6t4p2_local_7_eq_row_1 j

  · exact k6t4p2_local_7_eq_row_2 j

  · exact k6t4p2_local_7_eq_row_3 j

  · exact k6t4p2_local_7_eq_row_4 j

  · exact k6t4p2_local_7_eq_row_5 j

private theorem k6t4p2_local_7_paths : ∀ p ∈ k6t4p2_step_7_data.required, p.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_7_data.i k6t4p2_step_7_data.j) 6 := by decide

private theorem k6t4p2_local_7_bad : k6t4p2_step_7_data.bad.Check (addedEdgeGraph k6t4p2.graph k6t4p2_step_7_data.i k6t4p2_step_7_data.j) k6t4p2_local_7 6 4 := by decide

private theorem k6t4p2_step_7_check : k6t4p2_step_7.Check k6t4p2.graph k6t4p2_state_7 6 4 := by
  change k6t4p2_step_7_data.Check k6t4p2.graph k6t4p2_state_7 6 4
  refine ⟨k6t4p2_local_7_paths, ?_⟩
  rw [k6t4p2_local_7_eq]
  exact k6t4p2_local_7_bad

private theorem k6t4p2_update_7 : k6t4p2_step_7.apply k6t4p2_state_7 = k6t4p2_state_8 := by
  have h : ∀ i j : Fin 6, k6t4p2_step_7.apply k6t4p2_state_7 i j = k6t4p2_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k6t4p2_closure_8 : ClosureCheck k6t4p2.graph k6t4p2_state_8 6 4 [] := by trivial

private theorem k6t4p2_closure_7 : ClosureCheck k6t4p2.graph k6t4p2_state_7 6 4 [k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_7_check
  · rw [k6t4p2_update_7]
    exact k6t4p2_closure_8

private theorem k6t4p2_closure_6 : ClosureCheck k6t4p2.graph k6t4p2_state_6 6 4 [k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_6_check
  · rw [k6t4p2_update_6]
    exact k6t4p2_closure_7

private theorem k6t4p2_closure_5 : ClosureCheck k6t4p2.graph k6t4p2_state_5 6 4 [k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_5_check
  · rw [k6t4p2_update_5]
    exact k6t4p2_closure_6

private theorem k6t4p2_closure_4 : ClosureCheck k6t4p2.graph k6t4p2_state_4 6 4 [k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_4_check
  · rw [k6t4p2_update_4]
    exact k6t4p2_closure_5

private theorem k6t4p2_closure_3 : ClosureCheck k6t4p2.graph k6t4p2_state_3 6 4 [k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_3_check
  · rw [k6t4p2_update_3]
    exact k6t4p2_closure_4

private theorem k6t4p2_closure_2 : ClosureCheck k6t4p2.graph k6t4p2_state_2 6 4 [k6t4p2_step_2, k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_2_check
  · rw [k6t4p2_update_2]
    exact k6t4p2_closure_3

private theorem k6t4p2_closure_1 : ClosureCheck k6t4p2.graph k6t4p2_state_1 6 4 [k6t4p2_step_1, k6t4p2_step_2, k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_1_check
  · rw [k6t4p2_update_1]
    exact k6t4p2_closure_2

private theorem k6t4p2_closure_0 : ClosureCheck k6t4p2.graph k6t4p2_state_0 6 4 [k6t4p2_step_0, k6t4p2_step_1, k6t4p2_step_2, k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] := by
  constructor
  · exact k6t4p2_step_0_check
  · rw [k6t4p2_update_0]
    exact k6t4p2_closure_1

private theorem k6t4p2_matrix_eq : k6t4p2.matrix 6 = k6t4p2_state_8 := by
  change closureMatrix (k6t4p2.initialMatrix 6) _ = _
  rw [k6t4p2_initial_eq]
  change closureMatrix k6t4p2_state_0 [k6t4p2_step_0, k6t4p2_step_1, k6t4p2_step_2, k6t4p2_step_3, k6t4p2_step_4, k6t4p2_step_5, k6t4p2_step_6, k6t4p2_step_7] = _
  simp only [closureMatrix]
  rw [k6t4p2_update_0, k6t4p2_update_1, k6t4p2_update_2, k6t4p2_update_3, k6t4p2_update_4, k6t4p2_update_5, k6t4p2_update_6, k6t4p2_update_7]

private theorem k6t4p2_part_0 : k6t4p2.chains.flatten = List.finRange _ := by decide

private theorem k6t4p2_part_1 : k6t4p2.chains.map List.length = ([[], [], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t4p2_part_2 : k6t4p2.chains.map (fun l => l.map (fun i => decide (i ∈ k6t4p2.clique))) = ([[], [], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k6t4p2_templates_item_0 : (⟨0, 1, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_1 : (⟨0, 1, [[2, 3, 4, 5]], [], [], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_2 : (⟨0, 2, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_4 : (⟨0, 3, [], [], [2], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_5 : (⟨0, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_6 : (⟨0, 4, [], [], [3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_7 : (⟨0, 4, [], [], [5], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_8 : (⟨0, 5, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_9 : (⟨0, 5, [], [], [4, 3, 2], 1, 2⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_10 : (⟨1, 2, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_11 : (⟨1, 2, [], [], [3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_12 : (⟨1, 3, [], [], [2], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_13 : (⟨1, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_14 : (⟨1, 4, [], [], [3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_15 : (⟨1, 4, [], [], [5], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_16 : (⟨1, 5, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_17 : (⟨1, 5, [], [], [4, 3, 2], 1, 2⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_18 : (⟨2, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_19 : (⟨2, 4, [], [], [5], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_20 : (⟨2, 5, [], [], [], 3, 5⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_21 : (⟨3, 4, [], [2], [5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_22 : (⟨3, 5, [], [2], [], 2, 4⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_templates_item_23 : (⟨4, 5, [], [2, 3], [], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p2_part_3 : ∀ T ∈ k6t4p2.templates, T.Check k6t4p2.graph k6t4p2.clique 6 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t4p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t4p2_templates_item_0, k6t4p2_templates_item_1, k6t4p2_templates_item_2, k6t4p2_templates_item_3, k6t4p2_templates_item_4, k6t4p2_templates_item_5, k6t4p2_templates_item_6, k6t4p2_templates_item_7, k6t4p2_templates_item_8, k6t4p2_templates_item_9, k6t4p2_templates_item_10, k6t4p2_templates_item_11, k6t4p2_templates_item_12, k6t4p2_templates_item_13, k6t4p2_templates_item_14, k6t4p2_templates_item_15, k6t4p2_templates_item_16, k6t4p2_templates_item_17, k6t4p2_templates_item_18, k6t4p2_templates_item_19, k6t4p2_templates_item_20, k6t4p2_templates_item_21, k6t4p2_templates_item_22, k6t4p2_templates_item_23⟩

private theorem k6t4p2_part_4 : ∀ p ∈ k6t4p2.required, p.Check k6t4p2.graph 6 := by decide

private theorem k6t4p2_part_5 : ClosureCheck k6t4p2.graph (k6t4p2.initialMatrix 6) 6 4 k6t4p2.closure := by
  rw [k6t4p2_initial_eq]
  exact k6t4p2_closure_0

private theorem k6t4p2_part_6 : k6t4p2.bad.Check k6t4p2.graph (k6t4p2.matrix 6) 6 4 := by
  rw [k6t4p2_matrix_eq]
  decide

theorem k6t4p2_check : k6t4p2.Check 6 4 [[], [], [2]] :=
  ⟨k6t4p2_part_0, k6t4p2_part_1, k6t4p2_part_2, k6t4p2_part_3, k6t4p2_part_4, k6t4p2_part_5, k6t4p2_part_6⟩
def k6t4p3 : LayoutCertificate 6 where
  chains := [[0], [1, 2, 3, 4, 5]]
  clique := {0, 1, 3, 5}
  templates := [⟨0, 1, [], [], [], 2, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩,
    ⟨0, 2, [], [], [1], 1, 4⟩,
    ⟨0, 4, [], [], [3], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3, 2, 1], 1, 1⟩,
    ⟨1, 2, [], [], [3], 1, 4⟩,
    ⟨1, 4, [], [], [3], 1, 4⟩,
    ⟨2, 3, [], [1], [], 1, 4⟩,
    ⟨2, 4, [], [1], [3], 1, 3⟩,
    ⟨2, 5, [], [1], [], 1, 4⟩,
    ⟨3, 4, [], [], [5], 1, 4⟩,
    ⟨4, 5, [], [3], [], 1, 4⟩]
  required := [⟨2, 4, [3]⟩]
  closure := []
  bad := ⟨none, {(0, 2), (2, 2), (4, 2), (1, 1)}⟩


private def k6t4p3_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {1}],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4],
    #[∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[{1}, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p3_initial_eq_row_0 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 0 j = k6t4p3_state_0 0 j := by decide

private theorem k6t4p3_initial_eq_row_1 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 1 j = k6t4p3_state_0 1 j := by decide

private theorem k6t4p3_initial_eq_row_2 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 2 j = k6t4p3_state_0 2 j := by decide

private theorem k6t4p3_initial_eq_row_3 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 3 j = k6t4p3_state_0 3 j := by decide

private theorem k6t4p3_initial_eq_row_4 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 4 j = k6t4p3_state_0 4 j := by decide

private theorem k6t4p3_initial_eq_row_5 : ∀ j : Fin 6, (k6t4p3.initialMatrix 6) 5 j = k6t4p3_state_0 5 j := by decide

private theorem k6t4p3_initial_eq : (k6t4p3.initialMatrix 6) = k6t4p3_state_0 := by
  funext i j
  fin_cases i

  · exact k6t4p3_initial_eq_row_0 j

  · exact k6t4p3_initial_eq_row_1 j

  · exact k6t4p3_initial_eq_row_2 j

  · exact k6t4p3_initial_eq_row_3 j

  · exact k6t4p3_initial_eq_row_4 j

  · exact k6t4p3_initial_eq_row_5 j

private theorem k6t4p3_closure_0 : ClosureCheck k6t4p3.graph k6t4p3_state_0 6 4 [] := by trivial

private theorem k6t4p3_matrix_eq : k6t4p3.matrix 6 = k6t4p3_state_0 := by
  change closureMatrix (k6t4p3.initialMatrix 6) _ = _
  rw [k6t4p3_initial_eq]
  change closureMatrix k6t4p3_state_0 [] = _
  rfl

private theorem k6t4p3_part_0 : k6t4p3.chains.flatten = List.finRange _ := by decide

private theorem k6t4p3_part_1 : k6t4p3.chains.map List.length = ([[], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t4p3_part_2 : k6t4p3.chains.map (fun l => l.map (fun i => decide (i ∈ k6t4p3.clique))) = ([[], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t4p3_templates_item_0 : (⟨0, 1, [], [], [], 2, 5⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_2 : (⟨0, 2, [], [], [1], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_3 : (⟨0, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_4 : (⟨0, 5, [], [], [4, 3, 2, 1], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_5 : (⟨1, 2, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_6 : (⟨1, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_7 : (⟨2, 3, [], [1], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_8 : (⟨2, 4, [], [1], [3], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_9 : (⟨2, 5, [], [1], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_10 : (⟨3, 4, [], [], [5], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_templates_item_11 : (⟨4, 5, [], [3], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p3_part_3 : ∀ T ∈ k6t4p3.templates, T.Check k6t4p3.graph k6t4p3.clique 6 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t4p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t4p3_templates_item_0, k6t4p3_templates_item_1, k6t4p3_templates_item_2, k6t4p3_templates_item_3, k6t4p3_templates_item_4, k6t4p3_templates_item_5, k6t4p3_templates_item_6, k6t4p3_templates_item_7, k6t4p3_templates_item_8, k6t4p3_templates_item_9, k6t4p3_templates_item_10, k6t4p3_templates_item_11⟩

private theorem k6t4p3_required_item_0 : (⟨2, 4, [3]⟩ : RequiredPathData (Fin 6)).Check k6t4p3.graph 6 := by decide

private theorem k6t4p3_part_4 : ∀ p ∈ k6t4p3.required, p.Check k6t4p3.graph 6 := by
  simp only [k6t4p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact k6t4p3_required_item_0

private theorem k6t4p3_part_5 : ClosureCheck k6t4p3.graph (k6t4p3.initialMatrix 6) 6 4 k6t4p3.closure := by
  rw [k6t4p3_initial_eq]
  exact k6t4p3_closure_0

private theorem k6t4p3_part_6 : k6t4p3.bad.Check k6t4p3.graph (k6t4p3.matrix 6) 6 4 := by
  rw [k6t4p3_matrix_eq]
  decide

theorem k6t4p3_check : k6t4p3.Check 6 4 [[], [1, 1]] :=
  ⟨k6t4p3_part_0, k6t4p3_part_1, k6t4p3_part_2, k6t4p3_part_3, k6t4p3_part_4, k6t4p3_part_5, k6t4p3_part_6⟩
def k6t4p4 : LayoutCertificate 6 where
  chains := [[0, 1, 2], [3, 4, 5]]
  clique := {0, 2, 3, 5}
  templates := [⟨0, 1, [], [], [2], 1, 4⟩,
    ⟨0, 3, [], [], [], 2, 5⟩,
    ⟨0, 3, [], [2, 1], [4, 5], 1, 1⟩,
    ⟨0, 4, [], [], [3], 1, 4⟩,
    ⟨0, 5, [], [2, 1], [4, 3], 1, 1⟩,
    ⟨1, 2, [], [0], [], 1, 4⟩,
    ⟨1, 3, [], [0], [], 1, 4⟩,
    ⟨1, 4, [], [0], [3], 1, 3⟩,
    ⟨1, 5, [], [0], [], 1, 4⟩,
    ⟨2, 3, [], [0, 1], [4, 5], 1, 1⟩,
    ⟨3, 4, [], [], [5], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (3, 2), (1, 2), (4, 1)}⟩


private def k6t4p4_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, ∅, Finset.Icc 1 5, Finset.Icc 1 4, {1}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 4],
    #[∅, Finset.Icc 1 4, ∅, {1}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1}, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅, ∅],
    #[{1}, Finset.Icc 1 4, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t4p4_initial_eq_row_0 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 0 j = k6t4p4_state_0 0 j := by decide

private theorem k6t4p4_initial_eq_row_1 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 1 j = k6t4p4_state_0 1 j := by decide

private theorem k6t4p4_initial_eq_row_2 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 2 j = k6t4p4_state_0 2 j := by decide

private theorem k6t4p4_initial_eq_row_3 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 3 j = k6t4p4_state_0 3 j := by decide

private theorem k6t4p4_initial_eq_row_4 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 4 j = k6t4p4_state_0 4 j := by decide

private theorem k6t4p4_initial_eq_row_5 : ∀ j : Fin 6, (k6t4p4.initialMatrix 6) 5 j = k6t4p4_state_0 5 j := by decide

private theorem k6t4p4_initial_eq : (k6t4p4.initialMatrix 6) = k6t4p4_state_0 := by
  funext i j
  fin_cases i

  · exact k6t4p4_initial_eq_row_0 j

  · exact k6t4p4_initial_eq_row_1 j

  · exact k6t4p4_initial_eq_row_2 j

  · exact k6t4p4_initial_eq_row_3 j

  · exact k6t4p4_initial_eq_row_4 j

  · exact k6t4p4_initial_eq_row_5 j

private theorem k6t4p4_closure_0 : ClosureCheck k6t4p4.graph k6t4p4_state_0 6 4 [] := by trivial

private theorem k6t4p4_matrix_eq : k6t4p4.matrix 6 = k6t4p4_state_0 := by
  change closureMatrix (k6t4p4.initialMatrix 6) _ = _
  rw [k6t4p4_initial_eq]
  change closureMatrix k6t4p4_state_0 [] = _
  rfl

private theorem k6t4p4_part_0 : k6t4p4.chains.flatten = List.finRange _ := by decide

private theorem k6t4p4_part_1 : k6t4p4.chains.map List.length = ([[1], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t4p4_part_2 : k6t4p4.chains.map (fun l => l.map (fun i => decide (i ∈ k6t4p4.clique))) = ([[1], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t4p4_templates_item_0 : (⟨0, 1, [], [], [2], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_1 : (⟨0, 3, [], [], [], 2, 5⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_2 : (⟨0, 3, [], [2, 1], [4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_3 : (⟨0, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_4 : (⟨0, 5, [], [2, 1], [4, 3], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_5 : (⟨1, 2, [], [0], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_6 : (⟨1, 3, [], [0], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_7 : (⟨1, 4, [], [0], [3], 1, 3⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_8 : (⟨1, 5, [], [0], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_9 : (⟨2, 3, [], [0, 1], [4, 5], 1, 1⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_templates_item_10 : (⟨3, 4, [], [], [5], 1, 4⟩ : TemplateData (Fin 6)).Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t4p4_part_3 : ∀ T ∈ k6t4p4.templates, T.Check k6t4p4.graph k6t4p4.clique 6 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t4p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t4p4_templates_item_0, k6t4p4_templates_item_1, k6t4p4_templates_item_2, k6t4p4_templates_item_3, k6t4p4_templates_item_4, k6t4p4_templates_item_5, k6t4p4_templates_item_6, k6t4p4_templates_item_7, k6t4p4_templates_item_8, k6t4p4_templates_item_9, k6t4p4_templates_item_10⟩

private theorem k6t4p4_part_4 : ∀ p ∈ k6t4p4.required, p.Check k6t4p4.graph 6 := by decide

private theorem k6t4p4_part_5 : ClosureCheck k6t4p4.graph (k6t4p4.initialMatrix 6) 6 4 k6t4p4.closure := by
  rw [k6t4p4_initial_eq]
  exact k6t4p4_closure_0

private theorem k6t4p4_part_6 : k6t4p4.bad.Check k6t4p4.graph (k6t4p4.matrix 6) 6 4 := by
  rw [k6t4p4_matrix_eq]
  decide

theorem k6t4p4_check : k6t4p4.Check 6 4 [[1], [1]] :=
  ⟨k6t4p4_part_0, k6t4p4_part_1, k6t4p4_part_2, k6t4p4_part_3, k6t4p4_part_4, k6t4p4_part_5, k6t4p4_part_6⟩
def k6t5p0 : LayoutCertificate 5 where
  chains := [[0], [1], [2], [3], [4]]
  clique := {0, 1, 2, 3, 4}
  templates := [⟨0, 1, [], [], [], 1, 5⟩,
    ⟨0, 2, [], [], [], 1, 5⟩,
    ⟨0, 3, [], [], [], 1, 5⟩,
    ⟨0, 4, [], [], [], 1, 5⟩,
    ⟨1, 2, [], [], [], 1, 5⟩,
    ⟨1, 3, [], [], [], 1, 5⟩,
    ⟨1, 4, [], [], [], 1, 5⟩,
    ⟨2, 3, [], [], [], 1, 5⟩,
    ⟨2, 4, [], [], [], 1, 5⟩,
    ⟨3, 4, [], [], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2), (3, 2)}⟩


private def k6t5p0_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t5p0_initial_eq_row_0 : ∀ j : Fin 5, (k6t5p0.initialMatrix 6) 0 j = k6t5p0_state_0 0 j := by decide

private theorem k6t5p0_initial_eq_row_1 : ∀ j : Fin 5, (k6t5p0.initialMatrix 6) 1 j = k6t5p0_state_0 1 j := by decide

private theorem k6t5p0_initial_eq_row_2 : ∀ j : Fin 5, (k6t5p0.initialMatrix 6) 2 j = k6t5p0_state_0 2 j := by decide

private theorem k6t5p0_initial_eq_row_3 : ∀ j : Fin 5, (k6t5p0.initialMatrix 6) 3 j = k6t5p0_state_0 3 j := by decide

private theorem k6t5p0_initial_eq_row_4 : ∀ j : Fin 5, (k6t5p0.initialMatrix 6) 4 j = k6t5p0_state_0 4 j := by decide

private theorem k6t5p0_initial_eq : (k6t5p0.initialMatrix 6) = k6t5p0_state_0 := by
  funext i j
  fin_cases i

  · exact k6t5p0_initial_eq_row_0 j

  · exact k6t5p0_initial_eq_row_1 j

  · exact k6t5p0_initial_eq_row_2 j

  · exact k6t5p0_initial_eq_row_3 j

  · exact k6t5p0_initial_eq_row_4 j

private theorem k6t5p0_closure_0 : ClosureCheck k6t5p0.graph k6t5p0_state_0 6 5 [] := by trivial

private theorem k6t5p0_matrix_eq : k6t5p0.matrix 6 = k6t5p0_state_0 := by
  change closureMatrix (k6t5p0.initialMatrix 6) _ = _
  rw [k6t5p0_initial_eq]
  change closureMatrix k6t5p0_state_0 [] = _
  rfl

private theorem k6t5p0_part_0 : k6t5p0.chains.flatten = List.finRange _ := by decide

private theorem k6t5p0_part_1 : k6t5p0.chains.map List.length = ([[], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t5p0_part_2 : k6t5p0.chains.map (fun l => l.map (fun i => decide (i ∈ k6t5p0.clique))) = ([[], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k6t5p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_4 : (⟨1, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_5 : (⟨1, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_6 : (⟨1, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_7 : (⟨2, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_8 : (⟨2, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_templates_item_9 : (⟨3, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 5)).Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p0_part_3 : ∀ T ∈ k6t5p0.templates, T.Check k6t5p0.graph k6t5p0.clique 6 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k6t5p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t5p0_templates_item_0, k6t5p0_templates_item_1, k6t5p0_templates_item_2, k6t5p0_templates_item_3, k6t5p0_templates_item_4, k6t5p0_templates_item_5, k6t5p0_templates_item_6, k6t5p0_templates_item_7, k6t5p0_templates_item_8, k6t5p0_templates_item_9⟩

private theorem k6t5p0_part_4 : ∀ p ∈ k6t5p0.required, p.Check k6t5p0.graph 6 := by decide

private theorem k6t5p0_part_5 : ClosureCheck k6t5p0.graph (k6t5p0.initialMatrix 6) 6 5 k6t5p0.closure := by
  rw [k6t5p0_initial_eq]
  exact k6t5p0_closure_0

private theorem k6t5p0_part_6 : k6t5p0.bad.Check k6t5p0.graph (k6t5p0.matrix 6) 6 5 := by
  rw [k6t5p0_matrix_eq]
  decide

theorem k6t5p0_check : k6t5p0.Check 6 5 [[], [], [], [], []] :=
  ⟨k6t5p0_part_0, k6t5p0_part_1, k6t5p0_part_2, k6t5p0_part_3, k6t5p0_part_4, k6t5p0_part_5, k6t5p0_part_6⟩
def k6t5p1 : LayoutCertificate 6 where
  chains := [[0], [1], [2], [3, 4, 5]]
  clique := {0, 1, 2, 3, 5}
  templates := [⟨0, 1, [], [], [], 2, 5⟩,
    ⟨0, 1, [[3, 4, 5]], [], [], 1, 2⟩,
    ⟨0, 2, [], [], [], 2, 5⟩,
    ⟨0, 2, [[3, 4, 5]], [], [], 1, 2⟩,
    ⟨0, 3, [], [], [4, 5], 1, 3⟩,
    ⟨0, 4, [], [], [3], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3], 1, 3⟩,
    ⟨1, 2, [], [], [], 2, 5⟩,
    ⟨1, 2, [[3, 4, 5]], [], [], 1, 2⟩,
    ⟨1, 3, [], [], [4, 5], 1, 3⟩,
    ⟨1, 4, [], [], [3], 1, 4⟩,
    ⟨1, 5, [], [], [4, 3], 1, 3⟩,
    ⟨2, 3, [], [], [4, 5], 1, 3⟩,
    ⟨2, 4, [], [], [3], 1, 4⟩,
    ⟨2, 5, [], [], [4, 3], 1, 3⟩,
    ⟨3, 4, [], [], [5], 1, 4⟩,
    ⟨4, 5, [], [3], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2), (4, 2)}⟩


private def k6t5p1_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, {1, 2, 3}, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, {1, 2, 3}, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 1 4, {1, 2, 3}],
    #[{1, 2, 3}, {1, 2, 3}, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[{1, 2, 3}, {1, 2, 3}, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t5p1_initial_eq_row_0 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 0 j = k6t5p1_state_0 0 j := by decide

private theorem k6t5p1_initial_eq_row_1 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 1 j = k6t5p1_state_0 1 j := by decide

private theorem k6t5p1_initial_eq_row_2 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 2 j = k6t5p1_state_0 2 j := by decide

private theorem k6t5p1_initial_eq_row_3 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 3 j = k6t5p1_state_0 3 j := by decide

private theorem k6t5p1_initial_eq_row_4 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 4 j = k6t5p1_state_0 4 j := by decide

private theorem k6t5p1_initial_eq_row_5 : ∀ j : Fin 6, (k6t5p1.initialMatrix 6) 5 j = k6t5p1_state_0 5 j := by decide

private theorem k6t5p1_initial_eq : (k6t5p1.initialMatrix 6) = k6t5p1_state_0 := by
  funext i j
  fin_cases i

  · exact k6t5p1_initial_eq_row_0 j

  · exact k6t5p1_initial_eq_row_1 j

  · exact k6t5p1_initial_eq_row_2 j

  · exact k6t5p1_initial_eq_row_3 j

  · exact k6t5p1_initial_eq_row_4 j

  · exact k6t5p1_initial_eq_row_5 j

private theorem k6t5p1_closure_0 : ClosureCheck k6t5p1.graph k6t5p1_state_0 6 5 [] := by trivial

private theorem k6t5p1_matrix_eq : k6t5p1.matrix 6 = k6t5p1_state_0 := by
  change closureMatrix (k6t5p1.initialMatrix 6) _ = _
  rw [k6t5p1_initial_eq]
  change closureMatrix k6t5p1_state_0 [] = _
  rfl

private theorem k6t5p1_part_0 : k6t5p1.chains.flatten = List.finRange _ := by decide

private theorem k6t5p1_part_1 : k6t5p1.chains.map List.length = ([[], [], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t5p1_part_2 : k6t5p1.chains.map (fun l => l.map (fun i => decide (i ∈ k6t5p1.clique))) = ([[], [], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k6t5p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 5⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_1 : (⟨0, 1, [[3, 4, 5]], [], [], 1, 2⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 5⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_3 : (⟨0, 2, [[3, 4, 5]], [], [], 1, 2⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_4 : (⟨0, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_5 : (⟨0, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_6 : (⟨0, 5, [], [], [4, 3], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_7 : (⟨1, 2, [], [], [], 2, 5⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_8 : (⟨1, 2, [[3, 4, 5]], [], [], 1, 2⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_9 : (⟨1, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_10 : (⟨1, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_11 : (⟨1, 5, [], [], [4, 3], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_12 : (⟨2, 3, [], [], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_13 : (⟨2, 4, [], [], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_14 : (⟨2, 5, [], [], [4, 3], 1, 3⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_15 : (⟨3, 4, [], [], [5], 1, 4⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_templates_item_16 : (⟨4, 5, [], [3], [], 1, 4⟩ : TemplateData (Fin 6)).Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t5p1_part_3 : ∀ T ∈ k6t5p1.templates, T.Check k6t5p1.graph k6t5p1.clique 6 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k6t5p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t5p1_templates_item_0, k6t5p1_templates_item_1, k6t5p1_templates_item_2, k6t5p1_templates_item_3, k6t5p1_templates_item_4, k6t5p1_templates_item_5, k6t5p1_templates_item_6, k6t5p1_templates_item_7, k6t5p1_templates_item_8, k6t5p1_templates_item_9, k6t5p1_templates_item_10, k6t5p1_templates_item_11, k6t5p1_templates_item_12, k6t5p1_templates_item_13, k6t5p1_templates_item_14, k6t5p1_templates_item_15, k6t5p1_templates_item_16⟩

private theorem k6t5p1_part_4 : ∀ p ∈ k6t5p1.required, p.Check k6t5p1.graph 6 := by decide

private theorem k6t5p1_part_5 : ClosureCheck k6t5p1.graph (k6t5p1.initialMatrix 6) 6 5 k6t5p1.closure := by
  rw [k6t5p1_initial_eq]
  exact k6t5p1_closure_0

private theorem k6t5p1_part_6 : k6t5p1.bad.Check k6t5p1.graph (k6t5p1.matrix 6) 6 5 := by
  rw [k6t5p1_matrix_eq]
  decide

theorem k6t5p1_check : k6t5p1.Check 6 5 [[], [], [], [1]] :=
  ⟨k6t5p1_part_0, k6t5p1_part_1, k6t5p1_part_2, k6t5p1_part_3, k6t5p1_part_4, k6t5p1_part_5, k6t5p1_part_6⟩
def k6t6p0 : LayoutCertificate 6 where
  chains := [[0], [1], [2], [3], [4], [5]]
  clique := {0, 1, 2, 3, 4, 5}
  templates := [⟨0, 1, [], [], [], 1, 5⟩,
    ⟨0, 2, [], [], [], 1, 5⟩,
    ⟨0, 3, [], [], [], 1, 5⟩,
    ⟨0, 4, [], [], [], 1, 5⟩,
    ⟨0, 5, [], [], [], 1, 5⟩,
    ⟨1, 2, [], [], [], 1, 5⟩,
    ⟨1, 3, [], [], [], 1, 5⟩,
    ⟨1, 4, [], [], [], 1, 5⟩,
    ⟨1, 5, [], [], [], 1, 5⟩,
    ⟨2, 3, [], [], [], 1, 5⟩,
    ⟨2, 4, [], [], [], 1, 5⟩,
    ⟨2, 5, [], [], [], 1, 5⟩,
    ⟨3, 4, [], [], [], 1, 5⟩,
    ⟨3, 5, [], [], [], 1, 5⟩,
    ⟨4, 5, [], [], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 1), (1, 1), (2, 1), (3, 1), (4, 1), (5, 3)}⟩


private def k6t6p0_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k6t6p0_initial_eq_row_0 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 0 j = k6t6p0_state_0 0 j := by decide

private theorem k6t6p0_initial_eq_row_1 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 1 j = k6t6p0_state_0 1 j := by decide

private theorem k6t6p0_initial_eq_row_2 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 2 j = k6t6p0_state_0 2 j := by decide

private theorem k6t6p0_initial_eq_row_3 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 3 j = k6t6p0_state_0 3 j := by decide

private theorem k6t6p0_initial_eq_row_4 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 4 j = k6t6p0_state_0 4 j := by decide

private theorem k6t6p0_initial_eq_row_5 : ∀ j : Fin 6, (k6t6p0.initialMatrix 6) 5 j = k6t6p0_state_0 5 j := by decide

private theorem k6t6p0_initial_eq : (k6t6p0.initialMatrix 6) = k6t6p0_state_0 := by
  funext i j
  fin_cases i

  · exact k6t6p0_initial_eq_row_0 j

  · exact k6t6p0_initial_eq_row_1 j

  · exact k6t6p0_initial_eq_row_2 j

  · exact k6t6p0_initial_eq_row_3 j

  · exact k6t6p0_initial_eq_row_4 j

  · exact k6t6p0_initial_eq_row_5 j

private theorem k6t6p0_closure_0 : ClosureCheck k6t6p0.graph k6t6p0_state_0 6 6 [] := by trivial

private theorem k6t6p0_matrix_eq : k6t6p0.matrix 6 = k6t6p0_state_0 := by
  change closureMatrix (k6t6p0.initialMatrix 6) _ = _
  rw [k6t6p0_initial_eq]
  change closureMatrix k6t6p0_state_0 [] = _
  rfl

private theorem k6t6p0_part_0 : k6t6p0.chains.flatten = List.finRange _ := by decide

private theorem k6t6p0_part_1 : k6t6p0.chains.map List.length = ([[], [], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k6t6p0_part_2 : k6t6p0.chains.map (fun l => l.map (fun i => decide (i ∈ k6t6p0.clique))) = ([[], [], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k6t6p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_4 : (⟨0, 5, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_5 : (⟨1, 2, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_6 : (⟨1, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_7 : (⟨1, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_8 : (⟨1, 5, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_9 : (⟨2, 3, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_10 : (⟨2, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_11 : (⟨2, 5, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_12 : (⟨3, 4, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_13 : (⟨3, 5, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_templates_item_14 : (⟨4, 5, [], [], [], 1, 5⟩ : TemplateData (Fin 6)).Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k6t6p0_part_3 : ∀ T ∈ k6t6p0.templates, T.Check k6t6p0.graph k6t6p0.clique 6 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k6t6p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k6t6p0_templates_item_0, k6t6p0_templates_item_1, k6t6p0_templates_item_2, k6t6p0_templates_item_3, k6t6p0_templates_item_4, k6t6p0_templates_item_5, k6t6p0_templates_item_6, k6t6p0_templates_item_7, k6t6p0_templates_item_8, k6t6p0_templates_item_9, k6t6p0_templates_item_10, k6t6p0_templates_item_11, k6t6p0_templates_item_12, k6t6p0_templates_item_13, k6t6p0_templates_item_14⟩

private theorem k6t6p0_part_4 : ∀ p ∈ k6t6p0.required, p.Check k6t6p0.graph 6 := by decide

private theorem k6t6p0_part_5 : ClosureCheck k6t6p0.graph (k6t6p0.initialMatrix 6) 6 6 k6t6p0.closure := by
  rw [k6t6p0_initial_eq]
  exact k6t6p0_closure_0

private theorem k6t6p0_part_6 : k6t6p0.bad.Check k6t6p0.graph (k6t6p0.matrix 6) 6 6 := by
  rw [k6t6p0_matrix_eq]
  decide

theorem k6t6p0_check : k6t6p0.Check 6 6 [[], [], [], [], [], []] :=
  ⟨k6t6p0_part_0, k6t6p0_part_1, k6t6p0_part_2, k6t6p0_part_3, k6t6p0_part_4, k6t6p0_part_5, k6t6p0_part_6⟩
end CycleClique.Construction.Certificates

end OAI
