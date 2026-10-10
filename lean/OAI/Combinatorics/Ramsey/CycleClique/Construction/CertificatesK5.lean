import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateMatrixChunks
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastCertificateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastLayoutGraph

namespace OAI

namespace CycleClique.Construction.Certificates

def k5t3p0 : LayoutCertificate 3 where
  chains := [[0], [1], [2]]
  clique := {0, 1, 2}
  templates := [⟨0, 1, [], [], [], 1, 4⟩,
    ⟨0, 2, [], [], [], 1, 4⟩,
    ⟨1, 2, [], [], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2)}⟩


private def k5t3p0_state_0 : ForbiddenMatrix 3 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p0_initial_eq_row_0 : ∀ j : Fin 3, (k5t3p0.initialMatrix 5) 0 j = k5t3p0_state_0 0 j := by decide

private theorem k5t3p0_initial_eq_row_1 : ∀ j : Fin 3, (k5t3p0.initialMatrix 5) 1 j = k5t3p0_state_0 1 j := by decide

private theorem k5t3p0_initial_eq_row_2 : ∀ j : Fin 3, (k5t3p0.initialMatrix 5) 2 j = k5t3p0_state_0 2 j := by decide

private theorem k5t3p0_initial_eq : (k5t3p0.initialMatrix 5) = k5t3p0_state_0 := by
  funext i j
  fin_cases i

  · exact k5t3p0_initial_eq_row_0 j

  · exact k5t3p0_initial_eq_row_1 j

  · exact k5t3p0_initial_eq_row_2 j

private theorem k5t3p0_closure_0 : ClosureCheck k5t3p0.graph k5t3p0_state_0 5 3 [] := by trivial

private theorem k5t3p0_matrix_eq : k5t3p0.matrix 5 = k5t3p0_state_0 := by
  change closureMatrix (k5t3p0.initialMatrix 5) _ = _
  rw [k5t3p0_initial_eq]
  change closureMatrix k5t3p0_state_0 [] = _
  rfl

private theorem k5t3p0_part_0 : k5t3p0.chains.flatten = List.finRange _ := by decide

private theorem k5t3p0_part_1 : k5t3p0.chains.map List.length = ([[], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t3p0_part_2 : k5t3p0.chains.map (fun l => l.map (fun i => decide (i ∈ k5t3p0.clique))) = ([[], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k5t3p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 4⟩ : TemplateData (Fin 3)).Check k5t3p0.graph k5t3p0.clique 5 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 3)).Check k5t3p0.graph k5t3p0.clique 5 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p0_templates_item_2 : (⟨1, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 3)).Check k5t3p0.graph k5t3p0.clique 5 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p0_part_3 : ∀ T ∈ k5t3p0.templates, T.Check k5t3p0.graph k5t3p0.clique 5 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k5t3p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t3p0_templates_item_0, k5t3p0_templates_item_1, k5t3p0_templates_item_2⟩

private theorem k5t3p0_part_4 : ∀ p ∈ k5t3p0.required, p.Check k5t3p0.graph 5 := by decide

private theorem k5t3p0_part_5 : ClosureCheck k5t3p0.graph (k5t3p0.initialMatrix 5) 5 3 k5t3p0.closure := by
  rw [k5t3p0_initial_eq]
  exact k5t3p0_closure_0

private theorem k5t3p0_part_6 : k5t3p0.bad.Check k5t3p0.graph (k5t3p0.matrix 5) 5 3 := by
  rw [k5t3p0_matrix_eq]
  decide

theorem k5t3p0_check : k5t3p0.Check 5 3 [[], [], []] :=
  ⟨k5t3p0_part_0, k5t3p0_part_1, k5t3p0_part_2, k5t3p0_part_3, k5t3p0_part_4, k5t3p0_part_5, k5t3p0_part_6⟩
private def k5t3p1_step_0_data : EdgeAttachmentData 4 := ⟨2, 0, [⟨0, 2, []⟩], ⟨none, {(0, 2), (2, 2), (1, 2)}⟩⟩

private def k5t3p1_step_0 : ClosureStep 4 := .edge k5t3p1_step_0_data

def k5t3p1 : LayoutCertificate 4 where
  chains := [[0], [1, 2, 3]]
  clique := {0, 1, 3}
  templates := [⟨0, 1, [], [], [], 2, 4⟩,
    ⟨0, 1, [], [], [2, 3], 1, 2⟩,
    ⟨0, 2, [], [], [1], 1, 3⟩,
    ⟨0, 3, [], [], [2, 1], 1, 2⟩,
    ⟨1, 2, [], [], [3], 1, 3⟩,
    ⟨2, 3, [], [1], [], 1, 3⟩]
  required := [⟨1, 2, []⟩]
  closure := [k5t3p1_step_0]
  bad := ⟨none, {(0, 1), (2, 1), (1, 2)}⟩


private def k5t3p1_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, {1, 2, 3}, {1, 2}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, {1, 2, 3}],
    #[{1, 2}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p1_initial_eq_row_0 : ∀ j : Fin 4, (k5t3p1.initialMatrix 5) 0 j = k5t3p1_state_0 0 j := by decide

private theorem k5t3p1_initial_eq_row_1 : ∀ j : Fin 4, (k5t3p1.initialMatrix 5) 1 j = k5t3p1_state_0 1 j := by decide

private theorem k5t3p1_initial_eq_row_2 : ∀ j : Fin 4, (k5t3p1.initialMatrix 5) 2 j = k5t3p1_state_0 2 j := by decide

private theorem k5t3p1_initial_eq_row_3 : ∀ j : Fin 4, (k5t3p1.initialMatrix 5) 3 j = k5t3p1_state_0 3 j := by decide

private theorem k5t3p1_initial_eq : (k5t3p1.initialMatrix 5) = k5t3p1_state_0 := by
  funext i j
  fin_cases i

  · exact k5t3p1_initial_eq_row_0 j

  · exact k5t3p1_initial_eq_row_1 j

  · exact k5t3p1_initial_eq_row_2 j

  · exact k5t3p1_initial_eq_row_3 j

private def k5t3p1_state_1 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 3, {1, 2}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 0 3, Finset.Icc 1 4, ∅, {1, 2, 3}],
    #[{1, 2}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p1_local_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, {1, 2, 3}],
    #[{1, 2}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p1_local_0_eq_row_0 : ∀ j : Fin 4, (fun a b => k5t3p1_state_0 a b ∪ requiredMatrix 5 k5t3p1_step_0_data.required a b) 0 j = k5t3p1_local_0 0 j := by decide

private theorem k5t3p1_local_0_eq_row_1 : ∀ j : Fin 4, (fun a b => k5t3p1_state_0 a b ∪ requiredMatrix 5 k5t3p1_step_0_data.required a b) 1 j = k5t3p1_local_0 1 j := by decide

private theorem k5t3p1_local_0_eq_row_2 : ∀ j : Fin 4, (fun a b => k5t3p1_state_0 a b ∪ requiredMatrix 5 k5t3p1_step_0_data.required a b) 2 j = k5t3p1_local_0 2 j := by decide

private theorem k5t3p1_local_0_eq_row_3 : ∀ j : Fin 4, (fun a b => k5t3p1_state_0 a b ∪ requiredMatrix 5 k5t3p1_step_0_data.required a b) 3 j = k5t3p1_local_0 3 j := by decide

private theorem k5t3p1_local_0_eq : (fun a b => k5t3p1_state_0 a b ∪ requiredMatrix 5 k5t3p1_step_0_data.required a b) = k5t3p1_local_0 := by
  funext i j
  fin_cases i

  · exact k5t3p1_local_0_eq_row_0 j

  · exact k5t3p1_local_0_eq_row_1 j

  · exact k5t3p1_local_0_eq_row_2 j

  · exact k5t3p1_local_0_eq_row_3 j

private theorem k5t3p1_local_0_paths : ∀ p ∈ k5t3p1_step_0_data.required, p.Check (addedEdgeGraph k5t3p1.graph k5t3p1_step_0_data.i k5t3p1_step_0_data.j) 5 := by decide

private theorem k5t3p1_local_0_bad : k5t3p1_step_0_data.bad.Check (addedEdgeGraph k5t3p1.graph k5t3p1_step_0_data.i k5t3p1_step_0_data.j) k5t3p1_local_0 5 3 := by decide

private theorem k5t3p1_step_0_check : k5t3p1_step_0.Check k5t3p1.graph k5t3p1_state_0 5 3 := by
  change k5t3p1_step_0_data.Check k5t3p1.graph k5t3p1_state_0 5 3
  refine ⟨k5t3p1_local_0_paths, ?_⟩
  rw [k5t3p1_local_0_eq]
  exact k5t3p1_local_0_bad

private theorem k5t3p1_update_0 : k5t3p1_step_0.apply k5t3p1_state_0 = k5t3p1_state_1 := by
  have h : ∀ i j : Fin 4, k5t3p1_step_0.apply k5t3p1_state_0 i j = k5t3p1_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k5t3p1_closure_1 : ClosureCheck k5t3p1.graph k5t3p1_state_1 5 3 [] := by trivial

private theorem k5t3p1_closure_0 : ClosureCheck k5t3p1.graph k5t3p1_state_0 5 3 [k5t3p1_step_0] := by
  constructor
  · exact k5t3p1_step_0_check
  · rw [k5t3p1_update_0]
    exact k5t3p1_closure_1

private theorem k5t3p1_matrix_eq : k5t3p1.matrix 5 = k5t3p1_state_1 := by
  change closureMatrix (k5t3p1.initialMatrix 5) _ = _
  rw [k5t3p1_initial_eq]
  change closureMatrix k5t3p1_state_0 [k5t3p1_step_0] = _
  simp only [closureMatrix]
  rw [k5t3p1_update_0]

private theorem k5t3p1_part_0 : k5t3p1.chains.flatten = List.finRange _ := by decide

private theorem k5t3p1_part_1 : k5t3p1.chains.map List.length = ([[], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t3p1_part_2 : k5t3p1.chains.map (fun l => l.map (fun i => decide (i ∈ k5t3p1.clique))) = ([[], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k5t3p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 4⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_templates_item_1 : (⟨0, 1, [], [], [2, 3], 1, 2⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_templates_item_2 : (⟨0, 2, [], [], [1], 1, 3⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_templates_item_3 : (⟨0, 3, [], [], [2, 1], 1, 2⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_templates_item_4 : (⟨1, 2, [], [], [3], 1, 3⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_templates_item_5 : (⟨2, 3, [], [1], [], 1, 3⟩ : TemplateData (Fin 4)).Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p1_part_3 : ∀ T ∈ k5t3p1.templates, T.Check k5t3p1.graph k5t3p1.clique 5 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k5t3p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t3p1_templates_item_0, k5t3p1_templates_item_1, k5t3p1_templates_item_2, k5t3p1_templates_item_3, k5t3p1_templates_item_4, k5t3p1_templates_item_5⟩

private theorem k5t3p1_required_item_0 : (⟨1, 2, []⟩ : RequiredPathData (Fin 4)).Check k5t3p1.graph 5 := by decide

private theorem k5t3p1_part_4 : ∀ p ∈ k5t3p1.required, p.Check k5t3p1.graph 5 := by
  simp only [k5t3p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact k5t3p1_required_item_0

private theorem k5t3p1_part_5 : ClosureCheck k5t3p1.graph (k5t3p1.initialMatrix 5) 5 3 k5t3p1.closure := by
  rw [k5t3p1_initial_eq]
  exact k5t3p1_closure_0

private theorem k5t3p1_part_6 : k5t3p1.bad.Check k5t3p1.graph (k5t3p1.matrix 5) 5 3 := by
  rw [k5t3p1_matrix_eq]
  decide

theorem k5t3p1_check : k5t3p1.Check 5 3 [[], [1]] :=
  ⟨k5t3p1_part_0, k5t3p1_part_1, k5t3p1_part_2, k5t3p1_part_3, k5t3p1_part_4, k5t3p1_part_5, k5t3p1_part_6⟩
private def k5t3p2_step_0_data : EdgeAttachmentData 5 := ⟨3, 1, [⟨2, 3, [1]⟩, ⟨2, 4, [3, 1, 0]⟩, ⟨3, 4, [1]⟩], ⟨none, {(0, 0), (2, 2), (3, 2), (4, 1)}⟩⟩

private def k5t3p2_step_0 : ClosureStep 5 := .edge k5t3p2_step_0_data

private def k5t3p2_step_1_data : EdgeAttachmentData 5 := ⟨4, 2, [⟨0, 1, [4, 2]⟩, ⟨1, 3, [0, 4, 2]⟩, ⟨1, 2, [4]⟩, ⟨2, 3, [4]⟩], ⟨none, {(0, 0), (1, 2), (2, 2), (3, 1)}⟩⟩

private def k5t3p2_step_1 : ClosureStep 5 := .edge k5t3p2_step_1_data

private def k5t3p2_step_2_data : FreshAttachmentData 5 := ⟨3, 1, [⟨3, 0, [2, 1, 5, 4]⟩, ⟨3, 0, [2, 5, 4]⟩, ⟨3, 5, [2, 0, 4]⟩, ⟨3, 1, [2, 0, 4, 5]⟩, ⟨5, 0, [1, 2, 3, 4]⟩, ⟨0, 4, [2, 1, 5]⟩, ⟨0, 5, [2, 3, 4]⟩, ⟨0, 1, [2, 3, 4, 5]⟩], ⟨none, {(3, 1), (0, 0), (1, 0), (5, 1), (4, 1)}⟩⟩

private def k5t3p2_step_2 : ClosureStep 5 := .fresh k5t3p2_step_2_data

private def k5t3p2_step_3_data : FreshAttachmentData 5 := ⟨4, 1, [⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 3, [2, 0, 5, 4]⟩, ⟨1, 4, [5, 0, 2, 3]⟩, ⟨3, 0, [4, 5, 1, 2]⟩, ⟨3, 1, [4, 5, 0, 2]⟩, ⟨4, 0, [3, 2, 1, 5]⟩, ⟨4, 1, [3, 2, 0, 5]⟩], ⟨none, {(1, 1), (3, 1), (4, 1)}⟩⟩

private def k5t3p2_step_3 : ClosureStep 5 := .fresh k5t3p2_step_3_data

private def k5t3p2_step_4_data : FreshAttachmentData 5 := ⟨4, 2, [⟨2, 0, [1, 5, 4, 3]⟩, ⟨4, 0, [3, 2, 1, 5]⟩, ⟨4, 0, [3, 2, 5]⟩, ⟨4, 2, [3, 0, 5]⟩, ⟨4, 1, [3, 0, 5, 2]⟩, ⟨0, 2, [3, 4, 5]⟩, ⟨0, 1, [3, 4, 5, 2]⟩, ⟨0, 3, [5, 1, 2]⟩], ⟨none, {(4, 1), (0, 0), (1, 0), (2, 1), (3, 1)}⟩⟩

private def k5t3p2_step_4 : ClosureStep 5 := .fresh k5t3p2_step_4_data

private def k5t3p2_step_5_data : EdgeAttachmentData 5 := ⟨2, 0, [⟨0, 4, [2, 1]⟩, ⟨2, 0, []⟩], ⟨none, {(2, 2), (0, 2), (4, 1), (3, 0)}⟩⟩

private def k5t3p2_step_5 : ClosureStep 5 := .edge k5t3p2_step_5_data

private def k5t3p2_step_6_data : EdgeAttachmentData 5 := ⟨3, 0, [⟨1, 0, [2, 3]⟩], ⟨none, {(1, 2), (0, 2), (3, 1), (2, 0)}⟩⟩

private def k5t3p2_step_6 : ClosureStep 5 := .edge k5t3p2_step_6_data

def k5t3p2 : LayoutCertificate 5 where
  chains := [[0], [1, 2, 3, 4]]
  clique := {0, 1, 4}
  templates := [⟨0, 1, [], [], [], 3, 4⟩,
    ⟨0, 1, [], [], [2, 3, 4], 1, 1⟩,
    ⟨0, 2, [], [], [1], 2, 3⟩,
    ⟨0, 2, [], [], [3, 4], 1, 2⟩,
    ⟨0, 3, [], [], [2, 1], 1, 2⟩,
    ⟨0, 3, [], [], [4], 2, 3⟩,
    ⟨0, 4, [], [], [], 3, 4⟩,
    ⟨0, 4, [], [], [3, 2, 1], 1, 1⟩,
    ⟨1, 2, [], [], [3, 4], 1, 2⟩,
    ⟨1, 3, [], [], [4], 2, 3⟩,
    ⟨2, 3, [], [1], [4], 1, 2⟩,
    ⟨2, 4, [], [1], [], 2, 3⟩,
    ⟨3, 4, [], [1, 2], [], 1, 2⟩]
  required := [⟨1, 2, []⟩,
    ⟨2, 3, []⟩]
  closure := [k5t3p2_step_0, k5t3p2_step_1, k5t3p2_step_2, k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6]
  bad := ⟨none, {(2, 1), (3, 1), (0, 1)}⟩


private def k5t3p2_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, {2, 3}, ∅],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {2, 3}],
    #[{1, 2, 3}, {2, 3}, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, ∅, {2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_initial_eq_row_0 : ∀ j : Fin 5, (k5t3p2.initialMatrix 5) 0 j = k5t3p2_state_0 0 j := by decide

private theorem k5t3p2_initial_eq_row_1 : ∀ j : Fin 5, (k5t3p2.initialMatrix 5) 1 j = k5t3p2_state_0 1 j := by decide

private theorem k5t3p2_initial_eq_row_2 : ∀ j : Fin 5, (k5t3p2.initialMatrix 5) 2 j = k5t3p2_state_0 2 j := by decide

private theorem k5t3p2_initial_eq_row_3 : ∀ j : Fin 5, (k5t3p2.initialMatrix 5) 3 j = k5t3p2_state_0 3 j := by decide

private theorem k5t3p2_initial_eq_row_4 : ∀ j : Fin 5, (k5t3p2.initialMatrix 5) 4 j = k5t3p2_state_0 4 j := by decide

private theorem k5t3p2_initial_eq : (k5t3p2.initialMatrix 5) = k5t3p2_state_0 := by
  funext i j
  fin_cases i

  · exact k5t3p2_initial_eq_row_0 j

  · exact k5t3p2_initial_eq_row_1 j

  · exact k5t3p2_initial_eq_row_2 j

  · exact k5t3p2_initial_eq_row_3 j

  · exact k5t3p2_initial_eq_row_4 j

private def k5t3p2_state_1 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, {0, 2, 3}, ∅],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {2, 3}],
    #[{1, 2, 3}, {0, 2, 3}, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, ∅, {2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, {2, 3}, ∅],
    #[{1, 2, 3}, {1, 2, 4}, ∅, Finset.Icc 1 4, {1, 2, 3}],
    #[{1, 2, 3}, {2, 3}, Finset.Icc 1 4, ∅, {1, 2, 3}],
    #[{1, 3, 4}, ∅, {1, 2, 3}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_0_eq_row_0 : ∀ j : Fin 5, (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) 0 j = k5t3p2_local_0 0 j := by decide

private theorem k5t3p2_local_0_eq_row_1 : ∀ j : Fin 5, (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) 1 j = k5t3p2_local_0 1 j := by decide

private theorem k5t3p2_local_0_eq_row_2 : ∀ j : Fin 5, (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) 2 j = k5t3p2_local_0 2 j := by decide

private theorem k5t3p2_local_0_eq_row_3 : ∀ j : Fin 5, (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) 3 j = k5t3p2_local_0 3 j := by decide

private theorem k5t3p2_local_0_eq_row_4 : ∀ j : Fin 5, (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) 4 j = k5t3p2_local_0 4 j := by decide

private theorem k5t3p2_local_0_eq : (fun a b => k5t3p2_state_0 a b ∪ requiredMatrix 5 k5t3p2_step_0_data.required a b) = k5t3p2_local_0 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_0_eq_row_0 j

  · exact k5t3p2_local_0_eq_row_1 j

  · exact k5t3p2_local_0_eq_row_2 j

  · exact k5t3p2_local_0_eq_row_3 j

  · exact k5t3p2_local_0_eq_row_4 j

private theorem k5t3p2_local_0_paths : ∀ p ∈ k5t3p2_step_0_data.required, p.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_0_data.i k5t3p2_step_0_data.j) 5 := by decide

private theorem k5t3p2_local_0_bad : k5t3p2_step_0_data.bad.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_0_data.i k5t3p2_step_0_data.j) k5t3p2_local_0 5 3 := by decide

private theorem k5t3p2_step_0_check : k5t3p2_step_0.Check k5t3p2.graph k5t3p2_state_0 5 3 := by
  change k5t3p2_step_0_data.Check k5t3p2.graph k5t3p2_state_0 5 3
  refine ⟨k5t3p2_local_0_paths, ?_⟩
  rw [k5t3p2_local_0_eq]
  exact k5t3p2_local_0_bad

private theorem k5t3p2_update_0 : k5t3p2_step_0.apply k5t3p2_state_0 = k5t3p2_state_1 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_0.apply k5t3p2_state_0 i j = k5t3p2_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_2 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, {0, 2, 3}, ∅],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {0, 2, 3}],
    #[{1, 2, 3}, {0, 2, 3}, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, ∅, {0, 2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_1 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 0 3, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2, 3}],
    #[{1, 2, 3}, Finset.Icc 0 3, Finset.Icc 1 4, ∅, {1, 2}],
    #[{1, 3, 4}, ∅, {2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_1_eq_row_0 : ∀ j : Fin 5, (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) 0 j = k5t3p2_local_1 0 j := by decide

private theorem k5t3p2_local_1_eq_row_1 : ∀ j : Fin 5, (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) 1 j = k5t3p2_local_1 1 j := by decide

private theorem k5t3p2_local_1_eq_row_2 : ∀ j : Fin 5, (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) 2 j = k5t3p2_local_1 2 j := by decide

private theorem k5t3p2_local_1_eq_row_3 : ∀ j : Fin 5, (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) 3 j = k5t3p2_local_1 3 j := by decide

private theorem k5t3p2_local_1_eq_row_4 : ∀ j : Fin 5, (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) 4 j = k5t3p2_local_1 4 j := by decide

private theorem k5t3p2_local_1_eq : (fun a b => k5t3p2_state_1 a b ∪ requiredMatrix 5 k5t3p2_step_1_data.required a b) = k5t3p2_local_1 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_1_eq_row_0 j

  · exact k5t3p2_local_1_eq_row_1 j

  · exact k5t3p2_local_1_eq_row_2 j

  · exact k5t3p2_local_1_eq_row_3 j

  · exact k5t3p2_local_1_eq_row_4 j

private theorem k5t3p2_local_1_paths : ∀ p ∈ k5t3p2_step_1_data.required, p.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_1_data.i k5t3p2_step_1_data.j) 5 := by decide

private theorem k5t3p2_local_1_bad : k5t3p2_step_1_data.bad.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_1_data.i k5t3p2_step_1_data.j) k5t3p2_local_1 5 3 := by decide

private theorem k5t3p2_step_1_check : k5t3p2_step_1.Check k5t3p2.graph k5t3p2_state_1 5 3 := by
  change k5t3p2_step_1_data.Check k5t3p2.graph k5t3p2_state_1 5 3
  refine ⟨k5t3p2_local_1_paths, ?_⟩
  rw [k5t3p2_local_1_eq]
  exact k5t3p2_local_1_bad

private theorem k5t3p2_update_1 : k5t3p2_step_1.apply k5t3p2_state_1 = k5t3p2_state_2 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_1.apply k5t3p2_state_1 i j = k5t3p2_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_3 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, ∅],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {0, 2, 3}],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, ∅, {0, 2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_2 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {0}, ∅, {0, 1}, {1}, {0, 1}],
    #[{0}, ∅, {1, 3, 4}, Finset.Icc 0 3, {1, 2, 3}, {1, 3, 4}],
    #[∅, {1, 3, 4}, ∅, {1, 2, 4}, {0, 2, 3}, ∅],
    #[{0, 1}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[{1}, {1, 2, 3}, {0, 2, 3}, {1, 2, 4}, ∅, {1, 2}],
    #[{0, 1}, {1, 3, 4}, ∅, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_2_eq_row_0 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 0 j = k5t3p2_local_2 0 j := by decide

private theorem k5t3p2_local_2_eq_row_1 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 1 j = k5t3p2_local_2 1 j := by decide

private theorem k5t3p2_local_2_eq_row_2 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 2 j = k5t3p2_local_2 2 j := by decide

private theorem k5t3p2_local_2_eq_row_3 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 3 j = k5t3p2_local_2 3 j := by decide

private theorem k5t3p2_local_2_eq_row_4 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 4 j = k5t3p2_local_2 4 j := by decide

private theorem k5t3p2_local_2_eq_row_5 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) 5 j = k5t3p2_local_2 5 j := by decide

private theorem k5t3p2_local_2_eq : (fun a b => freshMatrix k5t3p2_state_2 a b ∪ requiredMatrix 5 k5t3p2_step_2_data.required a b) = k5t3p2_local_2 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_2_eq_row_0 j

  · exact k5t3p2_local_2_eq_row_1 j

  · exact k5t3p2_local_2_eq_row_2 j

  · exact k5t3p2_local_2_eq_row_3 j

  · exact k5t3p2_local_2_eq_row_4 j

  · exact k5t3p2_local_2_eq_row_5 j

private theorem k5t3p2_local_2_paths : ∀ p ∈ k5t3p2_step_2_data.required, p.Check (freshGraph k5t3p2.graph k5t3p2_step_2_data.i k5t3p2_step_2_data.j) 5 := by decide

private theorem k5t3p2_local_2_bad : k5t3p2_step_2_data.bad.Check (freshGraph k5t3p2.graph k5t3p2_step_2_data.i k5t3p2_step_2_data.j) k5t3p2_local_2 5 3 := by decide

private theorem k5t3p2_step_2_check : k5t3p2_step_2.Check k5t3p2.graph k5t3p2_state_2 5 3 := by
  change k5t3p2_step_2_data.Check k5t3p2.graph k5t3p2_state_2 5 3
  refine ⟨by decide, k5t3p2_local_2_paths, ?_⟩
  rw [k5t3p2_local_2_eq]
  exact k5t3p2_local_2_bad

private theorem k5t3p2_update_2 : k5t3p2_step_2.apply k5t3p2_state_2 = k5t3p2_state_3 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_2.apply k5t3p2_state_2 i j = k5t3p2_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_4 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {0, 2, 3}],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, {1}, {0, 2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_3 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {0}, ∅, {0}, {0}, ∅],
    #[{0}, ∅, {1, 3, 4}, Finset.Icc 0 3, Finset.Icc 0 3, {1, 3, 4}],
    #[∅, {1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, ∅],
    #[{0}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2, 4}, {0, 2, 3}],
    #[{0}, Finset.Icc 0 3, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[∅, {1, 3, 4}, ∅, {0, 2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_3_eq_row_0 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 0 j = k5t3p2_local_3 0 j := by decide

private theorem k5t3p2_local_3_eq_row_1 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 1 j = k5t3p2_local_3 1 j := by decide

private theorem k5t3p2_local_3_eq_row_2 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 2 j = k5t3p2_local_3 2 j := by decide

private theorem k5t3p2_local_3_eq_row_3 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 3 j = k5t3p2_local_3 3 j := by decide

private theorem k5t3p2_local_3_eq_row_4 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 4 j = k5t3p2_local_3 4 j := by decide

private theorem k5t3p2_local_3_eq_row_5 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) 5 j = k5t3p2_local_3 5 j := by decide

private theorem k5t3p2_local_3_eq : (fun a b => freshMatrix k5t3p2_state_3 a b ∪ requiredMatrix 5 k5t3p2_step_3_data.required a b) = k5t3p2_local_3 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_3_eq_row_0 j

  · exact k5t3p2_local_3_eq_row_1 j

  · exact k5t3p2_local_3_eq_row_2 j

  · exact k5t3p2_local_3_eq_row_3 j

  · exact k5t3p2_local_3_eq_row_4 j

  · exact k5t3p2_local_3_eq_row_5 j

private theorem k5t3p2_local_3_paths : ∀ p ∈ k5t3p2_step_3_data.required, p.Check (freshGraph k5t3p2.graph k5t3p2_step_3_data.i k5t3p2_step_3_data.j) 5 := by decide

private theorem k5t3p2_local_3_bad : k5t3p2_step_3_data.bad.Check (freshGraph k5t3p2.graph k5t3p2_step_3_data.i k5t3p2_step_3_data.j) k5t3p2_local_3 5 3 := by decide

private theorem k5t3p2_step_3_check : k5t3p2_step_3.Check k5t3p2.graph k5t3p2_state_3 5 3 := by
  change k5t3p2_step_3_data.Check k5t3p2.graph k5t3p2_state_3 5 3
  refine ⟨by decide, k5t3p2_local_3_paths, ?_⟩
  rw [k5t3p2_local_3_eq]
  exact k5t3p2_local_3_bad

private theorem k5t3p2_update_3 : k5t3p2_step_3.apply k5t3p2_state_3 = k5t3p2_state_4 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_3.apply k5t3p2_state_3 i j = k5t3p2_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_5 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, {1, 2, 3}, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[{1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, {1}, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {0}, {0, 1}, {1}, {0, 1}, ∅],
    #[{0}, ∅, {1, 3, 4}, {1, 2, 3}, Finset.Icc 0 3, {1, 3, 4}],
    #[{0, 1}, {1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[{1}, {1, 2, 3}, {1, 2, 4}, ∅, {1, 2, 4}, {0, 2, 3}],
    #[{0, 1}, Finset.Icc 0 3, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[∅, {1, 3, 4}, {1}, {0, 2, 3}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_4_eq_row_0 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 0 j = k5t3p2_local_4 0 j := by decide

private theorem k5t3p2_local_4_eq_row_1 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 1 j = k5t3p2_local_4 1 j := by decide

private theorem k5t3p2_local_4_eq_row_2 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 2 j = k5t3p2_local_4 2 j := by decide

private theorem k5t3p2_local_4_eq_row_3 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 3 j = k5t3p2_local_4 3 j := by decide

private theorem k5t3p2_local_4_eq_row_4 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 4 j = k5t3p2_local_4 4 j := by decide

private theorem k5t3p2_local_4_eq_row_5 : ∀ j : Fin 6, (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) 5 j = k5t3p2_local_4 5 j := by decide

private theorem k5t3p2_local_4_eq : (fun a b => freshMatrix k5t3p2_state_4 a b ∪ requiredMatrix 5 k5t3p2_step_4_data.required a b) = k5t3p2_local_4 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_4_eq_row_0 j

  · exact k5t3p2_local_4_eq_row_1 j

  · exact k5t3p2_local_4_eq_row_2 j

  · exact k5t3p2_local_4_eq_row_3 j

  · exact k5t3p2_local_4_eq_row_4 j

  · exact k5t3p2_local_4_eq_row_5 j

private theorem k5t3p2_local_4_paths : ∀ p ∈ k5t3p2_step_4_data.required, p.Check (freshGraph k5t3p2.graph k5t3p2_step_4_data.i k5t3p2_step_4_data.j) 5 := by decide

private theorem k5t3p2_local_4_bad : k5t3p2_step_4_data.bad.Check (freshGraph k5t3p2.graph k5t3p2_step_4_data.i k5t3p2_step_4_data.j) k5t3p2_local_4 5 3 := by decide

private theorem k5t3p2_step_4_check : k5t3p2_step_4.Check k5t3p2.graph k5t3p2_state_4 5 3 := by
  change k5t3p2_step_4_data.Check k5t3p2.graph k5t3p2_state_4 5 3
  refine ⟨by decide, k5t3p2_local_4_paths, ?_⟩
  rw [k5t3p2_local_4_eq]
  exact k5t3p2_local_4_bad

private theorem k5t3p2_update_4 : k5t3p2_step_4.apply k5t3p2_state_4 = k5t3p2_state_5 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_4.apply k5t3p2_state_4 i j = k5t3p2_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_6 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, Finset.Icc 0 3, {1, 2, 3}, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, {1}, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_5 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 4],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[Finset.Icc 1 4, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[Finset.Icc 1 4, {1}, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_5_eq_row_0 : ∀ j : Fin 5, (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) 0 j = k5t3p2_local_5 0 j := by decide

private theorem k5t3p2_local_5_eq_row_1 : ∀ j : Fin 5, (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) 1 j = k5t3p2_local_5 1 j := by decide

private theorem k5t3p2_local_5_eq_row_2 : ∀ j : Fin 5, (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) 2 j = k5t3p2_local_5 2 j := by decide

private theorem k5t3p2_local_5_eq_row_3 : ∀ j : Fin 5, (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) 3 j = k5t3p2_local_5 3 j := by decide

private theorem k5t3p2_local_5_eq_row_4 : ∀ j : Fin 5, (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) 4 j = k5t3p2_local_5 4 j := by decide

private theorem k5t3p2_local_5_eq : (fun a b => k5t3p2_state_5 a b ∪ requiredMatrix 5 k5t3p2_step_5_data.required a b) = k5t3p2_local_5 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_5_eq_row_0 j

  · exact k5t3p2_local_5_eq_row_1 j

  · exact k5t3p2_local_5_eq_row_2 j

  · exact k5t3p2_local_5_eq_row_3 j

  · exact k5t3p2_local_5_eq_row_4 j

private theorem k5t3p2_local_5_paths : ∀ p ∈ k5t3p2_step_5_data.required, p.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_5_data.i k5t3p2_step_5_data.j) 5 := by decide

private theorem k5t3p2_local_5_bad : k5t3p2_step_5_data.bad.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_5_data.i k5t3p2_step_5_data.j) k5t3p2_local_5 5 3 := by decide

private theorem k5t3p2_step_5_check : k5t3p2_step_5.Check k5t3p2.graph k5t3p2_state_5 5 3 := by
  change k5t3p2_step_5_data.Check k5t3p2.graph k5t3p2_state_5 5 3
  refine ⟨k5t3p2_local_5_paths, ?_⟩
  rw [k5t3p2_local_5_eq]
  exact k5t3p2_local_5_bad

private theorem k5t3p2_update_5 : k5t3p2_step_5.apply k5t3p2_state_5 = k5t3p2_state_6 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_5.apply k5t3p2_state_5 i j = k5t3p2_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k5t3p2_state_7 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 3, 4}, Finset.Icc 0 3, Finset.Icc 0 3, {1, 3, 4}],
    #[{1, 3, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[Finset.Icc 0 3, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, {1}, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k5t3p2_local_6 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 3, {1, 2, 3}, {1, 3, 4}],
    #[Finset.Icc 1 4, ∅, {1, 2, 4}, Finset.Icc 0 3, {1}],
    #[Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2, 4}, Finset.Icc 0 3],
    #[{1, 2, 3}, Finset.Icc 0 3, {1, 2, 4}, ∅, {1, 2}],
    #[{1, 3, 4}, {1}, Finset.Icc 0 3, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p2_local_6_eq_row_0 : ∀ j : Fin 5, (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) 0 j = k5t3p2_local_6 0 j := by decide

private theorem k5t3p2_local_6_eq_row_1 : ∀ j : Fin 5, (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) 1 j = k5t3p2_local_6 1 j := by decide

private theorem k5t3p2_local_6_eq_row_2 : ∀ j : Fin 5, (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) 2 j = k5t3p2_local_6 2 j := by decide

private theorem k5t3p2_local_6_eq_row_3 : ∀ j : Fin 5, (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) 3 j = k5t3p2_local_6 3 j := by decide

private theorem k5t3p2_local_6_eq_row_4 : ∀ j : Fin 5, (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) 4 j = k5t3p2_local_6 4 j := by decide

private theorem k5t3p2_local_6_eq : (fun a b => k5t3p2_state_6 a b ∪ requiredMatrix 5 k5t3p2_step_6_data.required a b) = k5t3p2_local_6 := by
  funext i j
  fin_cases i

  · exact k5t3p2_local_6_eq_row_0 j

  · exact k5t3p2_local_6_eq_row_1 j

  · exact k5t3p2_local_6_eq_row_2 j

  · exact k5t3p2_local_6_eq_row_3 j

  · exact k5t3p2_local_6_eq_row_4 j

private theorem k5t3p2_local_6_paths : ∀ p ∈ k5t3p2_step_6_data.required, p.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_6_data.i k5t3p2_step_6_data.j) 5 := by decide

private theorem k5t3p2_local_6_bad : k5t3p2_step_6_data.bad.Check (addedEdgeGraph k5t3p2.graph k5t3p2_step_6_data.i k5t3p2_step_6_data.j) k5t3p2_local_6 5 3 := by decide

private theorem k5t3p2_step_6_check : k5t3p2_step_6.Check k5t3p2.graph k5t3p2_state_6 5 3 := by
  change k5t3p2_step_6_data.Check k5t3p2.graph k5t3p2_state_6 5 3
  refine ⟨k5t3p2_local_6_paths, ?_⟩
  rw [k5t3p2_local_6_eq]
  exact k5t3p2_local_6_bad

private theorem k5t3p2_update_6 : k5t3p2_step_6.apply k5t3p2_state_6 = k5t3p2_state_7 := by
  have h : ∀ i j : Fin 5, k5t3p2_step_6.apply k5t3p2_state_6 i j = k5t3p2_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k5t3p2_closure_7 : ClosureCheck k5t3p2.graph k5t3p2_state_7 5 3 [] := by trivial

private theorem k5t3p2_closure_6 : ClosureCheck k5t3p2.graph k5t3p2_state_6 5 3 [k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_6_check
  · rw [k5t3p2_update_6]
    exact k5t3p2_closure_7

private theorem k5t3p2_closure_5 : ClosureCheck k5t3p2.graph k5t3p2_state_5 5 3 [k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_5_check
  · rw [k5t3p2_update_5]
    exact k5t3p2_closure_6

private theorem k5t3p2_closure_4 : ClosureCheck k5t3p2.graph k5t3p2_state_4 5 3 [k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_4_check
  · rw [k5t3p2_update_4]
    exact k5t3p2_closure_5

private theorem k5t3p2_closure_3 : ClosureCheck k5t3p2.graph k5t3p2_state_3 5 3 [k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_3_check
  · rw [k5t3p2_update_3]
    exact k5t3p2_closure_4

private theorem k5t3p2_closure_2 : ClosureCheck k5t3p2.graph k5t3p2_state_2 5 3 [k5t3p2_step_2, k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_2_check
  · rw [k5t3p2_update_2]
    exact k5t3p2_closure_3

private theorem k5t3p2_closure_1 : ClosureCheck k5t3p2.graph k5t3p2_state_1 5 3 [k5t3p2_step_1, k5t3p2_step_2, k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_1_check
  · rw [k5t3p2_update_1]
    exact k5t3p2_closure_2

private theorem k5t3p2_closure_0 : ClosureCheck k5t3p2.graph k5t3p2_state_0 5 3 [k5t3p2_step_0, k5t3p2_step_1, k5t3p2_step_2, k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] := by
  constructor
  · exact k5t3p2_step_0_check
  · rw [k5t3p2_update_0]
    exact k5t3p2_closure_1

private theorem k5t3p2_matrix_eq : k5t3p2.matrix 5 = k5t3p2_state_7 := by
  change closureMatrix (k5t3p2.initialMatrix 5) _ = _
  rw [k5t3p2_initial_eq]
  change closureMatrix k5t3p2_state_0 [k5t3p2_step_0, k5t3p2_step_1, k5t3p2_step_2, k5t3p2_step_3, k5t3p2_step_4, k5t3p2_step_5, k5t3p2_step_6] = _
  simp only [closureMatrix]
  rw [k5t3p2_update_0, k5t3p2_update_1, k5t3p2_update_2, k5t3p2_update_3, k5t3p2_update_4, k5t3p2_update_5, k5t3p2_update_6]

private theorem k5t3p2_part_0 : k5t3p2.chains.flatten = List.finRange _ := by decide

private theorem k5t3p2_part_1 : k5t3p2.chains.map List.length = ([[], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t3p2_part_2 : k5t3p2.chains.map (fun l => l.map (fun i => decide (i ∈ k5t3p2.clique))) = ([[], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k5t3p2_templates_item_0 : (⟨0, 1, [], [], [], 3, 4⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4], 1, 1⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_2 : (⟨0, 2, [], [], [1], 2, 3⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_3 : (⟨0, 2, [], [], [3, 4], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_4 : (⟨0, 3, [], [], [2, 1], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_5 : (⟨0, 3, [], [], [4], 2, 3⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_6 : (⟨0, 4, [], [], [], 3, 4⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_7 : (⟨0, 4, [], [], [3, 2, 1], 1, 1⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_8 : (⟨1, 2, [], [], [3, 4], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_9 : (⟨1, 3, [], [], [4], 2, 3⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_10 : (⟨2, 3, [], [1], [4], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_11 : (⟨2, 4, [], [1], [], 2, 3⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_templates_item_12 : (⟨3, 4, [], [1, 2], [], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p2_part_3 : ∀ T ∈ k5t3p2.templates, T.Check k5t3p2.graph k5t3p2.clique 5 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k5t3p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t3p2_templates_item_0, k5t3p2_templates_item_1, k5t3p2_templates_item_2, k5t3p2_templates_item_3, k5t3p2_templates_item_4, k5t3p2_templates_item_5, k5t3p2_templates_item_6, k5t3p2_templates_item_7, k5t3p2_templates_item_8, k5t3p2_templates_item_9, k5t3p2_templates_item_10, k5t3p2_templates_item_11, k5t3p2_templates_item_12⟩

private theorem k5t3p2_required_item_0 : (⟨1, 2, []⟩ : RequiredPathData (Fin 5)).Check k5t3p2.graph 5 := by decide

private theorem k5t3p2_required_item_1 : (⟨2, 3, []⟩ : RequiredPathData (Fin 5)).Check k5t3p2.graph 5 := by decide

private theorem k5t3p2_part_4 : ∀ p ∈ k5t3p2.required, p.Check k5t3p2.graph 5 := by
  simp only [k5t3p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t3p2_required_item_0, k5t3p2_required_item_1⟩

private theorem k5t3p2_part_5 : ClosureCheck k5t3p2.graph (k5t3p2.initialMatrix 5) 5 3 k5t3p2.closure := by
  rw [k5t3p2_initial_eq]
  exact k5t3p2_closure_0

private theorem k5t3p2_part_6 : k5t3p2.bad.Check k5t3p2.graph (k5t3p2.matrix 5) 5 3 := by
  rw [k5t3p2_matrix_eq]
  decide

theorem k5t3p2_check : k5t3p2.Check 5 3 [[], [2]] :=
  ⟨k5t3p2_part_0, k5t3p2_part_1, k5t3p2_part_2, k5t3p2_part_3, k5t3p2_part_4, k5t3p2_part_5, k5t3p2_part_6⟩
def k5t3p3 : LayoutCertificate 5 where
  chains := [[0, 1, 2, 3, 4]]
  clique := {0, 2, 4}
  templates := [⟨0, 1, [], [], [2], 1, 3⟩,
    ⟨0, 3, [], [], [2], 1, 3⟩,
    ⟨0, 4, [], [], [], 2, 4⟩,
    ⟨1, 3, [], [0], [2], 1, 2⟩,
    ⟨1, 4, [], [0], [], 1, 3⟩,
    ⟨3, 4, [], [2], [], 1, 3⟩]
  required := [⟨0, 4, [1, 2, 3]⟩]
  closure := []
  bad := ⟨none, {(1, 0), (0, 2), (4, 2), (3, 1)}⟩


private def k5t3p3_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4],
    #[{1, 2, 3}, ∅, ∅, {1, 2}, {1, 2, 3}],
    #[∅, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2}, ∅, ∅, {1, 2, 3}],
    #[Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t3p3_initial_eq_row_0 : ∀ j : Fin 5, (k5t3p3.initialMatrix 5) 0 j = k5t3p3_state_0 0 j := by decide

private theorem k5t3p3_initial_eq_row_1 : ∀ j : Fin 5, (k5t3p3.initialMatrix 5) 1 j = k5t3p3_state_0 1 j := by decide

private theorem k5t3p3_initial_eq_row_2 : ∀ j : Fin 5, (k5t3p3.initialMatrix 5) 2 j = k5t3p3_state_0 2 j := by decide

private theorem k5t3p3_initial_eq_row_3 : ∀ j : Fin 5, (k5t3p3.initialMatrix 5) 3 j = k5t3p3_state_0 3 j := by decide

private theorem k5t3p3_initial_eq_row_4 : ∀ j : Fin 5, (k5t3p3.initialMatrix 5) 4 j = k5t3p3_state_0 4 j := by decide

private theorem k5t3p3_initial_eq : (k5t3p3.initialMatrix 5) = k5t3p3_state_0 := by
  funext i j
  fin_cases i

  · exact k5t3p3_initial_eq_row_0 j

  · exact k5t3p3_initial_eq_row_1 j

  · exact k5t3p3_initial_eq_row_2 j

  · exact k5t3p3_initial_eq_row_3 j

  · exact k5t3p3_initial_eq_row_4 j

private theorem k5t3p3_closure_0 : ClosureCheck k5t3p3.graph k5t3p3_state_0 5 3 [] := by trivial

private theorem k5t3p3_matrix_eq : k5t3p3.matrix 5 = k5t3p3_state_0 := by
  change closureMatrix (k5t3p3.initialMatrix 5) _ = _
  rw [k5t3p3_initial_eq]
  change closureMatrix k5t3p3_state_0 [] = _
  rfl

private theorem k5t3p3_part_0 : k5t3p3.chains.flatten = List.finRange _ := by decide

private theorem k5t3p3_part_1 : k5t3p3.chains.map List.length = ([[1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t3p3_part_2 : k5t3p3.chains.map (fun l => l.map (fun i => decide (i ∈ k5t3p3.clique))) = ([[1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k5t3p3_templates_item_0 : (⟨0, 1, [], [], [2], 1, 3⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_templates_item_1 : (⟨0, 3, [], [], [2], 1, 3⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_templates_item_2 : (⟨0, 4, [], [], [], 2, 4⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_templates_item_3 : (⟨1, 3, [], [0], [2], 1, 2⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_templates_item_4 : (⟨1, 4, [], [0], [], 1, 3⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_templates_item_5 : (⟨3, 4, [], [2], [], 1, 3⟩ : TemplateData (Fin 5)).Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t3p3_part_3 : ∀ T ∈ k5t3p3.templates, T.Check k5t3p3.graph k5t3p3.clique 5 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k5t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t3p3_templates_item_0, k5t3p3_templates_item_1, k5t3p3_templates_item_2, k5t3p3_templates_item_3, k5t3p3_templates_item_4, k5t3p3_templates_item_5⟩

private theorem k5t3p3_required_item_0 : (⟨0, 4, [1, 2, 3]⟩ : RequiredPathData (Fin 5)).Check k5t3p3.graph 5 := by decide

private theorem k5t3p3_part_4 : ∀ p ∈ k5t3p3.required, p.Check k5t3p3.graph 5 := by
  simp only [k5t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact k5t3p3_required_item_0

private theorem k5t3p3_part_5 : ClosureCheck k5t3p3.graph (k5t3p3.initialMatrix 5) 5 3 k5t3p3.closure := by
  rw [k5t3p3_initial_eq]
  exact k5t3p3_closure_0

private theorem k5t3p3_part_6 : k5t3p3.bad.Check k5t3p3.graph (k5t3p3.matrix 5) 5 3 := by
  rw [k5t3p3_matrix_eq]
  decide

theorem k5t3p3_check : k5t3p3.Check 5 3 [[1, 1]] :=
  ⟨k5t3p3_part_0, k5t3p3_part_1, k5t3p3_part_2, k5t3p3_part_3, k5t3p3_part_4, k5t3p3_part_5, k5t3p3_part_6⟩
def k5t4p0 : LayoutCertificate 4 where
  chains := [[0], [1], [2], [3]]
  clique := {0, 1, 2, 3}
  templates := [⟨0, 1, [], [], [], 1, 4⟩,
    ⟨0, 2, [], [], [], 1, 4⟩,
    ⟨0, 3, [], [], [], 1, 4⟩,
    ⟨1, 2, [], [], [], 1, 4⟩,
    ⟨1, 3, [], [], [], 1, 4⟩,
    ⟨2, 3, [], [], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2)}⟩


private def k5t4p0_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t4p0_initial_eq_row_0 : ∀ j : Fin 4, (k5t4p0.initialMatrix 5) 0 j = k5t4p0_state_0 0 j := by decide

private theorem k5t4p0_initial_eq_row_1 : ∀ j : Fin 4, (k5t4p0.initialMatrix 5) 1 j = k5t4p0_state_0 1 j := by decide

private theorem k5t4p0_initial_eq_row_2 : ∀ j : Fin 4, (k5t4p0.initialMatrix 5) 2 j = k5t4p0_state_0 2 j := by decide

private theorem k5t4p0_initial_eq_row_3 : ∀ j : Fin 4, (k5t4p0.initialMatrix 5) 3 j = k5t4p0_state_0 3 j := by decide

private theorem k5t4p0_initial_eq : (k5t4p0.initialMatrix 5) = k5t4p0_state_0 := by
  funext i j
  fin_cases i

  · exact k5t4p0_initial_eq_row_0 j

  · exact k5t4p0_initial_eq_row_1 j

  · exact k5t4p0_initial_eq_row_2 j

  · exact k5t4p0_initial_eq_row_3 j

private theorem k5t4p0_closure_0 : ClosureCheck k5t4p0.graph k5t4p0_state_0 5 4 [] := by trivial

private theorem k5t4p0_matrix_eq : k5t4p0.matrix 5 = k5t4p0_state_0 := by
  change closureMatrix (k5t4p0.initialMatrix 5) _ = _
  rw [k5t4p0_initial_eq]
  change closureMatrix k5t4p0_state_0 [] = _
  rfl

private theorem k5t4p0_part_0 : k5t4p0.chains.flatten = List.finRange _ := by decide

private theorem k5t4p0_part_1 : k5t4p0.chains.map List.length = ([[], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t4p0_part_2 : k5t4p0.chains.map (fun l => l.map (fun i => decide (i ∈ k5t4p0.clique))) = ([[], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k5t4p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_templates_item_3 : (⟨1, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_templates_item_4 : (⟨1, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_templates_item_5 : (⟨2, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 4)).Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p0_part_3 : ∀ T ∈ k5t4p0.templates, T.Check k5t4p0.graph k5t4p0.clique 5 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k5t4p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t4p0_templates_item_0, k5t4p0_templates_item_1, k5t4p0_templates_item_2, k5t4p0_templates_item_3, k5t4p0_templates_item_4, k5t4p0_templates_item_5⟩

private theorem k5t4p0_part_4 : ∀ p ∈ k5t4p0.required, p.Check k5t4p0.graph 5 := by decide

private theorem k5t4p0_part_5 : ClosureCheck k5t4p0.graph (k5t4p0.initialMatrix 5) 5 4 k5t4p0.closure := by
  rw [k5t4p0_initial_eq]
  exact k5t4p0_closure_0

private theorem k5t4p0_part_6 : k5t4p0.bad.Check k5t4p0.graph (k5t4p0.matrix 5) 5 4 := by
  rw [k5t4p0_matrix_eq]
  decide

theorem k5t4p0_check : k5t4p0.Check 5 4 [[], [], [], []] :=
  ⟨k5t4p0_part_0, k5t4p0_part_1, k5t4p0_part_2, k5t4p0_part_3, k5t4p0_part_4, k5t4p0_part_5, k5t4p0_part_6⟩
def k5t4p1 : LayoutCertificate 5 where
  chains := [[0], [1], [2, 3, 4]]
  clique := {0, 1, 2, 4}
  templates := [⟨0, 1, [], [], [], 2, 4⟩,
    ⟨0, 1, [[2, 3, 4]], [], [], 1, 1⟩,
    ⟨0, 2, [], [], [], 2, 4⟩,
    ⟨0, 2, [], [], [3, 4], 1, 2⟩,
    ⟨0, 3, [], [], [2], 1, 3⟩,
    ⟨0, 4, [], [], [], 2, 4⟩,
    ⟨0, 4, [], [], [3, 2], 1, 2⟩,
    ⟨1, 2, [], [], [], 2, 4⟩,
    ⟨1, 2, [], [], [3, 4], 1, 2⟩,
    ⟨1, 3, [], [], [2], 1, 3⟩,
    ⟨2, 3, [], [], [4], 1, 3⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 1), (2, 1), (3, 0)}⟩


private def k5t4p1_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 4],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, {1, 2, 3}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, {1, 2, 3}, {1, 2, 3}, ∅, ∅],
    #[Finset.Icc 1 4, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t4p1_initial_eq_row_0 : ∀ j : Fin 5, (k5t4p1.initialMatrix 5) 0 j = k5t4p1_state_0 0 j := by decide

private theorem k5t4p1_initial_eq_row_1 : ∀ j : Fin 5, (k5t4p1.initialMatrix 5) 1 j = k5t4p1_state_0 1 j := by decide

private theorem k5t4p1_initial_eq_row_2 : ∀ j : Fin 5, (k5t4p1.initialMatrix 5) 2 j = k5t4p1_state_0 2 j := by decide

private theorem k5t4p1_initial_eq_row_3 : ∀ j : Fin 5, (k5t4p1.initialMatrix 5) 3 j = k5t4p1_state_0 3 j := by decide

private theorem k5t4p1_initial_eq_row_4 : ∀ j : Fin 5, (k5t4p1.initialMatrix 5) 4 j = k5t4p1_state_0 4 j := by decide

private theorem k5t4p1_initial_eq : (k5t4p1.initialMatrix 5) = k5t4p1_state_0 := by
  funext i j
  fin_cases i

  · exact k5t4p1_initial_eq_row_0 j

  · exact k5t4p1_initial_eq_row_1 j

  · exact k5t4p1_initial_eq_row_2 j

  · exact k5t4p1_initial_eq_row_3 j

  · exact k5t4p1_initial_eq_row_4 j

private theorem k5t4p1_closure_0 : ClosureCheck k5t4p1.graph k5t4p1_state_0 5 4 [] := by trivial

private theorem k5t4p1_matrix_eq : k5t4p1.matrix 5 = k5t4p1_state_0 := by
  change closureMatrix (k5t4p1.initialMatrix 5) _ = _
  rw [k5t4p1_initial_eq]
  change closureMatrix k5t4p1_state_0 [] = _
  rfl

private theorem k5t4p1_part_0 : k5t4p1.chains.flatten = List.finRange _ := by decide

private theorem k5t4p1_part_1 : k5t4p1.chains.map List.length = ([[], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t4p1_part_2 : k5t4p1.chains.map (fun l => l.map (fun i => decide (i ∈ k5t4p1.clique))) = ([[], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k5t4p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 4⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_1 : (⟨0, 1, [[2, 3, 4]], [], [], 1, 1⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 4⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_3 : (⟨0, 2, [], [], [3, 4], 1, 2⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_4 : (⟨0, 3, [], [], [2], 1, 3⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_5 : (⟨0, 4, [], [], [], 2, 4⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_6 : (⟨0, 4, [], [], [3, 2], 1, 2⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_7 : (⟨1, 2, [], [], [], 2, 4⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_8 : (⟨1, 2, [], [], [3, 4], 1, 2⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_9 : (⟨1, 3, [], [], [2], 1, 3⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_templates_item_10 : (⟨2, 3, [], [], [4], 1, 3⟩ : TemplateData (Fin 5)).Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t4p1_part_3 : ∀ T ∈ k5t4p1.templates, T.Check k5t4p1.graph k5t4p1.clique 5 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k5t4p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t4p1_templates_item_0, k5t4p1_templates_item_1, k5t4p1_templates_item_2, k5t4p1_templates_item_3, k5t4p1_templates_item_4, k5t4p1_templates_item_5, k5t4p1_templates_item_6, k5t4p1_templates_item_7, k5t4p1_templates_item_8, k5t4p1_templates_item_9, k5t4p1_templates_item_10⟩

private theorem k5t4p1_part_4 : ∀ p ∈ k5t4p1.required, p.Check k5t4p1.graph 5 := by decide

private theorem k5t4p1_part_5 : ClosureCheck k5t4p1.graph (k5t4p1.initialMatrix 5) 5 4 k5t4p1.closure := by
  rw [k5t4p1_initial_eq]
  exact k5t4p1_closure_0

private theorem k5t4p1_part_6 : k5t4p1.bad.Check k5t4p1.graph (k5t4p1.matrix 5) 5 4 := by
  rw [k5t4p1_matrix_eq]
  decide

theorem k5t4p1_check : k5t4p1.Check 5 4 [[], [], [1]] :=
  ⟨k5t4p1_part_0, k5t4p1_part_1, k5t4p1_part_2, k5t4p1_part_3, k5t4p1_part_4, k5t4p1_part_5, k5t4p1_part_6⟩
def k5t5p0 : LayoutCertificate 5 where
  chains := [[0], [1], [2], [3], [4]]
  clique := {0, 1, 2, 3, 4}
  templates := [⟨0, 1, [], [], [], 1, 4⟩,
    ⟨0, 2, [], [], [], 1, 4⟩,
    ⟨0, 3, [], [], [], 1, 4⟩,
    ⟨0, 4, [], [], [], 1, 4⟩,
    ⟨1, 2, [], [], [], 1, 4⟩,
    ⟨1, 3, [], [], [], 1, 4⟩,
    ⟨1, 4, [], [], [], 1, 4⟩,
    ⟨2, 3, [], [], [], 1, 4⟩,
    ⟨2, 4, [], [], [], 1, 4⟩,
    ⟨3, 4, [], [], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 1), (1, 1), (2, 1), (3, 1), (4, 3)}⟩


private def k5t5p0_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k5t5p0_initial_eq_row_0 : ∀ j : Fin 5, (k5t5p0.initialMatrix 5) 0 j = k5t5p0_state_0 0 j := by decide

private theorem k5t5p0_initial_eq_row_1 : ∀ j : Fin 5, (k5t5p0.initialMatrix 5) 1 j = k5t5p0_state_0 1 j := by decide

private theorem k5t5p0_initial_eq_row_2 : ∀ j : Fin 5, (k5t5p0.initialMatrix 5) 2 j = k5t5p0_state_0 2 j := by decide

private theorem k5t5p0_initial_eq_row_3 : ∀ j : Fin 5, (k5t5p0.initialMatrix 5) 3 j = k5t5p0_state_0 3 j := by decide

private theorem k5t5p0_initial_eq_row_4 : ∀ j : Fin 5, (k5t5p0.initialMatrix 5) 4 j = k5t5p0_state_0 4 j := by decide

private theorem k5t5p0_initial_eq : (k5t5p0.initialMatrix 5) = k5t5p0_state_0 := by
  funext i j
  fin_cases i

  · exact k5t5p0_initial_eq_row_0 j

  · exact k5t5p0_initial_eq_row_1 j

  · exact k5t5p0_initial_eq_row_2 j

  · exact k5t5p0_initial_eq_row_3 j

  · exact k5t5p0_initial_eq_row_4 j

private theorem k5t5p0_closure_0 : ClosureCheck k5t5p0.graph k5t5p0_state_0 5 5 [] := by trivial

private theorem k5t5p0_matrix_eq : k5t5p0.matrix 5 = k5t5p0_state_0 := by
  change closureMatrix (k5t5p0.initialMatrix 5) _ = _
  rw [k5t5p0_initial_eq]
  change closureMatrix k5t5p0_state_0 [] = _
  rfl

private theorem k5t5p0_part_0 : k5t5p0.chains.flatten = List.finRange _ := by decide

private theorem k5t5p0_part_1 : k5t5p0.chains.map List.length = ([[], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k5t5p0_part_2 : k5t5p0.chains.map (fun l => l.map (fun i => decide (i ∈ k5t5p0.clique))) = ([[], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k5t5p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_4 : (⟨1, 2, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_5 : (⟨1, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_6 : (⟨1, 4, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_7 : (⟨2, 3, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_8 : (⟨2, 4, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_templates_item_9 : (⟨3, 4, [], [], [], 1, 4⟩ : TemplateData (Fin 5)).Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k5t5p0_part_3 : ∀ T ∈ k5t5p0.templates, T.Check k5t5p0.graph k5t5p0.clique 5 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k5t5p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k5t5p0_templates_item_0, k5t5p0_templates_item_1, k5t5p0_templates_item_2, k5t5p0_templates_item_3, k5t5p0_templates_item_4, k5t5p0_templates_item_5, k5t5p0_templates_item_6, k5t5p0_templates_item_7, k5t5p0_templates_item_8, k5t5p0_templates_item_9⟩

private theorem k5t5p0_part_4 : ∀ p ∈ k5t5p0.required, p.Check k5t5p0.graph 5 := by decide

private theorem k5t5p0_part_5 : ClosureCheck k5t5p0.graph (k5t5p0.initialMatrix 5) 5 5 k5t5p0.closure := by
  rw [k5t5p0_initial_eq]
  exact k5t5p0_closure_0

private theorem k5t5p0_part_6 : k5t5p0.bad.Check k5t5p0.graph (k5t5p0.matrix 5) 5 5 := by
  rw [k5t5p0_matrix_eq]
  decide

theorem k5t5p0_check : k5t5p0.Check 5 5 [[], [], [], [], []] :=
  ⟨k5t5p0_part_0, k5t5p0_part_1, k5t5p0_part_2, k5t5p0_part_3, k5t5p0_part_4, k5t5p0_part_5, k5t5p0_part_6⟩
end CycleClique.Construction.Certificates

end OAI
