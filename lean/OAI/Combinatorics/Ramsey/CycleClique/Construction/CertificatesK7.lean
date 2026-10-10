import OAI.Combinatorics.Ramsey.CycleClique.Construction.LayoutCertificate
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CertificateMatrixChunks
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastCertificateMatrix
import OAI.Combinatorics.Ramsey.CycleClique.Construction.FastLayoutGraph

namespace OAI

namespace CycleClique.Construction.Certificates

def k7t3p0 : LayoutCertificate 3 where
  chains := [[0], [1], [2]]
  clique := {0, 1, 2}
  templates := [⟨0, 1, [], [], [], 1, 6⟩,
    ⟨0, 2, [], [], [], 1, 6⟩,
    ⟨1, 2, [], [], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2)}⟩


private def k7t3p0_state_0 : ForbiddenMatrix 3 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p0_initial_eq_row_0 : ∀ j : Fin 3, (k7t3p0.initialMatrix 7) 0 j = k7t3p0_state_0 0 j := by decide

private theorem k7t3p0_initial_eq_row_1 : ∀ j : Fin 3, (k7t3p0.initialMatrix 7) 1 j = k7t3p0_state_0 1 j := by decide

private theorem k7t3p0_initial_eq_row_2 : ∀ j : Fin 3, (k7t3p0.initialMatrix 7) 2 j = k7t3p0_state_0 2 j := by decide

private theorem k7t3p0_initial_eq : (k7t3p0.initialMatrix 7) = k7t3p0_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p0_initial_eq_row_0 j

  · exact k7t3p0_initial_eq_row_1 j

  · exact k7t3p0_initial_eq_row_2 j

private theorem k7t3p0_closure_0 : ClosureCheck k7t3p0.graph k7t3p0_state_0 7 3 [] := by trivial

private theorem k7t3p0_matrix_eq : k7t3p0.matrix 7 = k7t3p0_state_0 := by
  change closureMatrix (k7t3p0.initialMatrix 7) _ = _
  rw [k7t3p0_initial_eq]
  change closureMatrix k7t3p0_state_0 [] = _
  rfl

private theorem k7t3p0_part_0 : k7t3p0.chains.flatten = List.finRange _ := by decide

private theorem k7t3p0_part_1 : k7t3p0.chains.map List.length = ([[], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p0_part_2 : k7t3p0.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p0.clique))) = ([[], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 6⟩ : TemplateData (Fin 3)).Check k7t3p0.graph k7t3p0.clique 7 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 3)).Check k7t3p0.graph k7t3p0.clique 7 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p0_templates_item_2 : (⟨1, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 3)).Check k7t3p0.graph k7t3p0.clique 7 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p0_part_3 : ∀ T ∈ k7t3p0.templates, T.Check k7t3p0.graph k7t3p0.clique 7 (patternAmount ([[], [], []] : List (List ℕ))) (([[], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p0_templates_item_0, k7t3p0_templates_item_1, k7t3p0_templates_item_2⟩

private theorem k7t3p0_part_4 : ∀ p ∈ k7t3p0.required, p.Check k7t3p0.graph 7 := by decide

private theorem k7t3p0_part_5 : ClosureCheck k7t3p0.graph (k7t3p0.initialMatrix 7) 7 3 k7t3p0.closure := by
  rw [k7t3p0_initial_eq]
  exact k7t3p0_closure_0

private theorem k7t3p0_part_6 : k7t3p0.bad.Check k7t3p0.graph (k7t3p0.matrix 7) 7 3 := by
  rw [k7t3p0_matrix_eq]
  decide

theorem k7t3p0_check : k7t3p0.Check 7 3 [[], [], []] :=
  ⟨k7t3p0_part_0, k7t3p0_part_1, k7t3p0_part_2, k7t3p0_part_3, k7t3p0_part_4, k7t3p0_part_5, k7t3p0_part_6⟩
def k7t3p1 : LayoutCertificate 4 where
  chains := [[0], [1, 2, 3]]
  clique := {0, 1, 3}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [], [], [2, 3], 1, 4⟩,
    ⟨0, 2, [], [], [1], 1, 5⟩,
    ⟨0, 3, [], [], [2, 1], 1, 4⟩,
    ⟨1, 2, [], [], [3], 1, 5⟩,
    ⟨2, 3, [], [1], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (2, 2), (1, 2)}⟩


private def k7t3p1_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 4],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p1_initial_eq_row_0 : ∀ j : Fin 4, (k7t3p1.initialMatrix 7) 0 j = k7t3p1_state_0 0 j := by decide

private theorem k7t3p1_initial_eq_row_1 : ∀ j : Fin 4, (k7t3p1.initialMatrix 7) 1 j = k7t3p1_state_0 1 j := by decide

private theorem k7t3p1_initial_eq_row_2 : ∀ j : Fin 4, (k7t3p1.initialMatrix 7) 2 j = k7t3p1_state_0 2 j := by decide

private theorem k7t3p1_initial_eq_row_3 : ∀ j : Fin 4, (k7t3p1.initialMatrix 7) 3 j = k7t3p1_state_0 3 j := by decide

private theorem k7t3p1_initial_eq : (k7t3p1.initialMatrix 7) = k7t3p1_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p1_initial_eq_row_0 j

  · exact k7t3p1_initial_eq_row_1 j

  · exact k7t3p1_initial_eq_row_2 j

  · exact k7t3p1_initial_eq_row_3 j

private theorem k7t3p1_closure_0 : ClosureCheck k7t3p1.graph k7t3p1_state_0 7 3 [] := by trivial

private theorem k7t3p1_matrix_eq : k7t3p1.matrix 7 = k7t3p1_state_0 := by
  change closureMatrix (k7t3p1.initialMatrix 7) _ = _
  rw [k7t3p1_initial_eq]
  change closureMatrix k7t3p1_state_0 [] = _
  rfl

private theorem k7t3p1_part_0 : k7t3p1.chains.flatten = List.finRange _ := by decide

private theorem k7t3p1_part_1 : k7t3p1.chains.map List.length = ([[], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p1_part_2 : k7t3p1.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p1.clique))) = ([[], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_templates_item_1 : (⟨0, 1, [], [], [2, 3], 1, 4⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_templates_item_2 : (⟨0, 2, [], [], [1], 1, 5⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_templates_item_3 : (⟨0, 3, [], [], [2, 1], 1, 4⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_templates_item_4 : (⟨1, 2, [], [], [3], 1, 5⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_templates_item_5 : (⟨2, 3, [], [1], [], 1, 5⟩ : TemplateData (Fin 4)).Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p1_part_3 : ∀ T ∈ k7t3p1.templates, T.Check k7t3p1.graph k7t3p1.clique 7 (patternAmount ([[], [1]] : List (List ℕ))) (([[], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p1_templates_item_0, k7t3p1_templates_item_1, k7t3p1_templates_item_2, k7t3p1_templates_item_3, k7t3p1_templates_item_4, k7t3p1_templates_item_5⟩

private theorem k7t3p1_part_4 : ∀ p ∈ k7t3p1.required, p.Check k7t3p1.graph 7 := by decide

private theorem k7t3p1_part_5 : ClosureCheck k7t3p1.graph (k7t3p1.initialMatrix 7) 7 3 k7t3p1.closure := by
  rw [k7t3p1_initial_eq]
  exact k7t3p1_closure_0

private theorem k7t3p1_part_6 : k7t3p1.bad.Check k7t3p1.graph (k7t3p1.matrix 7) 7 3 := by
  rw [k7t3p1_matrix_eq]
  decide

theorem k7t3p1_check : k7t3p1.Check 7 3 [[], [1]] :=
  ⟨k7t3p1_part_0, k7t3p1_part_1, k7t3p1_part_2, k7t3p1_part_3, k7t3p1_part_4, k7t3p1_part_5, k7t3p1_part_6⟩
def k7t3p2 : LayoutCertificate 5 where
  chains := [[0], [1, 2, 3, 4]]
  clique := {0, 1, 4}
  templates := [⟨0, 1, [], [], [2, 3, 4], 1, 3⟩,
    ⟨0, 2, [], [], [1], 2, 5⟩,
    ⟨0, 2, [], [], [3, 4], 1, 4⟩,
    ⟨0, 3, [], [], [2, 1], 1, 4⟩,
    ⟨0, 4, [], [], [3, 2, 1], 1, 3⟩,
    ⟨1, 2, [], [], [3, 4], 1, 4⟩,
    ⟨2, 3, [], [1], [4], 1, 4⟩,
    ⟨3, 4, [], [1, 2], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (2, 2), (3, 2)}⟩


private def k7t3p2_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, {1, 2, 3}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[{1, 2, 3}, ∅, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[{1, 2, 3}, ∅, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p2_initial_eq_row_0 : ∀ j : Fin 5, (k7t3p2.initialMatrix 7) 0 j = k7t3p2_state_0 0 j := by decide

private theorem k7t3p2_initial_eq_row_1 : ∀ j : Fin 5, (k7t3p2.initialMatrix 7) 1 j = k7t3p2_state_0 1 j := by decide

private theorem k7t3p2_initial_eq_row_2 : ∀ j : Fin 5, (k7t3p2.initialMatrix 7) 2 j = k7t3p2_state_0 2 j := by decide

private theorem k7t3p2_initial_eq_row_3 : ∀ j : Fin 5, (k7t3p2.initialMatrix 7) 3 j = k7t3p2_state_0 3 j := by decide

private theorem k7t3p2_initial_eq_row_4 : ∀ j : Fin 5, (k7t3p2.initialMatrix 7) 4 j = k7t3p2_state_0 4 j := by decide

private theorem k7t3p2_initial_eq : (k7t3p2.initialMatrix 7) = k7t3p2_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p2_initial_eq_row_0 j

  · exact k7t3p2_initial_eq_row_1 j

  · exact k7t3p2_initial_eq_row_2 j

  · exact k7t3p2_initial_eq_row_3 j

  · exact k7t3p2_initial_eq_row_4 j

private theorem k7t3p2_closure_0 : ClosureCheck k7t3p2.graph k7t3p2_state_0 7 3 [] := by trivial

private theorem k7t3p2_matrix_eq : k7t3p2.matrix 7 = k7t3p2_state_0 := by
  change closureMatrix (k7t3p2.initialMatrix 7) _ = _
  rw [k7t3p2_initial_eq]
  change closureMatrix k7t3p2_state_0 [] = _
  rfl

private theorem k7t3p2_part_0 : k7t3p2.chains.flatten = List.finRange _ := by decide

private theorem k7t3p2_part_1 : k7t3p2.chains.map List.length = ([[], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p2_part_2 : k7t3p2.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p2.clique))) = ([[], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p2_templates_item_0 : (⟨0, 1, [], [], [2, 3, 4], 1, 3⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_1 : (⟨0, 2, [], [], [1], 2, 5⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_2 : (⟨0, 2, [], [], [3, 4], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_3 : (⟨0, 3, [], [], [2, 1], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_4 : (⟨0, 4, [], [], [3, 2, 1], 1, 3⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_5 : (⟨1, 2, [], [], [3, 4], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_6 : (⟨2, 3, [], [1], [4], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_templates_item_7 : (⟨3, 4, [], [1, 2], [], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p2_part_3 : ∀ T ∈ k7t3p2.templates, T.Check k7t3p2.graph k7t3p2.clique 7 (patternAmount ([[], [2]] : List (List ℕ))) (([[], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p2_templates_item_0, k7t3p2_templates_item_1, k7t3p2_templates_item_2, k7t3p2_templates_item_3, k7t3p2_templates_item_4, k7t3p2_templates_item_5, k7t3p2_templates_item_6, k7t3p2_templates_item_7⟩

private theorem k7t3p2_part_4 : ∀ p ∈ k7t3p2.required, p.Check k7t3p2.graph 7 := by decide

private theorem k7t3p2_part_5 : ClosureCheck k7t3p2.graph (k7t3p2.initialMatrix 7) 7 3 k7t3p2.closure := by
  rw [k7t3p2_initial_eq]
  exact k7t3p2_closure_0

private theorem k7t3p2_part_6 : k7t3p2.bad.Check k7t3p2.graph (k7t3p2.matrix 7) 7 3 := by
  rw [k7t3p2_matrix_eq]
  decide

theorem k7t3p2_check : k7t3p2.Check 7 3 [[], [2]] :=
  ⟨k7t3p2_part_0, k7t3p2_part_1, k7t3p2_part_2, k7t3p2_part_3, k7t3p2_part_4, k7t3p2_part_5, k7t3p2_part_6⟩
private def k7t3p3_step_0_data : FreshAttachmentData 6 := ⟨3, 0, [⟨1, 2, [0, 4, 3]⟩, ⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 6, [2, 1, 0, 4, 5]⟩, ⟨3, 5, [2, 6, 1, 0, 4]⟩, ⟨5, 0, [4, 3, 2, 6, 1]⟩, ⟨5, 2, [4, 0, 1, 6]⟩, ⟨5, 3, [4, 0, 1, 6, 2]⟩, ⟨5, 2, [6, 1, 0, 4, 3]⟩], ⟨none, {(1, 3), (3, 2), (5, 2), (2, 1)}⟩⟩

private def k7t3p3_step_0 : ClosureStep 6 := .fresh k7t3p3_step_0_data

private def k7t3p3_step_1_data : FreshAttachmentData 6 := ⟨3, 1, [⟨1, 0, [2, 3, 4]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨1, 0, [6, 5, 4, 3, 2]⟩, ⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 0, [2, 6, 5, 4]⟩, ⟨3, 5, [4, 0, 2, 1, 6]⟩, ⟨5, 0, [6, 1, 2, 3, 4]⟩, ⟨5, 3, [6, 1, 2, 0, 4]⟩, ⟨5, 0, [6, 2, 3, 4]⟩], ⟨none, {(5, 2), (3, 2), (1, 3), (0, 0)}⟩⟩

private def k7t3p3_step_1 : ClosureStep 6 := .fresh k7t3p3_step_1_data

private def k7t3p3_step_2_data : FreshAttachmentData 6 := ⟨4, 1, [⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 0, [2, 6, 5]⟩, ⟨1, 0, [2]⟩, ⟨1, 0, [6, 2, 3, 4, 5]⟩, ⟨1, 0, [6, 2]⟩, ⟨1, 4, [6, 5, 0, 2, 3]⟩, ⟨3, 0, [2, 1, 6, 5]⟩, ⟨3, 0, [2, 6, 5]⟩, ⟨3, 0, [4, 5, 6, 1, 2]⟩, ⟨3, 0, [4, 5]⟩, ⟨3, 6, [4, 5, 0, 2, 1]⟩, ⟨0, 4, [2, 1, 6, 5]⟩, ⟨0, 3, [2, 1, 6, 5, 4]⟩, ⟨0, 1, [2, 3, 4, 5, 6]⟩, ⟨0, 6, [5, 4, 3, 2, 1]⟩, ⟨0, 4, [5, 6, 1, 2, 3]⟩], ⟨none, {(1, 3), (3, 2), (0, 2), (4, 0)}⟩⟩

private def k7t3p3_step_2 : ClosureStep 6 := .fresh k7t3p3_step_2_data

private def k7t3p3_step_3_data : FreshAttachmentData 6 := ⟨5, 2, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 0, [2, 3]⟩, ⟨1, 4, [2, 3, 0, 6, 5]⟩, ⟨1, 0, [6, 2, 3]⟩, ⟨1, 0, [6, 5, 4, 3]⟩, ⟨1, 0, [6]⟩, ⟨5, 0, [4, 3, 2, 1, 6]⟩, ⟨5, 0, [4, 3, 2, 6]⟩, ⟨5, 0, [4, 3]⟩, ⟨5, 2, [4, 3, 0, 6, 1]⟩, ⟨5, 0, [6, 2, 3]⟩, ⟨0, 4, [3, 2, 1, 6, 5]⟩, ⟨0, 4, [3, 2, 6, 5]⟩, ⟨0, 2, [3, 4, 5, 6, 1]⟩, ⟨0, 1, [3, 4, 5, 6, 2]⟩, ⟨0, 5, [6, 1, 2, 3, 4]⟩], ⟨none, {(1, 3), (5, 2), (0, 2), (4, 0)}⟩⟩

private def k7t3p3_step_3 : ClosureStep 6 := .fresh k7t3p3_step_3_data

private def k7t3p3_step_4_data : FreshAttachmentData 6 := ⟨5, 3, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 0, [2, 3, 4]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨3, 0, [2, 1, 6, 5, 4]⟩, ⟨3, 5, [2, 1, 6, 0, 4]⟩, ⟨3, 0, [2, 6, 5, 4]⟩, ⟨5, 0, [4, 3, 2, 1, 6]⟩, ⟨5, 0, [4, 3, 2, 6]⟩, ⟨5, 3, [4, 0, 6, 1, 2]⟩], ⟨none, {(3, 2), (5, 2), (1, 3), (0, 0)}⟩⟩

private def k7t3p3_step_4 : ClosureStep 6 := .fresh k7t3p3_step_4_data

private def k7t3p3_step_5_data : EdgeAttachmentData 6 := ⟨2, 0, [⟨0, 3, [2]⟩, ⟨0, 5, [2, 3, 4]⟩], ⟨none, {(0, 3), (3, 2), (5, 3)}⟩⟩

private def k7t3p3_step_5 : ClosureStep 6 := .edge k7t3p3_step_5_data

private def k7t3p3_step_6_data : EdgeAttachmentData 6 := ⟨3, 0, [⟨0, 1, [3, 4, 5]⟩, ⟨1, 4, [2, 3, 0, 5]⟩], ⟨none, {(0, 3), (1, 3), (4, 2)}⟩⟩

private def k7t3p3_step_6 : ClosureStep 6 := .edge k7t3p3_step_6_data

private def k7t3p3_step_7_data : EdgeAttachmentData 6 := ⟨3, 1, [⟨0, 3, [1]⟩, ⟨0, 1, [5, 4, 3]⟩], ⟨none, {(0, 3), (3, 2), (1, 3)}⟩⟩

private def k7t3p3_step_7 : ClosureStep 6 := .edge k7t3p3_step_7_data

private def k7t3p3_step_8_data : EdgeAttachmentData 6 := ⟨4, 0, [⟨0, 3, [4]⟩, ⟨0, 1, [4, 3, 2]⟩], ⟨none, {(0, 3), (3, 2), (1, 3)}⟩⟩

private def k7t3p3_step_8 : ClosureStep 6 := .edge k7t3p3_step_8_data

private def k7t3p3_step_9_data : EdgeAttachmentData 6 := ⟨4, 2, [⟨0, 1, [5, 4, 2]⟩, ⟨1, 2, [5, 4]⟩], ⟨none, {(0, 3), (1, 3), (3, 0), (2, 1)}⟩⟩

private def k7t3p3_step_9 : ClosureStep 6 := .edge k7t3p3_step_9_data

private def k7t3p3_step_10_data : EdgeAttachmentData 6 := ⟨5, 3, [⟨0, 5, [1, 2, 3]⟩, ⟨0, 3, [5]⟩], ⟨none, {(0, 3), (3, 2), (5, 3)}⟩⟩

private def k7t3p3_step_10 : ClosureStep 6 := .edge k7t3p3_step_10_data

def k7t3p3 : LayoutCertificate 6 where
  chains := [[0], [1, 2, 3, 4, 5]]
  clique := {0, 1, 5}
  templates := [⟨0, 1, [], [], [], 4, 6⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩,
    ⟨0, 2, [], [], [1], 3, 5⟩,
    ⟨0, 2, [], [], [3, 4, 5], 1, 3⟩,
    ⟨0, 3, [], [], [2, 1], 2, 4⟩,
    ⟨0, 4, [], [], [3, 2, 1], 1, 3⟩,
    ⟨0, 4, [], [], [5], 3, 5⟩,
    ⟨0, 5, [], [], [], 4, 6⟩,
    ⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩,
    ⟨1, 2, [], [], [3, 4, 5], 1, 3⟩,
    ⟨1, 3, [], [], [4, 5], 2, 4⟩,
    ⟨1, 4, [], [], [5], 3, 5⟩,
    ⟨2, 3, [], [1], [4, 5], 1, 3⟩,
    ⟨2, 4, [], [1], [5], 2, 4⟩,
    ⟨3, 4, [], [1, 2], [5], 1, 3⟩,
    ⟨3, 5, [], [1, 2], [], 2, 4⟩,
    ⟨4, 5, [], [1, 2, 3], [], 1, 3⟩]
  required := [⟨1, 3, [2]⟩,
    ⟨3, 5, [4]⟩]
  closure := [k7t3p3_step_0, k7t3p3_step_1, k7t3p3_step_2, k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10]
  bad := ⟨none, {(3, 2), (0, 2), (2, 1)}⟩


private def k7t3p3_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, ∅],
    #[{2, 3, 4}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_initial_eq_row_0 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 0 j = k7t3p3_state_0 0 j := by decide

private theorem k7t3p3_initial_eq_row_1 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 1 j = k7t3p3_state_0 1 j := by decide

private theorem k7t3p3_initial_eq_row_2 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 2 j = k7t3p3_state_0 2 j := by decide

private theorem k7t3p3_initial_eq_row_3 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 3 j = k7t3p3_state_0 3 j := by decide

private theorem k7t3p3_initial_eq_row_4 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 4 j = k7t3p3_state_0 4 j := by decide

private theorem k7t3p3_initial_eq_row_5 : ∀ j : Fin 6, (k7t3p3.initialMatrix 7) 5 j = k7t3p3_state_0 5 j := by decide

private theorem k7t3p3_initial_eq : (k7t3p3.initialMatrix 7) = k7t3p3_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p3_initial_eq_row_0 j

  · exact k7t3p3_initial_eq_row_1 j

  · exact k7t3p3_initial_eq_row_2 j

  · exact k7t3p3_initial_eq_row_3 j

  · exact k7t3p3_initial_eq_row_4 j

  · exact k7t3p3_initial_eq_row_5 j

private def k7t3p3_state_1 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, ∅, ∅, {1}, ∅, {1}, ∅],
    #[∅, ∅, Finset.Icc 1 6, Finset.Icc 1 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[∅, Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 2 5, Finset.Icc 1 5, ∅],
    #[{1}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4, {1}],
    #[∅, {2, 3, 4}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[{1}, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_0_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 0 j = k7t3p3_local_0 0 j := by decide

private theorem k7t3p3_local_0_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 1 j = k7t3p3_local_0 1 j := by decide

private theorem k7t3p3_local_0_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 2 j = k7t3p3_local_0 2 j := by decide

private theorem k7t3p3_local_0_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 3 j = k7t3p3_local_0 3 j := by decide

private theorem k7t3p3_local_0_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 4 j = k7t3p3_local_0 4 j := by decide

private theorem k7t3p3_local_0_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 5 j = k7t3p3_local_0 5 j := by decide

private theorem k7t3p3_local_0_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) 6 j = k7t3p3_local_0 6 j := by decide

private theorem k7t3p3_local_0_eq : (fun a b => freshMatrix k7t3p3_state_0 a b ∪ requiredMatrix 7 k7t3p3_step_0_data.required a b) = k7t3p3_local_0 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_0_eq_row_0 j

  · exact k7t3p3_local_0_eq_row_1 j

  · exact k7t3p3_local_0_eq_row_2 j

  · exact k7t3p3_local_0_eq_row_3 j

  · exact k7t3p3_local_0_eq_row_4 j

  · exact k7t3p3_local_0_eq_row_5 j

  · exact k7t3p3_local_0_eq_row_6 j

private theorem k7t3p3_local_0_paths : ∀ p ∈ k7t3p3_step_0_data.required, p.Check (freshGraph k7t3p3.graph k7t3p3_step_0_data.i k7t3p3_step_0_data.j) 7 := by decide

private theorem k7t3p3_local_0_bad : k7t3p3_step_0_data.bad.Check (freshGraph k7t3p3.graph k7t3p3_step_0_data.i k7t3p3_step_0_data.j) k7t3p3_local_0 7 3 := by decide

private theorem k7t3p3_step_0_check : k7t3p3_step_0.Check k7t3p3.graph k7t3p3_state_0 7 3 := by
  change k7t3p3_step_0_data.Check k7t3p3.graph k7t3p3_state_0 7 3
  refine ⟨by decide, k7t3p3_local_0_paths, ?_⟩
  rw [k7t3p3_local_0_eq]
  exact k7t3p3_local_0_bad

private theorem k7t3p3_update_0 : k7t3p3_step_0.apply k7t3p3_state_0 = k7t3p3_state_1 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_0.apply k7t3p3_state_0 i j = k7t3p3_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_2 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 2, 3}, ∅, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 3}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[∅, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}, ∅],
    #[{1, 2}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4, ∅],
    #[∅, Finset.Icc 1 4, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[{1, 2}, Finset.Icc 1 5, {3, 4, 5}, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_1_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 0 j = k7t3p3_local_1 0 j := by decide

private theorem k7t3p3_local_1_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 1 j = k7t3p3_local_1 1 j := by decide

private theorem k7t3p3_local_1_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 2 j = k7t3p3_local_1 2 j := by decide

private theorem k7t3p3_local_1_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 3 j = k7t3p3_local_1 3 j := by decide

private theorem k7t3p3_local_1_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 4 j = k7t3p3_local_1 4 j := by decide

private theorem k7t3p3_local_1_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 5 j = k7t3p3_local_1 5 j := by decide

private theorem k7t3p3_local_1_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) 6 j = k7t3p3_local_1 6 j := by decide

private theorem k7t3p3_local_1_eq : (fun a b => freshMatrix k7t3p3_state_1 a b ∪ requiredMatrix 7 k7t3p3_step_1_data.required a b) = k7t3p3_local_1 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_1_eq_row_0 j

  · exact k7t3p3_local_1_eq_row_1 j

  · exact k7t3p3_local_1_eq_row_2 j

  · exact k7t3p3_local_1_eq_row_3 j

  · exact k7t3p3_local_1_eq_row_4 j

  · exact k7t3p3_local_1_eq_row_5 j

  · exact k7t3p3_local_1_eq_row_6 j

private theorem k7t3p3_local_1_paths : ∀ p ∈ k7t3p3_step_1_data.required, p.Check (freshGraph k7t3p3.graph k7t3p3_step_1_data.i k7t3p3_step_1_data.j) 7 := by decide

private theorem k7t3p3_local_1_bad : k7t3p3_step_1_data.bad.Check (freshGraph k7t3p3.graph k7t3p3_step_1_data.i k7t3p3_step_1_data.j) k7t3p3_local_1 7 3 := by decide

private theorem k7t3p3_step_1_check : k7t3p3_step_1.Check k7t3p3.graph k7t3p3_state_1 7 3 := by
  change k7t3p3_step_1_data.Check k7t3p3.graph k7t3p3_state_1 7 3
  refine ⟨by decide, k7t3p3_local_1_paths, ?_⟩
  rw [k7t3p3_local_1_eq]
  exact k7t3p3_local_1_bad

private theorem k7t3p3_update_1 : k7t3p3_step_1.apply k7t3p3_state_1 = k7t3p3_state_2 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_1.apply k7t3p3_state_1 i j = k7t3p3_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_3 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 4, {1, 2}, ∅, {1}],
    #[Finset.Icc 1 5, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[∅, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {3, 4, 5}, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[{1, 2}, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[∅, Finset.Icc 1 5, {3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1}, {1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_2_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 0 j = k7t3p3_local_2 0 j := by decide

private theorem k7t3p3_local_2_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 1 j = k7t3p3_local_2 1 j := by decide

private theorem k7t3p3_local_2_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 2 j = k7t3p3_local_2 2 j := by decide

private theorem k7t3p3_local_2_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 3 j = k7t3p3_local_2 3 j := by decide

private theorem k7t3p3_local_2_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 4 j = k7t3p3_local_2 4 j := by decide

private theorem k7t3p3_local_2_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 5 j = k7t3p3_local_2 5 j := by decide

private theorem k7t3p3_local_2_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) 6 j = k7t3p3_local_2 6 j := by decide

private theorem k7t3p3_local_2_eq : (fun a b => freshMatrix k7t3p3_state_2 a b ∪ requiredMatrix 7 k7t3p3_step_2_data.required a b) = k7t3p3_local_2 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_2_eq_row_0 j

  · exact k7t3p3_local_2_eq_row_1 j

  · exact k7t3p3_local_2_eq_row_2 j

  · exact k7t3p3_local_2_eq_row_3 j

  · exact k7t3p3_local_2_eq_row_4 j

  · exact k7t3p3_local_2_eq_row_5 j

  · exact k7t3p3_local_2_eq_row_6 j

private theorem k7t3p3_local_2_paths : ∀ p ∈ k7t3p3_step_2_data.required, p.Check (freshGraph k7t3p3.graph k7t3p3_step_2_data.i k7t3p3_step_2_data.j) 7 := by decide

private theorem k7t3p3_local_2_bad : k7t3p3_step_2_data.bad.Check (freshGraph k7t3p3.graph k7t3p3_step_2_data.i k7t3p3_step_2_data.j) k7t3p3_local_2 7 3 := by decide

private theorem k7t3p3_step_2_check : k7t3p3_step_2.Check k7t3p3.graph k7t3p3_state_2 7 3 := by
  change k7t3p3_step_2_data.Check k7t3p3.graph k7t3p3_state_2 7 3
  refine ⟨by decide, k7t3p3_local_2_paths, ?_⟩
  rw [k7t3p3_local_2_eq]
  exact k7t3p3_local_2_bad

private theorem k7t3p3_update_2 : k7t3p3_step_2.apply k7t3p3_state_2 = k7t3p3_state_3 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_2.apply k7t3p3_state_2 i j = k7t3p3_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_4 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, {1}, ∅, {1, 2}, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 5, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[∅, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, ∅],
    #[{1, 2}, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, ∅, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_3_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 0 j = k7t3p3_local_3 0 j := by decide

private theorem k7t3p3_local_3_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 1 j = k7t3p3_local_3 1 j := by decide

private theorem k7t3p3_local_3_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 2 j = k7t3p3_local_3 2 j := by decide

private theorem k7t3p3_local_3_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 3 j = k7t3p3_local_3 3 j := by decide

private theorem k7t3p3_local_3_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 4 j = k7t3p3_local_3 4 j := by decide

private theorem k7t3p3_local_3_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 5 j = k7t3p3_local_3 5 j := by decide

private theorem k7t3p3_local_3_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) 6 j = k7t3p3_local_3 6 j := by decide

private theorem k7t3p3_local_3_eq : (fun a b => freshMatrix k7t3p3_state_3 a b ∪ requiredMatrix 7 k7t3p3_step_3_data.required a b) = k7t3p3_local_3 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_3_eq_row_0 j

  · exact k7t3p3_local_3_eq_row_1 j

  · exact k7t3p3_local_3_eq_row_2 j

  · exact k7t3p3_local_3_eq_row_3 j

  · exact k7t3p3_local_3_eq_row_4 j

  · exact k7t3p3_local_3_eq_row_5 j

  · exact k7t3p3_local_3_eq_row_6 j

private theorem k7t3p3_local_3_paths : ∀ p ∈ k7t3p3_step_3_data.required, p.Check (freshGraph k7t3p3.graph k7t3p3_step_3_data.i k7t3p3_step_3_data.j) 7 := by decide

private theorem k7t3p3_local_3_bad : k7t3p3_step_3_data.bad.Check (freshGraph k7t3p3.graph k7t3p3_step_3_data.i k7t3p3_step_3_data.j) k7t3p3_local_3 7 3 := by decide

private theorem k7t3p3_step_3_check : k7t3p3_step_3.Check k7t3p3.graph k7t3p3_state_3 7 3 := by
  change k7t3p3_step_3_data.Check k7t3p3.graph k7t3p3_state_3 7 3
  refine ⟨by decide, k7t3p3_local_3_paths, ?_⟩
  rw [k7t3p3_local_3_eq]
  exact k7t3p3_local_3_bad

private theorem k7t3p3_update_3 : k7t3p3_step_3.apply k7t3p3_state_3 = k7t3p3_state_4 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_3.apply k7t3p3_state_3 i j = k7t3p3_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_5 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 2, 3}, ∅, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 3}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[∅, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[{1, 2}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4, {1}],
    #[∅, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5],
    #[{1, 2}, Finset.Icc 1 5, {1, 3, 4, 5}, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 2 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_4_eq_row_0 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 0 j = k7t3p3_local_4 0 j := by decide

private theorem k7t3p3_local_4_eq_row_1 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 1 j = k7t3p3_local_4 1 j := by decide

private theorem k7t3p3_local_4_eq_row_2 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 2 j = k7t3p3_local_4 2 j := by decide

private theorem k7t3p3_local_4_eq_row_3 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 3 j = k7t3p3_local_4 3 j := by decide

private theorem k7t3p3_local_4_eq_row_4 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 4 j = k7t3p3_local_4 4 j := by decide

private theorem k7t3p3_local_4_eq_row_5 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 5 j = k7t3p3_local_4 5 j := by decide

private theorem k7t3p3_local_4_eq_row_6 : ∀ j : Fin 7, (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) 6 j = k7t3p3_local_4 6 j := by decide

private theorem k7t3p3_local_4_eq : (fun a b => freshMatrix k7t3p3_state_4 a b ∪ requiredMatrix 7 k7t3p3_step_4_data.required a b) = k7t3p3_local_4 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_4_eq_row_0 j

  · exact k7t3p3_local_4_eq_row_1 j

  · exact k7t3p3_local_4_eq_row_2 j

  · exact k7t3p3_local_4_eq_row_3 j

  · exact k7t3p3_local_4_eq_row_4 j

  · exact k7t3p3_local_4_eq_row_5 j

  · exact k7t3p3_local_4_eq_row_6 j

private theorem k7t3p3_local_4_paths : ∀ p ∈ k7t3p3_step_4_data.required, p.Check (freshGraph k7t3p3.graph k7t3p3_step_4_data.i k7t3p3_step_4_data.j) 7 := by decide

private theorem k7t3p3_local_4_bad : k7t3p3_step_4_data.bad.Check (freshGraph k7t3p3.graph k7t3p3_step_4_data.i k7t3p3_step_4_data.j) k7t3p3_local_4 7 3 := by decide

private theorem k7t3p3_step_4_check : k7t3p3_step_4.Check k7t3p3.graph k7t3p3_state_4 7 3 := by
  change k7t3p3_step_4_data.Check k7t3p3.graph k7t3p3_state_4 7 3
  refine ⟨by decide, k7t3p3_local_4_paths, ?_⟩
  rw [k7t3p3_local_4_eq]
  exact k7t3p3_local_4_bad

private theorem k7t3p3_update_4 : k7t3p3_step_4.apply k7t3p3_state_4 = k7t3p3_state_5 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_4.apply k7t3p3_state_4 i j = k7t3p3_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_6 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_5 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_5_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 0 j = k7t3p3_local_5 0 j := by decide

private theorem k7t3p3_local_5_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 1 j = k7t3p3_local_5 1 j := by decide

private theorem k7t3p3_local_5_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 2 j = k7t3p3_local_5 2 j := by decide

private theorem k7t3p3_local_5_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 3 j = k7t3p3_local_5 3 j := by decide

private theorem k7t3p3_local_5_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 4 j = k7t3p3_local_5 4 j := by decide

private theorem k7t3p3_local_5_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) 5 j = k7t3p3_local_5 5 j := by decide

private theorem k7t3p3_local_5_eq : (fun a b => k7t3p3_state_5 a b ∪ requiredMatrix 7 k7t3p3_step_5_data.required a b) = k7t3p3_local_5 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_5_eq_row_0 j

  · exact k7t3p3_local_5_eq_row_1 j

  · exact k7t3p3_local_5_eq_row_2 j

  · exact k7t3p3_local_5_eq_row_3 j

  · exact k7t3p3_local_5_eq_row_4 j

  · exact k7t3p3_local_5_eq_row_5 j

private theorem k7t3p3_local_5_paths : ∀ p ∈ k7t3p3_step_5_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_5_data.i k7t3p3_step_5_data.j) 7 := by decide

private theorem k7t3p3_local_5_bad : k7t3p3_step_5_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_5_data.i k7t3p3_step_5_data.j) k7t3p3_local_5 7 3 := by decide

private theorem k7t3p3_step_5_check : k7t3p3_step_5.Check k7t3p3.graph k7t3p3_state_5 7 3 := by
  change k7t3p3_step_5_data.Check k7t3p3.graph k7t3p3_state_5 7 3
  refine ⟨k7t3p3_local_5_paths, ?_⟩
  rw [k7t3p3_local_5_eq]
  exact k7t3p3_local_5_bad

private theorem k7t3p3_update_5 : k7t3p3_step_5.apply k7t3p3_state_5 = k7t3p3_state_6 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_5.apply k7t3p3_state_5 i j = k7t3p3_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_6 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 1 5, Finset.Icc 1 5, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 1 4, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_6_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 0 j = k7t3p3_local_6 0 j := by decide

private theorem k7t3p3_local_6_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 1 j = k7t3p3_local_6 1 j := by decide

private theorem k7t3p3_local_6_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 2 j = k7t3p3_local_6 2 j := by decide

private theorem k7t3p3_local_6_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 3 j = k7t3p3_local_6 3 j := by decide

private theorem k7t3p3_local_6_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 4 j = k7t3p3_local_6 4 j := by decide

private theorem k7t3p3_local_6_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) 5 j = k7t3p3_local_6 5 j := by decide

private theorem k7t3p3_local_6_eq : (fun a b => k7t3p3_state_6 a b ∪ requiredMatrix 7 k7t3p3_step_6_data.required a b) = k7t3p3_local_6 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_6_eq_row_0 j

  · exact k7t3p3_local_6_eq_row_1 j

  · exact k7t3p3_local_6_eq_row_2 j

  · exact k7t3p3_local_6_eq_row_3 j

  · exact k7t3p3_local_6_eq_row_4 j

  · exact k7t3p3_local_6_eq_row_5 j

private theorem k7t3p3_local_6_paths : ∀ p ∈ k7t3p3_step_6_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_6_data.i k7t3p3_step_6_data.j) 7 := by decide

private theorem k7t3p3_local_6_bad : k7t3p3_step_6_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_6_data.i k7t3p3_step_6_data.j) k7t3p3_local_6 7 3 := by decide

private theorem k7t3p3_step_6_check : k7t3p3_step_6.Check k7t3p3.graph k7t3p3_state_6 7 3 := by
  change k7t3p3_step_6_data.Check k7t3p3.graph k7t3p3_state_6 7 3
  refine ⟨k7t3p3_local_6_paths, ?_⟩
  rw [k7t3p3_local_6_eq]
  exact k7t3p3_local_6_bad

private theorem k7t3p3_update_6 : k7t3p3_step_6.apply k7t3p3_state_6 = k7t3p3_state_7 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_6.apply k7t3p3_state_6 i j = k7t3p3_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_8 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_7 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_7_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 0 j = k7t3p3_local_7 0 j := by decide

private theorem k7t3p3_local_7_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 1 j = k7t3p3_local_7 1 j := by decide

private theorem k7t3p3_local_7_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 2 j = k7t3p3_local_7 2 j := by decide

private theorem k7t3p3_local_7_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 3 j = k7t3p3_local_7 3 j := by decide

private theorem k7t3p3_local_7_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 4 j = k7t3p3_local_7 4 j := by decide

private theorem k7t3p3_local_7_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) 5 j = k7t3p3_local_7 5 j := by decide

private theorem k7t3p3_local_7_eq : (fun a b => k7t3p3_state_7 a b ∪ requiredMatrix 7 k7t3p3_step_7_data.required a b) = k7t3p3_local_7 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_7_eq_row_0 j

  · exact k7t3p3_local_7_eq_row_1 j

  · exact k7t3p3_local_7_eq_row_2 j

  · exact k7t3p3_local_7_eq_row_3 j

  · exact k7t3p3_local_7_eq_row_4 j

  · exact k7t3p3_local_7_eq_row_5 j

private theorem k7t3p3_local_7_paths : ∀ p ∈ k7t3p3_step_7_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_7_data.i k7t3p3_step_7_data.j) 7 := by decide

private theorem k7t3p3_local_7_bad : k7t3p3_step_7_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_7_data.i k7t3p3_step_7_data.j) k7t3p3_local_7 7 3 := by decide

private theorem k7t3p3_step_7_check : k7t3p3_step_7.Check k7t3p3.graph k7t3p3_state_7 7 3 := by
  change k7t3p3_step_7_data.Check k7t3p3.graph k7t3p3_state_7 7 3
  refine ⟨k7t3p3_local_7_paths, ?_⟩
  rw [k7t3p3_local_7_eq]
  exact k7t3p3_local_7_bad

private theorem k7t3p3_update_7 : k7t3p3_step_7.apply k7t3p3_state_7 = k7t3p3_state_8 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_7.apply k7t3p3_state_7 i j = k7t3p3_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_9 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_8 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 1 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_8_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 0 j = k7t3p3_local_8 0 j := by decide

private theorem k7t3p3_local_8_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 1 j = k7t3p3_local_8 1 j := by decide

private theorem k7t3p3_local_8_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 2 j = k7t3p3_local_8 2 j := by decide

private theorem k7t3p3_local_8_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 3 j = k7t3p3_local_8 3 j := by decide

private theorem k7t3p3_local_8_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 4 j = k7t3p3_local_8 4 j := by decide

private theorem k7t3p3_local_8_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) 5 j = k7t3p3_local_8 5 j := by decide

private theorem k7t3p3_local_8_eq : (fun a b => k7t3p3_state_8 a b ∪ requiredMatrix 7 k7t3p3_step_8_data.required a b) = k7t3p3_local_8 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_8_eq_row_0 j

  · exact k7t3p3_local_8_eq_row_1 j

  · exact k7t3p3_local_8_eq_row_2 j

  · exact k7t3p3_local_8_eq_row_3 j

  · exact k7t3p3_local_8_eq_row_4 j

  · exact k7t3p3_local_8_eq_row_5 j

private theorem k7t3p3_local_8_paths : ∀ p ∈ k7t3p3_step_8_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_8_data.i k7t3p3_step_8_data.j) 7 := by decide

private theorem k7t3p3_local_8_bad : k7t3p3_step_8_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_8_data.i k7t3p3_step_8_data.j) k7t3p3_local_8 7 3 := by decide

private theorem k7t3p3_step_8_check : k7t3p3_step_8.Check k7t3p3.graph k7t3p3_state_8 7 3 := by
  change k7t3p3_step_8_data.Check k7t3p3.graph k7t3p3_state_8 7 3
  refine ⟨k7t3p3_local_8_paths, ?_⟩
  rw [k7t3p3_local_8_eq]
  exact k7t3p3_local_8_bad

private theorem k7t3p3_update_8 : k7t3p3_step_8.apply k7t3p3_state_8 = k7t3p3_state_9 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_8.apply k7t3p3_state_8 i j = k7t3p3_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_10 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 3, 4, 5}, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_9 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 4, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 1 4, ∅, {1, 2, 3}, {2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 3, 4, 5}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_9_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 0 j = k7t3p3_local_9 0 j := by decide

private theorem k7t3p3_local_9_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 1 j = k7t3p3_local_9 1 j := by decide

private theorem k7t3p3_local_9_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 2 j = k7t3p3_local_9 2 j := by decide

private theorem k7t3p3_local_9_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 3 j = k7t3p3_local_9 3 j := by decide

private theorem k7t3p3_local_9_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 4 j = k7t3p3_local_9 4 j := by decide

private theorem k7t3p3_local_9_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) 5 j = k7t3p3_local_9 5 j := by decide

private theorem k7t3p3_local_9_eq : (fun a b => k7t3p3_state_9 a b ∪ requiredMatrix 7 k7t3p3_step_9_data.required a b) = k7t3p3_local_9 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_9_eq_row_0 j

  · exact k7t3p3_local_9_eq_row_1 j

  · exact k7t3p3_local_9_eq_row_2 j

  · exact k7t3p3_local_9_eq_row_3 j

  · exact k7t3p3_local_9_eq_row_4 j

  · exact k7t3p3_local_9_eq_row_5 j

private theorem k7t3p3_local_9_paths : ∀ p ∈ k7t3p3_step_9_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_9_data.i k7t3p3_step_9_data.j) 7 := by decide

private theorem k7t3p3_local_9_bad : k7t3p3_step_9_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_9_data.i k7t3p3_step_9_data.j) k7t3p3_local_9 7 3 := by decide

private theorem k7t3p3_step_9_check : k7t3p3_step_9.Check k7t3p3.graph k7t3p3_state_9 7 3 := by
  change k7t3p3_step_9_data.Check k7t3p3.graph k7t3p3_state_9 7 3
  refine ⟨k7t3p3_local_9_paths, ?_⟩
  rw [k7t3p3_local_9_eq]
  exact k7t3p3_local_9_bad

private theorem k7t3p3_update_9 : k7t3p3_step_9.apply k7t3p3_state_9 = k7t3p3_state_10 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_9.apply k7t3p3_state_9 i j = k7t3p3_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p3_state_11 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4}, {1}],
    #[Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5],
    #[Finset.Icc 0 5, {1, 3, 4, 5}, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, ∅, {1}, Finset.Icc 0 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p3_local_10 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 1 6],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4}, {1}],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 3, 4, 5}, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, ∅, {1}, Finset.Icc 1 5, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p3_local_10_eq_row_0 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 0 j = k7t3p3_local_10 0 j := by decide

private theorem k7t3p3_local_10_eq_row_1 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 1 j = k7t3p3_local_10 1 j := by decide

private theorem k7t3p3_local_10_eq_row_2 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 2 j = k7t3p3_local_10 2 j := by decide

private theorem k7t3p3_local_10_eq_row_3 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 3 j = k7t3p3_local_10 3 j := by decide

private theorem k7t3p3_local_10_eq_row_4 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 4 j = k7t3p3_local_10 4 j := by decide

private theorem k7t3p3_local_10_eq_row_5 : ∀ j : Fin 6, (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) 5 j = k7t3p3_local_10 5 j := by decide

private theorem k7t3p3_local_10_eq : (fun a b => k7t3p3_state_10 a b ∪ requiredMatrix 7 k7t3p3_step_10_data.required a b) = k7t3p3_local_10 := by
  funext i j
  fin_cases i

  · exact k7t3p3_local_10_eq_row_0 j

  · exact k7t3p3_local_10_eq_row_1 j

  · exact k7t3p3_local_10_eq_row_2 j

  · exact k7t3p3_local_10_eq_row_3 j

  · exact k7t3p3_local_10_eq_row_4 j

  · exact k7t3p3_local_10_eq_row_5 j

private theorem k7t3p3_local_10_paths : ∀ p ∈ k7t3p3_step_10_data.required, p.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_10_data.i k7t3p3_step_10_data.j) 7 := by decide

private theorem k7t3p3_local_10_bad : k7t3p3_step_10_data.bad.Check (addedEdgeGraph k7t3p3.graph k7t3p3_step_10_data.i k7t3p3_step_10_data.j) k7t3p3_local_10 7 3 := by decide

private theorem k7t3p3_step_10_check : k7t3p3_step_10.Check k7t3p3.graph k7t3p3_state_10 7 3 := by
  change k7t3p3_step_10_data.Check k7t3p3.graph k7t3p3_state_10 7 3
  refine ⟨k7t3p3_local_10_paths, ?_⟩
  rw [k7t3p3_local_10_eq]
  exact k7t3p3_local_10_bad

private theorem k7t3p3_update_10 : k7t3p3_step_10.apply k7t3p3_state_10 = k7t3p3_state_11 := by
  have h : ∀ i j : Fin 6, k7t3p3_step_10.apply k7t3p3_state_10 i j = k7t3p3_state_11 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k7t3p3_closure_11 : ClosureCheck k7t3p3.graph k7t3p3_state_11 7 3 [] := by trivial

private theorem k7t3p3_closure_10 : ClosureCheck k7t3p3.graph k7t3p3_state_10 7 3 [k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_10_check
  · rw [k7t3p3_update_10]
    exact k7t3p3_closure_11

private theorem k7t3p3_closure_9 : ClosureCheck k7t3p3.graph k7t3p3_state_9 7 3 [k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_9_check
  · rw [k7t3p3_update_9]
    exact k7t3p3_closure_10

private theorem k7t3p3_closure_8 : ClosureCheck k7t3p3.graph k7t3p3_state_8 7 3 [k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_8_check
  · rw [k7t3p3_update_8]
    exact k7t3p3_closure_9

private theorem k7t3p3_closure_7 : ClosureCheck k7t3p3.graph k7t3p3_state_7 7 3 [k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_7_check
  · rw [k7t3p3_update_7]
    exact k7t3p3_closure_8

private theorem k7t3p3_closure_6 : ClosureCheck k7t3p3.graph k7t3p3_state_6 7 3 [k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_6_check
  · rw [k7t3p3_update_6]
    exact k7t3p3_closure_7

private theorem k7t3p3_closure_5 : ClosureCheck k7t3p3.graph k7t3p3_state_5 7 3 [k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_5_check
  · rw [k7t3p3_update_5]
    exact k7t3p3_closure_6

private theorem k7t3p3_closure_4 : ClosureCheck k7t3p3.graph k7t3p3_state_4 7 3 [k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_4_check
  · rw [k7t3p3_update_4]
    exact k7t3p3_closure_5

private theorem k7t3p3_closure_3 : ClosureCheck k7t3p3.graph k7t3p3_state_3 7 3 [k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_3_check
  · rw [k7t3p3_update_3]
    exact k7t3p3_closure_4

private theorem k7t3p3_closure_2 : ClosureCheck k7t3p3.graph k7t3p3_state_2 7 3 [k7t3p3_step_2, k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_2_check
  · rw [k7t3p3_update_2]
    exact k7t3p3_closure_3

private theorem k7t3p3_closure_1 : ClosureCheck k7t3p3.graph k7t3p3_state_1 7 3 [k7t3p3_step_1, k7t3p3_step_2, k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_1_check
  · rw [k7t3p3_update_1]
    exact k7t3p3_closure_2

private theorem k7t3p3_closure_0 : ClosureCheck k7t3p3.graph k7t3p3_state_0 7 3 [k7t3p3_step_0, k7t3p3_step_1, k7t3p3_step_2, k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] := by
  constructor
  · exact k7t3p3_step_0_check
  · rw [k7t3p3_update_0]
    exact k7t3p3_closure_1

private theorem k7t3p3_matrix_eq : k7t3p3.matrix 7 = k7t3p3_state_11 := by
  change closureMatrix (k7t3p3.initialMatrix 7) _ = _
  rw [k7t3p3_initial_eq]
  change closureMatrix k7t3p3_state_0 [k7t3p3_step_0, k7t3p3_step_1, k7t3p3_step_2, k7t3p3_step_3, k7t3p3_step_4, k7t3p3_step_5, k7t3p3_step_6, k7t3p3_step_7, k7t3p3_step_8, k7t3p3_step_9, k7t3p3_step_10] = _
  simp only [closureMatrix]
  rw [k7t3p3_update_0, k7t3p3_update_1, k7t3p3_update_2, k7t3p3_update_3, k7t3p3_update_4, k7t3p3_update_5, k7t3p3_update_6, k7t3p3_update_7, k7t3p3_update_8, k7t3p3_update_9, k7t3p3_update_10]

private theorem k7t3p3_part_0 : k7t3p3.chains.flatten = List.finRange _ := by decide

private theorem k7t3p3_part_1 : k7t3p3.chains.map List.length = ([[], [3]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p3_part_2 : k7t3p3.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p3.clique))) = ([[], [3]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p3_templates_item_0 : (⟨0, 1, [], [], [], 4, 6⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_2 : (⟨0, 2, [], [], [1], 3, 5⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_4 : (⟨0, 3, [], [], [2, 1], 2, 4⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_5 : (⟨0, 4, [], [], [3, 2, 1], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_6 : (⟨0, 4, [], [], [5], 3, 5⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_7 : (⟨0, 5, [], [], [], 4, 6⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_8 : (⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_9 : (⟨1, 2, [], [], [3, 4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_10 : (⟨1, 3, [], [], [4, 5], 2, 4⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_11 : (⟨1, 4, [], [], [5], 3, 5⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_12 : (⟨2, 3, [], [1], [4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_13 : (⟨2, 4, [], [1], [5], 2, 4⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_14 : (⟨3, 4, [], [1, 2], [5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_15 : (⟨3, 5, [], [1, 2], [], 2, 4⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_templates_item_16 : (⟨4, 5, [], [1, 2, 3], [], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p3_part_3 : ∀ T ∈ k7t3p3.templates, T.Check k7t3p3.graph k7t3p3.clique 7 (patternAmount ([[], [3]] : List (List ℕ))) (([[], [3]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p3_templates_item_0, k7t3p3_templates_item_1, k7t3p3_templates_item_2, k7t3p3_templates_item_3, k7t3p3_templates_item_4, k7t3p3_templates_item_5, k7t3p3_templates_item_6, k7t3p3_templates_item_7, k7t3p3_templates_item_8, k7t3p3_templates_item_9, k7t3p3_templates_item_10, k7t3p3_templates_item_11, k7t3p3_templates_item_12, k7t3p3_templates_item_13, k7t3p3_templates_item_14, k7t3p3_templates_item_15, k7t3p3_templates_item_16⟩

private theorem k7t3p3_required_item_0 : (⟨1, 3, [2]⟩ : RequiredPathData (Fin 6)).Check k7t3p3.graph 7 := by decide

private theorem k7t3p3_required_item_1 : (⟨3, 5, [4]⟩ : RequiredPathData (Fin 6)).Check k7t3p3.graph 7 := by decide

private theorem k7t3p3_part_4 : ∀ p ∈ k7t3p3.required, p.Check k7t3p3.graph 7 := by
  simp only [k7t3p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p3_required_item_0, k7t3p3_required_item_1⟩

private theorem k7t3p3_part_5 : ClosureCheck k7t3p3.graph (k7t3p3.initialMatrix 7) 7 3 k7t3p3.closure := by
  rw [k7t3p3_initial_eq]
  exact k7t3p3_closure_0

private theorem k7t3p3_part_6 : k7t3p3.bad.Check k7t3p3.graph (k7t3p3.matrix 7) 7 3 := by
  rw [k7t3p3_matrix_eq]
  decide

theorem k7t3p3_check : k7t3p3.Check 7 3 [[], [3]] :=
  ⟨k7t3p3_part_0, k7t3p3_part_1, k7t3p3_part_2, k7t3p3_part_3, k7t3p3_part_4, k7t3p3_part_5, k7t3p3_part_6⟩
private def k7t3p4_step_0_data : FreshAttachmentData 7 := ⟨3, 0, [⟨2, 0, [1, 7, 6, 5, 4]⟩, ⟨2, 7, [1, 0, 4, 5, 6]⟩, ⟨2, 0, [3, 4, 5, 6, 7, 1]⟩, ⟨2, 6, [3, 4, 0, 1, 7]⟩, ⟨2, 5, [3, 4, 0, 1, 7, 6]⟩, ⟨3, 0, [2, 1, 7, 6, 5, 4]⟩, ⟨3, 6, [2, 1, 0, 4, 5]⟩, ⟨3, 7, [2, 1, 0, 4, 5, 6]⟩, ⟨3, 6, [2, 7, 1, 0, 4, 5]⟩, ⟨3, 0, [2, 7, 6, 5, 4]⟩, ⟨3, 1, [2, 7, 6, 5, 4, 0]⟩, ⟨3, 2, [4, 0, 1]⟩, ⟨3, 5, [4, 0, 1, 2, 7, 6]⟩, ⟨3, 6, [4, 0, 1, 7]⟩, ⟨6, 0, [5, 4, 3, 2, 1]⟩, ⟨6, 0, [5, 4, 3, 2, 7, 1]⟩, ⟨6, 2, [5, 4, 0, 1]⟩, ⟨6, 3, [5, 4, 0, 1, 2]⟩, ⟨6, 2, [5, 4, 0, 1, 7]⟩, ⟨6, 3, [5, 4, 0, 1, 7, 2]⟩, ⟨6, 3, [7, 1, 0, 4]⟩, ⟨6, 0, [7, 2, 1]⟩, ⟨6, 0, [7, 2, 3, 4]⟩, ⟨0, 2, [4, 5, 6, 7, 1]⟩, ⟨0, 2, [4, 5, 6, 7]⟩], ⟨none, {(3, 1), (6, 3), (0, 0), (2, 2)}⟩⟩

private def k7t3p4_step_0 : ClosureStep 7 := .fresh k7t3p4_step_0_data

private def k7t3p4_step_1_data : FreshAttachmentData 7 := ⟨4, 0, [⟨3, 0, [2, 1, 7, 6, 5]⟩, ⟨3, 6, [2, 1, 0, 5]⟩, ⟨3, 7, [2, 1, 0, 5, 6]⟩, ⟨3, 0, [2, 7, 1]⟩, ⟨3, 6, [2, 7, 1, 0, 5]⟩, ⟨3, 0, [2, 7, 6, 5]⟩, ⟨3, 0, [4, 5, 6, 7, 2, 1]⟩, ⟨3, 6, [4, 5, 0, 1, 2, 7]⟩, ⟨3, 7, [4, 5, 0, 1]⟩, ⟨6, 0, [5, 4, 3, 2, 1]⟩, ⟨6, 0, [5, 4, 3, 2, 7, 1]⟩, ⟨6, 7, [5, 0, 1]⟩, ⟨6, 4, [5, 0, 1, 7, 2, 3]⟩, ⟨6, 2, [7, 1, 0, 5, 4, 3]⟩, ⟨6, 3, [7, 2, 1, 0, 5, 4]⟩, ⟨6, 1, [7, 2, 3, 4, 5, 0]⟩, ⟨7, 0, [1, 2, 3, 4, 5]⟩, ⟨7, 2, [1, 0, 5, 4, 3]⟩, ⟨7, 3, [2, 1, 0, 5, 4]⟩, ⟨7, 0, [6, 5, 4, 3, 2, 1]⟩, ⟨7, 4, [6, 5, 0, 1, 2, 3]⟩, ⟨0, 7, [5, 4, 3, 2, 1]⟩, ⟨0, 7, [5, 4, 3, 2]⟩], ⟨none, {(3, 3), (6, 1), (0, 0), (7, 2)}⟩⟩

private def k7t3p4_step_1 : ClosureStep 7 := .fresh k7t3p4_step_1_data

private def k7t3p4_step_2_data : FreshAttachmentData 7 := ⟨4, 1, [⟨1, 0, [7, 2, 3, 4, 5]⟩, ⟨1, 0, [7, 6, 5, 4, 3, 2]⟩, ⟨1, 4, [7, 6, 5, 0, 2, 3]⟩, ⟨6, 0, [5, 4, 3, 2]⟩, ⟨6, 1, [5, 0, 2]⟩, ⟨6, 0, [7, 1, 2, 3, 4, 5]⟩, ⟨6, 4, [7, 1, 2, 0, 5]⟩, ⟨6, 3, [7, 1, 2, 0, 5, 4]⟩, ⟨6, 0, [7, 2, 3, 4, 5]⟩, ⟨6, 3, [7, 2, 0, 5, 4]⟩, ⟨0, 6, [2, 1, 7]⟩, ⟨0, 4, [2, 1, 7, 6, 5]⟩, ⟨0, 3, [2, 1, 7, 6, 5, 4]⟩, ⟨0, 6, [2, 3, 4, 5]⟩, ⟨0, 7, [2, 3, 4, 5, 6]⟩, ⟨0, 1, [2, 3, 4, 5, 6, 7]⟩, ⟨0, 1, [2, 7]⟩, ⟨0, 6, [2, 7]⟩, ⟨0, 3, [2, 7, 6, 5, 4]⟩, ⟨0, 1, [5, 4, 3, 2]⟩, ⟨0, 6, [5, 4, 3, 2, 1, 7]⟩, ⟨0, 1, [5, 4, 3, 2, 7]⟩, ⟨0, 6, [5, 4, 3, 2, 7]⟩, ⟨0, 6, [5]⟩, ⟨0, 1, [5, 6, 7]⟩, ⟨0, 4, [5, 6, 7, 1, 2, 3]⟩], ⟨none, {(0, 2), (6, 3), (1, 2)}⟩⟩

private def k7t3p4_step_2 : ClosureStep 7 := .fresh k7t3p4_step_2_data

private def k7t3p4_step_3_data : FreshAttachmentData 7 := ⟨5, 2, [⟨1, 0, [2, 3, 4, 5, 6]⟩, ⟨1, 4, [2, 3, 0, 6, 5]⟩, ⟨1, 0, [2, 7, 6, 5, 4, 3]⟩, ⟨1, 5, [2, 7, 6, 0, 3, 4]⟩, ⟨1, 5, [7, 2, 3, 0, 6]⟩, ⟨1, 4, [7, 2, 3, 0, 6, 5]⟩, ⟨1, 2, [7, 6, 0, 3]⟩, ⟨4, 2, [3, 0, 6, 7, 1]⟩, ⟨4, 0, [5, 6, 7, 1, 2, 3]⟩, ⟨4, 7, [5, 6, 0, 3, 2, 1]⟩, ⟨4, 1, [5, 6, 0, 3, 2, 7]⟩, ⟨5, 0, [4, 3, 2, 1, 7, 6]⟩, ⟨5, 2, [4, 3, 0, 6, 7, 1]⟩, ⟨5, 2, [4, 3, 0, 6, 7]⟩, ⟨5, 1, [4, 3, 0, 6, 7, 2]⟩], ⟨none, {(1, 2), (4, 1), (5, 1), (2, 0)}⟩⟩

private def k7t3p4_step_3 : ClosureStep 7 := .fresh k7t3p4_step_3_data

private def k7t3p4_step_4_data : FreshAttachmentData 7 := ⟨6, 3, [⟨1, 0, [2, 3, 4, 5, 6, 7]⟩, ⟨1, 5, [2, 3, 4, 0, 7, 6]⟩, ⟨1, 0, [2, 7, 6, 5, 4]⟩, ⟨3, 0, [2, 1, 7, 6, 5, 4]⟩, ⟨3, 5, [2, 1, 7, 0, 4]⟩, ⟨3, 6, [2, 1, 7, 0, 4, 5]⟩, ⟨3, 0, [2, 7, 6, 5, 4]⟩, ⟨3, 6, [2, 7, 0, 4, 5]⟩, ⟨3, 0, [4, 5, 6, 7]⟩, ⟨3, 1, [4, 0, 7]⟩, ⟨0, 3, [4]⟩, ⟨0, 1, [4, 3, 2]⟩, ⟨0, 6, [4, 3, 2, 1, 7]⟩, ⟨0, 5, [4, 3, 2, 1, 7, 6]⟩, ⟨0, 1, [4, 3, 2, 7]⟩, ⟨0, 5, [4, 3, 2, 7, 6]⟩, ⟨0, 2, [4, 5, 6, 7, 1]⟩, ⟨0, 3, [4, 5, 6, 7, 1, 2]⟩, ⟨0, 1, [4, 5, 6, 7, 2]⟩, ⟨0, 3, [4, 5, 6, 7, 2]⟩, ⟨0, 3, [7, 1, 2]⟩, ⟨0, 6, [7, 1, 2, 3, 4, 5]⟩, ⟨0, 1, [7, 2]⟩, ⟨0, 3, [7, 2]⟩, ⟨0, 3, [7, 6, 5, 4]⟩, ⟨0, 1, [7, 6, 5, 4, 3, 2]⟩], ⟨none, {(0, 2), (3, 3), (1, 2)}⟩⟩

private def k7t3p4_step_4 : ClosureStep 7 := .fresh k7t3p4_step_4_data

private def k7t3p4_step_5_data : EdgeAttachmentData 7 := ⟨3, 1, [⟨0, 2, [6, 1, 3]⟩, ⟨2, 4, [1, 3]⟩, ⟨2, 5, [3, 1, 0, 6]⟩, ⟨2, 4, [3, 1, 0, 6, 5]⟩, ⟨4, 2, [5, 6, 0, 1, 3]⟩], ⟨none, {(0, 2), (2, 3), (4, 2), (5, 0)}⟩⟩

private def k7t3p4_step_5 : ClosureStep 7 := .edge k7t3p4_step_5_data

private def k7t3p4_step_6_data : FreshAttachmentData 7 := ⟨3, 1, [⟨1, 0, [2, 7, 6, 5, 4]⟩, ⟨1, 3, [2, 0, 4]⟩, ⟨1, 0, [7, 2, 3, 4]⟩, ⟨1, 0, [7, 6, 5, 4, 3, 2]⟩, ⟨1, 3, [7, 6, 5, 4, 0, 2]⟩, ⟨3, 0, [2, 1, 7, 6, 5, 4]⟩, ⟨3, 0, [2, 7, 6, 5, 4]⟩, ⟨3, 7, [2, 0, 4, 5, 6]⟩, ⟨3, 1, [2, 0, 4, 5, 6, 7]⟩, ⟨3, 5, [4, 0, 2, 1, 7, 6]⟩, ⟨3, 5, [4, 0, 2, 7, 6]⟩, ⟨5, 0, [6, 7, 1, 2, 3, 4]⟩, ⟨5, 3, [6, 7, 1, 2, 0, 4]⟩], ⟨none, {(1, 3), (3, 2), (5, 1), (4, 0)}⟩⟩

private def k7t3p4_step_6 : ClosureStep 7 := .fresh k7t3p4_step_6_data

private def k7t3p4_step_7_data : EdgeAttachmentData 7 := ⟨4, 2, [⟨0, 5, [1, 2, 4]⟩, ⟨3, 5, [2, 4]⟩, ⟨3, 1, [2, 4, 5, 6, 0]⟩, ⟨3, 5, [4, 2, 1, 0, 6]⟩, ⟨5, 3, [6, 0, 1, 2, 4]⟩, ⟨5, 4, [6, 1, 2]⟩], ⟨none, {(0, 2), (3, 2), (5, 3), (4, 0)}⟩⟩

private def k7t3p4_step_7 : ClosureStep 7 := .edge k7t3p4_step_7_data

private def k7t3p4_step_8_data : EdgeAttachmentData 7 := ⟨5, 3, [⟨0, 2, [6, 5, 3]⟩, ⟨2, 4, [1, 0, 6, 5, 3]⟩, ⟨2, 3, [1, 6, 5]⟩, ⟨4, 2, [3, 5, 6, 0, 1]⟩, ⟨4, 2, [5, 3]⟩, ⟨4, 6, [5, 3, 2, 1, 0]⟩], ⟨none, {(0, 2), (4, 2), (2, 3), (3, 0)}⟩⟩

private def k7t3p4_step_8 : ClosureStep 7 := .edge k7t3p4_step_8_data

private def k7t3p4_step_9_data : EdgeAttachmentData 7 := ⟨6, 4, [⟨0, 5, [1, 6, 4]⟩, ⟨3, 5, [2, 1, 0, 6, 4]⟩, ⟨3, 5, [4, 6]⟩, ⟨5, 2, [4, 6, 0, 1]⟩, ⟨5, 3, [4, 6, 0, 1, 2]⟩], ⟨none, {(0, 2), (3, 2), (5, 3), (2, 0)}⟩⟩

private def k7t3p4_step_9 : ClosureStep 7 := .edge k7t3p4_step_9_data

private def k7t3p4_step_10_data : FreshAttachmentData 7 := ⟨6, 4, [⟨1, 0, [2, 3, 4, 5, 6, 7]⟩, ⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 6, [2, 3, 4, 5, 0, 7]⟩, ⟨1, 0, [7, 2, 3, 4, 5]⟩, ⟨1, 6, [7, 0, 5]⟩, ⟨4, 0, [3, 2, 1, 7, 6, 5]⟩, ⟨4, 6, [3, 2, 1, 7, 0, 5]⟩, ⟨6, 0, [5, 4, 3, 2, 1, 7]⟩, ⟨6, 0, [5, 4, 3, 2, 7]⟩, ⟨6, 4, [5, 0, 7, 1, 2, 3]⟩, ⟨6, 4, [5, 0, 7, 2, 3]⟩, ⟨6, 2, [7, 0, 5, 4, 3]⟩, ⟨6, 1, [7, 0, 5, 4, 3, 2]⟩], ⟨none, {(1, 3), (6, 2), (4, 1), (5, 0)}⟩⟩

private def k7t3p4_step_10 : ClosureStep 7 := .fresh k7t3p4_step_10_data

private def k7t3p4_step_11_data : EdgeAttachmentData 7 := ⟨3, 0, [⟨4, 3, [5, 6, 0]⟩, ⟨4, 2, [5, 6, 1, 0, 3]⟩], ⟨none, {(4, 2), (3, 1), (0, 2), (2, 0)}⟩⟩

private def k7t3p4_step_11 : ClosureStep 7 := .edge k7t3p4_step_11_data

private def k7t3p4_step_12_data : EdgeAttachmentData 7 := ⟨4, 0, [⟨3, 4, [2, 1, 0]⟩, ⟨3, 5, [2, 1, 6, 0, 4]⟩], ⟨none, {(3, 2), (4, 1), (0, 2), (5, 0)}⟩⟩

private def k7t3p4_step_12 : ClosureStep 7 := .edge k7t3p4_step_12_data

private def k7t3p4_step_13_data : EdgeAttachmentData 7 := ⟨6, 3, [⟨0, 2, [1, 6, 3]⟩, ⟨3, 0, [6]⟩, ⟨3, 2, [6, 0, 1]⟩, ⟨3, 2, [6, 1]⟩], ⟨none, {(3, 2), (0, 3), (2, 2)}⟩⟩

private def k7t3p4_step_13 : ClosureStep 7 := .edge k7t3p4_step_13_data

def k7t3p4 : LayoutCertificate 7 where
  chains := [[0], [1, 2, 3, 4, 5, 6]]
  clique := {0, 1, 6}
  templates := [⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩,
    ⟨0, 2, [], [], [1], 4, 5⟩,
    ⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨0, 3, [], [], [2, 1], 3, 4⟩,
    ⟨0, 3, [], [], [4, 5, 6], 2, 3⟩,
    ⟨0, 4, [], [], [3, 2, 1], 2, 3⟩,
    ⟨0, 4, [], [], [5, 6], 3, 4⟩,
    ⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩,
    ⟨0, 5, [], [], [6], 4, 5⟩,
    ⟨0, 6, [], [], [5, 4, 3, 2, 1], 1, 1⟩,
    ⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨1, 5, [], [], [6], 4, 5⟩,
    ⟨2, 3, [], [1], [4, 5, 6], 1, 2⟩,
    ⟨2, 4, [], [1], [5, 6], 2, 3⟩,
    ⟨2, 5, [], [1], [6], 3, 4⟩,
    ⟨2, 6, [], [1], [], 4, 5⟩,
    ⟨3, 4, [], [1, 2], [5, 6], 1, 2⟩,
    ⟨3, 5, [], [1, 2], [6], 2, 3⟩,
    ⟨4, 5, [], [1, 2, 3], [6], 1, 2⟩,
    ⟨5, 6, [], [1, 2, 3, 4], [], 1, 2⟩]
  required := [⟨1, 5, [2, 3, 4]⟩,
    ⟨2, 4, [3]⟩,
    ⟨2, 6, [3, 4, 5]⟩,
    ⟨3, 5, [4]⟩]
  closure := [k7t3p4_step_0, k7t3p4_step_1, k7t3p4_step_2, k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13]
  bad := ⟨none, {(0, 2), (3, 2), (4, 0), (2, 0)}⟩


private def k7t3p4_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, {2, 3, 4}, {2, 3, 4}, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, ∅, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {3, 4}, {3, 4, 5}],
    #[{2, 3, 4}, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[{2, 3, 4}, ∅, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_initial_eq_row_0 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 0 j = k7t3p4_state_0 0 j := by decide

private theorem k7t3p4_initial_eq_row_1 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 1 j = k7t3p4_state_0 1 j := by decide

private theorem k7t3p4_initial_eq_row_2 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 2 j = k7t3p4_state_0 2 j := by decide

private theorem k7t3p4_initial_eq_row_3 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 3 j = k7t3p4_state_0 3 j := by decide

private theorem k7t3p4_initial_eq_row_4 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 4 j = k7t3p4_state_0 4 j := by decide

private theorem k7t3p4_initial_eq_row_5 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 5 j = k7t3p4_state_0 5 j := by decide

private theorem k7t3p4_initial_eq_row_6 : ∀ j : Fin 7, (k7t3p4.initialMatrix 7) 6 j = k7t3p4_state_0 6 j := by decide

private theorem k7t3p4_initial_eq : (k7t3p4.initialMatrix 7) = k7t3p4_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p4_initial_eq_row_0 j

  · exact k7t3p4_initial_eq_row_1 j

  · exact k7t3p4_initial_eq_row_2 j

  · exact k7t3p4_initial_eq_row_3 j

  · exact k7t3p4_initial_eq_row_4 j

  · exact k7t3p4_initial_eq_row_5 j

  · exact k7t3p4_initial_eq_row_6 j

private def k7t3p4_state_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, ∅, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[{2, 3, 4}, ∅, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_0 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, {0, 1, 2}, {0, 1}, ∅, ∅, Finset.Icc 0 3, ∅],
    #[∅, ∅, {1}, {0, 1, 2, 4, 5}, {2, 3, 4}, {2, 3, 4}, {1, 2, 4, 5}, {1}],
    #[{0, 1, 2}, {1}, ∅, {1, 2, 3}, ∅, {0}, Finset.Icc 1 5, {1}],
    #[{0, 1}, {0, 1, 2, 4, 5}, {1, 2, 3}, ∅, {1, 2}, {0, 2, 3, 5}, Finset.Icc 0 4, {0, 3, 4, 5}],
    #[∅, {2, 3, 4}, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[∅, {2, 3, 4}, {0}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[Finset.Icc 0 3, {1, 2, 4, 5}, Finset.Icc 1 5, Finset.Icc 0 4, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[∅, {1}, {1}, {0, 3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_0_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 0 j = k7t3p4_local_0 0 j := by decide

private theorem k7t3p4_local_0_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 1 j = k7t3p4_local_0 1 j := by decide

private theorem k7t3p4_local_0_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 2 j = k7t3p4_local_0 2 j := by decide

private theorem k7t3p4_local_0_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 3 j = k7t3p4_local_0 3 j := by decide

private theorem k7t3p4_local_0_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 4 j = k7t3p4_local_0 4 j := by decide

private theorem k7t3p4_local_0_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 5 j = k7t3p4_local_0 5 j := by decide

private theorem k7t3p4_local_0_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 6 j = k7t3p4_local_0 6 j := by decide

private theorem k7t3p4_local_0_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) 7 j = k7t3p4_local_0 7 j := by decide

private theorem k7t3p4_local_0_eq : (fun a b => freshMatrix k7t3p4_state_0 a b ∪ requiredMatrix 7 k7t3p4_step_0_data.required a b) = k7t3p4_local_0 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_0_eq_row_0 j

  · exact k7t3p4_local_0_eq_row_1 j

  · exact k7t3p4_local_0_eq_row_2 j

  · exact k7t3p4_local_0_eq_row_3 j

  · exact k7t3p4_local_0_eq_row_4 j

  · exact k7t3p4_local_0_eq_row_5 j

  · exact k7t3p4_local_0_eq_row_6 j

  · exact k7t3p4_local_0_eq_row_7 j

private theorem k7t3p4_local_0_paths : ∀ p ∈ k7t3p4_step_0_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_0_data.i k7t3p4_step_0_data.j) 7 := by decide

private theorem k7t3p4_local_0_bad : k7t3p4_step_0_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_0_data.i k7t3p4_step_0_data.j) k7t3p4_local_0 7 3 := by decide

private theorem k7t3p4_step_0_check : k7t3p4_step_0.Check k7t3p4.graph k7t3p4_state_0 7 3 := by
  change k7t3p4_step_0_data.Check k7t3p4.graph k7t3p4_state_0 7 3
  refine ⟨by decide, k7t3p4_local_0_paths, ?_⟩
  rw [k7t3p4_local_0_eq]
  exact k7t3p4_local_0_bad

private theorem k7t3p4_update_0 : k7t3p4_step_0.apply k7t3p4_state_0 = k7t3p4_state_1 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_0.apply k7t3p4_state_0 i j = k7t3p4_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, ∅, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[Finset.Icc 1 4, ∅, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_1 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, ∅, Finset.Icc 0 3, ∅, ∅, {0, 1}, {0, 1, 2}],
    #[∅, ∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, {2, 3, 4}, {0, 1, 2, 4, 5}, {1}],
    #[∅, {1}, ∅, {1, 2}, ∅, ∅, {0, 3, 4, 5}, {1}],
    #[Finset.Icc 0 3, {1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {0}],
    #[∅, {2, 3, 4}, ∅, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{0, 1}, {0, 1, 2, 4, 5}, {0, 3, 4, 5}, Finset.Icc 0 4, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2, 3}],
    #[{0, 1, 2}, {1}, {1}, Finset.Icc 1 5, {0}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_1_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 0 j = k7t3p4_local_1 0 j := by decide

private theorem k7t3p4_local_1_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 1 j = k7t3p4_local_1 1 j := by decide

private theorem k7t3p4_local_1_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 2 j = k7t3p4_local_1 2 j := by decide

private theorem k7t3p4_local_1_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 3 j = k7t3p4_local_1 3 j := by decide

private theorem k7t3p4_local_1_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 4 j = k7t3p4_local_1 4 j := by decide

private theorem k7t3p4_local_1_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 5 j = k7t3p4_local_1 5 j := by decide

private theorem k7t3p4_local_1_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 6 j = k7t3p4_local_1 6 j := by decide

private theorem k7t3p4_local_1_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) 7 j = k7t3p4_local_1 7 j := by decide

private theorem k7t3p4_local_1_eq : (fun a b => freshMatrix k7t3p4_state_1 a b ∪ requiredMatrix 7 k7t3p4_step_1_data.required a b) = k7t3p4_local_1 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_1_eq_row_0 j

  · exact k7t3p4_local_1_eq_row_1 j

  · exact k7t3p4_local_1_eq_row_2 j

  · exact k7t3p4_local_1_eq_row_3 j

  · exact k7t3p4_local_1_eq_row_4 j

  · exact k7t3p4_local_1_eq_row_5 j

  · exact k7t3p4_local_1_eq_row_6 j

  · exact k7t3p4_local_1_eq_row_7 j

private theorem k7t3p4_local_1_paths : ∀ p ∈ k7t3p4_step_1_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_1_data.i k7t3p4_step_1_data.j) 7 := by decide

private theorem k7t3p4_local_1_bad : k7t3p4_step_1_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_1_data.i k7t3p4_step_1_data.j) k7t3p4_local_1 7 3 := by decide

private theorem k7t3p4_step_1_check : k7t3p4_step_1.Check k7t3p4.graph k7t3p4_state_1 7 3 := by
  change k7t3p4_step_1_data.Check k7t3p4.graph k7t3p4_state_1 7 3
  refine ⟨by decide, k7t3p4_local_1_paths, ?_⟩
  rw [k7t3p4_local_1_eq]
  exact k7t3p4_local_1_bad

private theorem k7t3p4_update_1 : k7t3p4_step_1.apply k7t3p4_state_1 = k7t3p4_state_2 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_1.apply k7t3p4_state_1 i j = k7t3p4_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_2 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, Finset.Icc 0 4, ∅, {0, 1}, {0, 1}, ∅, Finset.Icc 0 5, {1}],
    #[Finset.Icc 0 4, ∅, {1}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5, {1}],
    #[∅, {1}, ∅, {1, 2}, ∅, ∅, {3, 4, 5}, ∅],
    #[{0, 1}, {1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {0, 1, 3, 4}, {3, 4, 5}],
    #[{0, 1}, Finset.Icc 0 4, ∅, {1, 2}, ∅, {1, 2}, {1, 2, 3, 5}, ∅],
    #[∅, Finset.Icc 1 4, ∅, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 1 5, {3, 4, 5}, {0, 1, 3, 4}, {1, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, {1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_2_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 0 j = k7t3p4_local_2 0 j := by decide

private theorem k7t3p4_local_2_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 1 j = k7t3p4_local_2 1 j := by decide

private theorem k7t3p4_local_2_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 2 j = k7t3p4_local_2 2 j := by decide

private theorem k7t3p4_local_2_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 3 j = k7t3p4_local_2 3 j := by decide

private theorem k7t3p4_local_2_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 4 j = k7t3p4_local_2 4 j := by decide

private theorem k7t3p4_local_2_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 5 j = k7t3p4_local_2 5 j := by decide

private theorem k7t3p4_local_2_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 6 j = k7t3p4_local_2 6 j := by decide

private theorem k7t3p4_local_2_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) 7 j = k7t3p4_local_2 7 j := by decide

private theorem k7t3p4_local_2_eq : (fun a b => freshMatrix k7t3p4_state_2 a b ∪ requiredMatrix 7 k7t3p4_step_2_data.required a b) = k7t3p4_local_2 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_2_eq_row_0 j

  · exact k7t3p4_local_2_eq_row_1 j

  · exact k7t3p4_local_2_eq_row_2 j

  · exact k7t3p4_local_2_eq_row_3 j

  · exact k7t3p4_local_2_eq_row_4 j

  · exact k7t3p4_local_2_eq_row_5 j

  · exact k7t3p4_local_2_eq_row_6 j

  · exact k7t3p4_local_2_eq_row_7 j

private theorem k7t3p4_local_2_paths : ∀ p ∈ k7t3p4_step_2_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_2_data.i k7t3p4_step_2_data.j) 7 := by decide

private theorem k7t3p4_local_2_bad : k7t3p4_step_2_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_2_data.i k7t3p4_step_2_data.j) k7t3p4_local_2 7 3 := by decide

private theorem k7t3p4_step_2_check : k7t3p4_step_2.Check k7t3p4.graph k7t3p4_state_2 7 3 := by
  change k7t3p4_step_2_data.Check k7t3p4.graph k7t3p4_state_2 7 3
  refine ⟨by decide, k7t3p4_local_2_paths, ?_⟩
  rw [k7t3p4_local_2_eq]
  exact k7t3p4_local_2_bad

private theorem k7t3p4_update_2 : k7t3p4_step_2.apply k7t3p4_state_2 = k7t3p4_state_3 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_2.apply k7t3p4_state_2 i j = k7t3p4_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_3 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1}, ∅, ∅, {0}, {0}, ∅, ∅],
    #[{0, 1}, ∅, {1, 2}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 4, 5}, {1}],
    #[∅, {1, 2}, ∅, {1, 2}, {1}, {0, 1}, {3, 4, 5}, ∅],
    #[∅, {1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {3, 4}, {3, 4, 5}],
    #[{0}, Finset.Icc 0 4, {1}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {0}],
    #[{0}, Finset.Icc 0 4, {0, 1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[∅, {1, 2, 4, 5}, {3, 4, 5}, {3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[∅, {1}, ∅, {3, 4, 5}, {0}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_3_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 0 j = k7t3p4_local_3 0 j := by decide

private theorem k7t3p4_local_3_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 1 j = k7t3p4_local_3 1 j := by decide

private theorem k7t3p4_local_3_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 2 j = k7t3p4_local_3 2 j := by decide

private theorem k7t3p4_local_3_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 3 j = k7t3p4_local_3 3 j := by decide

private theorem k7t3p4_local_3_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 4 j = k7t3p4_local_3 4 j := by decide

private theorem k7t3p4_local_3_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 5 j = k7t3p4_local_3 5 j := by decide

private theorem k7t3p4_local_3_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 6 j = k7t3p4_local_3 6 j := by decide

private theorem k7t3p4_local_3_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) 7 j = k7t3p4_local_3 7 j := by decide

private theorem k7t3p4_local_3_eq : (fun a b => freshMatrix k7t3p4_state_3 a b ∪ requiredMatrix 7 k7t3p4_step_3_data.required a b) = k7t3p4_local_3 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_3_eq_row_0 j

  · exact k7t3p4_local_3_eq_row_1 j

  · exact k7t3p4_local_3_eq_row_2 j

  · exact k7t3p4_local_3_eq_row_3 j

  · exact k7t3p4_local_3_eq_row_4 j

  · exact k7t3p4_local_3_eq_row_5 j

  · exact k7t3p4_local_3_eq_row_6 j

  · exact k7t3p4_local_3_eq_row_7 j

private theorem k7t3p4_local_3_paths : ∀ p ∈ k7t3p4_step_3_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_3_data.i k7t3p4_step_3_data.j) 7 := by decide

private theorem k7t3p4_local_3_bad : k7t3p4_step_3_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_3_data.i k7t3p4_step_3_data.j) k7t3p4_local_3 7 3 := by decide

private theorem k7t3p4_step_3_check : k7t3p4_step_3.Check k7t3p4.graph k7t3p4_state_3 7 3 := by
  change k7t3p4_step_3_data.Check k7t3p4.graph k7t3p4_state_3 7 3
  refine ⟨by decide, k7t3p4_local_3_paths, ?_⟩
  rw [k7t3p4_local_3_eq]
  exact k7t3p4_local_3_bad

private theorem k7t3p4_update_3 : k7t3p4_step_3.apply k7t3p4_state_3 = k7t3p4_state_4 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_3.apply k7t3p4_state_3 i j = k7t3p4_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_4 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, Finset.Icc 0 4, {1}, Finset.Icc 0 5, ∅, {0, 1}, {0, 1}, ∅],
    #[Finset.Icc 0 4, ∅, {1}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 0 4, {1, 2, 4, 5}, {1}],
    #[{1}, {1}, ∅, {1, 2}, ∅, {1}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 1 5, {1, 2}, ∅, {1, 2}, {1, 2, 3, 5}, {0, 1, 3, 4}, {3, 4, 5}],
    #[∅, Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, ∅],
    #[{0, 1}, Finset.Icc 0 4, {1}, {1, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{0, 1}, {1, 2, 4, 5}, {3, 4, 5}, {0, 1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[∅, {1}, ∅, {3, 4, 5}, ∅, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_4_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 0 j = k7t3p4_local_4 0 j := by decide

private theorem k7t3p4_local_4_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 1 j = k7t3p4_local_4 1 j := by decide

private theorem k7t3p4_local_4_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 2 j = k7t3p4_local_4 2 j := by decide

private theorem k7t3p4_local_4_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 3 j = k7t3p4_local_4 3 j := by decide

private theorem k7t3p4_local_4_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 4 j = k7t3p4_local_4 4 j := by decide

private theorem k7t3p4_local_4_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 5 j = k7t3p4_local_4 5 j := by decide

private theorem k7t3p4_local_4_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 6 j = k7t3p4_local_4 6 j := by decide

private theorem k7t3p4_local_4_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) 7 j = k7t3p4_local_4 7 j := by decide

private theorem k7t3p4_local_4_eq : (fun a b => freshMatrix k7t3p4_state_4 a b ∪ requiredMatrix 7 k7t3p4_step_4_data.required a b) = k7t3p4_local_4 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_4_eq_row_0 j

  · exact k7t3p4_local_4_eq_row_1 j

  · exact k7t3p4_local_4_eq_row_2 j

  · exact k7t3p4_local_4_eq_row_3 j

  · exact k7t3p4_local_4_eq_row_4 j

  · exact k7t3p4_local_4_eq_row_5 j

  · exact k7t3p4_local_4_eq_row_6 j

  · exact k7t3p4_local_4_eq_row_7 j

private theorem k7t3p4_local_4_paths : ∀ p ∈ k7t3p4_step_4_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_4_data.i k7t3p4_step_4_data.j) 7 := by decide

private theorem k7t3p4_local_4_bad : k7t3p4_step_4_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_4_data.i k7t3p4_step_4_data.j) k7t3p4_local_4 7 3 := by decide

private theorem k7t3p4_step_4_check : k7t3p4_step_4.Check k7t3p4.graph k7t3p4_state_4 7 3 := by
  change k7t3p4_step_4_data.Check k7t3p4.graph k7t3p4_state_4 7 3
  refine ⟨by decide, k7t3p4_local_4_paths, ?_⟩
  rw [k7t3p4_local_4_eq]
  exact k7t3p4_local_4_bad

private theorem k7t3p4_update_4 : k7t3p4_step_4.apply k7t3p4_state_4 = k7t3p4_state_5 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_4.apply k7t3p4_state_4 i j = k7t3p4_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, ∅, {1}, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2}, ∅, {1, 2}, Finset.Icc 1 5, Finset.Icc 1 4, {3, 4, 5}],
    #[Finset.Icc 1 4, ∅, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, Finset.Icc 1 5, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, Finset.Icc 1 4, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_5_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 0 j = k7t3p4_local_5 0 j := by decide

private theorem k7t3p4_local_5_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 1 j = k7t3p4_local_5 1 j := by decide

private theorem k7t3p4_local_5_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 2 j = k7t3p4_local_5 2 j := by decide

private theorem k7t3p4_local_5_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 3 j = k7t3p4_local_5 3 j := by decide

private theorem k7t3p4_local_5_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 4 j = k7t3p4_local_5 4 j := by decide

private theorem k7t3p4_local_5_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 5 j = k7t3p4_local_5 5 j := by decide

private theorem k7t3p4_local_5_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) 6 j = k7t3p4_local_5 6 j := by decide

private theorem k7t3p4_local_5_eq : (fun a b => k7t3p4_state_5 a b ∪ requiredMatrix 7 k7t3p4_step_5_data.required a b) = k7t3p4_local_5 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_5_eq_row_0 j

  · exact k7t3p4_local_5_eq_row_1 j

  · exact k7t3p4_local_5_eq_row_2 j

  · exact k7t3p4_local_5_eq_row_3 j

  · exact k7t3p4_local_5_eq_row_4 j

  · exact k7t3p4_local_5_eq_row_5 j

  · exact k7t3p4_local_5_eq_row_6 j

private theorem k7t3p4_local_5_paths : ∀ p ∈ k7t3p4_step_5_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_5_data.i k7t3p4_step_5_data.j) 7 := by decide

private theorem k7t3p4_local_5_bad : k7t3p4_step_5_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_5_data.i k7t3p4_step_5_data.j) k7t3p4_local_5 7 3 := by decide

private theorem k7t3p4_step_5_check : k7t3p4_step_5.Check k7t3p4.graph k7t3p4_state_5 7 3 := by
  change k7t3p4_step_5_data.Check k7t3p4.graph k7t3p4_state_5 7 3
  refine ⟨k7t3p4_local_5_paths, ?_⟩
  rw [k7t3p4_local_5_eq]
  exact k7t3p4_local_5_bad

private theorem k7t3p4_update_5 : k7t3p4_step_5.apply k7t3p4_state_5 = k7t3p4_state_6 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_5.apply k7t3p4_state_5 i j = k7t3p4_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_6 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1, 2}, ∅, {0, 1}, ∅, {0}, ∅, ∅],
    #[{0, 1, 2}, ∅, {1}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[∅, {1}, ∅, {1, 2}, {0}, {1}, {3, 4, 5}, ∅],
    #[{0, 1}, Finset.Icc 0 5, {1, 2}, ∅, {1, 2}, {0, 1, 2, 3, 5}, {1, 3, 4}, {1, 3, 4, 5}],
    #[∅, Finset.Icc 1 4, {0}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[{0}, Finset.Icc 1 4, {1}, {0, 1, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[∅, {1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[∅, {1}, ∅, {1, 3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_6_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 0 j = k7t3p4_local_6 0 j := by decide

private theorem k7t3p4_local_6_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 1 j = k7t3p4_local_6 1 j := by decide

private theorem k7t3p4_local_6_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 2 j = k7t3p4_local_6 2 j := by decide

private theorem k7t3p4_local_6_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 3 j = k7t3p4_local_6 3 j := by decide

private theorem k7t3p4_local_6_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 4 j = k7t3p4_local_6 4 j := by decide

private theorem k7t3p4_local_6_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 5 j = k7t3p4_local_6 5 j := by decide

private theorem k7t3p4_local_6_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 6 j = k7t3p4_local_6 6 j := by decide

private theorem k7t3p4_local_6_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) 7 j = k7t3p4_local_6 7 j := by decide

private theorem k7t3p4_local_6_eq : (fun a b => freshMatrix k7t3p4_state_6 a b ∪ requiredMatrix 7 k7t3p4_step_6_data.required a b) = k7t3p4_local_6 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_6_eq_row_0 j

  · exact k7t3p4_local_6_eq_row_1 j

  · exact k7t3p4_local_6_eq_row_2 j

  · exact k7t3p4_local_6_eq_row_3 j

  · exact k7t3p4_local_6_eq_row_4 j

  · exact k7t3p4_local_6_eq_row_5 j

  · exact k7t3p4_local_6_eq_row_6 j

  · exact k7t3p4_local_6_eq_row_7 j

private theorem k7t3p4_local_6_paths : ∀ p ∈ k7t3p4_step_6_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_6_data.i k7t3p4_step_6_data.j) 7 := by decide

private theorem k7t3p4_local_6_bad : k7t3p4_step_6_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_6_data.i k7t3p4_step_6_data.j) k7t3p4_local_6 7 3 := by decide

private theorem k7t3p4_step_6_check : k7t3p4_step_6.Check k7t3p4.graph k7t3p4_state_6 7 3 := by
  change k7t3p4_step_6_data.Check k7t3p4.graph k7t3p4_state_6 7 3
  refine ⟨by decide, k7t3p4_local_6_paths, ?_⟩
  rw [k7t3p4_local_6_eq]
  exact k7t3p4_local_6_bad

private theorem k7t3p4_update_6 : k7t3p4_step_6.apply k7t3p4_state_6 = k7t3p4_state_7 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_6.apply k7t3p4_state_6 i j = k7t3p4_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, Finset.Icc 1 5, {1}],
    #[Finset.Icc 1 4, {1}, {2, 3, 5}, {1, 2}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {3, 4, 5}, {1, 3, 4}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_7_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 0 j = k7t3p4_local_7 0 j := by decide

private theorem k7t3p4_local_7_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 1 j = k7t3p4_local_7 1 j := by decide

private theorem k7t3p4_local_7_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 2 j = k7t3p4_local_7 2 j := by decide

private theorem k7t3p4_local_7_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 3 j = k7t3p4_local_7 3 j := by decide

private theorem k7t3p4_local_7_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 4 j = k7t3p4_local_7 4 j := by decide

private theorem k7t3p4_local_7_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 5 j = k7t3p4_local_7 5 j := by decide

private theorem k7t3p4_local_7_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) 6 j = k7t3p4_local_7 6 j := by decide

private theorem k7t3p4_local_7_eq : (fun a b => k7t3p4_state_7 a b ∪ requiredMatrix 7 k7t3p4_step_7_data.required a b) = k7t3p4_local_7 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_7_eq_row_0 j

  · exact k7t3p4_local_7_eq_row_1 j

  · exact k7t3p4_local_7_eq_row_2 j

  · exact k7t3p4_local_7_eq_row_3 j

  · exact k7t3p4_local_7_eq_row_4 j

  · exact k7t3p4_local_7_eq_row_5 j

  · exact k7t3p4_local_7_eq_row_6 j

private theorem k7t3p4_local_7_paths : ∀ p ∈ k7t3p4_step_7_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_7_data.i k7t3p4_step_7_data.j) 7 := by decide

private theorem k7t3p4_local_7_bad : k7t3p4_step_7_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_7_data.i k7t3p4_step_7_data.j) k7t3p4_local_7 7 3 := by decide

private theorem k7t3p4_step_7_check : k7t3p4_step_7.Check k7t3p4.graph k7t3p4_state_7 7 3 := by
  change k7t3p4_step_7_data.Check k7t3p4.graph k7t3p4_state_7 7 3
  refine ⟨k7t3p4_local_7_paths, ?_⟩
  rw [k7t3p4_local_7_eq]
  exact k7t3p4_local_7_bad

private theorem k7t3p4_update_7 : k7t3p4_step_7.apply k7t3p4_state_7 = k7t3p4_state_8 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_7.apply k7t3p4_state_7 i j = k7t3p4_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2, 3}, ∅, {1, 2}, {2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, Finset.Icc 0 5, {1, 2}, ∅, {1, 2}, {1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_8_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 0 j = k7t3p4_local_8 0 j := by decide

private theorem k7t3p4_local_8_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 1 j = k7t3p4_local_8 1 j := by decide

private theorem k7t3p4_local_8_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 2 j = k7t3p4_local_8 2 j := by decide

private theorem k7t3p4_local_8_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 3 j = k7t3p4_local_8 3 j := by decide

private theorem k7t3p4_local_8_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 4 j = k7t3p4_local_8 4 j := by decide

private theorem k7t3p4_local_8_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 5 j = k7t3p4_local_8 5 j := by decide

private theorem k7t3p4_local_8_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) 6 j = k7t3p4_local_8 6 j := by decide

private theorem k7t3p4_local_8_eq : (fun a b => k7t3p4_state_8 a b ∪ requiredMatrix 7 k7t3p4_step_8_data.required a b) = k7t3p4_local_8 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_8_eq_row_0 j

  · exact k7t3p4_local_8_eq_row_1 j

  · exact k7t3p4_local_8_eq_row_2 j

  · exact k7t3p4_local_8_eq_row_3 j

  · exact k7t3p4_local_8_eq_row_4 j

  · exact k7t3p4_local_8_eq_row_5 j

  · exact k7t3p4_local_8_eq_row_6 j

private theorem k7t3p4_local_8_paths : ∀ p ∈ k7t3p4_step_8_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_8_data.i k7t3p4_step_8_data.j) 7 := by decide

private theorem k7t3p4_local_8_bad : k7t3p4_step_8_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_8_data.i k7t3p4_step_8_data.j) k7t3p4_local_8 7 3 := by decide

private theorem k7t3p4_step_8_check : k7t3p4_step_8.Check k7t3p4.graph k7t3p4_state_8 7 3 := by
  change k7t3p4_step_8_data.Check k7t3p4.graph k7t3p4_state_8 7 3
  refine ⟨k7t3p4_local_8_paths, ?_⟩
  rw [k7t3p4_local_8_eq]
  exact k7t3p4_local_8_bad

private theorem k7t3p4_update_8 : k7t3p4_step_8.apply k7t3p4_state_8 = k7t3p4_state_9 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_8.apply k7t3p4_state_8 i j = k7t3p4_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, Finset.Icc 1 4, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, Finset.Icc 0 5, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, ∅],
    #[Finset.Icc 1 5, {3, 4, 5}, Finset.Icc 1 4, Finset.Icc 0 5, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_9_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 0 j = k7t3p4_local_9 0 j := by decide

private theorem k7t3p4_local_9_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 1 j = k7t3p4_local_9 1 j := by decide

private theorem k7t3p4_local_9_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 2 j = k7t3p4_local_9 2 j := by decide

private theorem k7t3p4_local_9_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 3 j = k7t3p4_local_9 3 j := by decide

private theorem k7t3p4_local_9_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 4 j = k7t3p4_local_9 4 j := by decide

private theorem k7t3p4_local_9_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 5 j = k7t3p4_local_9 5 j := by decide

private theorem k7t3p4_local_9_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) 6 j = k7t3p4_local_9 6 j := by decide

private theorem k7t3p4_local_9_eq : (fun a b => k7t3p4_state_9 a b ∪ requiredMatrix 7 k7t3p4_step_9_data.required a b) = k7t3p4_local_9 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_9_eq_row_0 j

  · exact k7t3p4_local_9_eq_row_1 j

  · exact k7t3p4_local_9_eq_row_2 j

  · exact k7t3p4_local_9_eq_row_3 j

  · exact k7t3p4_local_9_eq_row_4 j

  · exact k7t3p4_local_9_eq_row_5 j

  · exact k7t3p4_local_9_eq_row_6 j

private theorem k7t3p4_local_9_paths : ∀ p ∈ k7t3p4_step_9_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_9_data.i k7t3p4_step_9_data.j) 7 := by decide

private theorem k7t3p4_local_9_bad : k7t3p4_step_9_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_9_data.i k7t3p4_step_9_data.j) k7t3p4_local_9 7 3 := by decide

private theorem k7t3p4_step_9_check : k7t3p4_step_9.Check k7t3p4.graph k7t3p4_state_9 7 3 := by
  change k7t3p4_step_9_data.Check k7t3p4.graph k7t3p4_state_9 7 3
  refine ⟨k7t3p4_local_9_paths, ?_⟩
  rw [k7t3p4_local_9_eq]
  exact k7t3p4_local_9_bad

private theorem k7t3p4_update_9 : k7t3p4_step_9.apply k7t3p4_state_9 = k7t3p4_state_10 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_9.apply k7t3p4_state_9 i j = k7t3p4_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_11 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_10 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1, 2}, ∅, ∅, {0}, ∅, {0, 1}, ∅],
    #[{0, 1, 2}, ∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 0 5, {1}],
    #[∅, {1}, ∅, {1, 2}, {0, 1}, {1}, {1, 3, 4, 5}, ∅],
    #[∅, {1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[{0}, Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 1, 2, 3, 5}, {1}],
    #[∅, Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0}],
    #[{0, 1}, Finset.Icc 0 5, {1, 3, 4, 5}, {1, 3, 4}, {0, 1, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[∅, {1}, ∅, {3, 4, 5}, {1}, {0}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_10_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 0 j = k7t3p4_local_10 0 j := by decide

private theorem k7t3p4_local_10_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 1 j = k7t3p4_local_10 1 j := by decide

private theorem k7t3p4_local_10_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 2 j = k7t3p4_local_10 2 j := by decide

private theorem k7t3p4_local_10_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 3 j = k7t3p4_local_10 3 j := by decide

private theorem k7t3p4_local_10_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 4 j = k7t3p4_local_10 4 j := by decide

private theorem k7t3p4_local_10_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 5 j = k7t3p4_local_10 5 j := by decide

private theorem k7t3p4_local_10_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 6 j = k7t3p4_local_10 6 j := by decide

private theorem k7t3p4_local_10_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) 7 j = k7t3p4_local_10 7 j := by decide

private theorem k7t3p4_local_10_eq : (fun a b => freshMatrix k7t3p4_state_10 a b ∪ requiredMatrix 7 k7t3p4_step_10_data.required a b) = k7t3p4_local_10 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_10_eq_row_0 j

  · exact k7t3p4_local_10_eq_row_1 j

  · exact k7t3p4_local_10_eq_row_2 j

  · exact k7t3p4_local_10_eq_row_3 j

  · exact k7t3p4_local_10_eq_row_4 j

  · exact k7t3p4_local_10_eq_row_5 j

  · exact k7t3p4_local_10_eq_row_6 j

  · exact k7t3p4_local_10_eq_row_7 j

private theorem k7t3p4_local_10_paths : ∀ p ∈ k7t3p4_step_10_data.required, p.Check (freshGraph k7t3p4.graph k7t3p4_step_10_data.i k7t3p4_step_10_data.j) 7 := by decide

private theorem k7t3p4_local_10_bad : k7t3p4_step_10_data.bad.Check (freshGraph k7t3p4.graph k7t3p4_step_10_data.i k7t3p4_step_10_data.j) k7t3p4_local_10 7 3 := by decide

private theorem k7t3p4_step_10_check : k7t3p4_step_10.Check k7t3p4.graph k7t3p4_state_10 7 3 := by
  change k7t3p4_step_10_data.Check k7t3p4.graph k7t3p4_state_10 7 3
  refine ⟨by decide, k7t3p4_local_10_paths, ?_⟩
  rw [k7t3p4_local_10_eq]
  exact k7t3p4_local_10_bad

private theorem k7t3p4_update_10 : k7t3p4_step_10.apply k7t3p4_state_10 = k7t3p4_state_11 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_10.apply k7t3p4_state_10 i j = k7t3p4_state_11 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_12 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_11 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 1, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 1 4, {0, 1}, {1, 2}, ∅, {1, 2, 3}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 1, 2, 3, 5}, {1, 2, 3}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_11_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 0 j = k7t3p4_local_11 0 j := by decide

private theorem k7t3p4_local_11_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 1 j = k7t3p4_local_11 1 j := by decide

private theorem k7t3p4_local_11_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 2 j = k7t3p4_local_11 2 j := by decide

private theorem k7t3p4_local_11_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 3 j = k7t3p4_local_11 3 j := by decide

private theorem k7t3p4_local_11_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 4 j = k7t3p4_local_11 4 j := by decide

private theorem k7t3p4_local_11_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 5 j = k7t3p4_local_11 5 j := by decide

private theorem k7t3p4_local_11_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) 6 j = k7t3p4_local_11 6 j := by decide

private theorem k7t3p4_local_11_eq : (fun a b => k7t3p4_state_11 a b ∪ requiredMatrix 7 k7t3p4_step_11_data.required a b) = k7t3p4_local_11 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_11_eq_row_0 j

  · exact k7t3p4_local_11_eq_row_1 j

  · exact k7t3p4_local_11_eq_row_2 j

  · exact k7t3p4_local_11_eq_row_3 j

  · exact k7t3p4_local_11_eq_row_4 j

  · exact k7t3p4_local_11_eq_row_5 j

  · exact k7t3p4_local_11_eq_row_6 j

private theorem k7t3p4_local_11_paths : ∀ p ∈ k7t3p4_step_11_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_11_data.i k7t3p4_step_11_data.j) 7 := by decide

private theorem k7t3p4_local_11_bad : k7t3p4_step_11_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_11_data.i k7t3p4_step_11_data.j) k7t3p4_local_11 7 3 := by decide

private theorem k7t3p4_step_11_check : k7t3p4_step_11.Check k7t3p4.graph k7t3p4_state_11 7 3 := by
  change k7t3p4_step_11_data.Check k7t3p4.graph k7t3p4_state_11 7 3
  refine ⟨k7t3p4_local_11_paths, ?_⟩
  rw [k7t3p4_local_11_eq]
  exact k7t3p4_local_11_bad

private theorem k7t3p4_update_11 : k7t3p4_step_11.apply k7t3p4_state_11 = k7t3p4_state_12 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_11.apply k7t3p4_state_11 i j = k7t3p4_state_12 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_13 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 0 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_12 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 1 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, {0, 1}, {1, 2}, ∅, {1, 2, 3}, {0, 1, 2, 3, 5}, {1}],
    #[Finset.Icc 1 4, {1}, {0, 2, 3, 5}, {1, 2, 3}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 1, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_12_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 0 j = k7t3p4_local_12 0 j := by decide

private theorem k7t3p4_local_12_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 1 j = k7t3p4_local_12 1 j := by decide

private theorem k7t3p4_local_12_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 2 j = k7t3p4_local_12 2 j := by decide

private theorem k7t3p4_local_12_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 3 j = k7t3p4_local_12 3 j := by decide

private theorem k7t3p4_local_12_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 4 j = k7t3p4_local_12 4 j := by decide

private theorem k7t3p4_local_12_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 5 j = k7t3p4_local_12 5 j := by decide

private theorem k7t3p4_local_12_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) 6 j = k7t3p4_local_12 6 j := by decide

private theorem k7t3p4_local_12_eq : (fun a b => k7t3p4_state_12 a b ∪ requiredMatrix 7 k7t3p4_step_12_data.required a b) = k7t3p4_local_12 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_12_eq_row_0 j

  · exact k7t3p4_local_12_eq_row_1 j

  · exact k7t3p4_local_12_eq_row_2 j

  · exact k7t3p4_local_12_eq_row_3 j

  · exact k7t3p4_local_12_eq_row_4 j

  · exact k7t3p4_local_12_eq_row_5 j

  · exact k7t3p4_local_12_eq_row_6 j

private theorem k7t3p4_local_12_paths : ∀ p ∈ k7t3p4_step_12_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_12_data.i k7t3p4_step_12_data.j) 7 := by decide

private theorem k7t3p4_local_12_bad : k7t3p4_step_12_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_12_data.i k7t3p4_step_12_data.j) k7t3p4_local_12 7 3 := by decide

private theorem k7t3p4_step_12_check : k7t3p4_step_12.Check k7t3p4.graph k7t3p4_state_12 7 3 := by
  change k7t3p4_step_12_data.Check k7t3p4.graph k7t3p4_state_12 7 3
  refine ⟨k7t3p4_local_12_paths, ?_⟩
  rw [k7t3p4_local_12_eq]
  exact k7t3p4_local_12_bad

private theorem k7t3p4_update_12 : k7t3p4_step_12.apply k7t3p4_state_12 = k7t3p4_state_13 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_12.apply k7t3p4_state_12 i j = k7t3p4_state_13 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p4_state_14 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, {1, 2, 4, 5}, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[{1, 2, 4, 5}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 4, {0, 1}, {1, 2}, ∅, {1, 2}, {0, 2, 3, 5}, {0, 1}],
    #[Finset.Icc 0 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {0, 1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p4_local_13 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1}, Finset.Icc 1 5, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 4, 5}, {1}],
    #[{1}, ∅, {1, 2}, {0, 1}, {1}, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, {1, 2}, ∅, Finset.Icc 1 4, {0, 2, 3, 5}, {1, 3, 4}, {3, 4, 5}],
    #[Finset.Icc 0 5, {0, 1}, Finset.Icc 1 4, ∅, {1, 2}, {0, 2, 3, 5}, {1}],
    #[Finset.Icc 0 4, {1}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}, {0, 1}],
    #[{1, 2, 4, 5}, {3, 4, 5}, {1, 3, 4}, {0, 2, 3, 5}, {1, 2}, ∅, {1, 2}],
    #[{1}, ∅, {3, 4, 5}, {1}, {0, 1}, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p4_local_13_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 0 j = k7t3p4_local_13 0 j := by decide

private theorem k7t3p4_local_13_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 1 j = k7t3p4_local_13 1 j := by decide

private theorem k7t3p4_local_13_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 2 j = k7t3p4_local_13 2 j := by decide

private theorem k7t3p4_local_13_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 3 j = k7t3p4_local_13 3 j := by decide

private theorem k7t3p4_local_13_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 4 j = k7t3p4_local_13 4 j := by decide

private theorem k7t3p4_local_13_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 5 j = k7t3p4_local_13 5 j := by decide

private theorem k7t3p4_local_13_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) 6 j = k7t3p4_local_13 6 j := by decide

private theorem k7t3p4_local_13_eq : (fun a b => k7t3p4_state_13 a b ∪ requiredMatrix 7 k7t3p4_step_13_data.required a b) = k7t3p4_local_13 := by
  funext i j
  fin_cases i

  · exact k7t3p4_local_13_eq_row_0 j

  · exact k7t3p4_local_13_eq_row_1 j

  · exact k7t3p4_local_13_eq_row_2 j

  · exact k7t3p4_local_13_eq_row_3 j

  · exact k7t3p4_local_13_eq_row_4 j

  · exact k7t3p4_local_13_eq_row_5 j

  · exact k7t3p4_local_13_eq_row_6 j

private theorem k7t3p4_local_13_paths : ∀ p ∈ k7t3p4_step_13_data.required, p.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_13_data.i k7t3p4_step_13_data.j) 7 := by decide

private theorem k7t3p4_local_13_bad : k7t3p4_step_13_data.bad.Check (addedEdgeGraph k7t3p4.graph k7t3p4_step_13_data.i k7t3p4_step_13_data.j) k7t3p4_local_13 7 3 := by decide

private theorem k7t3p4_step_13_check : k7t3p4_step_13.Check k7t3p4.graph k7t3p4_state_13 7 3 := by
  change k7t3p4_step_13_data.Check k7t3p4.graph k7t3p4_state_13 7 3
  refine ⟨k7t3p4_local_13_paths, ?_⟩
  rw [k7t3p4_local_13_eq]
  exact k7t3p4_local_13_bad

private theorem k7t3p4_update_13 : k7t3p4_step_13.apply k7t3p4_state_13 = k7t3p4_state_14 := by
  have h : ∀ i j : Fin 7, k7t3p4_step_13.apply k7t3p4_state_13 i j = k7t3p4_state_14 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k7t3p4_closure_14 : ClosureCheck k7t3p4.graph k7t3p4_state_14 7 3 [] := by trivial

private theorem k7t3p4_closure_13 : ClosureCheck k7t3p4.graph k7t3p4_state_13 7 3 [k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_13_check
  · rw [k7t3p4_update_13]
    exact k7t3p4_closure_14

private theorem k7t3p4_closure_12 : ClosureCheck k7t3p4.graph k7t3p4_state_12 7 3 [k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_12_check
  · rw [k7t3p4_update_12]
    exact k7t3p4_closure_13

private theorem k7t3p4_closure_11 : ClosureCheck k7t3p4.graph k7t3p4_state_11 7 3 [k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_11_check
  · rw [k7t3p4_update_11]
    exact k7t3p4_closure_12

private theorem k7t3p4_closure_10 : ClosureCheck k7t3p4.graph k7t3p4_state_10 7 3 [k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_10_check
  · rw [k7t3p4_update_10]
    exact k7t3p4_closure_11

private theorem k7t3p4_closure_9 : ClosureCheck k7t3p4.graph k7t3p4_state_9 7 3 [k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_9_check
  · rw [k7t3p4_update_9]
    exact k7t3p4_closure_10

private theorem k7t3p4_closure_8 : ClosureCheck k7t3p4.graph k7t3p4_state_8 7 3 [k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_8_check
  · rw [k7t3p4_update_8]
    exact k7t3p4_closure_9

private theorem k7t3p4_closure_7 : ClosureCheck k7t3p4.graph k7t3p4_state_7 7 3 [k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_7_check
  · rw [k7t3p4_update_7]
    exact k7t3p4_closure_8

private theorem k7t3p4_closure_6 : ClosureCheck k7t3p4.graph k7t3p4_state_6 7 3 [k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_6_check
  · rw [k7t3p4_update_6]
    exact k7t3p4_closure_7

private theorem k7t3p4_closure_5 : ClosureCheck k7t3p4.graph k7t3p4_state_5 7 3 [k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_5_check
  · rw [k7t3p4_update_5]
    exact k7t3p4_closure_6

private theorem k7t3p4_closure_4 : ClosureCheck k7t3p4.graph k7t3p4_state_4 7 3 [k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_4_check
  · rw [k7t3p4_update_4]
    exact k7t3p4_closure_5

private theorem k7t3p4_closure_3 : ClosureCheck k7t3p4.graph k7t3p4_state_3 7 3 [k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_3_check
  · rw [k7t3p4_update_3]
    exact k7t3p4_closure_4

private theorem k7t3p4_closure_2 : ClosureCheck k7t3p4.graph k7t3p4_state_2 7 3 [k7t3p4_step_2, k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_2_check
  · rw [k7t3p4_update_2]
    exact k7t3p4_closure_3

private theorem k7t3p4_closure_1 : ClosureCheck k7t3p4.graph k7t3p4_state_1 7 3 [k7t3p4_step_1, k7t3p4_step_2, k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_1_check
  · rw [k7t3p4_update_1]
    exact k7t3p4_closure_2

private theorem k7t3p4_closure_0 : ClosureCheck k7t3p4.graph k7t3p4_state_0 7 3 [k7t3p4_step_0, k7t3p4_step_1, k7t3p4_step_2, k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] := by
  constructor
  · exact k7t3p4_step_0_check
  · rw [k7t3p4_update_0]
    exact k7t3p4_closure_1

private theorem k7t3p4_matrix_eq : k7t3p4.matrix 7 = k7t3p4_state_14 := by
  change closureMatrix (k7t3p4.initialMatrix 7) _ = _
  rw [k7t3p4_initial_eq]
  change closureMatrix k7t3p4_state_0 [k7t3p4_step_0, k7t3p4_step_1, k7t3p4_step_2, k7t3p4_step_3, k7t3p4_step_4, k7t3p4_step_5, k7t3p4_step_6, k7t3p4_step_7, k7t3p4_step_8, k7t3p4_step_9, k7t3p4_step_10, k7t3p4_step_11, k7t3p4_step_12, k7t3p4_step_13] = _
  simp only [closureMatrix]
  rw [k7t3p4_update_0, k7t3p4_update_1, k7t3p4_update_2, k7t3p4_update_3, k7t3p4_update_4, k7t3p4_update_5, k7t3p4_update_6, k7t3p4_update_7, k7t3p4_update_8, k7t3p4_update_9, k7t3p4_update_10, k7t3p4_update_11, k7t3p4_update_12, k7t3p4_update_13]

private theorem k7t3p4_part_0 : k7t3p4.chains.flatten = List.finRange _ := by decide

private theorem k7t3p4_part_1 : k7t3p4.chains.map List.length = ([[], [4]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p4_part_2 : k7t3p4.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p4.clique))) = ([[], [4]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p4_templates_item_0 : (⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_1 : (⟨0, 2, [], [], [1], 4, 5⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_2 : (⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_3 : (⟨0, 3, [], [], [2, 1], 3, 4⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_4 : (⟨0, 3, [], [], [4, 5, 6], 2, 3⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_5 : (⟨0, 4, [], [], [3, 2, 1], 2, 3⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_6 : (⟨0, 4, [], [], [5, 6], 3, 4⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_7 : (⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_8 : (⟨0, 5, [], [], [6], 4, 5⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_9 : (⟨0, 6, [], [], [5, 4, 3, 2, 1], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_10 : (⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_11 : (⟨1, 5, [], [], [6], 4, 5⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_12 : (⟨2, 3, [], [1], [4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_13 : (⟨2, 4, [], [1], [5, 6], 2, 3⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_14 : (⟨2, 5, [], [1], [6], 3, 4⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_15 : (⟨2, 6, [], [1], [], 4, 5⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_16 : (⟨3, 4, [], [1, 2], [5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_17 : (⟨3, 5, [], [1, 2], [6], 2, 3⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_18 : (⟨4, 5, [], [1, 2, 3], [6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_templates_item_19 : (⟨5, 6, [], [1, 2, 3, 4], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p4_part_3 : ∀ T ∈ k7t3p4.templates, T.Check k7t3p4.graph k7t3p4.clique 7 (patternAmount ([[], [4]] : List (List ℕ))) (([[], [4]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p4_templates_item_0, k7t3p4_templates_item_1, k7t3p4_templates_item_2, k7t3p4_templates_item_3, k7t3p4_templates_item_4, k7t3p4_templates_item_5, k7t3p4_templates_item_6, k7t3p4_templates_item_7, k7t3p4_templates_item_8, k7t3p4_templates_item_9, k7t3p4_templates_item_10, k7t3p4_templates_item_11, k7t3p4_templates_item_12, k7t3p4_templates_item_13, k7t3p4_templates_item_14, k7t3p4_templates_item_15, k7t3p4_templates_item_16, k7t3p4_templates_item_17, k7t3p4_templates_item_18, k7t3p4_templates_item_19⟩

private theorem k7t3p4_required_item_0 : (⟨1, 5, [2, 3, 4]⟩ : RequiredPathData (Fin 7)).Check k7t3p4.graph 7 := by decide

private theorem k7t3p4_required_item_1 : (⟨2, 4, [3]⟩ : RequiredPathData (Fin 7)).Check k7t3p4.graph 7 := by decide

private theorem k7t3p4_required_item_2 : (⟨2, 6, [3, 4, 5]⟩ : RequiredPathData (Fin 7)).Check k7t3p4.graph 7 := by decide

private theorem k7t3p4_required_item_3 : (⟨3, 5, [4]⟩ : RequiredPathData (Fin 7)).Check k7t3p4.graph 7 := by decide

private theorem k7t3p4_part_4 : ∀ p ∈ k7t3p4.required, p.Check k7t3p4.graph 7 := by
  simp only [k7t3p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p4_required_item_0, k7t3p4_required_item_1, k7t3p4_required_item_2, k7t3p4_required_item_3⟩

private theorem k7t3p4_part_5 : ClosureCheck k7t3p4.graph (k7t3p4.initialMatrix 7) 7 3 k7t3p4.closure := by
  rw [k7t3p4_initial_eq]
  exact k7t3p4_closure_0

private theorem k7t3p4_part_6 : k7t3p4.bad.Check k7t3p4.graph (k7t3p4.matrix 7) 7 3 := by
  rw [k7t3p4_matrix_eq]
  decide

theorem k7t3p4_check : k7t3p4.Check 7 3 [[], [4]] :=
  ⟨k7t3p4_part_0, k7t3p4_part_1, k7t3p4_part_2, k7t3p4_part_3, k7t3p4_part_4, k7t3p4_part_5, k7t3p4_part_6⟩
def k7t3p5 : LayoutCertificate 5 where
  chains := [[0, 1, 2, 3, 4]]
  clique := {0, 2, 4}
  templates := [⟨0, 1, [], [], [2], 1, 5⟩,
    ⟨0, 3, [], [], [2], 1, 5⟩,
    ⟨1, 2, [], [0], [], 1, 5⟩,
    ⟨1, 3, [], [0], [2], 1, 4⟩,
    ⟨1, 4, [], [0], [], 1, 5⟩,
    ⟨2, 3, [], [], [4], 1, 5⟩,
    ⟨3, 4, [], [2], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(1, 2), (3, 2), (0, 2)}⟩


private def k7t3p5_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p5_initial_eq_row_0 : ∀ j : Fin 5, (k7t3p5.initialMatrix 7) 0 j = k7t3p5_state_0 0 j := by decide

private theorem k7t3p5_initial_eq_row_1 : ∀ j : Fin 5, (k7t3p5.initialMatrix 7) 1 j = k7t3p5_state_0 1 j := by decide

private theorem k7t3p5_initial_eq_row_2 : ∀ j : Fin 5, (k7t3p5.initialMatrix 7) 2 j = k7t3p5_state_0 2 j := by decide

private theorem k7t3p5_initial_eq_row_3 : ∀ j : Fin 5, (k7t3p5.initialMatrix 7) 3 j = k7t3p5_state_0 3 j := by decide

private theorem k7t3p5_initial_eq_row_4 : ∀ j : Fin 5, (k7t3p5.initialMatrix 7) 4 j = k7t3p5_state_0 4 j := by decide

private theorem k7t3p5_initial_eq : (k7t3p5.initialMatrix 7) = k7t3p5_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p5_initial_eq_row_0 j

  · exact k7t3p5_initial_eq_row_1 j

  · exact k7t3p5_initial_eq_row_2 j

  · exact k7t3p5_initial_eq_row_3 j

  · exact k7t3p5_initial_eq_row_4 j

private theorem k7t3p5_closure_0 : ClosureCheck k7t3p5.graph k7t3p5_state_0 7 3 [] := by trivial

private theorem k7t3p5_matrix_eq : k7t3p5.matrix 7 = k7t3p5_state_0 := by
  change closureMatrix (k7t3p5.initialMatrix 7) _ = _
  rw [k7t3p5_initial_eq]
  change closureMatrix k7t3p5_state_0 [] = _
  rfl

private theorem k7t3p5_part_0 : k7t3p5.chains.flatten = List.finRange _ := by decide

private theorem k7t3p5_part_1 : k7t3p5.chains.map List.length = ([[1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p5_part_2 : k7t3p5.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p5.clique))) = ([[1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p5_templates_item_0 : (⟨0, 1, [], [], [2], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_1 : (⟨0, 3, [], [], [2], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_2 : (⟨1, 2, [], [0], [], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_3 : (⟨1, 3, [], [0], [2], 1, 4⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_4 : (⟨1, 4, [], [0], [], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_5 : (⟨2, 3, [], [], [4], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_templates_item_6 : (⟨3, 4, [], [2], [], 1, 5⟩ : TemplateData (Fin 5)).Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p5_part_3 : ∀ T ∈ k7t3p5.templates, T.Check k7t3p5.graph k7t3p5.clique 7 (patternAmount ([[1, 1]] : List (List ℕ))) (([[1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p5_templates_item_0, k7t3p5_templates_item_1, k7t3p5_templates_item_2, k7t3p5_templates_item_3, k7t3p5_templates_item_4, k7t3p5_templates_item_5, k7t3p5_templates_item_6⟩

private theorem k7t3p5_part_4 : ∀ p ∈ k7t3p5.required, p.Check k7t3p5.graph 7 := by decide

private theorem k7t3p5_part_5 : ClosureCheck k7t3p5.graph (k7t3p5.initialMatrix 7) 7 3 k7t3p5.closure := by
  rw [k7t3p5_initial_eq]
  exact k7t3p5_closure_0

private theorem k7t3p5_part_6 : k7t3p5.bad.Check k7t3p5.graph (k7t3p5.matrix 7) 7 3 := by
  rw [k7t3p5_matrix_eq]
  decide

theorem k7t3p5_check : k7t3p5.Check 7 3 [[1, 1]] :=
  ⟨k7t3p5_part_0, k7t3p5_part_1, k7t3p5_part_2, k7t3p5_part_3, k7t3p5_part_4, k7t3p5_part_5, k7t3p5_part_6⟩
def k7t3p6 : LayoutCertificate 6 where
  chains := [[0, 1, 2, 3, 4, 5]]
  clique := {0, 2, 5}
  templates := [⟨0, 1, [], [], [2], 2, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩,
    ⟨0, 3, [], [], [2], 2, 5⟩,
    ⟨0, 3, [], [], [4, 5], 1, 4⟩,
    ⟨0, 4, [], [], [3, 2], 1, 4⟩,
    ⟨1, 2, [], [0], [3, 4, 5], 1, 2⟩,
    ⟨1, 3, [], [0], [2], 1, 4⟩,
    ⟨1, 4, [], [0], [3, 2], 1, 3⟩,
    ⟨1, 4, [], [0], [5], 1, 4⟩,
    ⟨1, 5, [], [0], [4, 3, 2], 1, 2⟩,
    ⟨2, 3, [], [], [4, 5], 1, 4⟩,
    ⟨3, 4, [], [2], [5], 1, 4⟩,
    ⟨4, 5, [], [2, 3], [], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(1, 2), (0, 2), (3, 2), (4, 2)}⟩


private def k7t3p6_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 5, ∅, {1, 2}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2}],
    #[∅, {1, 2}, ∅, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[∅, {1, 2}, ∅, ∅, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p6_initial_eq_row_0 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 0 j = k7t3p6_state_0 0 j := by decide

private theorem k7t3p6_initial_eq_row_1 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 1 j = k7t3p6_state_0 1 j := by decide

private theorem k7t3p6_initial_eq_row_2 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 2 j = k7t3p6_state_0 2 j := by decide

private theorem k7t3p6_initial_eq_row_3 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 3 j = k7t3p6_state_0 3 j := by decide

private theorem k7t3p6_initial_eq_row_4 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 4 j = k7t3p6_state_0 4 j := by decide

private theorem k7t3p6_initial_eq_row_5 : ∀ j : Fin 6, (k7t3p6.initialMatrix 7) 5 j = k7t3p6_state_0 5 j := by decide

private theorem k7t3p6_initial_eq : (k7t3p6.initialMatrix 7) = k7t3p6_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p6_initial_eq_row_0 j

  · exact k7t3p6_initial_eq_row_1 j

  · exact k7t3p6_initial_eq_row_2 j

  · exact k7t3p6_initial_eq_row_3 j

  · exact k7t3p6_initial_eq_row_4 j

  · exact k7t3p6_initial_eq_row_5 j

private theorem k7t3p6_closure_0 : ClosureCheck k7t3p6.graph k7t3p6_state_0 7 3 [] := by trivial

private theorem k7t3p6_matrix_eq : k7t3p6.matrix 7 = k7t3p6_state_0 := by
  change closureMatrix (k7t3p6.initialMatrix 7) _ = _
  rw [k7t3p6_initial_eq]
  change closureMatrix k7t3p6_state_0 [] = _
  rfl

private theorem k7t3p6_part_0 : k7t3p6.chains.flatten = List.finRange _ := by decide

private theorem k7t3p6_part_1 : k7t3p6.chains.map List.length = ([[1, 2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p6_part_2 : k7t3p6.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p6.clique))) = ([[1, 2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p6_templates_item_0 : (⟨0, 1, [], [], [2], 2, 5⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_2 : (⟨0, 3, [], [], [2], 2, 5⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_3 : (⟨0, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_4 : (⟨0, 4, [], [], [3, 2], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_5 : (⟨1, 2, [], [0], [3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_6 : (⟨1, 3, [], [0], [2], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_7 : (⟨1, 4, [], [0], [3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_8 : (⟨1, 4, [], [0], [5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_9 : (⟨1, 5, [], [0], [4, 3, 2], 1, 2⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_10 : (⟨2, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_11 : (⟨3, 4, [], [2], [5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_templates_item_12 : (⟨4, 5, [], [2, 3], [], 1, 4⟩ : TemplateData (Fin 6)).Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p6_part_3 : ∀ T ∈ k7t3p6.templates, T.Check k7t3p6.graph k7t3p6.clique 7 (patternAmount ([[1, 2]] : List (List ℕ))) (([[1, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p6_templates_item_0, k7t3p6_templates_item_1, k7t3p6_templates_item_2, k7t3p6_templates_item_3, k7t3p6_templates_item_4, k7t3p6_templates_item_5, k7t3p6_templates_item_6, k7t3p6_templates_item_7, k7t3p6_templates_item_8, k7t3p6_templates_item_9, k7t3p6_templates_item_10, k7t3p6_templates_item_11, k7t3p6_templates_item_12⟩

private theorem k7t3p6_part_4 : ∀ p ∈ k7t3p6.required, p.Check k7t3p6.graph 7 := by decide

private theorem k7t3p6_part_5 : ClosureCheck k7t3p6.graph (k7t3p6.initialMatrix 7) 7 3 k7t3p6.closure := by
  rw [k7t3p6_initial_eq]
  exact k7t3p6_closure_0

private theorem k7t3p6_part_6 : k7t3p6.bad.Check k7t3p6.graph (k7t3p6.matrix 7) 7 3 := by
  rw [k7t3p6_matrix_eq]
  decide

theorem k7t3p6_check : k7t3p6.Check 7 3 [[1, 2]] :=
  ⟨k7t3p6_part_0, k7t3p6_part_1, k7t3p6_part_2, k7t3p6_part_3, k7t3p6_part_4, k7t3p6_part_5, k7t3p6_part_6⟩
private def k7t3p7_step_0_data : EdgeAttachmentData 7 := ⟨3, 1, [⟨1, 3, []⟩, ⟨1, 0, [3, 4, 5, 6]⟩, ⟨1, 2, [3, 4, 5, 6]⟩, ⟨2, 3, [0, 1]⟩, ⟨2, 5, [0, 1, 3, 4]⟩, ⟨2, 6, [0, 1, 3, 4, 5]⟩, ⟨2, 3, [1]⟩, ⟨2, 6, [1, 3, 4, 5]⟩, ⟨2, 0, [1, 3, 4, 5, 6]⟩, ⟨2, 4, [3, 1, 0, 6, 5]⟩, ⟨2, 5, [6, 0, 1, 3, 4]⟩, ⟨2, 1, [6, 5, 4, 3]⟩], ⟨none, {(1, 3), (2, 3), (3, 3)}⟩⟩

private def k7t3p7_step_0 : ClosureStep 7 := .edge k7t3p7_step_0_data

private def k7t3p7_step_1_data : EdgeAttachmentData 7 := ⟨4, 0, [⟨0, 1, [4, 5, 6, 2]⟩, ⟨1, 2, [0, 4, 5, 6]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨3, 6, [2, 1, 0, 4, 5]⟩, ⟨3, 5, [4, 0, 1, 2, 6]⟩], ⟨none, {(1, 3), (3, 2), (0, 3)}⟩⟩

private def k7t3p7_step_1 : ClosureStep 7 := .edge k7t3p7_step_1_data

private def k7t3p7_step_2_data : FreshAttachmentData 7 := ⟨4, 0, [⟨2, 0, [1, 3, 4, 5]⟩, ⟨2, 0, [1, 3, 7, 6, 5]⟩, ⟨2, 6, [1, 0, 5, 4, 3, 7]⟩, ⟨2, 4, [1, 0, 5, 6, 7, 3]⟩, ⟨2, 0, [3, 1]⟩, ⟨2, 0, [3, 4, 5, 6, 7, 1]⟩, ⟨2, 0, [3, 4, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 0, [3, 1]⟩, ⟨4, 7, [3, 1, 0, 5, 6]⟩, ⟨4, 0, [3, 2, 1, 7, 6, 5]⟩, ⟨4, 0, [3, 2, 1]⟩, ⟨4, 6, [3, 2, 1, 0, 5]⟩, ⟨4, 7, [3, 2, 1, 0, 5, 6]⟩, ⟨4, 0, [3, 7, 6, 5]⟩, ⟨4, 2, [3, 7, 6, 5, 0, 1]⟩, ⟨4, 6, [5, 0, 1, 2, 3, 7]⟩, ⟨0, 6, [1, 2, 3, 4, 5]⟩, ⟨0, 7, [1, 2, 3, 4, 5, 6]⟩, ⟨0, 5, [1, 2, 3, 7, 6]⟩, ⟨0, 4, [1, 2, 3, 7, 6, 5]⟩, ⟨0, 7, [1, 3, 4, 5, 6]⟩, ⟨0, 4, [1, 3, 7, 6, 5]⟩, ⟨0, 3, [1, 7, 6, 5, 4]⟩, ⟨0, 2, [1, 7, 6, 5, 4, 3]⟩, ⟨0, 6, [5, 4, 3, 2, 1, 7]⟩, ⟨0, 2, [5, 4, 3, 7, 1]⟩, ⟨0, 1, [5, 6, 7, 3, 2]⟩], ⟨none, {(2, 2), (4, 2), (0, 2)}⟩⟩

private def k7t3p7_step_2 : ClosureStep 7 := .fresh k7t3p7_step_2_data

private def k7t3p7_step_3_data : EdgeAttachmentData 7 := ⟨4, 1, [⟨0, 1, [2, 6, 5, 4]⟩, ⟨1, 0, [4, 3, 2, 6]⟩, ⟨1, 2, [4, 5, 6, 0]⟩, ⟨3, 6, [2, 0, 1, 4, 5]⟩, ⟨3, 5, [2, 6, 0, 1, 4]⟩], ⟨none, {(1, 3), (3, 2), (0, 3)}⟩⟩

private def k7t3p7_step_3 : ClosureStep 7 := .edge k7t3p7_step_3_data

private def k7t3p7_step_4_data : EdgeAttachmentData 7 := ⟨4, 2, [⟨0, 1, [6, 5, 4, 2]⟩, ⟨1, 2, [0, 6, 5, 4]⟩, ⟨1, 0, [2, 4, 5, 6]⟩, ⟨3, 5, [4, 2, 1, 0, 6]⟩], ⟨none, {(1, 3), (0, 3), (3, 2)}⟩⟩

private def k7t3p7_step_4 : ClosureStep 7 := .edge k7t3p7_step_4_data

private def k7t3p7_step_5_data : FreshAttachmentData 7 := ⟨4, 2, [⟨2, 0, [1, 7, 6, 5, 4, 3]⟩, ⟨2, 4, [1, 7, 6, 5, 0, 3]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 0, [3, 2, 1, 7, 6, 5]⟩, ⟨4, 2, [3, 0, 5, 6, 7, 1]⟩, ⟨4, 6, [5, 0, 3, 1, 7]⟩, ⟨4, 7, [5, 0, 3, 2, 1]⟩, ⟨4, 6, [5, 0, 3, 2, 1, 7]⟩, ⟨6, 0, [7, 1, 2, 3, 4, 5]⟩, ⟨6, 0, [7, 1, 2, 3]⟩, ⟨6, 4, [7, 1, 2, 3, 0, 5]⟩, ⟨6, 0, [7, 1, 3, 4, 5]⟩, ⟨6, 4, [7, 1, 3, 0, 5]⟩], ⟨none, {(4, 2), (6, 3), (2, 1), (5, 0)}⟩⟩

private def k7t3p7_step_5 : ClosureStep 7 := .fresh k7t3p7_step_5_data

private def k7t3p7_step_6_data : EdgeAttachmentData 7 := ⟨5, 1, [⟨0, 4, [1, 5, 6, 2, 3]⟩, ⟨0, 6, [2, 1, 5]⟩, ⟨0, 1, [2, 3, 4, 5]⟩, ⟨3, 6, [4, 5, 1, 0, 2]⟩, ⟨6, 3, [0, 1, 5, 4]⟩, ⟨6, 2, [0, 1, 5, 4, 3]⟩, ⟨6, 3, [0, 2, 1, 5, 4]⟩, ⟨6, 4, [5, 1, 0, 2, 3]⟩], ⟨none, {(0, 3), (1, 2), (6, 2), (3, 2)}⟩⟩

private def k7t3p7_step_6 : ClosureStep 7 := .edge k7t3p7_step_6_data

private def k7t3p7_step_7_data : EdgeAttachmentData 7 := ⟨5, 3, [⟨0, 4, [1, 2, 6, 5, 3]⟩, ⟨0, 6, [2, 3, 5]⟩, ⟨0, 1, [6, 5, 3, 2]⟩, ⟨1, 2, [0, 6, 5, 3]⟩, ⟨1, 0, [2, 3, 5, 6]⟩, ⟨6, 4, [0, 1, 2, 3, 5]⟩], ⟨none, {(1, 3), (0, 3), (6, 2)}⟩⟩

private def k7t3p7_step_7 : ClosureStep 7 := .edge k7t3p7_step_7_data

private def k7t3p7_step_8_data : EdgeAttachmentData 7 := ⟨6, 4, [⟨0, 1, [6, 4, 3, 2]⟩, ⟨1, 2, [0, 6, 4, 3]⟩, ⟨1, 0, [2, 3, 4, 6]⟩, ⟨3, 5, [2, 1, 0, 6, 4]⟩], ⟨none, {(1, 3), (0, 3), (3, 2)}⟩⟩

private def k7t3p7_step_8 : ClosureStep 7 := .edge k7t3p7_step_8_data

private def k7t3p7_step_9_data : FreshAttachmentData 7 := ⟨6, 4, [⟨2, 0, [1, 3, 4, 5, 6, 7]⟩, ⟨2, 6, [1, 3, 4, 5, 0, 7]⟩, ⟨2, 0, [1, 3, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 6, [3, 1, 7, 0, 5]⟩, ⟨4, 0, [3, 2, 1, 7, 6, 5]⟩, ⟨4, 0, [3, 2, 1, 7]⟩, ⟨4, 6, [3, 2, 1, 7, 0, 5]⟩, ⟨6, 0, [5, 4, 3, 1, 7]⟩, ⟨6, 0, [5, 4, 3, 2, 1, 7]⟩, ⟨6, 3, [5, 0, 7, 1, 2]⟩, ⟨6, 4, [5, 0, 7, 1, 2, 3]⟩, ⟨6, 4, [5, 0, 7, 1, 3]⟩, ⟨6, 2, [7, 0, 5, 4, 3, 1]⟩, ⟨6, 1, [7, 0, 5, 4, 3, 2]⟩], ⟨none, {(4, 3), (6, 2), (2, 2)}⟩⟩

private def k7t3p7_step_9 : ClosureStep 7 := .fresh k7t3p7_step_9_data

def k7t3p7 : LayoutCertificate 7 where
  chains := [[0, 1, 2, 3, 4, 5, 6]]
  clique := {0, 2, 6}
  templates := [⟨0, 1, [], [], [2], 3, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩,
    ⟨0, 2, [], [], [3, 4, 5, 6], 2, 2⟩,
    ⟨0, 3, [], [], [2], 3, 5⟩,
    ⟨0, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨0, 4, [], [], [3, 2], 2, 4⟩,
    ⟨0, 5, [], [], [4, 3, 2], 1, 3⟩,
    ⟨0, 6, [], [], [], 4, 6⟩,
    ⟨0, 6, [], [], [5, 4, 3, 2], 2, 2⟩,
    ⟨1, 2, [], [0], [], 3, 5⟩,
    ⟨1, 2, [], [0], [3, 4, 5, 6], 1, 1⟩,
    ⟨1, 3, [], [0], [2], 2, 4⟩,
    ⟨1, 3, [], [0], [4, 5, 6], 1, 2⟩,
    ⟨1, 4, [], [0], [3, 2], 1, 3⟩,
    ⟨1, 5, [], [0], [4, 3, 2], 1, 2⟩,
    ⟨1, 5, [], [0], [6], 2, 4⟩,
    ⟨1, 6, [], [0], [], 3, 5⟩,
    ⟨1, 6, [], [0], [5, 4, 3, 2], 1, 1⟩,
    ⟨2, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨2, 4, [], [], [5, 6], 2, 4⟩,
    ⟨3, 4, [], [2], [5, 6], 1, 3⟩,
    ⟨3, 5, [], [2], [6], 2, 4⟩,
    ⟨3, 6, [], [2], [], 3, 5⟩,
    ⟨4, 5, [], [2, 3], [6], 1, 3⟩,
    ⟨5, 6, [], [2, 3, 4], [], 1, 3⟩]
  required := [⟨0, 1, []⟩,
    ⟨0, 6, [1, 2, 3, 4, 5]⟩,
    ⟨1, 2, []⟩,
    ⟨1, 3, [2]⟩,
    ⟨1, 4, [2, 3]⟩,
    ⟨1, 6, [2, 3, 4, 5]⟩,
    ⟨2, 3, []⟩,
    ⟨3, 5, [4]⟩]
  closure := [k7t3p7_step_0, k7t3p7_step_1, k7t3p7_step_2, k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9]
  bad := ⟨none, {(4, 2), (1, 2), (3, 1)}⟩


private def k7t3p7_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[{2, 3, 4}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_initial_eq_row_0 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 0 j = k7t3p7_state_0 0 j := by decide

private theorem k7t3p7_initial_eq_row_1 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 1 j = k7t3p7_state_0 1 j := by decide

private theorem k7t3p7_initial_eq_row_2 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 2 j = k7t3p7_state_0 2 j := by decide

private theorem k7t3p7_initial_eq_row_3 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 3 j = k7t3p7_state_0 3 j := by decide

private theorem k7t3p7_initial_eq_row_4 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 4 j = k7t3p7_state_0 4 j := by decide

private theorem k7t3p7_initial_eq_row_5 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 5 j = k7t3p7_state_0 5 j := by decide

private theorem k7t3p7_initial_eq_row_6 : ∀ j : Fin 7, (k7t3p7.initialMatrix 7) 6 j = k7t3p7_state_0 6 j := by decide

private theorem k7t3p7_initial_eq : (k7t3p7.initialMatrix 7) = k7t3p7_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p7_initial_eq_row_0 j

  · exact k7t3p7_initial_eq_row_1 j

  · exact k7t3p7_initial_eq_row_2 j

  · exact k7t3p7_initial_eq_row_3 j

  · exact k7t3p7_initial_eq_row_4 j

  · exact k7t3p7_initial_eq_row_5 j

  · exact k7t3p7_initial_eq_row_6 j

private def k7t3p7_state_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[{2, 3, 4}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {1, 2}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 2}, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 4, {1, 2}, {1, 2}],
    #[Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[{2, 3, 4}, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, {1, 2}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, {1, 2}, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_0_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 0 j = k7t3p7_local_0 0 j := by decide

private theorem k7t3p7_local_0_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 1 j = k7t3p7_local_0 1 j := by decide

private theorem k7t3p7_local_0_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 2 j = k7t3p7_local_0 2 j := by decide

private theorem k7t3p7_local_0_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 3 j = k7t3p7_local_0 3 j := by decide

private theorem k7t3p7_local_0_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 4 j = k7t3p7_local_0 4 j := by decide

private theorem k7t3p7_local_0_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 5 j = k7t3p7_local_0 5 j := by decide

private theorem k7t3p7_local_0_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) 6 j = k7t3p7_local_0 6 j := by decide

private theorem k7t3p7_local_0_eq : (fun a b => k7t3p7_state_0 a b ∪ requiredMatrix 7 k7t3p7_step_0_data.required a b) = k7t3p7_local_0 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_0_eq_row_0 j

  · exact k7t3p7_local_0_eq_row_1 j

  · exact k7t3p7_local_0_eq_row_2 j

  · exact k7t3p7_local_0_eq_row_3 j

  · exact k7t3p7_local_0_eq_row_4 j

  · exact k7t3p7_local_0_eq_row_5 j

  · exact k7t3p7_local_0_eq_row_6 j

private theorem k7t3p7_local_0_paths : ∀ p ∈ k7t3p7_step_0_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_0_data.i k7t3p7_step_0_data.j) 7 := by decide

private theorem k7t3p7_local_0_bad : k7t3p7_step_0_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_0_data.i k7t3p7_step_0_data.j) k7t3p7_local_0 7 3 := by decide

private theorem k7t3p7_step_0_check : k7t3p7_step_0.Check k7t3p7.graph k7t3p7_state_0 7 3 := by
  change k7t3p7_step_0_data.Check k7t3p7.graph k7t3p7_state_0 7 3
  refine ⟨k7t3p7_local_0_paths, ?_⟩
  rw [k7t3p7_local_0_eq]
  exact k7t3p7_local_0_bad

private theorem k7t3p7_update_0 : k7t3p7_step_0.apply k7t3p7_state_0 = k7t3p7_state_1 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_0.apply k7t3p7_state_0 i j = k7t3p7_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, {0, 2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[{0, 2, 3, 4}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, Finset.Icc 1 6, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}],
    #[{2, 3, 4}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {1, 3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_1_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 0 j = k7t3p7_local_1 0 j := by decide

private theorem k7t3p7_local_1_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 1 j = k7t3p7_local_1 1 j := by decide

private theorem k7t3p7_local_1_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 2 j = k7t3p7_local_1 2 j := by decide

private theorem k7t3p7_local_1_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 3 j = k7t3p7_local_1 3 j := by decide

private theorem k7t3p7_local_1_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 4 j = k7t3p7_local_1 4 j := by decide

private theorem k7t3p7_local_1_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 5 j = k7t3p7_local_1 5 j := by decide

private theorem k7t3p7_local_1_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) 6 j = k7t3p7_local_1 6 j := by decide

private theorem k7t3p7_local_1_eq : (fun a b => k7t3p7_state_1 a b ∪ requiredMatrix 7 k7t3p7_step_1_data.required a b) = k7t3p7_local_1 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_1_eq_row_0 j

  · exact k7t3p7_local_1_eq_row_1 j

  · exact k7t3p7_local_1_eq_row_2 j

  · exact k7t3p7_local_1_eq_row_3 j

  · exact k7t3p7_local_1_eq_row_4 j

  · exact k7t3p7_local_1_eq_row_5 j

  · exact k7t3p7_local_1_eq_row_6 j

private theorem k7t3p7_local_1_paths : ∀ p ∈ k7t3p7_step_1_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_1_data.i k7t3p7_step_1_data.j) 7 := by decide

private theorem k7t3p7_local_1_bad : k7t3p7_step_1_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_1_data.i k7t3p7_step_1_data.j) k7t3p7_local_1 7 3 := by decide

private theorem k7t3p7_step_1_check : k7t3p7_step_1.Check k7t3p7.graph k7t3p7_state_1 7 3 := by
  change k7t3p7_step_1_data.Check k7t3p7.graph k7t3p7_state_1 7 3
  refine ⟨k7t3p7_local_1_paths, ?_⟩
  rw [k7t3p7_local_1_eq]
  exact k7t3p7_local_1_bad

private theorem k7t3p7_update_1 : k7t3p7_step_1.apply k7t3p7_state_1 = k7t3p7_state_2 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_1.apply k7t3p7_state_1 i j = k7t3p7_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_2 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {1}, Finset.Icc 0 4, {1}, Finset.Icc 0 4, {1}, {0, 1}, {0, 1}],
    #[{1}, ∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, {0, 2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 0 4, {1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{1}, {2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 0 4, Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {0, 1, 3, 4, 5}],
    #[{1}, {0, 2, 3, 4}, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{0, 1}, {1, 2, 3}, Finset.Icc 0 4, ∅, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{0, 1}, {1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {0, 1, 3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_2_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 0 j = k7t3p7_local_2 0 j := by decide

private theorem k7t3p7_local_2_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 1 j = k7t3p7_local_2 1 j := by decide

private theorem k7t3p7_local_2_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 2 j = k7t3p7_local_2 2 j := by decide

private theorem k7t3p7_local_2_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 3 j = k7t3p7_local_2 3 j := by decide

private theorem k7t3p7_local_2_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 4 j = k7t3p7_local_2 4 j := by decide

private theorem k7t3p7_local_2_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 5 j = k7t3p7_local_2 5 j := by decide

private theorem k7t3p7_local_2_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 6 j = k7t3p7_local_2 6 j := by decide

private theorem k7t3p7_local_2_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) 7 j = k7t3p7_local_2 7 j := by decide

private theorem k7t3p7_local_2_eq : (fun a b => freshMatrix k7t3p7_state_2 a b ∪ requiredMatrix 7 k7t3p7_step_2_data.required a b) = k7t3p7_local_2 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_2_eq_row_0 j

  · exact k7t3p7_local_2_eq_row_1 j

  · exact k7t3p7_local_2_eq_row_2 j

  · exact k7t3p7_local_2_eq_row_3 j

  · exact k7t3p7_local_2_eq_row_4 j

  · exact k7t3p7_local_2_eq_row_5 j

  · exact k7t3p7_local_2_eq_row_6 j

  · exact k7t3p7_local_2_eq_row_7 j

private theorem k7t3p7_local_2_paths : ∀ p ∈ k7t3p7_step_2_data.required, p.Check (freshGraph k7t3p7.graph k7t3p7_step_2_data.i k7t3p7_step_2_data.j) 7 := by decide

private theorem k7t3p7_local_2_bad : k7t3p7_step_2_data.bad.Check (freshGraph k7t3p7.graph k7t3p7_step_2_data.i k7t3p7_step_2_data.j) k7t3p7_local_2 7 3 := by decide

private theorem k7t3p7_step_2_check : k7t3p7_step_2.Check k7t3p7.graph k7t3p7_state_2 7 3 := by
  change k7t3p7_step_2_data.Check k7t3p7.graph k7t3p7_state_2 7 3
  refine ⟨by decide, k7t3p7_local_2_paths, ?_⟩
  rw [k7t3p7_local_2_eq]
  exact k7t3p7_local_2_bad

private theorem k7t3p7_update_2 : k7t3p7_step_2.apply k7t3p7_state_2 = k7t3p7_state_3 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_2.apply k7t3p7_state_2 i j = k7t3p7_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, Finset.Icc 1 6, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1, 3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {1, 3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_3_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 0 j = k7t3p7_local_3 0 j := by decide

private theorem k7t3p7_local_3_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 1 j = k7t3p7_local_3 1 j := by decide

private theorem k7t3p7_local_3_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 2 j = k7t3p7_local_3 2 j := by decide

private theorem k7t3p7_local_3_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 3 j = k7t3p7_local_3 3 j := by decide

private theorem k7t3p7_local_3_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 4 j = k7t3p7_local_3 4 j := by decide

private theorem k7t3p7_local_3_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 5 j = k7t3p7_local_3 5 j := by decide

private theorem k7t3p7_local_3_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) 6 j = k7t3p7_local_3 6 j := by decide

private theorem k7t3p7_local_3_eq : (fun a b => k7t3p7_state_3 a b ∪ requiredMatrix 7 k7t3p7_step_3_data.required a b) = k7t3p7_local_3 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_3_eq_row_0 j

  · exact k7t3p7_local_3_eq_row_1 j

  · exact k7t3p7_local_3_eq_row_2 j

  · exact k7t3p7_local_3_eq_row_3 j

  · exact k7t3p7_local_3_eq_row_4 j

  · exact k7t3p7_local_3_eq_row_5 j

  · exact k7t3p7_local_3_eq_row_6 j

private theorem k7t3p7_local_3_paths : ∀ p ∈ k7t3p7_step_3_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_3_data.i k7t3p7_step_3_data.j) 7 := by decide

private theorem k7t3p7_local_3_bad : k7t3p7_step_3_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_3_data.i k7t3p7_step_3_data.j) k7t3p7_local_3 7 3 := by decide

private theorem k7t3p7_step_3_check : k7t3p7_step_3.Check k7t3p7.graph k7t3p7_state_3 7 3 := by
  change k7t3p7_step_3_data.Check k7t3p7.graph k7t3p7_state_3 7 3
  refine ⟨k7t3p7_local_3_paths, ?_⟩
  rw [k7t3p7_local_3_eq]
  exact k7t3p7_local_3_bad

private theorem k7t3p7_update_3 : k7t3p7_step_3.apply k7t3p7_state_3 = k7t3p7_state_4 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_3.apply k7t3p7_state_3 i j = k7t3p7_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {0, 2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, Finset.Icc 1 6, ∅, {1, 2, 3, 6}, {2, 3, 4}, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 1 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_4_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 0 j = k7t3p7_local_4 0 j := by decide

private theorem k7t3p7_local_4_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 1 j = k7t3p7_local_4 1 j := by decide

private theorem k7t3p7_local_4_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 2 j = k7t3p7_local_4 2 j := by decide

private theorem k7t3p7_local_4_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 3 j = k7t3p7_local_4 3 j := by decide

private theorem k7t3p7_local_4_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 4 j = k7t3p7_local_4 4 j := by decide

private theorem k7t3p7_local_4_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 5 j = k7t3p7_local_4 5 j := by decide

private theorem k7t3p7_local_4_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) 6 j = k7t3p7_local_4 6 j := by decide

private theorem k7t3p7_local_4_eq : (fun a b => k7t3p7_state_4 a b ∪ requiredMatrix 7 k7t3p7_step_4_data.required a b) = k7t3p7_local_4 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_4_eq_row_0 j

  · exact k7t3p7_local_4_eq_row_1 j

  · exact k7t3p7_local_4_eq_row_2 j

  · exact k7t3p7_local_4_eq_row_3 j

  · exact k7t3p7_local_4_eq_row_4 j

  · exact k7t3p7_local_4_eq_row_5 j

  · exact k7t3p7_local_4_eq_row_6 j

private theorem k7t3p7_local_4_paths : ∀ p ∈ k7t3p7_step_4_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_4_data.i k7t3p7_step_4_data.j) 7 := by decide

private theorem k7t3p7_local_4_bad : k7t3p7_step_4_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_4_data.i k7t3p7_step_4_data.j) k7t3p7_local_4 7 3 := by decide

private theorem k7t3p7_step_4_check : k7t3p7_step_4.Check k7t3p7.graph k7t3p7_state_4 7 3 := by
  change k7t3p7_step_4_data.Check k7t3p7.graph k7t3p7_state_4 7 3
  refine ⟨k7t3p7_local_4_paths, ?_⟩
  rw [k7t3p7_local_4_eq]
  exact k7t3p7_local_4_bad

private theorem k7t3p7_update_4 : k7t3p7_step_4.apply k7t3p7_state_4 = k7t3p7_state_5 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_4.apply k7t3p7_state_4 i j = k7t3p7_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_5 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, {0}, ∅, {0, 1}, ∅, {0, 1, 2}, ∅],
    #[∅, ∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{0}, {1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, {2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, {0, 2, 3, 4}, ∅, ∅],
    #[{0, 1}, Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1, 3, 4, 5}],
    #[∅, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{0, 1, 2}, {1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {1, 3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_5_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 0 j = k7t3p7_local_5 0 j := by decide

private theorem k7t3p7_local_5_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 1 j = k7t3p7_local_5 1 j := by decide

private theorem k7t3p7_local_5_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 2 j = k7t3p7_local_5 2 j := by decide

private theorem k7t3p7_local_5_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 3 j = k7t3p7_local_5 3 j := by decide

private theorem k7t3p7_local_5_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 4 j = k7t3p7_local_5 4 j := by decide

private theorem k7t3p7_local_5_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 5 j = k7t3p7_local_5 5 j := by decide

private theorem k7t3p7_local_5_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 6 j = k7t3p7_local_5 6 j := by decide

private theorem k7t3p7_local_5_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) 7 j = k7t3p7_local_5 7 j := by decide

private theorem k7t3p7_local_5_eq : (fun a b => freshMatrix k7t3p7_state_5 a b ∪ requiredMatrix 7 k7t3p7_step_5_data.required a b) = k7t3p7_local_5 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_5_eq_row_0 j

  · exact k7t3p7_local_5_eq_row_1 j

  · exact k7t3p7_local_5_eq_row_2 j

  · exact k7t3p7_local_5_eq_row_3 j

  · exact k7t3p7_local_5_eq_row_4 j

  · exact k7t3p7_local_5_eq_row_5 j

  · exact k7t3p7_local_5_eq_row_6 j

  · exact k7t3p7_local_5_eq_row_7 j

private theorem k7t3p7_local_5_paths : ∀ p ∈ k7t3p7_step_5_data.required, p.Check (freshGraph k7t3p7.graph k7t3p7_step_5_data.i k7t3p7_step_5_data.j) 7 := by decide

private theorem k7t3p7_local_5_bad : k7t3p7_step_5_data.bad.Check (freshGraph k7t3p7.graph k7t3p7_step_5_data.i k7t3p7_step_5_data.j) k7t3p7_local_5 7 3 := by decide

private theorem k7t3p7_step_5_check : k7t3p7_step_5.Check k7t3p7.graph k7t3p7_state_5 7 3 := by
  change k7t3p7_step_5_data.Check k7t3p7.graph k7t3p7_state_5 7 3
  refine ⟨by decide, k7t3p7_local_5_paths, ?_⟩
  rw [k7t3p7_local_5_eq]
  exact k7t3p7_local_5_bad

private theorem k7t3p7_update_5 : k7t3p7_step_5.apply k7t3p7_state_5 = k7t3p7_state_6 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_5.apply k7t3p7_state_5 i j = k7t3p7_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, {1}],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, Finset.Icc 1 5],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {1}],
    #[{1, 2, 3}, Finset.Icc 1 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 5, {1}, Finset.Icc 1 5, {1}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_6_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 0 j = k7t3p7_local_6 0 j := by decide

private theorem k7t3p7_local_6_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 1 j = k7t3p7_local_6 1 j := by decide

private theorem k7t3p7_local_6_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 2 j = k7t3p7_local_6 2 j := by decide

private theorem k7t3p7_local_6_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 3 j = k7t3p7_local_6 3 j := by decide

private theorem k7t3p7_local_6_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 4 j = k7t3p7_local_6 4 j := by decide

private theorem k7t3p7_local_6_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 5 j = k7t3p7_local_6 5 j := by decide

private theorem k7t3p7_local_6_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) 6 j = k7t3p7_local_6 6 j := by decide

private theorem k7t3p7_local_6_eq : (fun a b => k7t3p7_state_6 a b ∪ requiredMatrix 7 k7t3p7_step_6_data.required a b) = k7t3p7_local_6 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_6_eq_row_0 j

  · exact k7t3p7_local_6_eq_row_1 j

  · exact k7t3p7_local_6_eq_row_2 j

  · exact k7t3p7_local_6_eq_row_3 j

  · exact k7t3p7_local_6_eq_row_4 j

  · exact k7t3p7_local_6_eq_row_5 j

  · exact k7t3p7_local_6_eq_row_6 j

private theorem k7t3p7_local_6_paths : ∀ p ∈ k7t3p7_step_6_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_6_data.i k7t3p7_step_6_data.j) 7 := by decide

private theorem k7t3p7_local_6_bad : k7t3p7_step_6_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_6_data.i k7t3p7_step_6_data.j) k7t3p7_local_6 7 3 := by decide

private theorem k7t3p7_step_6_check : k7t3p7_step_6.Check k7t3p7.graph k7t3p7_state_6 7 3 := by
  change k7t3p7_step_6_data.Check k7t3p7.graph k7t3p7_state_6 7 3
  refine ⟨k7t3p7_local_6_paths, ?_⟩
  rw [k7t3p7_local_6_eq]
  exact k7t3p7_local_6_bad

private theorem k7t3p7_update_6 : k7t3p7_step_6.apply k7t3p7_state_6 = k7t3p7_state_7 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_6.apply k7t3p7_state_6 i j = k7t3p7_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, Finset.Icc 1 6, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 2 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {1}],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 5, ∅, {3, 4, 5}, {1}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_7_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 0 j = k7t3p7_local_7 0 j := by decide

private theorem k7t3p7_local_7_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 1 j = k7t3p7_local_7 1 j := by decide

private theorem k7t3p7_local_7_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 2 j = k7t3p7_local_7 2 j := by decide

private theorem k7t3p7_local_7_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 3 j = k7t3p7_local_7 3 j := by decide

private theorem k7t3p7_local_7_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 4 j = k7t3p7_local_7 4 j := by decide

private theorem k7t3p7_local_7_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 5 j = k7t3p7_local_7 5 j := by decide

private theorem k7t3p7_local_7_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) 6 j = k7t3p7_local_7 6 j := by decide

private theorem k7t3p7_local_7_eq : (fun a b => k7t3p7_state_7 a b ∪ requiredMatrix 7 k7t3p7_step_7_data.required a b) = k7t3p7_local_7 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_7_eq_row_0 j

  · exact k7t3p7_local_7_eq_row_1 j

  · exact k7t3p7_local_7_eq_row_2 j

  · exact k7t3p7_local_7_eq_row_3 j

  · exact k7t3p7_local_7_eq_row_4 j

  · exact k7t3p7_local_7_eq_row_5 j

  · exact k7t3p7_local_7_eq_row_6 j

private theorem k7t3p7_local_7_paths : ∀ p ∈ k7t3p7_step_7_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_7_data.i k7t3p7_step_7_data.j) 7 := by decide

private theorem k7t3p7_local_7_bad : k7t3p7_step_7_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_7_data.i k7t3p7_step_7_data.j) k7t3p7_local_7 7 3 := by decide

private theorem k7t3p7_step_7_check : k7t3p7_step_7.Check k7t3p7.graph k7t3p7_state_7 7 3 := by
  change k7t3p7_step_7_data.Check k7t3p7.graph k7t3p7_state_7 7 3
  refine ⟨k7t3p7_local_7_paths, ?_⟩
  rw [k7t3p7_local_7_eq]
  exact k7t3p7_local_7_bad

private theorem k7t3p7_update_7 : k7t3p7_step_7.apply k7t3p7_state_7 = k7t3p7_state_8 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_7.apply k7t3p7_state_7 i j = k7t3p7_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0}],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, {0}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, Finset.Icc 1 6, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_8_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 0 j = k7t3p7_local_8 0 j := by decide

private theorem k7t3p7_local_8_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 1 j = k7t3p7_local_8 1 j := by decide

private theorem k7t3p7_local_8_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 2 j = k7t3p7_local_8 2 j := by decide

private theorem k7t3p7_local_8_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 3 j = k7t3p7_local_8 3 j := by decide

private theorem k7t3p7_local_8_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 4 j = k7t3p7_local_8 4 j := by decide

private theorem k7t3p7_local_8_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 5 j = k7t3p7_local_8 5 j := by decide

private theorem k7t3p7_local_8_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) 6 j = k7t3p7_local_8 6 j := by decide

private theorem k7t3p7_local_8_eq : (fun a b => k7t3p7_state_8 a b ∪ requiredMatrix 7 k7t3p7_step_8_data.required a b) = k7t3p7_local_8 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_8_eq_row_0 j

  · exact k7t3p7_local_8_eq_row_1 j

  · exact k7t3p7_local_8_eq_row_2 j

  · exact k7t3p7_local_8_eq_row_3 j

  · exact k7t3p7_local_8_eq_row_4 j

  · exact k7t3p7_local_8_eq_row_5 j

  · exact k7t3p7_local_8_eq_row_6 j

private theorem k7t3p7_local_8_paths : ∀ p ∈ k7t3p7_step_8_data.required, p.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_8_data.i k7t3p7_step_8_data.j) 7 := by decide

private theorem k7t3p7_local_8_bad : k7t3p7_step_8_data.bad.Check (addedEdgeGraph k7t3p7.graph k7t3p7_step_8_data.i k7t3p7_step_8_data.j) k7t3p7_local_8 7 3 := by decide

private theorem k7t3p7_step_8_check : k7t3p7_step_8.Check k7t3p7.graph k7t3p7_state_8 7 3 := by
  change k7t3p7_step_8_data.Check k7t3p7.graph k7t3p7_state_8 7 3
  refine ⟨k7t3p7_local_8_paths, ?_⟩
  rw [k7t3p7_local_8_eq]
  exact k7t3p7_local_8_bad

private theorem k7t3p7_update_8 : k7t3p7_step_8.apply k7t3p7_state_8 = k7t3p7_state_9 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_8.apply k7t3p7_state_8 i j = k7t3p7_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p7_state_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[{2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {3, 4, 5}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0, 1}],
    #[{1, 2, 3}, Finset.Icc 0 4, ∅, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, {0, 1}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p7_local_9 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, {0, 1}, ∅, {0, 1, 2}, ∅, {0, 1}, ∅],
    #[∅, ∅, {1, 3, 4, 5, 6}, {2}, Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 3, {1, 2, 4, 5, 6}],
    #[{0, 1}, {1, 3, 4, 5, 6}, ∅, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[∅, {2}, {1, 3, 4, 5, 6}, ∅, {1, 2, 3, 6}, Finset.Icc 0 4, {1}, ∅],
    #[{0, 1, 2}, Finset.Icc 1 5, Finset.Icc 0 5, {1, 2, 3, 6}, ∅, {1, 2, 3}, Finset.Icc 0 5, {3, 4, 5}],
    #[∅, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0}],
    #[{0, 1}, Finset.Icc 0 3, Finset.Icc 0 4, {1}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, ∅, {3, 4, 5}, {0}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p7_local_9_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 0 j = k7t3p7_local_9 0 j := by decide

private theorem k7t3p7_local_9_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 1 j = k7t3p7_local_9 1 j := by decide

private theorem k7t3p7_local_9_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 2 j = k7t3p7_local_9 2 j := by decide

private theorem k7t3p7_local_9_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 3 j = k7t3p7_local_9 3 j := by decide

private theorem k7t3p7_local_9_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 4 j = k7t3p7_local_9 4 j := by decide

private theorem k7t3p7_local_9_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 5 j = k7t3p7_local_9 5 j := by decide

private theorem k7t3p7_local_9_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 6 j = k7t3p7_local_9 6 j := by decide

private theorem k7t3p7_local_9_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) 7 j = k7t3p7_local_9 7 j := by decide

private theorem k7t3p7_local_9_eq : (fun a b => freshMatrix k7t3p7_state_9 a b ∪ requiredMatrix 7 k7t3p7_step_9_data.required a b) = k7t3p7_local_9 := by
  funext i j
  fin_cases i

  · exact k7t3p7_local_9_eq_row_0 j

  · exact k7t3p7_local_9_eq_row_1 j

  · exact k7t3p7_local_9_eq_row_2 j

  · exact k7t3p7_local_9_eq_row_3 j

  · exact k7t3p7_local_9_eq_row_4 j

  · exact k7t3p7_local_9_eq_row_5 j

  · exact k7t3p7_local_9_eq_row_6 j

  · exact k7t3p7_local_9_eq_row_7 j

private theorem k7t3p7_local_9_paths : ∀ p ∈ k7t3p7_step_9_data.required, p.Check (freshGraph k7t3p7.graph k7t3p7_step_9_data.i k7t3p7_step_9_data.j) 7 := by decide

private theorem k7t3p7_local_9_bad : k7t3p7_step_9_data.bad.Check (freshGraph k7t3p7.graph k7t3p7_step_9_data.i k7t3p7_step_9_data.j) k7t3p7_local_9 7 3 := by decide

private theorem k7t3p7_step_9_check : k7t3p7_step_9.Check k7t3p7.graph k7t3p7_state_9 7 3 := by
  change k7t3p7_step_9_data.Check k7t3p7.graph k7t3p7_state_9 7 3
  refine ⟨by decide, k7t3p7_local_9_paths, ?_⟩
  rw [k7t3p7_local_9_eq]
  exact k7t3p7_local_9_bad

private theorem k7t3p7_update_9 : k7t3p7_step_9.apply k7t3p7_state_9 = k7t3p7_state_10 := by
  have h : ∀ i j : Fin 7, k7t3p7_step_9.apply k7t3p7_state_9 i j = k7t3p7_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k7t3p7_closure_10 : ClosureCheck k7t3p7.graph k7t3p7_state_10 7 3 [] := by trivial

private theorem k7t3p7_closure_9 : ClosureCheck k7t3p7.graph k7t3p7_state_9 7 3 [k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_9_check
  · rw [k7t3p7_update_9]
    exact k7t3p7_closure_10

private theorem k7t3p7_closure_8 : ClosureCheck k7t3p7.graph k7t3p7_state_8 7 3 [k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_8_check
  · rw [k7t3p7_update_8]
    exact k7t3p7_closure_9

private theorem k7t3p7_closure_7 : ClosureCheck k7t3p7.graph k7t3p7_state_7 7 3 [k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_7_check
  · rw [k7t3p7_update_7]
    exact k7t3p7_closure_8

private theorem k7t3p7_closure_6 : ClosureCheck k7t3p7.graph k7t3p7_state_6 7 3 [k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_6_check
  · rw [k7t3p7_update_6]
    exact k7t3p7_closure_7

private theorem k7t3p7_closure_5 : ClosureCheck k7t3p7.graph k7t3p7_state_5 7 3 [k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_5_check
  · rw [k7t3p7_update_5]
    exact k7t3p7_closure_6

private theorem k7t3p7_closure_4 : ClosureCheck k7t3p7.graph k7t3p7_state_4 7 3 [k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_4_check
  · rw [k7t3p7_update_4]
    exact k7t3p7_closure_5

private theorem k7t3p7_closure_3 : ClosureCheck k7t3p7.graph k7t3p7_state_3 7 3 [k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_3_check
  · rw [k7t3p7_update_3]
    exact k7t3p7_closure_4

private theorem k7t3p7_closure_2 : ClosureCheck k7t3p7.graph k7t3p7_state_2 7 3 [k7t3p7_step_2, k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_2_check
  · rw [k7t3p7_update_2]
    exact k7t3p7_closure_3

private theorem k7t3p7_closure_1 : ClosureCheck k7t3p7.graph k7t3p7_state_1 7 3 [k7t3p7_step_1, k7t3p7_step_2, k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_1_check
  · rw [k7t3p7_update_1]
    exact k7t3p7_closure_2

private theorem k7t3p7_closure_0 : ClosureCheck k7t3p7.graph k7t3p7_state_0 7 3 [k7t3p7_step_0, k7t3p7_step_1, k7t3p7_step_2, k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] := by
  constructor
  · exact k7t3p7_step_0_check
  · rw [k7t3p7_update_0]
    exact k7t3p7_closure_1

private theorem k7t3p7_matrix_eq : k7t3p7.matrix 7 = k7t3p7_state_10 := by
  change closureMatrix (k7t3p7.initialMatrix 7) _ = _
  rw [k7t3p7_initial_eq]
  change closureMatrix k7t3p7_state_0 [k7t3p7_step_0, k7t3p7_step_1, k7t3p7_step_2, k7t3p7_step_3, k7t3p7_step_4, k7t3p7_step_5, k7t3p7_step_6, k7t3p7_step_7, k7t3p7_step_8, k7t3p7_step_9] = _
  simp only [closureMatrix]
  rw [k7t3p7_update_0, k7t3p7_update_1, k7t3p7_update_2, k7t3p7_update_3, k7t3p7_update_4, k7t3p7_update_5, k7t3p7_update_6, k7t3p7_update_7, k7t3p7_update_8, k7t3p7_update_9]

private theorem k7t3p7_part_0 : k7t3p7.chains.flatten = List.finRange _ := by decide

private theorem k7t3p7_part_1 : k7t3p7.chains.map List.length = ([[1, 3]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p7_part_2 : k7t3p7.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p7.clique))) = ([[1, 3]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p7_templates_item_0 : (⟨0, 1, [], [], [2], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_2 : (⟨0, 2, [], [], [3, 4, 5, 6], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_3 : (⟨0, 3, [], [], [2], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_4 : (⟨0, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_5 : (⟨0, 4, [], [], [3, 2], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_6 : (⟨0, 5, [], [], [4, 3, 2], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_7 : (⟨0, 6, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_8 : (⟨0, 6, [], [], [5, 4, 3, 2], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_9 : (⟨1, 2, [], [0], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_10 : (⟨1, 2, [], [0], [3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_11 : (⟨1, 3, [], [0], [2], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_12 : (⟨1, 3, [], [0], [4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_13 : (⟨1, 4, [], [0], [3, 2], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_14 : (⟨1, 5, [], [0], [4, 3, 2], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_15 : (⟨1, 5, [], [0], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_16 : (⟨1, 6, [], [0], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_17 : (⟨1, 6, [], [0], [5, 4, 3, 2], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_18 : (⟨2, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_19 : (⟨2, 4, [], [], [5, 6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_20 : (⟨3, 4, [], [2], [5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_21 : (⟨3, 5, [], [2], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_22 : (⟨3, 6, [], [2], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_23 : (⟨4, 5, [], [2, 3], [6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_templates_item_24 : (⟨5, 6, [], [2, 3, 4], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p7_part_3 : ∀ T ∈ k7t3p7.templates, T.Check k7t3p7.graph k7t3p7.clique 7 (patternAmount ([[1, 3]] : List (List ℕ))) (([[1, 3]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p7_templates_item_0, k7t3p7_templates_item_1, k7t3p7_templates_item_2, k7t3p7_templates_item_3, k7t3p7_templates_item_4, k7t3p7_templates_item_5, k7t3p7_templates_item_6, k7t3p7_templates_item_7, k7t3p7_templates_item_8, k7t3p7_templates_item_9, k7t3p7_templates_item_10, k7t3p7_templates_item_11, k7t3p7_templates_item_12, k7t3p7_templates_item_13, k7t3p7_templates_item_14, k7t3p7_templates_item_15, k7t3p7_templates_item_16, k7t3p7_templates_item_17, k7t3p7_templates_item_18, k7t3p7_templates_item_19, k7t3p7_templates_item_20, k7t3p7_templates_item_21, k7t3p7_templates_item_22, k7t3p7_templates_item_23, k7t3p7_templates_item_24⟩

private theorem k7t3p7_required_item_0 : (⟨0, 1, []⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_1 : (⟨0, 6, [1, 2, 3, 4, 5]⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_2 : (⟨1, 2, []⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_3 : (⟨1, 3, [2]⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_4 : (⟨1, 4, [2, 3]⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_5 : (⟨1, 6, [2, 3, 4, 5]⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_6 : (⟨2, 3, []⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_required_item_7 : (⟨3, 5, [4]⟩ : RequiredPathData (Fin 7)).Check k7t3p7.graph 7 := by decide

private theorem k7t3p7_part_4 : ∀ p ∈ k7t3p7.required, p.Check k7t3p7.graph 7 := by
  simp only [k7t3p7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p7_required_item_0, k7t3p7_required_item_1, k7t3p7_required_item_2, k7t3p7_required_item_3, k7t3p7_required_item_4, k7t3p7_required_item_5, k7t3p7_required_item_6, k7t3p7_required_item_7⟩

private theorem k7t3p7_part_5 : ClosureCheck k7t3p7.graph (k7t3p7.initialMatrix 7) 7 3 k7t3p7.closure := by
  rw [k7t3p7_initial_eq]
  exact k7t3p7_closure_0

private theorem k7t3p7_part_6 : k7t3p7.bad.Check k7t3p7.graph (k7t3p7.matrix 7) 7 3 := by
  rw [k7t3p7_matrix_eq]
  decide

theorem k7t3p7_check : k7t3p7.Check 7 3 [[1, 3]] :=
  ⟨k7t3p7_part_0, k7t3p7_part_1, k7t3p7_part_2, k7t3p7_part_3, k7t3p7_part_4, k7t3p7_part_5, k7t3p7_part_6⟩
private def k7t3p8_step_0_data : EdgeAttachmentData 7 := ⟨2, 0, [⟨1, 2, [0]⟩, ⟨1, 6, [0, 2, 3, 4, 5]⟩, ⟨1, 3, [2, 0, 6, 5, 4]⟩, ⟨6, 1, [5, 4, 3, 0, 2]⟩], ⟨none, {(1, 3), (2, 3), (6, 2)}⟩⟩

private def k7t3p8_step_0 : ClosureStep 7 := .edge k7t3p8_step_0_data

private def k7t3p8_step_1_data : FreshAttachmentData 7 := ⟨2, 0, [⟨2, 0, [1, 7, 6, 5, 4, 3]⟩, ⟨2, 7, [1, 0, 3, 4, 5, 6]⟩, ⟨2, 5, [1, 0, 3, 4, 7, 6]⟩, ⟨2, 6, [3, 0, 1, 7, 4, 5]⟩, ⟨2, 4, [3, 0, 1, 7, 6, 5]⟩, ⟨5, 0, [4, 7, 1, 2, 3]⟩, ⟨5, 0, [6, 7, 4, 1, 2, 3]⟩, ⟨5, 2, [6, 7, 4, 1, 0, 3]⟩, ⟨6, 0, [5, 4, 1, 2, 3]⟩, ⟨6, 0, [5, 4, 7, 1, 2, 3]⟩, ⟨6, 2, [5, 4, 7, 1, 0, 3]⟩], ⟨none, {(5, 2), (6, 2), (2, 2), (3, 0)}⟩⟩

private def k7t3p8_step_1 : ClosureStep 7 := .fresh k7t3p8_step_1_data

private def k7t3p8_step_2_data : EdgeAttachmentData 7 := ⟨3, 1, [⟨0, 2, [6, 5, 4, 3, 1]⟩, ⟨1, 0, [3]⟩, ⟨2, 0, [1, 3, 4, 5, 6]⟩, ⟨2, 1, [3]⟩], ⟨none, {(2, 3), (1, 3), (0, 2)}⟩⟩

private def k7t3p8_step_2 : ClosureStep 7 := .edge k7t3p8_step_2_data

private def k7t3p8_step_3_data : EdgeAttachmentData 7 := ⟨4, 1, [⟨0, 2, [1, 4, 5, 6, 3]⟩, ⟨0, 5, [6, 3, 2, 1, 4]⟩, ⟨0, 3, [6, 5, 4, 1, 2]⟩, ⟨2, 0, [1, 4, 5, 6, 3]⟩, ⟨5, 0, [4, 1, 2, 3, 6]⟩], ⟨none, {(0, 2), (2, 2), (5, 2), (1, 2)}⟩⟩

private def k7t3p8_step_3 : ClosureStep 7 := .edge k7t3p8_step_3_data

private def k7t3p8_step_4_data : EdgeAttachmentData 7 := ⟨4, 2, [⟨0, 6, [1, 2, 4, 3]⟩, ⟨0, 5, [1, 2, 4, 3, 6]⟩, ⟨0, 3, [1, 2, 4, 5, 6]⟩, ⟨0, 3, [6, 5, 4, 2]⟩, ⟨3, 6, [0, 1, 2, 4, 5]⟩, ⟨3, 1, [0, 6, 5, 4, 2]⟩, ⟨3, 0, [2, 4, 5, 6]⟩, ⟨3, 6, [4, 2, 1, 0]⟩, ⟨3, 5, [4, 2, 1, 0, 6]⟩, ⟨3, 0, [6, 5, 4, 2, 1]⟩, ⟨6, 3, [0, 1, 2, 4]⟩, ⟨6, 0, [3, 4, 2, 1]⟩, ⟨6, 3, [5, 4, 2, 1, 0]⟩, ⟨6, 1, [5, 4, 2, 3, 0]⟩], ⟨none, {(3, 3), (0, 3), (6, 3)}⟩⟩

private def k7t3p8_step_4 : ClosureStep 7 := .edge k7t3p8_step_4_data

private def k7t3p8_step_5_data : EdgeAttachmentData 7 := ⟨5, 0, [⟨1, 6, [2, 3, 4, 5, 0]⟩, ⟨4, 6, [3, 2, 1, 0, 5]⟩, ⟨6, 5, [0]⟩, ⟨6, 1, [0, 5, 4, 3, 2]⟩, ⟨6, 4, [3, 2, 1, 0, 5]⟩], ⟨none, {(6, 3), (1, 2), (4, 2), (5, 2)}⟩⟩

private def k7t3p8_step_5 : ClosureStep 7 := .edge k7t3p8_step_5_data

private def k7t3p8_step_6_data : FreshAttachmentData 7 := ⟨5, 0, [⟨2, 0, [1, 7, 4, 5, 6]⟩, ⟨2, 7, [1, 0, 6, 5, 4]⟩, ⟨2, 0, [3, 4, 5, 6, 7, 1]⟩, ⟨2, 7, [3, 4, 5, 6, 0, 1]⟩, ⟨2, 5, [3, 4, 7, 1, 0, 6]⟩, ⟨3, 0, [2, 1, 4, 5, 6]⟩, ⟨3, 0, [2, 1, 7, 4, 5, 6]⟩, ⟨3, 7, [2, 1, 0, 6, 5, 4]⟩, ⟨3, 5, [2, 1, 0, 6, 7, 4]⟩, ⟨7, 0, [1, 2, 3, 4, 5, 6]⟩, ⟨7, 2, [1, 0, 6, 5, 4, 3]⟩, ⟨7, 5, [4, 3, 2, 1, 0, 6]⟩, ⟨7, 2, [4, 5, 6, 0, 1]⟩, ⟨7, 3, [4, 5, 6, 0, 1, 2]⟩, ⟨7, 4, [6, 0, 1, 2, 3]⟩], ⟨none, {(2, 2), (3, 2), (7, 2)}⟩⟩

private def k7t3p8_step_6 : ClosureStep 7 := .fresh k7t3p8_step_6_data

private def k7t3p8_step_7_data : EdgeAttachmentData 7 := ⟨5, 1, [⟨0, 6, [1, 5, 4, 3]⟩, ⟨0, 2, [6, 3, 4, 5, 1]⟩, ⟨2, 4, [1, 5]⟩, ⟨2, 0, [1, 5, 4, 3, 6]⟩, ⟨4, 6, [5, 1, 2, 3, 0]⟩, ⟨6, 4, [0, 3, 2, 1, 5]⟩, ⟨6, 0, [3, 4, 5, 1]⟩], ⟨none, {(2, 2), (4, 2), (0, 3), (6, 3)}⟩⟩

private def k7t3p8_step_7 : ClosureStep 7 := .edge k7t3p8_step_7_data

private def k7t3p8_step_8_data : EdgeAttachmentData 7 := ⟨5, 2, [⟨1, 6, [2, 5, 4, 3, 0]⟩, ⟨4, 6, [3, 0, 1, 2, 5]⟩, ⟨6, 3, [0, 1, 2, 5, 4]⟩, ⟨6, 1, [0, 3, 4, 5, 2]⟩, ⟨6, 4, [3, 0, 1, 2, 5]⟩], ⟨none, {(6, 2), (4, 2), (1, 2), (5, 2)}⟩⟩

private def k7t3p8_step_8 : ClosureStep 7 := .edge k7t3p8_step_8_data

private def k7t3p8_step_9_data : EdgeAttachmentData 7 := ⟨5, 3, [⟨4, 5, [3]⟩, ⟨4, 6, [5, 3, 2, 1, 0]⟩, ⟨5, 6, [3]⟩, ⟨6, 4, [0, 1, 2, 3, 5]⟩], ⟨none, {(4, 3), (5, 3), (6, 2)}⟩⟩

private def k7t3p8_step_9 : ClosureStep 7 := .edge k7t3p8_step_9_data

private def k7t3p8_step_10_data : EdgeAttachmentData 7 := ⟨6, 1, [⟨0, 2, [1, 6, 5, 4, 3]⟩, ⟨0, 1, [6]⟩, ⟨0, 5, [6, 1, 2, 3, 4]⟩, ⟨2, 0, [1, 6, 5, 4, 3]⟩, ⟨5, 0, [4, 3, 2, 1, 6]⟩], ⟨none, {(0, 3), (2, 2), (5, 2), (1, 2)}⟩⟩

private def k7t3p8_step_10 : ClosureStep 7 := .edge k7t3p8_step_10_data

private def k7t3p8_step_11_data : FreshAttachmentData 7 := ⟨6, 1, [⟨1, 0, [2, 3, 4, 5, 6, 7]⟩, ⟨1, 6, [2, 0, 7, 4, 5]⟩, ⟨1, 4, [2, 0, 7, 6, 5]⟩, ⟨1, 3, [2, 0, 7, 6, 5, 4]⟩, ⟨1, 5, [4, 3, 2, 0, 7, 6]⟩, ⟨1, 6, [7, 0, 2, 3, 4, 5]⟩, ⟨5, 0, [4, 3, 2, 1, 7]⟩, ⟨5, 0, [6, 7, 1, 4, 3, 2]⟩, ⟨5, 3, [6, 7, 0, 2, 1, 4]⟩, ⟨5, 1, [6, 7, 0, 2, 3, 4]⟩, ⟨6, 3, [5, 4, 1, 7, 0, 2]⟩, ⟨6, 0, [5, 4, 3, 2, 1, 7]⟩, ⟨6, 1, [5, 4, 3, 2, 0, 7]⟩, ⟨6, 0, [5, 4, 7, 1, 2]⟩, ⟨6, 1, [5, 4, 7, 0, 2]⟩], ⟨none, {(5, 2), (6, 2), (1, 2)}⟩⟩

private def k7t3p8_step_11 : ClosureStep 7 := .fresh k7t3p8_step_11_data

private def k7t3p8_step_12_data : EdgeAttachmentData 7 := ⟨6, 2, [⟨2, 4, [6, 3]⟩, ⟨2, 5, [6]⟩, ⟨5, 0, [4, 3, 6, 2, 1]⟩], ⟨none, {(2, 3), (4, 2), (5, 2), (1, 1)}⟩⟩

private def k7t3p8_step_12 : ClosureStep 7 := .edge k7t3p8_step_12_data

private def k7t3p8_templates_block_0 : List (TemplateData (Fin 7)) := [⟨0, 1, [], [], [2, 3], 2, 4⟩, ⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩, ⟨0, 2, [], [], [3], 3, 5⟩, ⟨0, 2, [], [], [3, 4, 5, 6], 2, 2⟩, ⟨0, 3, [], [], [], 4, 6⟩, ⟨0, 3, [], [], [4, 5, 6], 3, 3⟩, ⟨0, 4, [], [], [3], 3, 5⟩, ⟨0, 4, [], [], [5, 6], 2, 4⟩, ⟨0, 4, [], [3, 2, 1], [5, 6], 1, 1⟩, ⟨0, 5, [], [], [4, 3], 2, 4⟩, ⟨0, 5, [], [], [6], 3, 5⟩, ⟨0, 6, [], [], [], 4, 6⟩]

private def k7t3p8_templates_block_1 : List (TemplateData (Fin 7)) := [⟨0, 6, [], [3, 2, 1], [], 3, 3⟩, ⟨1, 2, [], [0], [3], 2, 4⟩, ⟨1, 2, [], [0], [3, 4, 5, 6], 1, 1⟩, ⟨1, 3, [], [0], [4, 5, 6], 2, 2⟩, ⟨1, 4, [], [0], [3], 2, 4⟩, ⟨1, 4, [], [0], [5, 6], 1, 3⟩, ⟨1, 5, [], [0], [4, 3], 1, 3⟩, ⟨1, 5, [], [0], [6], 2, 4⟩, ⟨1, 6, [], [0], [], 3, 5⟩, ⟨1, 6, [], [3, 2], [], 2, 4⟩, ⟨2, 3, [], [0, 1], [], 2, 4⟩, ⟨2, 3, [], [0, 1], [4, 5, 6], 1, 1⟩]

private def k7t3p8_templates_block_2 : List (TemplateData (Fin 7)) := [⟨2, 4, [], [0, 1], [3], 1, 3⟩, ⟨2, 5, [], [0, 1], [4, 3], 1, 2⟩, ⟨2, 5, [], [0, 1], [6], 1, 3⟩, ⟨2, 5, [], [3], [6], 2, 4⟩, ⟨2, 6, [], [0, 1], [], 2, 4⟩, ⟨2, 6, [], [3], [], 3, 5⟩, ⟨2, 6, [], [0, 1], [5, 4, 3], 1, 1⟩, ⟨3, 4, [], [], [5, 6], 2, 4⟩, ⟨3, 4, [], [0, 1, 2], [5, 6], 1, 1⟩, ⟨3, 5, [], [0, 1, 2], [6], 2, 2⟩, ⟨3, 6, [], [], [], 4, 6⟩, ⟨3, 6, [], [0, 1, 2], [], 3, 3⟩]

private def k7t3p8_templates_block_3 : List (TemplateData (Fin 7)) := [⟨4, 5, [], [3], [6], 2, 4⟩, ⟨4, 5, [], [0, 1, 2, 3], [6], 1, 1⟩, ⟨4, 6, [], [3], [], 3, 5⟩, ⟨4, 6, [], [0, 1, 2, 3], [], 2, 2⟩, ⟨5, 6, [], [3, 4], [], 2, 4⟩, ⟨5, 6, [], [0, 1, 2, 3, 4], [], 1, 1⟩]

def k7t3p8 : LayoutCertificate 7 where
  chains := [[0, 1, 2, 3, 4, 5, 6]]
  clique := {0, 3, 6}
  templates := k7t3p8_templates_block_0 ++ k7t3p8_templates_block_1 ++ k7t3p8_templates_block_2 ++ k7t3p8_templates_block_3
  required := [⟨0, 6, [1, 2, 3, 4, 5]⟩,
    ⟨1, 2, []⟩,
    ⟨2, 4, [3]⟩,
    ⟨4, 5, []⟩]
  closure := [k7t3p8_step_0, k7t3p8_step_1, k7t3p8_step_2, k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12]
  bad := ⟨none, {(2, 2), (1, 2), (5, 2)}⟩


private def k7t3p8_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 2 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 2 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_template_matrix_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 2 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {4, 5, 6}],
    #[Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 2 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 3 6, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 2 5, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{4, 5, 6}, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_template_matrix_0_eq_row_0 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 0 j = k7t3p8_template_matrix_0 0 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_1 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 1 j = k7t3p8_template_matrix_0 1 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_2 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 2 j = k7t3p8_template_matrix_0 2 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_3 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 3 j = k7t3p8_template_matrix_0 3 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_4 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 4 j = k7t3p8_template_matrix_0 4 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_5 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 5 j = k7t3p8_template_matrix_0 5 j := by decide

private theorem k7t3p8_template_matrix_0_eq_row_6 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_0) 6 j = k7t3p8_template_matrix_0 6 j := by decide

private theorem k7t3p8_template_matrix_0_eq : (templateMatrix k7t3p8_templates_block_0) = k7t3p8_template_matrix_0 := by
  funext i j
  fin_cases i

  · exact k7t3p8_template_matrix_0_eq_row_0 j

  · exact k7t3p8_template_matrix_0_eq_row_1 j

  · exact k7t3p8_template_matrix_0_eq_row_2 j

  · exact k7t3p8_template_matrix_0_eq_row_3 j

  · exact k7t3p8_template_matrix_0_eq_row_4 j

  · exact k7t3p8_template_matrix_0_eq_row_5 j

  · exact k7t3p8_template_matrix_0_eq_row_6 j

private def k7t3p8_template_matrix_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, ∅, ∅, {3}],
    #[∅, ∅, Finset.Icc 1 4, {2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, ∅, ∅],
    #[∅, {2}, Finset.Icc 1 4, ∅, ∅, ∅, ∅],
    #[∅, Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅],
    #[∅, Finset.Icc 1 4, ∅, ∅, ∅, ∅, ∅],
    #[{3}, Finset.Icc 2 5, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_template_matrix_1_eq_row_0 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 0 j = k7t3p8_template_matrix_1 0 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_1 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 1 j = k7t3p8_template_matrix_1 1 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_2 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 2 j = k7t3p8_template_matrix_1 2 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_3 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 3 j = k7t3p8_template_matrix_1 3 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_4 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 4 j = k7t3p8_template_matrix_1 4 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_5 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 5 j = k7t3p8_template_matrix_1 5 j := by decide

private theorem k7t3p8_template_matrix_1_eq_row_6 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_1) 6 j = k7t3p8_template_matrix_1 6 j := by decide

private theorem k7t3p8_template_matrix_1_eq : (templateMatrix k7t3p8_templates_block_1) = k7t3p8_template_matrix_1 := by
  funext i j
  fin_cases i

  · exact k7t3p8_template_matrix_1_eq_row_0 j

  · exact k7t3p8_template_matrix_1_eq_row_1 j

  · exact k7t3p8_template_matrix_1_eq_row_2 j

  · exact k7t3p8_template_matrix_1_eq_row_3 j

  · exact k7t3p8_template_matrix_1_eq_row_4 j

  · exact k7t3p8_template_matrix_1_eq_row_5 j

  · exact k7t3p8_template_matrix_1_eq_row_6 j

private def k7t3p8_template_matrix_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, {1, 2, 3}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, ∅, ∅, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[∅, ∅, {1, 2, 3}, Finset.Icc 1 4, ∅, ∅, ∅],
    #[∅, ∅, Finset.Icc 1 4, {2}, ∅, ∅, ∅],
    #[∅, ∅, Finset.Icc 1 5, Finset.Icc 3 6, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_template_matrix_2_eq_row_0 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 0 j = k7t3p8_template_matrix_2 0 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_1 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 1 j = k7t3p8_template_matrix_2 1 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_2 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 2 j = k7t3p8_template_matrix_2 2 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_3 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 3 j = k7t3p8_template_matrix_2 3 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_4 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 4 j = k7t3p8_template_matrix_2 4 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_5 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 5 j = k7t3p8_template_matrix_2 5 j := by decide

private theorem k7t3p8_template_matrix_2_eq_row_6 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_2) 6 j = k7t3p8_template_matrix_2 6 j := by decide

private theorem k7t3p8_template_matrix_2_eq : (templateMatrix k7t3p8_templates_block_2) = k7t3p8_template_matrix_2 := by
  funext i j
  fin_cases i

  · exact k7t3p8_template_matrix_2_eq_row_0 j

  · exact k7t3p8_template_matrix_2_eq_row_1 j

  · exact k7t3p8_template_matrix_2_eq_row_2 j

  · exact k7t3p8_template_matrix_2_eq_row_3 j

  · exact k7t3p8_template_matrix_2_eq_row_4 j

  · exact k7t3p8_template_matrix_2_eq_row_5 j

  · exact k7t3p8_template_matrix_2_eq_row_6 j

private def k7t3p8_template_matrix_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, Finset.Icc 1 4, Finset.Icc 2 5],
    #[∅, ∅, ∅, ∅, Finset.Icc 1 4, ∅, Finset.Icc 1 4],
    #[∅, ∅, ∅, ∅, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_template_matrix_3_eq_row_0 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 0 j = k7t3p8_template_matrix_3 0 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_1 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 1 j = k7t3p8_template_matrix_3 1 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_2 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 2 j = k7t3p8_template_matrix_3 2 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_3 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 3 j = k7t3p8_template_matrix_3 3 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_4 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 4 j = k7t3p8_template_matrix_3 4 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_5 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 5 j = k7t3p8_template_matrix_3 5 j := by decide

private theorem k7t3p8_template_matrix_3_eq_row_6 : ∀ j : Fin 7, (templateMatrix k7t3p8_templates_block_3) 6 j = k7t3p8_template_matrix_3 6 j := by decide

private theorem k7t3p8_template_matrix_3_eq : (templateMatrix k7t3p8_templates_block_3) = k7t3p8_template_matrix_3 := by
  funext i j
  fin_cases i

  · exact k7t3p8_template_matrix_3_eq_row_0 j

  · exact k7t3p8_template_matrix_3_eq_row_1 j

  · exact k7t3p8_template_matrix_3_eq_row_2 j

  · exact k7t3p8_template_matrix_3_eq_row_3 j

  · exact k7t3p8_template_matrix_3_eq_row_4 j

  · exact k7t3p8_template_matrix_3_eq_row_5 j

  · exact k7t3p8_template_matrix_3_eq_row_6 j

private theorem k7t3p8_initial_merged_eq_row_0 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 0 j = k7t3p8_state_0 0 j := by decide

private theorem k7t3p8_initial_merged_eq_row_1 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 1 j = k7t3p8_state_0 1 j := by decide

private theorem k7t3p8_initial_merged_eq_row_2 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 2 j = k7t3p8_state_0 2 j := by decide

private theorem k7t3p8_initial_merged_eq_row_3 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 3 j = k7t3p8_state_0 3 j := by decide

private theorem k7t3p8_initial_merged_eq_row_4 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 4 j = k7t3p8_state_0 4 j := by decide

private theorem k7t3p8_initial_merged_eq_row_5 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 5 j = k7t3p8_state_0 5 j := by decide

private theorem k7t3p8_initial_merged_eq_row_6 : ∀ j : Fin 7, (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) 6 j = k7t3p8_state_0 6 j := by decide

private theorem k7t3p8_initial_merged_eq : (fun i j => (((k7t3p8_template_matrix_0 i j ∪ k7t3p8_template_matrix_1 i j) ∪ k7t3p8_template_matrix_2 i j) ∪ k7t3p8_template_matrix_3 i j) ∪ requiredMatrix 7 k7t3p8.required i j) = k7t3p8_state_0 := by
  funext i j
  fin_cases i

  · exact k7t3p8_initial_merged_eq_row_0 j

  · exact k7t3p8_initial_merged_eq_row_1 j

  · exact k7t3p8_initial_merged_eq_row_2 j

  · exact k7t3p8_initial_merged_eq_row_3 j

  · exact k7t3p8_initial_merged_eq_row_4 j

  · exact k7t3p8_initial_merged_eq_row_5 j

  · exact k7t3p8_initial_merged_eq_row_6 j

private theorem k7t3p8_initial_eq : k7t3p8.initialMatrix 7 = k7t3p8_state_0 := by
  funext i j
  change templateMatrix (k7t3p8_templates_block_0 ++ k7t3p8_templates_block_1 ++ k7t3p8_templates_block_2 ++ k7t3p8_templates_block_3) i j ∪ requiredMatrix 7 k7t3p8.required i j = _
  simp only [templateMatrix_append, k7t3p8_template_matrix_0_eq, k7t3p8_template_matrix_1_eq, k7t3p8_template_matrix_2_eq, k7t3p8_template_matrix_3_eq]
  exact congrFun (congrFun k7t3p8_initial_merged_eq i) j

private def k7t3p8_state_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, {0, 2, 3, 4, 5}, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[{0, 2, 3, 4, 5}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 2 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, Finset.Icc 1 6, {1, 2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 2 5, Finset.Icc 1 6, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {1, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_0_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 0 j = k7t3p8_local_0 0 j := by decide

private theorem k7t3p8_local_0_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 1 j = k7t3p8_local_0 1 j := by decide

private theorem k7t3p8_local_0_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 2 j = k7t3p8_local_0 2 j := by decide

private theorem k7t3p8_local_0_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 3 j = k7t3p8_local_0 3 j := by decide

private theorem k7t3p8_local_0_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 4 j = k7t3p8_local_0 4 j := by decide

private theorem k7t3p8_local_0_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 5 j = k7t3p8_local_0 5 j := by decide

private theorem k7t3p8_local_0_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) 6 j = k7t3p8_local_0 6 j := by decide

private theorem k7t3p8_local_0_eq : (fun a b => k7t3p8_state_0 a b ∪ requiredMatrix 7 k7t3p8_step_0_data.required a b) = k7t3p8_local_0 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_0_eq_row_0 j

  · exact k7t3p8_local_0_eq_row_1 j

  · exact k7t3p8_local_0_eq_row_2 j

  · exact k7t3p8_local_0_eq_row_3 j

  · exact k7t3p8_local_0_eq_row_4 j

  · exact k7t3p8_local_0_eq_row_5 j

  · exact k7t3p8_local_0_eq_row_6 j

private theorem k7t3p8_local_0_paths : ∀ p ∈ k7t3p8_step_0_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_0_data.i k7t3p8_step_0_data.j) 7 := by decide

private theorem k7t3p8_local_0_bad : k7t3p8_step_0_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_0_data.i k7t3p8_step_0_data.j) k7t3p8_local_0 7 3 := by decide

private theorem k7t3p8_step_0_check : k7t3p8_step_0.Check k7t3p8.graph k7t3p8_state_0 7 3 := by
  change k7t3p8_step_0_data.Check k7t3p8.graph k7t3p8_state_0 7 3
  refine ⟨k7t3p8_local_0_paths, ?_⟩
  rw [k7t3p8_local_0_eq]
  exact k7t3p8_local_0_bad

private theorem k7t3p8_update_0 : k7t3p8_step_0.apply k7t3p8_state_0 = k7t3p8_state_1 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_0.apply k7t3p8_state_0 i j = k7t3p8_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_1 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, {0}, ∅, ∅, {0, 1}, {0, 1}, ∅],
    #[∅, ∅, Finset.Icc 1 4, {0, 2, 3, 4, 5}, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[{0}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4, 5}],
    #[∅, {0, 2, 3, 4, 5}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[{0, 1}, Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[{0, 1}, Finset.Icc 2 5, Finset.Icc 0 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[∅, {1, 3, 4, 5, 6}, {0, 2, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_1_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 0 j = k7t3p8_local_1 0 j := by decide

private theorem k7t3p8_local_1_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 1 j = k7t3p8_local_1 1 j := by decide

private theorem k7t3p8_local_1_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 2 j = k7t3p8_local_1 2 j := by decide

private theorem k7t3p8_local_1_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 3 j = k7t3p8_local_1 3 j := by decide

private theorem k7t3p8_local_1_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 4 j = k7t3p8_local_1 4 j := by decide

private theorem k7t3p8_local_1_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 5 j = k7t3p8_local_1 5 j := by decide

private theorem k7t3p8_local_1_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 6 j = k7t3p8_local_1 6 j := by decide

private theorem k7t3p8_local_1_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) 7 j = k7t3p8_local_1 7 j := by decide

private theorem k7t3p8_local_1_eq : (fun a b => freshMatrix k7t3p8_state_1 a b ∪ requiredMatrix 7 k7t3p8_step_1_data.required a b) = k7t3p8_local_1 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_1_eq_row_0 j

  · exact k7t3p8_local_1_eq_row_1 j

  · exact k7t3p8_local_1_eq_row_2 j

  · exact k7t3p8_local_1_eq_row_3 j

  · exact k7t3p8_local_1_eq_row_4 j

  · exact k7t3p8_local_1_eq_row_5 j

  · exact k7t3p8_local_1_eq_row_6 j

  · exact k7t3p8_local_1_eq_row_7 j

private theorem k7t3p8_local_1_paths : ∀ p ∈ k7t3p8_step_1_data.required, p.Check (freshGraph k7t3p8.graph k7t3p8_step_1_data.i k7t3p8_step_1_data.j) 7 := by decide

private theorem k7t3p8_local_1_bad : k7t3p8_step_1_data.bad.Check (freshGraph k7t3p8.graph k7t3p8_step_1_data.i k7t3p8_step_1_data.j) k7t3p8_local_1 7 3 := by decide

private theorem k7t3p8_step_1_check : k7t3p8_step_1.Check k7t3p8.graph k7t3p8_state_1 7 3 := by
  change k7t3p8_step_1_data.Check k7t3p8.graph k7t3p8_state_1 7 3
  refine ⟨by decide, k7t3p8_local_1_paths, ?_⟩
  rw [k7t3p8_local_1_eq]
  exact k7t3p8_local_1_bad

private theorem k7t3p8_update_1 : k7t3p8_step_1.apply k7t3p8_state_1 = k7t3p8_state_2 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_1.apply k7t3p8_state_1 i j = k7t3p8_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 6, {2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 1 6, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_2_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 0 j = k7t3p8_local_2 0 j := by decide

private theorem k7t3p8_local_2_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 1 j = k7t3p8_local_2 1 j := by decide

private theorem k7t3p8_local_2_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 2 j = k7t3p8_local_2 2 j := by decide

private theorem k7t3p8_local_2_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 3 j = k7t3p8_local_2 3 j := by decide

private theorem k7t3p8_local_2_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 4 j = k7t3p8_local_2 4 j := by decide

private theorem k7t3p8_local_2_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 5 j = k7t3p8_local_2 5 j := by decide

private theorem k7t3p8_local_2_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) 6 j = k7t3p8_local_2 6 j := by decide

private theorem k7t3p8_local_2_eq : (fun a b => k7t3p8_state_2 a b ∪ requiredMatrix 7 k7t3p8_step_2_data.required a b) = k7t3p8_local_2 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_2_eq_row_0 j

  · exact k7t3p8_local_2_eq_row_1 j

  · exact k7t3p8_local_2_eq_row_2 j

  · exact k7t3p8_local_2_eq_row_3 j

  · exact k7t3p8_local_2_eq_row_4 j

  · exact k7t3p8_local_2_eq_row_5 j

  · exact k7t3p8_local_2_eq_row_6 j

private theorem k7t3p8_local_2_paths : ∀ p ∈ k7t3p8_step_2_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_2_data.i k7t3p8_step_2_data.j) 7 := by decide

private theorem k7t3p8_local_2_bad : k7t3p8_step_2_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_2_data.i k7t3p8_step_2_data.j) k7t3p8_local_2 7 3 := by decide

private theorem k7t3p8_step_2_check : k7t3p8_step_2.Check k7t3p8.graph k7t3p8_state_2 7 3 := by
  change k7t3p8_step_2_data.Check k7t3p8.graph k7t3p8_state_2 7 3
  refine ⟨k7t3p8_local_2_paths, ?_⟩
  rw [k7t3p8_local_2_eq]
  exact k7t3p8_local_2_bad

private theorem k7t3p8_update_2 : k7t3p8_step_2.apply k7t3p8_state_2 = k7t3p8_state_3 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_2.apply k7t3p8_state_2 i j = k7t3p8_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, {1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[{1, 3, 4, 5, 6}, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_3_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 0 j = k7t3p8_local_3 0 j := by decide

private theorem k7t3p8_local_3_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 1 j = k7t3p8_local_3 1 j := by decide

private theorem k7t3p8_local_3_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 2 j = k7t3p8_local_3 2 j := by decide

private theorem k7t3p8_local_3_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 3 j = k7t3p8_local_3 3 j := by decide

private theorem k7t3p8_local_3_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 4 j = k7t3p8_local_3 4 j := by decide

private theorem k7t3p8_local_3_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 5 j = k7t3p8_local_3 5 j := by decide

private theorem k7t3p8_local_3_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) 6 j = k7t3p8_local_3 6 j := by decide

private theorem k7t3p8_local_3_eq : (fun a b => k7t3p8_state_3 a b ∪ requiredMatrix 7 k7t3p8_step_3_data.required a b) = k7t3p8_local_3 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_3_eq_row_0 j

  · exact k7t3p8_local_3_eq_row_1 j

  · exact k7t3p8_local_3_eq_row_2 j

  · exact k7t3p8_local_3_eq_row_3 j

  · exact k7t3p8_local_3_eq_row_4 j

  · exact k7t3p8_local_3_eq_row_5 j

  · exact k7t3p8_local_3_eq_row_6 j

private theorem k7t3p8_local_3_paths : ∀ p ∈ k7t3p8_step_3_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_3_data.i k7t3p8_step_3_data.j) 7 := by decide

private theorem k7t3p8_local_3_bad : k7t3p8_step_3_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_3_data.i k7t3p8_step_3_data.j) k7t3p8_local_3 7 3 := by decide

private theorem k7t3p8_step_3_check : k7t3p8_step_3.Check k7t3p8.graph k7t3p8_state_3 7 3 := by
  change k7t3p8_step_3_data.Check k7t3p8.graph k7t3p8_state_3 7 3
  refine ⟨k7t3p8_local_3_paths, ?_⟩
  rw [k7t3p8_local_3_eq]
  exact k7t3p8_local_3_bad

private theorem k7t3p8_update_3 : k7t3p8_step_3.apply k7t3p8_state_3 = k7t3p8_state_4 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_3.apply k7t3p8_state_3 i j = k7t3p8_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 1, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 1 6, {0, 1, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {1, 2}, Finset.Icc 1 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 4, {1, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_4_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 0 j = k7t3p8_local_4 0 j := by decide

private theorem k7t3p8_local_4_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 1 j = k7t3p8_local_4 1 j := by decide

private theorem k7t3p8_local_4_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 2 j = k7t3p8_local_4 2 j := by decide

private theorem k7t3p8_local_4_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 3 j = k7t3p8_local_4 3 j := by decide

private theorem k7t3p8_local_4_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 4 j = k7t3p8_local_4 4 j := by decide

private theorem k7t3p8_local_4_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 5 j = k7t3p8_local_4 5 j := by decide

private theorem k7t3p8_local_4_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) 6 j = k7t3p8_local_4 6 j := by decide

private theorem k7t3p8_local_4_eq : (fun a b => k7t3p8_state_4 a b ∪ requiredMatrix 7 k7t3p8_step_4_data.required a b) = k7t3p8_local_4 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_4_eq_row_0 j

  · exact k7t3p8_local_4_eq_row_1 j

  · exact k7t3p8_local_4_eq_row_2 j

  · exact k7t3p8_local_4_eq_row_3 j

  · exact k7t3p8_local_4_eq_row_4 j

  · exact k7t3p8_local_4_eq_row_5 j

  · exact k7t3p8_local_4_eq_row_6 j

private theorem k7t3p8_local_4_paths : ∀ p ∈ k7t3p8_step_4_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_4_data.i k7t3p8_step_4_data.j) 7 := by decide

private theorem k7t3p8_local_4_bad : k7t3p8_step_4_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_4_data.i k7t3p8_step_4_data.j) k7t3p8_local_4 7 3 := by decide

private theorem k7t3p8_step_4_check : k7t3p8_step_4.Check k7t3p8.graph k7t3p8_state_4 7 3 := by
  change k7t3p8_step_4_data.Check k7t3p8.graph k7t3p8_state_4 7 3
  refine ⟨k7t3p8_local_4_paths, ?_⟩
  rw [k7t3p8_local_4_eq]
  exact k7t3p8_local_4_bad

private theorem k7t3p8_update_4 : k7t3p8_step_4.apply k7t3p8_state_4 = k7t3p8_state_5 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_4.apply k7t3p8_state_4 i j = k7t3p8_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, {0, 2, 3, 4, 5}, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[{0, 2, 3, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 2 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 1 5],
    #[Finset.Icc 2 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 5],
    #[{1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_5_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 0 j = k7t3p8_local_5 0 j := by decide

private theorem k7t3p8_local_5_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 1 j = k7t3p8_local_5 1 j := by decide

private theorem k7t3p8_local_5_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 2 j = k7t3p8_local_5 2 j := by decide

private theorem k7t3p8_local_5_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 3 j = k7t3p8_local_5 3 j := by decide

private theorem k7t3p8_local_5_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 4 j = k7t3p8_local_5 4 j := by decide

private theorem k7t3p8_local_5_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 5 j = k7t3p8_local_5 5 j := by decide

private theorem k7t3p8_local_5_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) 6 j = k7t3p8_local_5 6 j := by decide

private theorem k7t3p8_local_5_eq : (fun a b => k7t3p8_state_5 a b ∪ requiredMatrix 7 k7t3p8_step_5_data.required a b) = k7t3p8_local_5 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_5_eq_row_0 j

  · exact k7t3p8_local_5_eq_row_1 j

  · exact k7t3p8_local_5_eq_row_2 j

  · exact k7t3p8_local_5_eq_row_3 j

  · exact k7t3p8_local_5_eq_row_4 j

  · exact k7t3p8_local_5_eq_row_5 j

  · exact k7t3p8_local_5_eq_row_6 j

private theorem k7t3p8_local_5_paths : ∀ p ∈ k7t3p8_step_5_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_5_data.i k7t3p8_step_5_data.j) 7 := by decide

private theorem k7t3p8_local_5_bad : k7t3p8_step_5_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_5_data.i k7t3p8_step_5_data.j) k7t3p8_local_5 7 3 := by decide

private theorem k7t3p8_step_5_check : k7t3p8_step_5.Check k7t3p8.graph k7t3p8_state_5 7 3 := by
  change k7t3p8_step_5_data.Check k7t3p8.graph k7t3p8_state_5 7 3
  refine ⟨k7t3p8_local_5_paths, ?_⟩
  rw [k7t3p8_local_5_eq]
  exact k7t3p8_local_5_bad

private theorem k7t3p8_update_5 : k7t3p8_step_5.apply k7t3p8_state_5 = k7t3p8_state_6 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_5.apply k7t3p8_state_5 i j = k7t3p8_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_6 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, {0, 1}, {0, 1}, ∅, ∅, ∅, {0}],
    #[∅, ∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, {0, 2, 3, 4, 5}, {1, 3, 4, 5, 6}],
    #[{0, 1}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 0 5],
    #[{0, 1}, Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 0 5],
    #[∅, Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, {1, 3, 4, 5, 6}],
    #[∅, Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2, 3, 4, 5}],
    #[∅, {0, 2, 3, 4, 5}, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{0}, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}, {0, 2, 3, 4, 5}, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_6_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 0 j = k7t3p8_local_6 0 j := by decide

private theorem k7t3p8_local_6_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 1 j = k7t3p8_local_6 1 j := by decide

private theorem k7t3p8_local_6_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 2 j = k7t3p8_local_6 2 j := by decide

private theorem k7t3p8_local_6_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 3 j = k7t3p8_local_6 3 j := by decide

private theorem k7t3p8_local_6_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 4 j = k7t3p8_local_6 4 j := by decide

private theorem k7t3p8_local_6_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 5 j = k7t3p8_local_6 5 j := by decide

private theorem k7t3p8_local_6_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 6 j = k7t3p8_local_6 6 j := by decide

private theorem k7t3p8_local_6_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) 7 j = k7t3p8_local_6 7 j := by decide

private theorem k7t3p8_local_6_eq : (fun a b => freshMatrix k7t3p8_state_6 a b ∪ requiredMatrix 7 k7t3p8_step_6_data.required a b) = k7t3p8_local_6 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_6_eq_row_0 j

  · exact k7t3p8_local_6_eq_row_1 j

  · exact k7t3p8_local_6_eq_row_2 j

  · exact k7t3p8_local_6_eq_row_3 j

  · exact k7t3p8_local_6_eq_row_4 j

  · exact k7t3p8_local_6_eq_row_5 j

  · exact k7t3p8_local_6_eq_row_6 j

  · exact k7t3p8_local_6_eq_row_7 j

private theorem k7t3p8_local_6_paths : ∀ p ∈ k7t3p8_step_6_data.required, p.Check (freshGraph k7t3p8.graph k7t3p8_step_6_data.i k7t3p8_step_6_data.j) 7 := by decide

private theorem k7t3p8_local_6_bad : k7t3p8_step_6_data.bad.Check (freshGraph k7t3p8.graph k7t3p8_step_6_data.i k7t3p8_step_6_data.j) k7t3p8_local_6 7 3 := by decide

private theorem k7t3p8_step_6_check : k7t3p8_step_6.Check k7t3p8.graph k7t3p8_state_6 7 3 := by
  change k7t3p8_step_6_data.Check k7t3p8.graph k7t3p8_state_6 7 3
  refine ⟨by decide, k7t3p8_local_6_paths, ?_⟩
  rw [k7t3p8_local_6_eq]
  exact k7t3p8_local_6_bad

private theorem k7t3p8_update_6 : k7t3p8_step_6.apply k7t3p8_state_6 = k7t3p8_state_7 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_6.apply k7t3p8_state_6 i j = k7t3p8_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, Finset.Icc 1 6],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 1 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[Finset.Icc 1 6, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_7_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 0 j = k7t3p8_local_7 0 j := by decide

private theorem k7t3p8_local_7_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 1 j = k7t3p8_local_7 1 j := by decide

private theorem k7t3p8_local_7_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 2 j = k7t3p8_local_7 2 j := by decide

private theorem k7t3p8_local_7_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 3 j = k7t3p8_local_7 3 j := by decide

private theorem k7t3p8_local_7_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 4 j = k7t3p8_local_7 4 j := by decide

private theorem k7t3p8_local_7_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 5 j = k7t3p8_local_7 5 j := by decide

private theorem k7t3p8_local_7_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) 6 j = k7t3p8_local_7 6 j := by decide

private theorem k7t3p8_local_7_eq : (fun a b => k7t3p8_state_7 a b ∪ requiredMatrix 7 k7t3p8_step_7_data.required a b) = k7t3p8_local_7 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_7_eq_row_0 j

  · exact k7t3p8_local_7_eq_row_1 j

  · exact k7t3p8_local_7_eq_row_2 j

  · exact k7t3p8_local_7_eq_row_3 j

  · exact k7t3p8_local_7_eq_row_4 j

  · exact k7t3p8_local_7_eq_row_5 j

  · exact k7t3p8_local_7_eq_row_6 j

private theorem k7t3p8_local_7_paths : ∀ p ∈ k7t3p8_step_7_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_7_data.i k7t3p8_step_7_data.j) 7 := by decide

private theorem k7t3p8_local_7_bad : k7t3p8_step_7_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_7_data.i k7t3p8_step_7_data.j) k7t3p8_local_7 7 3 := by decide

private theorem k7t3p8_step_7_check : k7t3p8_step_7.Check k7t3p8.graph k7t3p8_state_7 7 3 := by
  change k7t3p8_step_7_data.Check k7t3p8.graph k7t3p8_state_7 7 3
  refine ⟨k7t3p8_local_7_paths, ?_⟩
  rw [k7t3p8_local_7_eq]
  exact k7t3p8_local_7_bad

private theorem k7t3p8_update_7 : k7t3p8_step_7.apply k7t3p8_state_7 = k7t3p8_state_8 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_7.apply k7t3p8_state_7 i j = k7t3p8_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 1 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 4, {2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 5, {1, 3, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_8_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 0 j = k7t3p8_local_8 0 j := by decide

private theorem k7t3p8_local_8_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 1 j = k7t3p8_local_8 1 j := by decide

private theorem k7t3p8_local_8_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 2 j = k7t3p8_local_8 2 j := by decide

private theorem k7t3p8_local_8_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 3 j = k7t3p8_local_8 3 j := by decide

private theorem k7t3p8_local_8_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 4 j = k7t3p8_local_8 4 j := by decide

private theorem k7t3p8_local_8_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 5 j = k7t3p8_local_8 5 j := by decide

private theorem k7t3p8_local_8_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) 6 j = k7t3p8_local_8 6 j := by decide

private theorem k7t3p8_local_8_eq : (fun a b => k7t3p8_state_8 a b ∪ requiredMatrix 7 k7t3p8_step_8_data.required a b) = k7t3p8_local_8 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_8_eq_row_0 j

  · exact k7t3p8_local_8_eq_row_1 j

  · exact k7t3p8_local_8_eq_row_2 j

  · exact k7t3p8_local_8_eq_row_3 j

  · exact k7t3p8_local_8_eq_row_4 j

  · exact k7t3p8_local_8_eq_row_5 j

  · exact k7t3p8_local_8_eq_row_6 j

private theorem k7t3p8_local_8_paths : ∀ p ∈ k7t3p8_step_8_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_8_data.i k7t3p8_step_8_data.j) 7 := by decide

private theorem k7t3p8_local_8_bad : k7t3p8_step_8_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_8_data.i k7t3p8_step_8_data.j) k7t3p8_local_8 7 3 := by decide

private theorem k7t3p8_step_8_check : k7t3p8_step_8.Check k7t3p8.graph k7t3p8_state_8 7 3 := by
  change k7t3p8_step_8_data.Check k7t3p8.graph k7t3p8_state_8 7 3
  refine ⟨k7t3p8_local_8_paths, ?_⟩
  rw [k7t3p8_local_8_eq]
  exact k7t3p8_local_8_bad

private theorem k7t3p8_update_8 : k7t3p8_step_8.apply k7t3p8_state_8 = k7t3p8_state_9 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_8.apply k7t3p8_state_8 i j = k7t3p8_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, Finset.Icc 1 6, Finset.Icc 1 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {2}, Finset.Icc 1 6, ∅, Finset.Icc 1 5],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_9_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 0 j = k7t3p8_local_9 0 j := by decide

private theorem k7t3p8_local_9_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 1 j = k7t3p8_local_9 1 j := by decide

private theorem k7t3p8_local_9_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 2 j = k7t3p8_local_9 2 j := by decide

private theorem k7t3p8_local_9_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 3 j = k7t3p8_local_9 3 j := by decide

private theorem k7t3p8_local_9_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 4 j = k7t3p8_local_9 4 j := by decide

private theorem k7t3p8_local_9_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 5 j = k7t3p8_local_9 5 j := by decide

private theorem k7t3p8_local_9_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) 6 j = k7t3p8_local_9 6 j := by decide

private theorem k7t3p8_local_9_eq : (fun a b => k7t3p8_state_9 a b ∪ requiredMatrix 7 k7t3p8_step_9_data.required a b) = k7t3p8_local_9 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_9_eq_row_0 j

  · exact k7t3p8_local_9_eq_row_1 j

  · exact k7t3p8_local_9_eq_row_2 j

  · exact k7t3p8_local_9_eq_row_3 j

  · exact k7t3p8_local_9_eq_row_4 j

  · exact k7t3p8_local_9_eq_row_5 j

  · exact k7t3p8_local_9_eq_row_6 j

private theorem k7t3p8_local_9_paths : ∀ p ∈ k7t3p8_step_9_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_9_data.i k7t3p8_step_9_data.j) 7 := by decide

private theorem k7t3p8_local_9_bad : k7t3p8_step_9_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_9_data.i k7t3p8_step_9_data.j) k7t3p8_local_9 7 3 := by decide

private theorem k7t3p8_step_9_check : k7t3p8_step_9.Check k7t3p8.graph k7t3p8_state_9 7 3 := by
  change k7t3p8_step_9_data.Check k7t3p8.graph k7t3p8_state_9 7 3
  refine ⟨k7t3p8_local_9_paths, ?_⟩
  rw [k7t3p8_local_9_eq]
  exact k7t3p8_local_9_bad

private theorem k7t3p8_update_9 : k7t3p8_step_9.apply k7t3p8_state_9 = k7t3p8_state_10 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_9.apply k7t3p8_state_9 i j = k7t3p8_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_11 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4, 5}],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, {0, 2, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 5, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 2 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 2 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_10_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 0 j = k7t3p8_local_10 0 j := by decide

private theorem k7t3p8_local_10_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 1 j = k7t3p8_local_10 1 j := by decide

private theorem k7t3p8_local_10_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 2 j = k7t3p8_local_10 2 j := by decide

private theorem k7t3p8_local_10_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 3 j = k7t3p8_local_10 3 j := by decide

private theorem k7t3p8_local_10_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 4 j = k7t3p8_local_10 4 j := by decide

private theorem k7t3p8_local_10_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 5 j = k7t3p8_local_10 5 j := by decide

private theorem k7t3p8_local_10_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) 6 j = k7t3p8_local_10 6 j := by decide

private theorem k7t3p8_local_10_eq : (fun a b => k7t3p8_state_10 a b ∪ requiredMatrix 7 k7t3p8_step_10_data.required a b) = k7t3p8_local_10 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_10_eq_row_0 j

  · exact k7t3p8_local_10_eq_row_1 j

  · exact k7t3p8_local_10_eq_row_2 j

  · exact k7t3p8_local_10_eq_row_3 j

  · exact k7t3p8_local_10_eq_row_4 j

  · exact k7t3p8_local_10_eq_row_5 j

  · exact k7t3p8_local_10_eq_row_6 j

private theorem k7t3p8_local_10_paths : ∀ p ∈ k7t3p8_step_10_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_10_data.i k7t3p8_step_10_data.j) 7 := by decide

private theorem k7t3p8_local_10_bad : k7t3p8_step_10_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_10_data.i k7t3p8_step_10_data.j) k7t3p8_local_10 7 3 := by decide

private theorem k7t3p8_step_10_check : k7t3p8_step_10.Check k7t3p8.graph k7t3p8_state_10 7 3 := by
  change k7t3p8_step_10_data.Check k7t3p8.graph k7t3p8_state_10 7 3
  refine ⟨k7t3p8_local_10_paths, ?_⟩
  rw [k7t3p8_local_10_eq]
  exact k7t3p8_local_10_bad

private theorem k7t3p8_update_10 : k7t3p8_step_10.apply k7t3p8_state_10 = k7t3p8_state_11 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_10.apply k7t3p8_state_10 i j = k7t3p8_state_11 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_12 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_11 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0}, ∅, ∅, ∅, {0, 1}, {0, 1}, ∅],
    #[{0}, ∅, Finset.Icc 1 4, Finset.Icc 0 5, {1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[∅, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4, 5}],
    #[∅, Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 1 5],
    #[∅, {1, 3, 4, 5, 6}, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[{0, 1}, Finset.Icc 0 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[{0, 1}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[∅, {1, 3, 4, 5, 6}, {0, 2, 3, 4, 5}, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_11_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 0 j = k7t3p8_local_11 0 j := by decide

private theorem k7t3p8_local_11_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 1 j = k7t3p8_local_11 1 j := by decide

private theorem k7t3p8_local_11_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 2 j = k7t3p8_local_11 2 j := by decide

private theorem k7t3p8_local_11_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 3 j = k7t3p8_local_11 3 j := by decide

private theorem k7t3p8_local_11_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 4 j = k7t3p8_local_11 4 j := by decide

private theorem k7t3p8_local_11_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 5 j = k7t3p8_local_11 5 j := by decide

private theorem k7t3p8_local_11_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 6 j = k7t3p8_local_11 6 j := by decide

private theorem k7t3p8_local_11_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) 7 j = k7t3p8_local_11 7 j := by decide

private theorem k7t3p8_local_11_eq : (fun a b => freshMatrix k7t3p8_state_11 a b ∪ requiredMatrix 7 k7t3p8_step_11_data.required a b) = k7t3p8_local_11 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_11_eq_row_0 j

  · exact k7t3p8_local_11_eq_row_1 j

  · exact k7t3p8_local_11_eq_row_2 j

  · exact k7t3p8_local_11_eq_row_3 j

  · exact k7t3p8_local_11_eq_row_4 j

  · exact k7t3p8_local_11_eq_row_5 j

  · exact k7t3p8_local_11_eq_row_6 j

  · exact k7t3p8_local_11_eq_row_7 j

private theorem k7t3p8_local_11_paths : ∀ p ∈ k7t3p8_step_11_data.required, p.Check (freshGraph k7t3p8.graph k7t3p8_step_11_data.i k7t3p8_step_11_data.j) 7 := by decide

private theorem k7t3p8_local_11_bad : k7t3p8_step_11_data.bad.Check (freshGraph k7t3p8.graph k7t3p8_step_11_data.i k7t3p8_step_11_data.j) k7t3p8_local_11 7 3 := by decide

private theorem k7t3p8_step_11_check : k7t3p8_step_11.Check k7t3p8.graph k7t3p8_state_11 7 3 := by
  change k7t3p8_step_11_data.Check k7t3p8.graph k7t3p8_state_11 7 3
  refine ⟨by decide, k7t3p8_local_11_paths, ?_⟩
  rw [k7t3p8_local_11_eq]
  exact k7t3p8_local_11_bad

private theorem k7t3p8_update_11 : k7t3p8_step_11.apply k7t3p8_state_11 = k7t3p8_state_12 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_11.apply k7t3p8_state_11 i j = k7t3p8_state_12 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t3p8_state_13 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, {0, 1, 2, 3, 5}, Finset.Icc 0 4, Finset.Icc 0 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, {0, 1, 2, 3, 5}, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t3p8_local_12 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 3 6, Finset.Icc 1 5, Finset.Icc 0 5, {1, 3, 4, 5, 6}],
    #[Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, {0, 2}, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 5],
    #[Finset.Icc 0 5, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4, Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 1 5],
    #[Finset.Icc 3 6, {0, 2}, Finset.Icc 1 4, ∅, Finset.Icc 1 4, {0, 2}, Finset.Icc 3 6],
    #[Finset.Icc 1 5, Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 1 4, ∅, {1, 2, 3, 4, 6}, Finset.Icc 2 5],
    #[Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {0, 2}, {1, 2, 3, 4, 6}, ∅, Finset.Icc 1 4],
    #[{1, 3, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 5, Finset.Icc 3 6, Finset.Icc 2 5, Finset.Icc 1 4, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t3p8_local_12_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 0 j = k7t3p8_local_12 0 j := by decide

private theorem k7t3p8_local_12_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 1 j = k7t3p8_local_12 1 j := by decide

private theorem k7t3p8_local_12_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 2 j = k7t3p8_local_12 2 j := by decide

private theorem k7t3p8_local_12_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 3 j = k7t3p8_local_12 3 j := by decide

private theorem k7t3p8_local_12_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 4 j = k7t3p8_local_12 4 j := by decide

private theorem k7t3p8_local_12_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 5 j = k7t3p8_local_12 5 j := by decide

private theorem k7t3p8_local_12_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) 6 j = k7t3p8_local_12 6 j := by decide

private theorem k7t3p8_local_12_eq : (fun a b => k7t3p8_state_12 a b ∪ requiredMatrix 7 k7t3p8_step_12_data.required a b) = k7t3p8_local_12 := by
  funext i j
  fin_cases i

  · exact k7t3p8_local_12_eq_row_0 j

  · exact k7t3p8_local_12_eq_row_1 j

  · exact k7t3p8_local_12_eq_row_2 j

  · exact k7t3p8_local_12_eq_row_3 j

  · exact k7t3p8_local_12_eq_row_4 j

  · exact k7t3p8_local_12_eq_row_5 j

  · exact k7t3p8_local_12_eq_row_6 j

private theorem k7t3p8_local_12_paths : ∀ p ∈ k7t3p8_step_12_data.required, p.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_12_data.i k7t3p8_step_12_data.j) 7 := by decide

private theorem k7t3p8_local_12_bad : k7t3p8_step_12_data.bad.Check (addedEdgeGraph k7t3p8.graph k7t3p8_step_12_data.i k7t3p8_step_12_data.j) k7t3p8_local_12 7 3 := by decide

private theorem k7t3p8_step_12_check : k7t3p8_step_12.Check k7t3p8.graph k7t3p8_state_12 7 3 := by
  change k7t3p8_step_12_data.Check k7t3p8.graph k7t3p8_state_12 7 3
  refine ⟨k7t3p8_local_12_paths, ?_⟩
  rw [k7t3p8_local_12_eq]
  exact k7t3p8_local_12_bad

private theorem k7t3p8_update_12 : k7t3p8_step_12.apply k7t3p8_state_12 = k7t3p8_state_13 := by
  have h : ∀ i j : Fin 7, k7t3p8_step_12.apply k7t3p8_state_12 i j = k7t3p8_state_13 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k7t3p8_closure_13 : ClosureCheck k7t3p8.graph k7t3p8_state_13 7 3 [] := by trivial

private theorem k7t3p8_closure_12 : ClosureCheck k7t3p8.graph k7t3p8_state_12 7 3 [k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_12_check
  · rw [k7t3p8_update_12]
    exact k7t3p8_closure_13

private theorem k7t3p8_closure_11 : ClosureCheck k7t3p8.graph k7t3p8_state_11 7 3 [k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_11_check
  · rw [k7t3p8_update_11]
    exact k7t3p8_closure_12

private theorem k7t3p8_closure_10 : ClosureCheck k7t3p8.graph k7t3p8_state_10 7 3 [k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_10_check
  · rw [k7t3p8_update_10]
    exact k7t3p8_closure_11

private theorem k7t3p8_closure_9 : ClosureCheck k7t3p8.graph k7t3p8_state_9 7 3 [k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_9_check
  · rw [k7t3p8_update_9]
    exact k7t3p8_closure_10

private theorem k7t3p8_closure_8 : ClosureCheck k7t3p8.graph k7t3p8_state_8 7 3 [k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_8_check
  · rw [k7t3p8_update_8]
    exact k7t3p8_closure_9

private theorem k7t3p8_closure_7 : ClosureCheck k7t3p8.graph k7t3p8_state_7 7 3 [k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_7_check
  · rw [k7t3p8_update_7]
    exact k7t3p8_closure_8

private theorem k7t3p8_closure_6 : ClosureCheck k7t3p8.graph k7t3p8_state_6 7 3 [k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_6_check
  · rw [k7t3p8_update_6]
    exact k7t3p8_closure_7

private theorem k7t3p8_closure_5 : ClosureCheck k7t3p8.graph k7t3p8_state_5 7 3 [k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_5_check
  · rw [k7t3p8_update_5]
    exact k7t3p8_closure_6

private theorem k7t3p8_closure_4 : ClosureCheck k7t3p8.graph k7t3p8_state_4 7 3 [k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_4_check
  · rw [k7t3p8_update_4]
    exact k7t3p8_closure_5

private theorem k7t3p8_closure_3 : ClosureCheck k7t3p8.graph k7t3p8_state_3 7 3 [k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_3_check
  · rw [k7t3p8_update_3]
    exact k7t3p8_closure_4

private theorem k7t3p8_closure_2 : ClosureCheck k7t3p8.graph k7t3p8_state_2 7 3 [k7t3p8_step_2, k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_2_check
  · rw [k7t3p8_update_2]
    exact k7t3p8_closure_3

private theorem k7t3p8_closure_1 : ClosureCheck k7t3p8.graph k7t3p8_state_1 7 3 [k7t3p8_step_1, k7t3p8_step_2, k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_1_check
  · rw [k7t3p8_update_1]
    exact k7t3p8_closure_2

private theorem k7t3p8_closure_0 : ClosureCheck k7t3p8.graph k7t3p8_state_0 7 3 [k7t3p8_step_0, k7t3p8_step_1, k7t3p8_step_2, k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] := by
  constructor
  · exact k7t3p8_step_0_check
  · rw [k7t3p8_update_0]
    exact k7t3p8_closure_1

private theorem k7t3p8_matrix_eq : k7t3p8.matrix 7 = k7t3p8_state_13 := by
  change closureMatrix (k7t3p8.initialMatrix 7) _ = _
  rw [k7t3p8_initial_eq]
  change closureMatrix k7t3p8_state_0 [k7t3p8_step_0, k7t3p8_step_1, k7t3p8_step_2, k7t3p8_step_3, k7t3p8_step_4, k7t3p8_step_5, k7t3p8_step_6, k7t3p8_step_7, k7t3p8_step_8, k7t3p8_step_9, k7t3p8_step_10, k7t3p8_step_11, k7t3p8_step_12] = _
  simp only [closureMatrix]
  rw [k7t3p8_update_0, k7t3p8_update_1, k7t3p8_update_2, k7t3p8_update_3, k7t3p8_update_4, k7t3p8_update_5, k7t3p8_update_6, k7t3p8_update_7, k7t3p8_update_8, k7t3p8_update_9, k7t3p8_update_10, k7t3p8_update_11, k7t3p8_update_12]

private theorem k7t3p8_part_0 : k7t3p8.chains.flatten = List.finRange _ := by decide

private theorem k7t3p8_part_1 : k7t3p8.chains.map List.length = ([[2, 2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t3p8_part_2 : k7t3p8.chains.map (fun l => l.map (fun i => decide (i ∈ k7t3p8.clique))) = ([[2, 2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t3p8_templates_item_0 : (⟨0, 1, [], [], [2, 3], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_2 : (⟨0, 2, [], [], [3], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5, 6], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_4 : (⟨0, 3, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_5 : (⟨0, 3, [], [], [4, 5, 6], 3, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_6 : (⟨0, 4, [], [], [3], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_7 : (⟨0, 4, [], [], [5, 6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_8 : (⟨0, 4, [], [3, 2, 1], [5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_9 : (⟨0, 5, [], [], [4, 3], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_10 : (⟨0, 5, [], [], [6], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_11 : (⟨0, 6, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_12 : (⟨0, 6, [], [3, 2, 1], [], 3, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_13 : (⟨1, 2, [], [0], [3], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_14 : (⟨1, 2, [], [0], [3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_15 : (⟨1, 3, [], [0], [4, 5, 6], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_16 : (⟨1, 4, [], [0], [3], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_17 : (⟨1, 4, [], [0], [5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_18 : (⟨1, 5, [], [0], [4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_19 : (⟨1, 5, [], [0], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_20 : (⟨1, 6, [], [0], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_21 : (⟨1, 6, [], [3, 2], [], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_22 : (⟨2, 3, [], [0, 1], [], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_23 : (⟨2, 3, [], [0, 1], [4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_24 : (⟨2, 4, [], [0, 1], [3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_25 : (⟨2, 5, [], [0, 1], [4, 3], 1, 2⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_26 : (⟨2, 5, [], [0, 1], [6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_27 : (⟨2, 5, [], [3], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_28 : (⟨2, 6, [], [0, 1], [], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_29 : (⟨2, 6, [], [3], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_30 : (⟨2, 6, [], [0, 1], [5, 4, 3], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_31 : (⟨3, 4, [], [], [5, 6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_32 : (⟨3, 4, [], [0, 1, 2], [5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_33 : (⟨3, 5, [], [0, 1, 2], [6], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_34 : (⟨3, 6, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_35 : (⟨3, 6, [], [0, 1, 2], [], 3, 3⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_36 : (⟨4, 5, [], [3], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_37 : (⟨4, 5, [], [0, 1, 2, 3], [6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_38 : (⟨4, 6, [], [3], [], 3, 5⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_39 : (⟨4, 6, [], [0, 1, 2, 3], [], 2, 2⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_40 : (⟨5, 6, [], [3, 4], [], 2, 4⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_item_41 : (⟨5, 6, [], [0, 1, 2, 3, 4], [], 1, 1⟩ : TemplateData (Fin 7)).Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t3p8_templates_block_0_check : ∀ T ∈ k7t3p8_templates_block_0, T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p8_templates_block_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p8_templates_item_0, k7t3p8_templates_item_1, k7t3p8_templates_item_2, k7t3p8_templates_item_3, k7t3p8_templates_item_4, k7t3p8_templates_item_5, k7t3p8_templates_item_6, k7t3p8_templates_item_7, k7t3p8_templates_item_8, k7t3p8_templates_item_9, k7t3p8_templates_item_10, k7t3p8_templates_item_11⟩

private theorem k7t3p8_templates_block_1_check : ∀ T ∈ k7t3p8_templates_block_1, T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p8_templates_block_1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p8_templates_item_12, k7t3p8_templates_item_13, k7t3p8_templates_item_14, k7t3p8_templates_item_15, k7t3p8_templates_item_16, k7t3p8_templates_item_17, k7t3p8_templates_item_18, k7t3p8_templates_item_19, k7t3p8_templates_item_20, k7t3p8_templates_item_21, k7t3p8_templates_item_22, k7t3p8_templates_item_23⟩

private theorem k7t3p8_templates_block_2_check : ∀ T ∈ k7t3p8_templates_block_2, T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p8_templates_block_2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p8_templates_item_24, k7t3p8_templates_item_25, k7t3p8_templates_item_26, k7t3p8_templates_item_27, k7t3p8_templates_item_28, k7t3p8_templates_item_29, k7t3p8_templates_item_30, k7t3p8_templates_item_31, k7t3p8_templates_item_32, k7t3p8_templates_item_33, k7t3p8_templates_item_34, k7t3p8_templates_item_35⟩

private theorem k7t3p8_templates_block_3_check : ∀ T ∈ k7t3p8_templates_block_3, T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t3p8_templates_block_3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p8_templates_item_36, k7t3p8_templates_item_37, k7t3p8_templates_item_38, k7t3p8_templates_item_39, k7t3p8_templates_item_40, k7t3p8_templates_item_41⟩

private theorem k7t3p8_part_3 : ∀ T ∈ k7t3p8.templates, T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum := by
  change ∀ T ∈ (k7t3p8_templates_block_0 ++ k7t3p8_templates_block_1 ++ k7t3p8_templates_block_2 ++ k7t3p8_templates_block_3), T.Check k7t3p8.graph k7t3p8.clique 7 (patternAmount ([[2, 2]] : List (List ℕ))) (([[2, 2]] : List (List ℕ)).map List.length).sum
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨k7t3p8_templates_block_0_check, k7t3p8_templates_block_1_check⟩, k7t3p8_templates_block_2_check⟩, k7t3p8_templates_block_3_check⟩

private theorem k7t3p8_required_item_0 : (⟨0, 6, [1, 2, 3, 4, 5]⟩ : RequiredPathData (Fin 7)).Check k7t3p8.graph 7 := by decide

private theorem k7t3p8_required_item_1 : (⟨1, 2, []⟩ : RequiredPathData (Fin 7)).Check k7t3p8.graph 7 := by decide

private theorem k7t3p8_required_item_2 : (⟨2, 4, [3]⟩ : RequiredPathData (Fin 7)).Check k7t3p8.graph 7 := by decide

private theorem k7t3p8_required_item_3 : (⟨4, 5, []⟩ : RequiredPathData (Fin 7)).Check k7t3p8.graph 7 := by decide

private theorem k7t3p8_part_4 : ∀ p ∈ k7t3p8.required, p.Check k7t3p8.graph 7 := by
  simp only [k7t3p8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t3p8_required_item_0, k7t3p8_required_item_1, k7t3p8_required_item_2, k7t3p8_required_item_3⟩

private theorem k7t3p8_part_5 : ClosureCheck k7t3p8.graph (k7t3p8.initialMatrix 7) 7 3 k7t3p8.closure := by
  rw [k7t3p8_initial_eq]
  exact k7t3p8_closure_0

private theorem k7t3p8_part_6 : k7t3p8.bad.Check k7t3p8.graph (k7t3p8.matrix 7) 7 3 := by
  rw [k7t3p8_matrix_eq]
  decide

theorem k7t3p8_check : k7t3p8.Check 7 3 [[2, 2]] :=
  ⟨k7t3p8_part_0, k7t3p8_part_1, k7t3p8_part_2, k7t3p8_part_3, k7t3p8_part_4, k7t3p8_part_5, k7t3p8_part_6⟩
def k7t4p0 : LayoutCertificate 4 where
  chains := [[0], [1], [2], [3]]
  clique := {0, 1, 2, 3}
  templates := [⟨0, 1, [], [], [], 1, 6⟩,
    ⟨0, 2, [], [], [], 1, 6⟩,
    ⟨0, 3, [], [], [], 1, 6⟩,
    ⟨1, 2, [], [], [], 1, 6⟩,
    ⟨1, 3, [], [], [], 1, 6⟩,
    ⟨2, 3, [], [], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 2), (1, 2), (2, 2)}⟩


private def k7t4p0_state_0 : ForbiddenMatrix 4 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p0_initial_eq_row_0 : ∀ j : Fin 4, (k7t4p0.initialMatrix 7) 0 j = k7t4p0_state_0 0 j := by decide

private theorem k7t4p0_initial_eq_row_1 : ∀ j : Fin 4, (k7t4p0.initialMatrix 7) 1 j = k7t4p0_state_0 1 j := by decide

private theorem k7t4p0_initial_eq_row_2 : ∀ j : Fin 4, (k7t4p0.initialMatrix 7) 2 j = k7t4p0_state_0 2 j := by decide

private theorem k7t4p0_initial_eq_row_3 : ∀ j : Fin 4, (k7t4p0.initialMatrix 7) 3 j = k7t4p0_state_0 3 j := by decide

private theorem k7t4p0_initial_eq : (k7t4p0.initialMatrix 7) = k7t4p0_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p0_initial_eq_row_0 j

  · exact k7t4p0_initial_eq_row_1 j

  · exact k7t4p0_initial_eq_row_2 j

  · exact k7t4p0_initial_eq_row_3 j

private theorem k7t4p0_closure_0 : ClosureCheck k7t4p0.graph k7t4p0_state_0 7 4 [] := by trivial

private theorem k7t4p0_matrix_eq : k7t4p0.matrix 7 = k7t4p0_state_0 := by
  change closureMatrix (k7t4p0.initialMatrix 7) _ = _
  rw [k7t4p0_initial_eq]
  change closureMatrix k7t4p0_state_0 [] = _
  rfl

private theorem k7t4p0_part_0 : k7t4p0.chains.flatten = List.finRange _ := by decide

private theorem k7t4p0_part_1 : k7t4p0.chains.map List.length = ([[], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p0_part_2 : k7t4p0.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p0.clique))) = ([[], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_templates_item_3 : (⟨1, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_templates_item_4 : (⟨1, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_templates_item_5 : (⟨2, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 4)).Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p0_part_3 : ∀ T ∈ k7t4p0.templates, T.Check k7t4p0.graph k7t4p0.clique 7 (patternAmount ([[], [], [], []] : List (List ℕ))) (([[], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p0_templates_item_0, k7t4p0_templates_item_1, k7t4p0_templates_item_2, k7t4p0_templates_item_3, k7t4p0_templates_item_4, k7t4p0_templates_item_5⟩

private theorem k7t4p0_part_4 : ∀ p ∈ k7t4p0.required, p.Check k7t4p0.graph 7 := by decide

private theorem k7t4p0_part_5 : ClosureCheck k7t4p0.graph (k7t4p0.initialMatrix 7) 7 4 k7t4p0.closure := by
  rw [k7t4p0_initial_eq]
  exact k7t4p0_closure_0

private theorem k7t4p0_part_6 : k7t4p0.bad.Check k7t4p0.graph (k7t4p0.matrix 7) 7 4 := by
  rw [k7t4p0_matrix_eq]
  decide

theorem k7t4p0_check : k7t4p0.Check 7 4 [[], [], [], []] :=
  ⟨k7t4p0_part_0, k7t4p0_part_1, k7t4p0_part_2, k7t4p0_part_3, k7t4p0_part_4, k7t4p0_part_5, k7t4p0_part_6⟩
def k7t4p1 : LayoutCertificate 5 where
  chains := [[0], [1], [2, 3, 4]]
  clique := {0, 1, 2, 4}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [[2, 3, 4]], [], [], 1, 3⟩,
    ⟨0, 2, [], [], [], 2, 6⟩,
    ⟨0, 2, [], [], [3, 4], 1, 4⟩,
    ⟨0, 3, [], [], [2], 1, 5⟩,
    ⟨0, 4, [], [], [], 2, 6⟩,
    ⟨0, 4, [], [], [3, 2], 1, 4⟩,
    ⟨1, 2, [], [], [], 2, 6⟩,
    ⟨1, 2, [], [], [3, 4], 1, 4⟩,
    ⟨1, 3, [], [], [2], 1, 5⟩,
    ⟨1, 4, [], [], [], 2, 6⟩,
    ⟨1, 4, [], [], [3, 2], 1, 4⟩,
    ⟨2, 3, [], [], [4], 1, 5⟩,
    ⟨3, 4, [], [2], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (3, 2)}⟩


private def k7t4p1_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p1_initial_eq_row_0 : ∀ j : Fin 5, (k7t4p1.initialMatrix 7) 0 j = k7t4p1_state_0 0 j := by decide

private theorem k7t4p1_initial_eq_row_1 : ∀ j : Fin 5, (k7t4p1.initialMatrix 7) 1 j = k7t4p1_state_0 1 j := by decide

private theorem k7t4p1_initial_eq_row_2 : ∀ j : Fin 5, (k7t4p1.initialMatrix 7) 2 j = k7t4p1_state_0 2 j := by decide

private theorem k7t4p1_initial_eq_row_3 : ∀ j : Fin 5, (k7t4p1.initialMatrix 7) 3 j = k7t4p1_state_0 3 j := by decide

private theorem k7t4p1_initial_eq_row_4 : ∀ j : Fin 5, (k7t4p1.initialMatrix 7) 4 j = k7t4p1_state_0 4 j := by decide

private theorem k7t4p1_initial_eq : (k7t4p1.initialMatrix 7) = k7t4p1_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p1_initial_eq_row_0 j

  · exact k7t4p1_initial_eq_row_1 j

  · exact k7t4p1_initial_eq_row_2 j

  · exact k7t4p1_initial_eq_row_3 j

  · exact k7t4p1_initial_eq_row_4 j

private theorem k7t4p1_closure_0 : ClosureCheck k7t4p1.graph k7t4p1_state_0 7 4 [] := by trivial

private theorem k7t4p1_matrix_eq : k7t4p1.matrix 7 = k7t4p1_state_0 := by
  change closureMatrix (k7t4p1.initialMatrix 7) _ = _
  rw [k7t4p1_initial_eq]
  change closureMatrix k7t4p1_state_0 [] = _
  rfl

private theorem k7t4p1_part_0 : k7t4p1.chains.flatten = List.finRange _ := by decide

private theorem k7t4p1_part_1 : k7t4p1.chains.map List.length = ([[], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p1_part_2 : k7t4p1.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p1.clique))) = ([[], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_1 : (⟨0, 1, [[2, 3, 4]], [], [], 1, 3⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_3 : (⟨0, 2, [], [], [3, 4], 1, 4⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_4 : (⟨0, 3, [], [], [2], 1, 5⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_5 : (⟨0, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_6 : (⟨0, 4, [], [], [3, 2], 1, 4⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_7 : (⟨1, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_8 : (⟨1, 2, [], [], [3, 4], 1, 4⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_9 : (⟨1, 3, [], [], [2], 1, 5⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_10 : (⟨1, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_11 : (⟨1, 4, [], [], [3, 2], 1, 4⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_12 : (⟨2, 3, [], [], [4], 1, 5⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_templates_item_13 : (⟨3, 4, [], [2], [], 1, 5⟩ : TemplateData (Fin 5)).Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p1_part_3 : ∀ T ∈ k7t4p1.templates, T.Check k7t4p1.graph k7t4p1.clique 7 (patternAmount ([[], [], [1]] : List (List ℕ))) (([[], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p1_templates_item_0, k7t4p1_templates_item_1, k7t4p1_templates_item_2, k7t4p1_templates_item_3, k7t4p1_templates_item_4, k7t4p1_templates_item_5, k7t4p1_templates_item_6, k7t4p1_templates_item_7, k7t4p1_templates_item_8, k7t4p1_templates_item_9, k7t4p1_templates_item_10, k7t4p1_templates_item_11, k7t4p1_templates_item_12, k7t4p1_templates_item_13⟩

private theorem k7t4p1_part_4 : ∀ p ∈ k7t4p1.required, p.Check k7t4p1.graph 7 := by decide

private theorem k7t4p1_part_5 : ClosureCheck k7t4p1.graph (k7t4p1.initialMatrix 7) 7 4 k7t4p1.closure := by
  rw [k7t4p1_initial_eq]
  exact k7t4p1_closure_0

private theorem k7t4p1_part_6 : k7t4p1.bad.Check k7t4p1.graph (k7t4p1.matrix 7) 7 4 := by
  rw [k7t4p1_matrix_eq]
  decide

theorem k7t4p1_check : k7t4p1.Check 7 4 [[], [], [1]] :=
  ⟨k7t4p1_part_0, k7t4p1_part_1, k7t4p1_part_2, k7t4p1_part_3, k7t4p1_part_4, k7t4p1_part_5, k7t4p1_part_6⟩
def k7t4p2 : LayoutCertificate 6 where
  chains := [[0], [1], [2, 3, 4, 5]]
  clique := {0, 1, 2, 5}
  templates := [⟨0, 1, [], [], [], 3, 6⟩,
    ⟨0, 1, [[2, 3, 4, 5]], [], [], 1, 2⟩,
    ⟨0, 2, [], [], [], 3, 6⟩,
    ⟨0, 2, [], [], [3, 4, 5], 1, 3⟩,
    ⟨0, 3, [], [], [2], 2, 5⟩,
    ⟨0, 3, [], [], [4, 5], 1, 4⟩,
    ⟨0, 4, [], [], [3, 2], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3, 2], 1, 3⟩,
    ⟨1, 2, [], [], [], 3, 6⟩,
    ⟨1, 2, [], [], [3, 4, 5], 1, 3⟩,
    ⟨1, 3, [], [], [2], 2, 5⟩,
    ⟨1, 3, [], [], [4, 5], 1, 4⟩,
    ⟨1, 4, [], [], [3, 2], 1, 4⟩,
    ⟨1, 5, [], [], [4, 3, 2], 1, 3⟩,
    ⟨2, 3, [], [], [4, 5], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t4p2_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2, 3}, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p2_initial_eq_row_0 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 0 j = k7t4p2_state_0 0 j := by decide

private theorem k7t4p2_initial_eq_row_1 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 1 j = k7t4p2_state_0 1 j := by decide

private theorem k7t4p2_initial_eq_row_2 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 2 j = k7t4p2_state_0 2 j := by decide

private theorem k7t4p2_initial_eq_row_3 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 3 j = k7t4p2_state_0 3 j := by decide

private theorem k7t4p2_initial_eq_row_4 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 4 j = k7t4p2_state_0 4 j := by decide

private theorem k7t4p2_initial_eq_row_5 : ∀ j : Fin 6, (k7t4p2.initialMatrix 7) 5 j = k7t4p2_state_0 5 j := by decide

private theorem k7t4p2_initial_eq : (k7t4p2.initialMatrix 7) = k7t4p2_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p2_initial_eq_row_0 j

  · exact k7t4p2_initial_eq_row_1 j

  · exact k7t4p2_initial_eq_row_2 j

  · exact k7t4p2_initial_eq_row_3 j

  · exact k7t4p2_initial_eq_row_4 j

  · exact k7t4p2_initial_eq_row_5 j

private theorem k7t4p2_closure_0 : ClosureCheck k7t4p2.graph k7t4p2_state_0 7 4 [] := by trivial

private theorem k7t4p2_matrix_eq : k7t4p2.matrix 7 = k7t4p2_state_0 := by
  change closureMatrix (k7t4p2.initialMatrix 7) _ = _
  rw [k7t4p2_initial_eq]
  change closureMatrix k7t4p2_state_0 [] = _
  rfl

private theorem k7t4p2_part_0 : k7t4p2.chains.flatten = List.finRange _ := by decide

private theorem k7t4p2_part_1 : k7t4p2.chains.map List.length = ([[], [], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p2_part_2 : k7t4p2.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p2.clique))) = ([[], [], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p2_templates_item_0 : (⟨0, 1, [], [], [], 3, 6⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_1 : (⟨0, 1, [[2, 3, 4, 5]], [], [], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_2 : (⟨0, 2, [], [], [], 3, 6⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_4 : (⟨0, 3, [], [], [2], 2, 5⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_5 : (⟨0, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_6 : (⟨0, 4, [], [], [3, 2], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_7 : (⟨0, 5, [], [], [4, 3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_8 : (⟨1, 2, [], [], [], 3, 6⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_9 : (⟨1, 2, [], [], [3, 4, 5], 1, 3⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_10 : (⟨1, 3, [], [], [2], 2, 5⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_11 : (⟨1, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_12 : (⟨1, 4, [], [], [3, 2], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_13 : (⟨1, 5, [], [], [4, 3, 2], 1, 3⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_templates_item_14 : (⟨2, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p2_part_3 : ∀ T ∈ k7t4p2.templates, T.Check k7t4p2.graph k7t4p2.clique 7 (patternAmount ([[], [], [2]] : List (List ℕ))) (([[], [], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p2_templates_item_0, k7t4p2_templates_item_1, k7t4p2_templates_item_2, k7t4p2_templates_item_3, k7t4p2_templates_item_4, k7t4p2_templates_item_5, k7t4p2_templates_item_6, k7t4p2_templates_item_7, k7t4p2_templates_item_8, k7t4p2_templates_item_9, k7t4p2_templates_item_10, k7t4p2_templates_item_11, k7t4p2_templates_item_12, k7t4p2_templates_item_13, k7t4p2_templates_item_14⟩

private theorem k7t4p2_part_4 : ∀ p ∈ k7t4p2.required, p.Check k7t4p2.graph 7 := by decide

private theorem k7t4p2_part_5 : ClosureCheck k7t4p2.graph (k7t4p2.initialMatrix 7) 7 4 k7t4p2.closure := by
  rw [k7t4p2_initial_eq]
  exact k7t4p2_closure_0

private theorem k7t4p2_part_6 : k7t4p2.bad.Check k7t4p2.graph (k7t4p2.matrix 7) 7 4 := by
  rw [k7t4p2_matrix_eq]
  decide

theorem k7t4p2_check : k7t4p2.Check 7 4 [[], [], [2]] :=
  ⟨k7t4p2_part_0, k7t4p2_part_1, k7t4p2_part_2, k7t4p2_part_3, k7t4p2_part_4, k7t4p2_part_5, k7t4p2_part_6⟩
private def k7t4p3_step_0_data : EdgeAttachmentData 7 := ⟨3, 0, [⟨0, 6, [3, 2, 1]⟩, ⟨0, 4, [3, 2, 1, 6, 5]⟩, ⟨0, 1, [3, 4, 5, 6]⟩, ⟨1, 6, [0, 3, 2]⟩, ⟨1, 4, [0, 3, 2, 6, 5]⟩, ⟨1, 0, [6, 2, 3]⟩, ⟨1, 0, [6, 5, 4, 3]⟩, ⟨6, 2, [5, 4, 3, 0, 1]⟩, ⟨6, 2, [5, 4, 3, 0]⟩], ⟨none, {(1, 3), (0, 3), (6, 3)}⟩⟩

private def k7t4p3_step_0 : ClosureStep 7 := .edge k7t4p3_step_0_data

private def k7t4p3_step_1_data : EdgeAttachmentData 7 := ⟨3, 1, [⟨0, 6, [1, 3, 2]⟩, ⟨0, 4, [1, 3, 2, 6, 5]⟩, ⟨0, 1, [6, 2, 3]⟩, ⟨0, 1, [6, 5, 4, 3]⟩, ⟨1, 6, [3, 2, 0]⟩, ⟨1, 4, [3, 2, 0, 6, 5]⟩, ⟨1, 0, [3, 4, 5, 6]⟩, ⟨6, 2, [5, 4, 3, 1, 0]⟩, ⟨6, 2, [5, 4, 3, 1]⟩], ⟨none, {(0, 3), (1, 3), (6, 3)}⟩⟩

private def k7t4p3_step_1 : ClosureStep 7 := .edge k7t4p3_step_1_data

private def k7t4p3_step_2_data : EdgeAttachmentData 7 := ⟨4, 0, [⟨0, 1, [4, 3, 2]⟩, ⟨0, 1, [4, 3, 2, 6]⟩, ⟨1, 0, [2, 6, 5, 4]⟩, ⟨3, 6, [2, 1, 0, 4, 5]⟩, ⟨3, 5, [2, 1, 6, 0, 4]⟩], ⟨none, {(0, 3), (1, 3), (3, 2)}⟩⟩

private def k7t4p3_step_2 : ClosureStep 7 := .edge k7t4p3_step_2_data

private def k7t4p3_step_3_required_block_0 : List (RequiredPathData (Fin 8)) := [⟨4, 0, [3, 1, 2, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 0, [3, 1]⟩, ⟨4, 7, [3, 1, 0, 5, 6]⟩, ⟨4, 2, [3, 1, 0, 5, 6, 7]⟩, ⟨4, 0, [3, 2, 1]⟩, ⟨4, 6, [3, 2, 1, 0, 5]⟩, ⟨4, 7, [3, 2, 1, 0, 5, 6]⟩, ⟨4, 0, [3, 2, 7, 1]⟩, ⟨4, 6, [3, 2, 7, 1, 0, 5]⟩, ⟨4, 1, [3, 2, 7, 6, 5, 0]⟩, ⟨6, 0, [5, 4, 3, 1]⟩]

private def k7t4p3_step_3_required_block_1 : List (RequiredPathData (Fin 8)) := [⟨6, 0, [5, 4, 3, 2, 1]⟩, ⟨6, 0, [5, 4, 3, 2, 7, 1]⟩, ⟨6, 4, [5, 0, 1, 2, 3]⟩, ⟨6, 3, [5, 0, 1, 2, 7]⟩, ⟨6, 4, [5, 0, 1, 2, 7, 3]⟩, ⟨6, 0, [7, 1]⟩, ⟨6, 2, [7, 1, 0, 5, 4, 3]⟩, ⟨6, 0, [7, 2, 1]⟩, ⟨6, 3, [7, 2, 1, 0, 5, 4]⟩, ⟨6, 1, [7, 2, 3, 4, 5, 0]⟩, ⟨0, 6, [1, 2, 3, 4, 5]⟩, ⟨0, 7, [1, 2, 3, 4, 5, 6]⟩]

private def k7t4p3_step_3_required_block_2 : List (RequiredPathData (Fin 8)) := [⟨0, 5, [1, 2, 3, 7, 6]⟩, ⟨0, 4, [1, 2, 3, 7, 6, 5]⟩, ⟨0, 6, [1, 2, 7, 3, 4, 5]⟩, ⟨0, 4, [1, 2, 7, 6, 5]⟩, ⟨0, 3, [1, 2, 7, 6, 5, 4]⟩, ⟨0, 7, [1, 3, 4, 5, 6]⟩, ⟨0, 2, [1, 3, 4, 5, 6, 7]⟩, ⟨0, 3, [1, 7, 6, 5, 4]⟩, ⟨0, 2, [5, 4, 3, 1, 7]⟩, ⟨0, 1, [5, 4, 3, 2, 7]⟩]

private def k7t4p3_step_3_data : FreshAttachmentData 7 := ⟨4, 0, k7t4p3_step_3_required_block_0 ++ k7t4p3_step_3_required_block_1 ++ k7t4p3_step_3_required_block_2, ⟨none, {(4, 2), (6, 2), (0, 2)}⟩⟩

private def k7t4p3_step_3 : ClosureStep 7 := .fresh k7t4p3_step_3_data

private def k7t4p3_step_4_data : EdgeAttachmentData 7 := ⟨4, 1, [⟨0, 1, [2, 3, 4]⟩, ⟨0, 1, [2, 6, 5, 4]⟩, ⟨1, 0, [4, 3, 2, 6]⟩, ⟨3, 6, [2, 0, 1, 4, 5]⟩, ⟨3, 5, [2, 0, 6, 1, 4]⟩], ⟨none, {(0, 3), (1, 3), (3, 2)}⟩⟩

private def k7t4p3_step_4 : ClosureStep 7 := .edge k7t4p3_step_4_data

private def k7t4p3_step_5_required_block_0 : List (RequiredPathData (Fin 8)) := [⟨4, 0, [3, 1, 2, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 2]⟩, ⟨4, 6, [3, 1, 2, 0, 5]⟩, ⟨4, 7, [3, 1, 2, 0, 5, 6]⟩, ⟨4, 0, [3, 1, 7, 2]⟩, ⟨4, 6, [3, 1, 7, 2, 0, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 2, [3, 1, 7, 6, 5, 0]⟩, ⟨4, 0, [3, 2]⟩, ⟨4, 7, [3, 2, 0, 5, 6]⟩, ⟨4, 1, [3, 2, 0, 5, 6, 7]⟩, ⟨6, 0, [5, 4, 3, 1, 2]⟩]

private def k7t4p3_step_5_required_block_1 : List (RequiredPathData (Fin 8)) := [⟨6, 0, [5, 4, 3, 1, 7, 2]⟩, ⟨6, 0, [5, 4, 3, 2]⟩, ⟨6, 4, [5, 0, 2, 1, 3]⟩, ⟨6, 3, [5, 0, 2, 1, 7]⟩, ⟨6, 4, [5, 0, 2, 1, 7, 3]⟩, ⟨6, 0, [7, 1, 2]⟩, ⟨6, 3, [7, 1, 2, 0, 5, 4]⟩, ⟨6, 2, [7, 1, 3, 4, 5, 0]⟩, ⟨6, 0, [7, 2]⟩, ⟨6, 1, [7, 2, 0, 5, 4, 3]⟩, ⟨0, 6, [2, 1, 3, 4, 5]⟩, ⟨0, 7, [2, 1, 3, 4, 5, 6]⟩]

private def k7t4p3_step_5_required_block_2 : List (RequiredPathData (Fin 8)) := [⟨0, 5, [2, 1, 3, 7, 6]⟩, ⟨0, 4, [2, 1, 3, 7, 6, 5]⟩, ⟨0, 6, [2, 1, 7, 3, 4, 5]⟩, ⟨0, 4, [2, 1, 7, 6, 5]⟩, ⟨0, 3, [2, 1, 7, 6, 5, 4]⟩, ⟨0, 7, [2, 3, 4, 5, 6]⟩, ⟨0, 1, [2, 3, 4, 5, 6, 7]⟩, ⟨0, 3, [2, 7, 6, 5, 4]⟩, ⟨0, 2, [5, 4, 3, 1, 7]⟩, ⟨0, 1, [5, 4, 3, 2, 7]⟩]

private def k7t4p3_step_5_data : FreshAttachmentData 7 := ⟨4, 1, k7t4p3_step_5_required_block_0 ++ k7t4p3_step_5_required_block_1 ++ k7t4p3_step_5_required_block_2, ⟨none, {(4, 2), (6, 2), (0, 2)}⟩⟩

private def k7t4p3_step_5 : ClosureStep 7 := .fresh k7t4p3_step_5_data

private def k7t4p3_step_6_data : EdgeAttachmentData 7 := ⟨4, 2, [⟨0, 1, [2, 4, 5, 6]⟩, ⟨3, 5, [4, 2, 0, 1, 6]⟩, ⟨5, 3, [6, 0, 1, 2, 4]⟩], ⟨none, {(3, 2), (5, 3), (0, 2), (1, 0)}⟩⟩

private def k7t4p3_step_6 : ClosureStep 7 := .edge k7t4p3_step_6_data

private def k7t4p3_step_7_data : FreshAttachmentData 7 := ⟨4, 2, [⟨1, 0, [2, 3, 7, 6, 5]⟩, ⟨1, 0, [2, 7, 6, 5, 4, 3]⟩, ⟨1, 4, [2, 7, 6, 5, 0, 3]⟩, ⟨4, 0, [3, 1, 2, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 2, [3, 0, 5, 6, 7, 1]⟩, ⟨4, 1, [3, 0, 5, 6, 7, 2]⟩, ⟨4, 7, [5, 0, 3, 1, 2]⟩, ⟨4, 6, [5, 0, 3, 1, 2, 7]⟩, ⟨4, 6, [5, 0, 3, 1, 7]⟩, ⟨6, 0, [7, 1, 2, 3, 4, 5]⟩, ⟨6, 0, [7, 1, 2, 3]⟩, ⟨6, 4, [7, 1, 2, 3, 0, 5]⟩, ⟨6, 0, [7, 1, 3, 4, 5]⟩, ⟨6, 4, [7, 1, 3, 0, 5]⟩], ⟨none, {(4, 2), (6, 3), (1, 2)}⟩⟩

private def k7t4p3_step_7 : ClosureStep 7 := .fresh k7t4p3_step_7_data

private def k7t4p3_step_8_data : EdgeAttachmentData 7 := ⟨5, 0, [⟨0, 2, [5, 4, 3]⟩, ⟨0, 1, [5, 4, 3, 2]⟩, ⟨0, 4, [5, 6, 1, 2, 3]⟩, ⟨1, 2, [0, 5, 6]⟩, ⟨1, 4, [0, 5, 6, 2, 3]⟩, ⟨1, 0, [2, 3, 4, 5]⟩, ⟨1, 0, [2, 6, 5]⟩, ⟨2, 6, [3, 4, 5, 0, 1]⟩, ⟨2, 6, [3, 4, 5, 0]⟩], ⟨none, {(1, 3), (0, 3), (2, 3)}⟩⟩

private def k7t4p3_step_8 : ClosureStep 7 := .edge k7t4p3_step_8_data

private def k7t4p3_step_9_data : EdgeAttachmentData 7 := ⟨5, 3, [⟨0, 4, [1, 2, 6, 5, 3]⟩, ⟨0, 1, [2, 3, 5, 6]⟩, ⟨0, 2, [6, 5, 3]⟩, ⟨2, 4, [0, 1, 6, 5, 3]⟩, ⟨2, 3, [6, 5]⟩], ⟨none, {(0, 3), (2, 3), (4, 0), (3, 1)}⟩⟩

private def k7t4p3_step_9 : ClosureStep 7 := .edge k7t4p3_step_9_data

private def k7t4p3_step_10_data : EdgeAttachmentData 7 := ⟨6, 3, [⟨0, 4, [1, 2, 3, 6, 5]⟩, ⟨2, 5, [0, 1, 6, 3, 4]⟩, ⟨2, 5, [0, 6, 3, 4]⟩, ⟨2, 0, [3, 6, 1]⟩, ⟨5, 2, [4, 3, 6, 0, 1]⟩], ⟨none, {(2, 3), (0, 3), (5, 2)}⟩⟩

private def k7t4p3_step_10 : ClosureStep 7 := .edge k7t4p3_step_10_data

private def k7t4p3_step_11_data : EdgeAttachmentData 7 := ⟨6, 4, [⟨0, 1, [2, 3, 4, 6]⟩, ⟨3, 5, [2, 0, 1, 6, 4]⟩, ⟨5, 3, [4, 6, 0, 1, 2]⟩], ⟨none, {(3, 2), (0, 2), (5, 3), (1, 0)}⟩⟩

private def k7t4p3_step_11 : ClosureStep 7 := .edge k7t4p3_step_11_data

private def k7t4p3_step_12_data : FreshAttachmentData 7 := ⟨6, 4, [⟨1, 0, [2, 3, 4, 5, 6, 7]⟩, ⟨1, 6, [2, 3, 4, 5, 0, 7]⟩, ⟨1, 0, [2, 3, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 2, 7, 6, 5]⟩, ⟨4, 0, [3, 1, 2, 7]⟩, ⟨4, 6, [3, 1, 2, 7, 0, 5]⟩, ⟨4, 0, [3, 1, 7, 6, 5]⟩, ⟨4, 6, [3, 1, 7, 0, 5]⟩, ⟨6, 0, [5, 4, 3, 1, 2, 7]⟩, ⟨6, 0, [5, 4, 3, 1, 7]⟩, ⟨6, 3, [5, 0, 7, 1, 2]⟩, ⟨6, 4, [5, 0, 7, 1, 2, 3]⟩, ⟨6, 4, [5, 0, 7, 1, 3]⟩, ⟨6, 2, [7, 0, 5, 4, 3, 1]⟩, ⟨6, 1, [7, 0, 5, 4, 3, 2]⟩], ⟨none, {(6, 2), (4, 3), (1, 2)}⟩⟩

private def k7t4p3_step_12 : ClosureStep 7 := .fresh k7t4p3_step_12_data

def k7t4p3 : LayoutCertificate 7 where
  chains := [[0], [1], [2, 3, 4, 5, 6]]
  clique := {0, 1, 2, 6}
  templates := [⟨0, 1, [], [], [], 4, 6⟩,
    ⟨0, 1, [[2, 3, 4, 5, 6]], [], [], 1, 1⟩,
    ⟨0, 2, [], [], [], 4, 6⟩,
    ⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨0, 3, [], [], [2], 3, 5⟩,
    ⟨0, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨0, 4, [], [], [3, 2], 2, 4⟩,
    ⟨0, 5, [], [], [4, 3, 2], 1, 3⟩,
    ⟨0, 5, [], [], [6], 3, 5⟩,
    ⟨0, 6, [], [], [], 4, 6⟩,
    ⟨0, 6, [], [], [5, 4, 3, 2], 1, 2⟩,
    ⟨1, 2, [], [], [], 4, 6⟩,
    ⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨1, 3, [], [], [2], 3, 5⟩,
    ⟨1, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨1, 4, [], [], [3, 2], 2, 4⟩,
    ⟨1, 5, [], [], [4, 3, 2], 1, 3⟩,
    ⟨1, 6, [], [], [], 4, 6⟩,
    ⟨1, 6, [], [], [5, 4, 3, 2], 1, 2⟩,
    ⟨2, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨2, 4, [], [], [5, 6], 2, 4⟩,
    ⟨2, 5, [], [], [6], 3, 5⟩,
    ⟨3, 4, [], [2], [5, 6], 1, 3⟩,
    ⟨3, 5, [], [2], [6], 2, 4⟩,
    ⟨4, 5, [], [2, 3], [6], 1, 3⟩,
    ⟨5, 6, [], [2, 3, 4], [], 1, 3⟩]
  required := [⟨3, 5, [4]⟩]
  closure := [k7t4p3_step_0, k7t4p3_step_1, k7t4p3_step_2, k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12]
  bad := ⟨none, {(4, 2), (0, 2), (3, 1)}⟩


private def k7t4p3_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 1 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[{2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_initial_eq_row_0 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 0 j = k7t4p3_state_0 0 j := by decide

private theorem k7t4p3_initial_eq_row_1 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 1 j = k7t4p3_state_0 1 j := by decide

private theorem k7t4p3_initial_eq_row_2 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 2 j = k7t4p3_state_0 2 j := by decide

private theorem k7t4p3_initial_eq_row_3 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 3 j = k7t4p3_state_0 3 j := by decide

private theorem k7t4p3_initial_eq_row_4 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 4 j = k7t4p3_state_0 4 j := by decide

private theorem k7t4p3_initial_eq_row_5 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 5 j = k7t4p3_state_0 5 j := by decide

private theorem k7t4p3_initial_eq_row_6 : ∀ j : Fin 7, (k7t4p3.initialMatrix 7) 6 j = k7t4p3_state_0 6 j := by decide

private theorem k7t4p3_initial_eq : (k7t4p3.initialMatrix 7) = k7t4p3_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p3_initial_eq_row_0 j

  · exact k7t4p3_initial_eq_row_1 j

  · exact k7t4p3_initial_eq_row_2 j

  · exact k7t4p3_initial_eq_row_3 j

  · exact k7t4p3_initial_eq_row_4 j

  · exact k7t4p3_initial_eq_row_5 j

  · exact k7t4p3_initial_eq_row_6 j

private def k7t4p3_state_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[{2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 6],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, {1, 2}],
    #[Finset.Icc 1 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 6, {1, 2}, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_0_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 0 j = k7t4p3_local_0 0 j := by decide

private theorem k7t4p3_local_0_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 1 j = k7t4p3_local_0 1 j := by decide

private theorem k7t4p3_local_0_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 2 j = k7t4p3_local_0 2 j := by decide

private theorem k7t4p3_local_0_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 3 j = k7t4p3_local_0 3 j := by decide

private theorem k7t4p3_local_0_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 4 j = k7t4p3_local_0 4 j := by decide

private theorem k7t4p3_local_0_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 5 j = k7t4p3_local_0 5 j := by decide

private theorem k7t4p3_local_0_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) 6 j = k7t4p3_local_0 6 j := by decide

private theorem k7t4p3_local_0_eq : (fun a b => k7t4p3_state_0 a b ∪ requiredMatrix 7 k7t4p3_step_0_data.required a b) = k7t4p3_local_0 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_0_eq_row_0 j

  · exact k7t4p3_local_0_eq_row_1 j

  · exact k7t4p3_local_0_eq_row_2 j

  · exact k7t4p3_local_0_eq_row_3 j

  · exact k7t4p3_local_0_eq_row_4 j

  · exact k7t4p3_local_0_eq_row_5 j

  · exact k7t4p3_local_0_eq_row_6 j

private theorem k7t4p3_local_0_paths : ∀ p ∈ k7t4p3_step_0_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_0_data.i k7t4p3_step_0_data.j) 7 := by decide

private theorem k7t4p3_local_0_bad : k7t4p3_step_0_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_0_data.i k7t4p3_step_0_data.j) k7t4p3_local_0 7 4 := by decide

private theorem k7t4p3_step_0_check : k7t4p3_step_0.Check k7t4p3.graph k7t4p3_state_0 7 4 := by
  change k7t4p3_step_0_data.Check k7t4p3.graph k7t4p3_state_0 7 4
  refine ⟨k7t4p3_local_0_paths, ?_⟩
  rw [k7t4p3_local_0_eq]
  exact k7t4p3_local_0_bad

private theorem k7t4p3_update_0 : k7t4p3_step_0.apply k7t4p3_state_0 = k7t4p3_state_1 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_0.apply k7t4p3_state_0 i j = k7t4p3_state_1 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[{2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_1 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 1 4, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, {1, 2, 4, 5, 6}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 6],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, {1, 2}],
    #[Finset.Icc 0 5, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 6, {1, 2}, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_1_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 0 j = k7t4p3_local_1 0 j := by decide

private theorem k7t4p3_local_1_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 1 j = k7t4p3_local_1 1 j := by decide

private theorem k7t4p3_local_1_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 2 j = k7t4p3_local_1 2 j := by decide

private theorem k7t4p3_local_1_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 3 j = k7t4p3_local_1 3 j := by decide

private theorem k7t4p3_local_1_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 4 j = k7t4p3_local_1 4 j := by decide

private theorem k7t4p3_local_1_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 5 j = k7t4p3_local_1 5 j := by decide

private theorem k7t4p3_local_1_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) 6 j = k7t4p3_local_1 6 j := by decide

private theorem k7t4p3_local_1_eq : (fun a b => k7t4p3_state_1 a b ∪ requiredMatrix 7 k7t4p3_step_1_data.required a b) = k7t4p3_local_1 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_1_eq_row_0 j

  · exact k7t4p3_local_1_eq_row_1 j

  · exact k7t4p3_local_1_eq_row_2 j

  · exact k7t4p3_local_1_eq_row_3 j

  · exact k7t4p3_local_1_eq_row_4 j

  · exact k7t4p3_local_1_eq_row_5 j

  · exact k7t4p3_local_1_eq_row_6 j

private theorem k7t4p3_local_1_paths : ∀ p ∈ k7t4p3_step_1_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_1_data.i k7t4p3_step_1_data.j) 7 := by decide

private theorem k7t4p3_local_1_bad : k7t4p3_step_1_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_1_data.i k7t4p3_step_1_data.j) k7t4p3_local_1 7 4 := by decide

private theorem k7t4p3_step_1_check : k7t4p3_step_1.Check k7t4p3.graph k7t4p3_state_1 7 4 := by
  change k7t4p3_step_1_data.Check k7t4p3.graph k7t4p3_state_1 7 4
  refine ⟨k7t4p3_local_1_paths, ?_⟩
  rw [k7t4p3_local_1_eq]
  exact k7t4p3_local_1_bad

private theorem k7t4p3_update_1 : k7t4p3_step_1.apply k7t4p3_state_1 = k7t4p3_state_2 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_1.apply k7t4p3_state_1 i j = k7t4p3_state_2 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_3 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {0, 2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[{0, 2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_2 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1}],
    #[{2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_2_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 0 j = k7t4p3_local_2 0 j := by decide

private theorem k7t4p3_local_2_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 1 j = k7t4p3_local_2 1 j := by decide

private theorem k7t4p3_local_2_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 2 j = k7t4p3_local_2 2 j := by decide

private theorem k7t4p3_local_2_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 3 j = k7t4p3_local_2 3 j := by decide

private theorem k7t4p3_local_2_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 4 j = k7t4p3_local_2 4 j := by decide

private theorem k7t4p3_local_2_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 5 j = k7t4p3_local_2 5 j := by decide

private theorem k7t4p3_local_2_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) 6 j = k7t4p3_local_2 6 j := by decide

private theorem k7t4p3_local_2_eq : (fun a b => k7t4p3_state_2 a b ∪ requiredMatrix 7 k7t4p3_step_2_data.required a b) = k7t4p3_local_2 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_2_eq_row_0 j

  · exact k7t4p3_local_2_eq_row_1 j

  · exact k7t4p3_local_2_eq_row_2 j

  · exact k7t4p3_local_2_eq_row_3 j

  · exact k7t4p3_local_2_eq_row_4 j

  · exact k7t4p3_local_2_eq_row_5 j

  · exact k7t4p3_local_2_eq_row_6 j

private theorem k7t4p3_local_2_paths : ∀ p ∈ k7t4p3_step_2_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_2_data.i k7t4p3_step_2_data.j) 7 := by decide

private theorem k7t4p3_local_2_bad : k7t4p3_step_2_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_2_data.i k7t4p3_step_2_data.j) k7t4p3_local_2 7 4 := by decide

private theorem k7t4p3_step_2_check : k7t4p3_step_2.Check k7t4p3.graph k7t4p3_state_2 7 4 := by
  change k7t4p3_step_2_data.Check k7t4p3.graph k7t4p3_state_2 7 4
  refine ⟨k7t4p3_local_2_paths, ?_⟩
  rw [k7t4p3_local_2_eq]
  exact k7t4p3_local_2_bad

private theorem k7t4p3_update_2 : k7t4p3_step_2.apply k7t4p3_state_2 = k7t4p3_state_3 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_2.apply k7t4p3_state_2 i j = k7t4p3_state_3 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_3 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {1}, {0, 1}, {0, 1}, Finset.Icc 0 4, {1}, Finset.Icc 0 4, {0, 1}],
    #[{1}, ∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {0, 2, 3, 4}, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{0, 1}, {1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, Finset.Icc 0 3, {1, 2, 4, 5, 6}],
    #[{0, 1}, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {0, 1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5, {0, 1}],
    #[{1}, {0, 2, 3, 4}, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 0 3, {0, 1, 3, 4, 5}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{0, 1}, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0, 1}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_3_required_0 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, Finset.Icc 0 4, ∅, {2}, ∅],
    #[∅, ∅, ∅, ∅, {0}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, {0}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 0 4, {0}, {0}, ∅, ∅, ∅, {0, 1}, {0, 1}],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{2}, ∅, ∅, ∅, {0, 1}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, {0, 1}, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_3_required_0_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 0 j = k7t4p3_local_3_required_0 0 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 1 j = k7t4p3_local_3_required_0 1 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 2 j = k7t4p3_local_3_required_0 2 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 3 j = k7t4p3_local_3_required_0 3 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 4 j = k7t4p3_local_3_required_0 4 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 5 j = k7t4p3_local_3_required_0 5 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 6 j = k7t4p3_local_3_required_0 6 j := by decide

private theorem k7t4p3_local_3_required_0_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_0) 7 j = k7t4p3_local_3_required_0 7 j := by decide

private theorem k7t4p3_local_3_required_0_eq : (requiredMatrix 7 k7t4p3_step_3_required_block_0) = k7t4p3_local_3_required_0 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_3_required_0_eq_row_0 j

  · exact k7t4p3_local_3_required_0_eq_row_1 j

  · exact k7t4p3_local_3_required_0_eq_row_2 j

  · exact k7t4p3_local_3_required_0_eq_row_3 j

  · exact k7t4p3_local_3_required_0_eq_row_4 j

  · exact k7t4p3_local_3_required_0_eq_row_5 j

  · exact k7t4p3_local_3_required_0_eq_row_6 j

  · exact k7t4p3_local_3_required_0_eq_row_7 j

private theorem k7t4p3_local_3_path_0_0 : (⟨4, 0, [3, 1, 2, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_1 : (⟨4, 0, [3, 1, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_2 : (⟨4, 0, [3, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_3 : (⟨4, 7, [3, 1, 0, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_4 : (⟨4, 2, [3, 1, 0, 5, 6, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_5 : (⟨4, 0, [3, 2, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_6 : (⟨4, 6, [3, 2, 1, 0, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_7 : (⟨4, 7, [3, 2, 1, 0, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_8 : (⟨4, 0, [3, 2, 7, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_9 : (⟨4, 6, [3, 2, 7, 1, 0, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_10 : (⟨4, 1, [3, 2, 7, 6, 5, 0]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_0_11 : (⟨6, 0, [5, 4, 3, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_paths_block_0 : ∀ p ∈ k7t4p3_step_3_required_block_0, p.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by
  simp only [k7t4p3_step_3_required_block_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_3_path_0_0, k7t4p3_local_3_path_0_1, k7t4p3_local_3_path_0_2, k7t4p3_local_3_path_0_3, k7t4p3_local_3_path_0_4, k7t4p3_local_3_path_0_5, k7t4p3_local_3_path_0_6, k7t4p3_local_3_path_0_7, k7t4p3_local_3_path_0_8, k7t4p3_local_3_path_0_9, k7t4p3_local_3_path_0_10, k7t4p3_local_3_path_0_11⟩

private def k7t4p3_local_3_required_1 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, ∅, ∅, {0, 1, 3, 4}, {0}],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0, 1}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0, 1}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1, 3, 4}, {0}, {0}, {0, 1}, {0, 1}, ∅, ∅, ∅],
    #[{0}, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_3_required_1_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 0 j = k7t4p3_local_3_required_1 0 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 1 j = k7t4p3_local_3_required_1 1 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 2 j = k7t4p3_local_3_required_1 2 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 3 j = k7t4p3_local_3_required_1 3 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 4 j = k7t4p3_local_3_required_1 4 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 5 j = k7t4p3_local_3_required_1 5 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 6 j = k7t4p3_local_3_required_1 6 j := by decide

private theorem k7t4p3_local_3_required_1_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_1) 7 j = k7t4p3_local_3_required_1 7 j := by decide

private theorem k7t4p3_local_3_required_1_eq : (requiredMatrix 7 k7t4p3_step_3_required_block_1) = k7t4p3_local_3_required_1 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_3_required_1_eq_row_0 j

  · exact k7t4p3_local_3_required_1_eq_row_1 j

  · exact k7t4p3_local_3_required_1_eq_row_2 j

  · exact k7t4p3_local_3_required_1_eq_row_3 j

  · exact k7t4p3_local_3_required_1_eq_row_4 j

  · exact k7t4p3_local_3_required_1_eq_row_5 j

  · exact k7t4p3_local_3_required_1_eq_row_6 j

  · exact k7t4p3_local_3_required_1_eq_row_7 j

private theorem k7t4p3_local_3_path_1_0 : (⟨6, 0, [5, 4, 3, 2, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_1 : (⟨6, 0, [5, 4, 3, 2, 7, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_2 : (⟨6, 4, [5, 0, 1, 2, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_3 : (⟨6, 3, [5, 0, 1, 2, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_4 : (⟨6, 4, [5, 0, 1, 2, 7, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_5 : (⟨6, 0, [7, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_6 : (⟨6, 2, [7, 1, 0, 5, 4, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_7 : (⟨6, 0, [7, 2, 1]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_8 : (⟨6, 3, [7, 2, 1, 0, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_9 : (⟨6, 1, [7, 2, 3, 4, 5, 0]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_10 : (⟨0, 6, [1, 2, 3, 4, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_1_11 : (⟨0, 7, [1, 2, 3, 4, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_paths_block_1 : ∀ p ∈ k7t4p3_step_3_required_block_1, p.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by
  simp only [k7t4p3_step_3_required_block_1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_3_path_1_0, k7t4p3_local_3_path_1_1, k7t4p3_local_3_path_1_2, k7t4p3_local_3_path_1_3, k7t4p3_local_3_path_1_4, k7t4p3_local_3_path_1_5, k7t4p3_local_3_path_1_6, k7t4p3_local_3_path_1_7, k7t4p3_local_3_path_1_8, k7t4p3_local_3_path_1_9, k7t4p3_local_3_path_1_10, k7t4p3_local_3_path_1_11⟩

private def k7t4p3_local_3_required_2 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {1}, {0, 1}, {0, 1}, {0, 1}, {1}, {0}, {1}],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_3_required_2_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 0 j = k7t4p3_local_3_required_2 0 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 1 j = k7t4p3_local_3_required_2 1 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 2 j = k7t4p3_local_3_required_2 2 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 3 j = k7t4p3_local_3_required_2 3 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 4 j = k7t4p3_local_3_required_2 4 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 5 j = k7t4p3_local_3_required_2 5 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 6 j = k7t4p3_local_3_required_2 6 j := by decide

private theorem k7t4p3_local_3_required_2_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_3_required_block_2) 7 j = k7t4p3_local_3_required_2 7 j := by decide

private theorem k7t4p3_local_3_required_2_eq : (requiredMatrix 7 k7t4p3_step_3_required_block_2) = k7t4p3_local_3_required_2 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_3_required_2_eq_row_0 j

  · exact k7t4p3_local_3_required_2_eq_row_1 j

  · exact k7t4p3_local_3_required_2_eq_row_2 j

  · exact k7t4p3_local_3_required_2_eq_row_3 j

  · exact k7t4p3_local_3_required_2_eq_row_4 j

  · exact k7t4p3_local_3_required_2_eq_row_5 j

  · exact k7t4p3_local_3_required_2_eq_row_6 j

  · exact k7t4p3_local_3_required_2_eq_row_7 j

private theorem k7t4p3_local_3_path_2_0 : (⟨0, 5, [1, 2, 3, 7, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_1 : (⟨0, 4, [1, 2, 3, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_2 : (⟨0, 6, [1, 2, 7, 3, 4, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_3 : (⟨0, 4, [1, 2, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_4 : (⟨0, 3, [1, 2, 7, 6, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_5 : (⟨0, 7, [1, 3, 4, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_6 : (⟨0, 2, [1, 3, 4, 5, 6, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_7 : (⟨0, 3, [1, 7, 6, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_8 : (⟨0, 2, [5, 4, 3, 1, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_path_2_9 : (⟨0, 1, [5, 4, 3, 2, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by decide

private theorem k7t4p3_local_3_paths_block_2 : ∀ p ∈ k7t4p3_step_3_required_block_2, p.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by
  simp only [k7t4p3_step_3_required_block_2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_3_path_2_0, k7t4p3_local_3_path_2_1, k7t4p3_local_3_path_2_2, k7t4p3_local_3_path_2_3, k7t4p3_local_3_path_2_4, k7t4p3_local_3_path_2_5, k7t4p3_local_3_path_2_6, k7t4p3_local_3_path_2_7, k7t4p3_local_3_path_2_8, k7t4p3_local_3_path_2_9⟩

private theorem k7t4p3_local_3_merged_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 0 j = k7t4p3_local_3 0 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 1 j = k7t4p3_local_3 1 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 2 j = k7t4p3_local_3 2 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 3 j = k7t4p3_local_3 3 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 4 j = k7t4p3_local_3 4 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 5 j = k7t4p3_local_3 5 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 6 j = k7t4p3_local_3 6 j := by decide

private theorem k7t4p3_local_3_merged_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) 7 j = k7t4p3_local_3 7 j := by decide

private theorem k7t4p3_local_3_merged_eq : (fun a b => freshMatrix k7t4p3_state_3 a b ∪ (((k7t4p3_local_3_required_0 a b ∪ k7t4p3_local_3_required_1 a b) ∪ k7t4p3_local_3_required_2 a b))) = k7t4p3_local_3 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_3_merged_eq_row_0 j

  · exact k7t4p3_local_3_merged_eq_row_1 j

  · exact k7t4p3_local_3_merged_eq_row_2 j

  · exact k7t4p3_local_3_merged_eq_row_3 j

  · exact k7t4p3_local_3_merged_eq_row_4 j

  · exact k7t4p3_local_3_merged_eq_row_5 j

  · exact k7t4p3_local_3_merged_eq_row_6 j

  · exact k7t4p3_local_3_merged_eq_row_7 j

private theorem k7t4p3_local_3_eq : (fun a b => freshMatrix k7t4p3_state_3 a b ∪ requiredMatrix 7 k7t4p3_step_3_data.required a b) = k7t4p3_local_3 := by
  funext a b
  change freshMatrix k7t4p3_state_3 a b ∪ requiredMatrix 7 (k7t4p3_step_3_required_block_0 ++ k7t4p3_step_3_required_block_1 ++ k7t4p3_step_3_required_block_2) a b = _
  simp only [requiredMatrix_append, k7t4p3_local_3_required_0_eq, k7t4p3_local_3_required_1_eq, k7t4p3_local_3_required_2_eq]
  exact congrFun (congrFun k7t4p3_local_3_merged_eq a) b

private theorem k7t4p3_local_3_paths : ∀ p ∈ k7t4p3_step_3_data.required, p.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7 := by
  change ∀ p ∈ (k7t4p3_step_3_required_block_0 ++ k7t4p3_step_3_required_block_1 ++ k7t4p3_step_3_required_block_2), p.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) 7
  simp only [List.forall_mem_append]
  exact ⟨⟨k7t4p3_local_3_paths_block_0, k7t4p3_local_3_paths_block_1⟩, k7t4p3_local_3_paths_block_2⟩

private theorem k7t4p3_local_3_bad : k7t4p3_step_3_data.bad.Check (freshGraph k7t4p3.graph k7t4p3_step_3_data.i k7t4p3_step_3_data.j) k7t4p3_local_3 7 4 := by decide

private theorem k7t4p3_step_3_check : k7t4p3_step_3.Check k7t4p3.graph k7t4p3_state_3 7 4 := by
  change k7t4p3_step_3_data.Check k7t4p3.graph k7t4p3_state_3 7 4
  refine ⟨by decide, k7t4p3_local_3_paths, ?_⟩
  rw [k7t4p3_local_3_eq]
  exact k7t4p3_local_3_bad

private theorem k7t4p3_update_3 : k7t4p3_step_3.apply k7t4p3_state_3 = k7t4p3_state_4 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_3.apply k7t4p3_state_3 i j = k7t4p3_state_4 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_5 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {0, 2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, {0, 2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_4 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {2, 3, 4}, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5, {1}],
    #[Finset.Icc 0 4, {2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_4_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 0 j = k7t4p3_local_4 0 j := by decide

private theorem k7t4p3_local_4_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 1 j = k7t4p3_local_4 1 j := by decide

private theorem k7t4p3_local_4_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 2 j = k7t4p3_local_4 2 j := by decide

private theorem k7t4p3_local_4_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 3 j = k7t4p3_local_4 3 j := by decide

private theorem k7t4p3_local_4_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 4 j = k7t4p3_local_4 4 j := by decide

private theorem k7t4p3_local_4_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 5 j = k7t4p3_local_4 5 j := by decide

private theorem k7t4p3_local_4_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) 6 j = k7t4p3_local_4 6 j := by decide

private theorem k7t4p3_local_4_eq : (fun a b => k7t4p3_state_4 a b ∪ requiredMatrix 7 k7t4p3_step_4_data.required a b) = k7t4p3_local_4 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_4_eq_row_0 j

  · exact k7t4p3_local_4_eq_row_1 j

  · exact k7t4p3_local_4_eq_row_2 j

  · exact k7t4p3_local_4_eq_row_3 j

  · exact k7t4p3_local_4_eq_row_4 j

  · exact k7t4p3_local_4_eq_row_5 j

  · exact k7t4p3_local_4_eq_row_6 j

private theorem k7t4p3_local_4_paths : ∀ p ∈ k7t4p3_step_4_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_4_data.i k7t4p3_step_4_data.j) 7 := by decide

private theorem k7t4p3_local_4_bad : k7t4p3_step_4_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_4_data.i k7t4p3_step_4_data.j) k7t4p3_local_4 7 4 := by decide

private theorem k7t4p3_step_4_check : k7t4p3_step_4.Check k7t4p3.graph k7t4p3_state_4 7 4 := by
  change k7t4p3_step_4_data.Check k7t4p3.graph k7t4p3_state_4 7 4
  refine ⟨k7t4p3_local_4_paths, ?_⟩
  rw [k7t4p3_local_4_eq]
  exact k7t4p3_local_4_bad

private theorem k7t4p3_update_4 : k7t4p3_step_4.apply k7t4p3_state_4 = k7t4p3_state_5 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_4.apply k7t4p3_state_4 i j = k7t4p3_state_5 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_5 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1}, {1}, {0, 1}, Finset.Icc 0 4, {1}, Finset.Icc 0 4, {0, 1}],
    #[{0, 1}, ∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1}, {1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, {0, 2, 3, 4}, Finset.Icc 0 3, {1, 2, 4, 5, 6}],
    #[{0, 1}, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {0, 1, 3, 4, 5}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5, {0, 1}],
    #[{1}, Finset.Icc 0 4, {0, 2, 3, 4}, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 5, Finset.Icc 0 3, {0, 1, 3, 4, 5}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{0, 1}, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0, 1}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_5_required_0 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, Finset.Icc 0 4, ∅, {1}, ∅],
    #[∅, ∅, ∅, ∅, {0}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, {0}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 0 4, {0}, {0}, ∅, ∅, ∅, {0, 1}, {0, 1}],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, {0, 1}, ∅, ∅, ∅],
    #[∅, ∅, ∅, ∅, {0, 1}, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_5_required_0_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 0 j = k7t4p3_local_5_required_0 0 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 1 j = k7t4p3_local_5_required_0 1 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 2 j = k7t4p3_local_5_required_0 2 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 3 j = k7t4p3_local_5_required_0 3 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 4 j = k7t4p3_local_5_required_0 4 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 5 j = k7t4p3_local_5_required_0 5 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 6 j = k7t4p3_local_5_required_0 6 j := by decide

private theorem k7t4p3_local_5_required_0_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_0) 7 j = k7t4p3_local_5_required_0 7 j := by decide

private theorem k7t4p3_local_5_required_0_eq : (requiredMatrix 7 k7t4p3_step_5_required_block_0) = k7t4p3_local_5_required_0 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_5_required_0_eq_row_0 j

  · exact k7t4p3_local_5_required_0_eq_row_1 j

  · exact k7t4p3_local_5_required_0_eq_row_2 j

  · exact k7t4p3_local_5_required_0_eq_row_3 j

  · exact k7t4p3_local_5_required_0_eq_row_4 j

  · exact k7t4p3_local_5_required_0_eq_row_5 j

  · exact k7t4p3_local_5_required_0_eq_row_6 j

  · exact k7t4p3_local_5_required_0_eq_row_7 j

private theorem k7t4p3_local_5_path_0_0 : (⟨4, 0, [3, 1, 2, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_1 : (⟨4, 0, [3, 1, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_2 : (⟨4, 6, [3, 1, 2, 0, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_3 : (⟨4, 7, [3, 1, 2, 0, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_4 : (⟨4, 0, [3, 1, 7, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_5 : (⟨4, 6, [3, 1, 7, 2, 0, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_6 : (⟨4, 0, [3, 1, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_7 : (⟨4, 2, [3, 1, 7, 6, 5, 0]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_8 : (⟨4, 0, [3, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_9 : (⟨4, 7, [3, 2, 0, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_10 : (⟨4, 1, [3, 2, 0, 5, 6, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_0_11 : (⟨6, 0, [5, 4, 3, 1, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_paths_block_0 : ∀ p ∈ k7t4p3_step_5_required_block_0, p.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by
  simp only [k7t4p3_step_5_required_block_0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_5_path_0_0, k7t4p3_local_5_path_0_1, k7t4p3_local_5_path_0_2, k7t4p3_local_5_path_0_3, k7t4p3_local_5_path_0_4, k7t4p3_local_5_path_0_5, k7t4p3_local_5_path_0_6, k7t4p3_local_5_path_0_7, k7t4p3_local_5_path_0_8, k7t4p3_local_5_path_0_9, k7t4p3_local_5_path_0_10, k7t4p3_local_5_path_0_11⟩

private def k7t4p3_local_5_required_1 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, ∅, ∅, ∅, ∅, ∅, Finset.Icc 0 4, {0}],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0, 1}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, {0, 1}, ∅],
    #[∅, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[Finset.Icc 0 4, {0}, {0}, {0, 1}, {0, 1}, ∅, ∅, ∅],
    #[{0}, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_5_required_1_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 0 j = k7t4p3_local_5_required_1 0 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 1 j = k7t4p3_local_5_required_1 1 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 2 j = k7t4p3_local_5_required_1 2 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 3 j = k7t4p3_local_5_required_1 3 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 4 j = k7t4p3_local_5_required_1 4 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 5 j = k7t4p3_local_5_required_1 5 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 6 j = k7t4p3_local_5_required_1 6 j := by decide

private theorem k7t4p3_local_5_required_1_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_1) 7 j = k7t4p3_local_5_required_1 7 j := by decide

private theorem k7t4p3_local_5_required_1_eq : (requiredMatrix 7 k7t4p3_step_5_required_block_1) = k7t4p3_local_5_required_1 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_5_required_1_eq_row_0 j

  · exact k7t4p3_local_5_required_1_eq_row_1 j

  · exact k7t4p3_local_5_required_1_eq_row_2 j

  · exact k7t4p3_local_5_required_1_eq_row_3 j

  · exact k7t4p3_local_5_required_1_eq_row_4 j

  · exact k7t4p3_local_5_required_1_eq_row_5 j

  · exact k7t4p3_local_5_required_1_eq_row_6 j

  · exact k7t4p3_local_5_required_1_eq_row_7 j

private theorem k7t4p3_local_5_path_1_0 : (⟨6, 0, [5, 4, 3, 1, 7, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_1 : (⟨6, 0, [5, 4, 3, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_2 : (⟨6, 4, [5, 0, 2, 1, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_3 : (⟨6, 3, [5, 0, 2, 1, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_4 : (⟨6, 4, [5, 0, 2, 1, 7, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_5 : (⟨6, 0, [7, 1, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_6 : (⟨6, 3, [7, 1, 2, 0, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_7 : (⟨6, 2, [7, 1, 3, 4, 5, 0]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_8 : (⟨6, 0, [7, 2]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_9 : (⟨6, 1, [7, 2, 0, 5, 4, 3]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_10 : (⟨0, 6, [2, 1, 3, 4, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_1_11 : (⟨0, 7, [2, 1, 3, 4, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_paths_block_1 : ∀ p ∈ k7t4p3_step_5_required_block_1, p.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by
  simp only [k7t4p3_step_5_required_block_1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_5_path_1_0, k7t4p3_local_5_path_1_1, k7t4p3_local_5_path_1_2, k7t4p3_local_5_path_1_3, k7t4p3_local_5_path_1_4, k7t4p3_local_5_path_1_5, k7t4p3_local_5_path_1_6, k7t4p3_local_5_path_1_7, k7t4p3_local_5_path_1_8, k7t4p3_local_5_path_1_9, k7t4p3_local_5_path_1_10, k7t4p3_local_5_path_1_11⟩

private def k7t4p3_local_5_required_2 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1}, {1}, {0, 1}, {0, 1}, {1}, {0}, {1}],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0, 1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{0}, ∅, ∅, ∅, ∅, ∅, ∅, ∅],
    #[{1}, ∅, ∅, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_5_required_2_eq_row_0 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 0 j = k7t4p3_local_5_required_2 0 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_1 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 1 j = k7t4p3_local_5_required_2 1 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_2 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 2 j = k7t4p3_local_5_required_2 2 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_3 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 3 j = k7t4p3_local_5_required_2 3 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_4 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 4 j = k7t4p3_local_5_required_2 4 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_5 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 5 j = k7t4p3_local_5_required_2 5 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_6 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 6 j = k7t4p3_local_5_required_2 6 j := by decide

private theorem k7t4p3_local_5_required_2_eq_row_7 : ∀ j : Fin 8, (requiredMatrix 7 k7t4p3_step_5_required_block_2) 7 j = k7t4p3_local_5_required_2 7 j := by decide

private theorem k7t4p3_local_5_required_2_eq : (requiredMatrix 7 k7t4p3_step_5_required_block_2) = k7t4p3_local_5_required_2 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_5_required_2_eq_row_0 j

  · exact k7t4p3_local_5_required_2_eq_row_1 j

  · exact k7t4p3_local_5_required_2_eq_row_2 j

  · exact k7t4p3_local_5_required_2_eq_row_3 j

  · exact k7t4p3_local_5_required_2_eq_row_4 j

  · exact k7t4p3_local_5_required_2_eq_row_5 j

  · exact k7t4p3_local_5_required_2_eq_row_6 j

  · exact k7t4p3_local_5_required_2_eq_row_7 j

private theorem k7t4p3_local_5_path_2_0 : (⟨0, 5, [2, 1, 3, 7, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_1 : (⟨0, 4, [2, 1, 3, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_2 : (⟨0, 6, [2, 1, 7, 3, 4, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_3 : (⟨0, 4, [2, 1, 7, 6, 5]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_4 : (⟨0, 3, [2, 1, 7, 6, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_5 : (⟨0, 7, [2, 3, 4, 5, 6]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_6 : (⟨0, 1, [2, 3, 4, 5, 6, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_7 : (⟨0, 3, [2, 7, 6, 5, 4]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_8 : (⟨0, 2, [5, 4, 3, 1, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_path_2_9 : (⟨0, 1, [5, 4, 3, 2, 7]⟩ : RequiredPathData (Fin 8)).Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by decide

private theorem k7t4p3_local_5_paths_block_2 : ∀ p ∈ k7t4p3_step_5_required_block_2, p.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by
  simp only [k7t4p3_step_5_required_block_2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_local_5_path_2_0, k7t4p3_local_5_path_2_1, k7t4p3_local_5_path_2_2, k7t4p3_local_5_path_2_3, k7t4p3_local_5_path_2_4, k7t4p3_local_5_path_2_5, k7t4p3_local_5_path_2_6, k7t4p3_local_5_path_2_7, k7t4p3_local_5_path_2_8, k7t4p3_local_5_path_2_9⟩

private theorem k7t4p3_local_5_merged_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 0 j = k7t4p3_local_5 0 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 1 j = k7t4p3_local_5 1 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 2 j = k7t4p3_local_5 2 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 3 j = k7t4p3_local_5 3 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 4 j = k7t4p3_local_5 4 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 5 j = k7t4p3_local_5 5 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 6 j = k7t4p3_local_5 6 j := by decide

private theorem k7t4p3_local_5_merged_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) 7 j = k7t4p3_local_5 7 j := by decide

private theorem k7t4p3_local_5_merged_eq : (fun a b => freshMatrix k7t4p3_state_5 a b ∪ (((k7t4p3_local_5_required_0 a b ∪ k7t4p3_local_5_required_1 a b) ∪ k7t4p3_local_5_required_2 a b))) = k7t4p3_local_5 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_5_merged_eq_row_0 j

  · exact k7t4p3_local_5_merged_eq_row_1 j

  · exact k7t4p3_local_5_merged_eq_row_2 j

  · exact k7t4p3_local_5_merged_eq_row_3 j

  · exact k7t4p3_local_5_merged_eq_row_4 j

  · exact k7t4p3_local_5_merged_eq_row_5 j

  · exact k7t4p3_local_5_merged_eq_row_6 j

  · exact k7t4p3_local_5_merged_eq_row_7 j

private theorem k7t4p3_local_5_eq : (fun a b => freshMatrix k7t4p3_state_5 a b ∪ requiredMatrix 7 k7t4p3_step_5_data.required a b) = k7t4p3_local_5 := by
  funext a b
  change freshMatrix k7t4p3_state_5 a b ∪ requiredMatrix 7 (k7t4p3_step_5_required_block_0 ++ k7t4p3_step_5_required_block_1 ++ k7t4p3_step_5_required_block_2) a b = _
  simp only [requiredMatrix_append, k7t4p3_local_5_required_0_eq, k7t4p3_local_5_required_1_eq, k7t4p3_local_5_required_2_eq]
  exact congrFun (congrFun k7t4p3_local_5_merged_eq a) b

private theorem k7t4p3_local_5_paths : ∀ p ∈ k7t4p3_step_5_data.required, p.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7 := by
  change ∀ p ∈ (k7t4p3_step_5_required_block_0 ++ k7t4p3_step_5_required_block_1 ++ k7t4p3_step_5_required_block_2), p.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) 7
  simp only [List.forall_mem_append]
  exact ⟨⟨k7t4p3_local_5_paths_block_0, k7t4p3_local_5_paths_block_1⟩, k7t4p3_local_5_paths_block_2⟩

private theorem k7t4p3_local_5_bad : k7t4p3_step_5_data.bad.Check (freshGraph k7t4p3.graph k7t4p3_step_5_data.i k7t4p3_step_5_data.j) k7t4p3_local_5 7 4 := by decide

private theorem k7t4p3_step_5_check : k7t4p3_step_5.Check k7t4p3.graph k7t4p3_state_5 7 4 := by
  change k7t4p3_step_5_data.Check k7t4p3.graph k7t4p3_state_5 7 4
  refine ⟨by decide, k7t4p3_local_5_paths, ?_⟩
  rw [k7t4p3_local_5_eq]
  exact k7t4p3_local_5_bad

private theorem k7t4p3_update_5 : k7t4p3_step_5.apply k7t4p3_state_5 = k7t4p3_state_6 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_5.apply k7t4p3_state_5 i j = k7t4p3_state_6 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_7 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {0, 2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_6 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {2, 3, 4}, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, {2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 1 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_6_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 0 j = k7t4p3_local_6 0 j := by decide

private theorem k7t4p3_local_6_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 1 j = k7t4p3_local_6 1 j := by decide

private theorem k7t4p3_local_6_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 2 j = k7t4p3_local_6 2 j := by decide

private theorem k7t4p3_local_6_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 3 j = k7t4p3_local_6 3 j := by decide

private theorem k7t4p3_local_6_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 4 j = k7t4p3_local_6 4 j := by decide

private theorem k7t4p3_local_6_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 5 j = k7t4p3_local_6 5 j := by decide

private theorem k7t4p3_local_6_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) 6 j = k7t4p3_local_6 6 j := by decide

private theorem k7t4p3_local_6_eq : (fun a b => k7t4p3_state_6 a b ∪ requiredMatrix 7 k7t4p3_step_6_data.required a b) = k7t4p3_local_6 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_6_eq_row_0 j

  · exact k7t4p3_local_6_eq_row_1 j

  · exact k7t4p3_local_6_eq_row_2 j

  · exact k7t4p3_local_6_eq_row_3 j

  · exact k7t4p3_local_6_eq_row_4 j

  · exact k7t4p3_local_6_eq_row_5 j

  · exact k7t4p3_local_6_eq_row_6 j

private theorem k7t4p3_local_6_paths : ∀ p ∈ k7t4p3_step_6_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_6_data.i k7t4p3_step_6_data.j) 7 := by decide

private theorem k7t4p3_local_6_bad : k7t4p3_step_6_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_6_data.i k7t4p3_step_6_data.j) k7t4p3_local_6 7 4 := by decide

private theorem k7t4p3_step_6_check : k7t4p3_step_6.Check k7t4p3.graph k7t4p3_state_6 7 4 := by
  change k7t4p3_step_6_data.Check k7t4p3.graph k7t4p3_state_6 7 4
  refine ⟨k7t4p3_local_6_paths, ?_⟩
  rw [k7t4p3_local_6_eq]
  exact k7t4p3_local_6_bad

private theorem k7t4p3_update_6 : k7t4p3_step_6.apply k7t4p3_state_6 = k7t4p3_state_7 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_6.apply k7t4p3_state_6 i j = k7t4p3_state_7 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_7 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1}, ∅, ∅, {0, 1}, ∅, {0, 1, 2}, ∅],
    #[{0, 1}, ∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[∅, {1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, {0, 2, 3, 4}, {3, 4, 5}, ∅],
    #[{0, 1}, Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5, {1}],
    #[∅, Finset.Icc 0 4, Finset.Icc 0 4, {0, 2, 3, 4}, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[{0, 1, 2}, Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_7_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 0 j = k7t4p3_local_7 0 j := by decide

private theorem k7t4p3_local_7_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 1 j = k7t4p3_local_7 1 j := by decide

private theorem k7t4p3_local_7_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 2 j = k7t4p3_local_7 2 j := by decide

private theorem k7t4p3_local_7_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 3 j = k7t4p3_local_7 3 j := by decide

private theorem k7t4p3_local_7_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 4 j = k7t4p3_local_7 4 j := by decide

private theorem k7t4p3_local_7_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 5 j = k7t4p3_local_7 5 j := by decide

private theorem k7t4p3_local_7_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 6 j = k7t4p3_local_7 6 j := by decide

private theorem k7t4p3_local_7_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) 7 j = k7t4p3_local_7 7 j := by decide

private theorem k7t4p3_local_7_eq : (fun a b => freshMatrix k7t4p3_state_7 a b ∪ requiredMatrix 7 k7t4p3_step_7_data.required a b) = k7t4p3_local_7 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_7_eq_row_0 j

  · exact k7t4p3_local_7_eq_row_1 j

  · exact k7t4p3_local_7_eq_row_2 j

  · exact k7t4p3_local_7_eq_row_3 j

  · exact k7t4p3_local_7_eq_row_4 j

  · exact k7t4p3_local_7_eq_row_5 j

  · exact k7t4p3_local_7_eq_row_6 j

  · exact k7t4p3_local_7_eq_row_7 j

private theorem k7t4p3_local_7_paths : ∀ p ∈ k7t4p3_step_7_data.required, p.Check (freshGraph k7t4p3.graph k7t4p3_step_7_data.i k7t4p3_step_7_data.j) 7 := by decide

private theorem k7t4p3_local_7_bad : k7t4p3_step_7_data.bad.Check (freshGraph k7t4p3.graph k7t4p3_step_7_data.i k7t4p3_step_7_data.j) k7t4p3_local_7 7 4 := by decide

private theorem k7t4p3_step_7_check : k7t4p3_step_7.Check k7t4p3.graph k7t4p3_state_7 7 4 := by
  change k7t4p3_step_7_data.Check k7t4p3.graph k7t4p3_state_7 7 4
  refine ⟨by decide, k7t4p3_local_7_paths, ?_⟩
  rw [k7t4p3_local_7_eq]
  exact k7t4p3_local_7_bad

private theorem k7t4p3_update_7 : k7t4p3_step_7.apply k7t4p3_state_7 = k7t4p3_state_8 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_7.apply k7t4p3_state_7 i j = k7t4p3_state_8 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_8 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 1 5, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, {1, 2}],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, {1, 2}, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_8_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 0 j = k7t4p3_local_8 0 j := by decide

private theorem k7t4p3_local_8_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 1 j = k7t4p3_local_8 1 j := by decide

private theorem k7t4p3_local_8_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 2 j = k7t4p3_local_8 2 j := by decide

private theorem k7t4p3_local_8_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 3 j = k7t4p3_local_8 3 j := by decide

private theorem k7t4p3_local_8_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 4 j = k7t4p3_local_8 4 j := by decide

private theorem k7t4p3_local_8_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 5 j = k7t4p3_local_8 5 j := by decide

private theorem k7t4p3_local_8_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) 6 j = k7t4p3_local_8 6 j := by decide

private theorem k7t4p3_local_8_eq : (fun a b => k7t4p3_state_8 a b ∪ requiredMatrix 7 k7t4p3_step_8_data.required a b) = k7t4p3_local_8 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_8_eq_row_0 j

  · exact k7t4p3_local_8_eq_row_1 j

  · exact k7t4p3_local_8_eq_row_2 j

  · exact k7t4p3_local_8_eq_row_3 j

  · exact k7t4p3_local_8_eq_row_4 j

  · exact k7t4p3_local_8_eq_row_5 j

  · exact k7t4p3_local_8_eq_row_6 j

private theorem k7t4p3_local_8_paths : ∀ p ∈ k7t4p3_step_8_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_8_data.i k7t4p3_step_8_data.j) 7 := by decide

private theorem k7t4p3_local_8_bad : k7t4p3_step_8_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_8_data.i k7t4p3_step_8_data.j) k7t4p3_local_8 7 4 := by decide

private theorem k7t4p3_step_8_check : k7t4p3_step_8.Check k7t4p3.graph k7t4p3_state_8 7 4 := by
  change k7t4p3_step_8_data.Check k7t4p3.graph k7t4p3_state_8 7 4
  refine ⟨k7t4p3_local_8_paths, ?_⟩
  rw [k7t4p3_local_8_eq]
  exact k7t4p3_local_8_bad

private theorem k7t4p3_update_8 : k7t4p3_step_8.apply k7t4p3_state_8 = k7t4p3_state_9 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_8.apply k7t4p3_state_8 i j = k7t4p3_state_9 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_9 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, {1, 2, 4, 5, 6}, ∅, Finset.Icc 1 4, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, Finset.Icc 1 4, ∅, {1, 2, 3}, Finset.Icc 2 5, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 2 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_9_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 0 j = k7t4p3_local_9 0 j := by decide

private theorem k7t4p3_local_9_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 1 j = k7t4p3_local_9 1 j := by decide

private theorem k7t4p3_local_9_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 2 j = k7t4p3_local_9 2 j := by decide

private theorem k7t4p3_local_9_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 3 j = k7t4p3_local_9 3 j := by decide

private theorem k7t4p3_local_9_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 4 j = k7t4p3_local_9 4 j := by decide

private theorem k7t4p3_local_9_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 5 j = k7t4p3_local_9 5 j := by decide

private theorem k7t4p3_local_9_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) 6 j = k7t4p3_local_9 6 j := by decide

private theorem k7t4p3_local_9_eq : (fun a b => k7t4p3_state_9 a b ∪ requiredMatrix 7 k7t4p3_step_9_data.required a b) = k7t4p3_local_9 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_9_eq_row_0 j

  · exact k7t4p3_local_9_eq_row_1 j

  · exact k7t4p3_local_9_eq_row_2 j

  · exact k7t4p3_local_9_eq_row_3 j

  · exact k7t4p3_local_9_eq_row_4 j

  · exact k7t4p3_local_9_eq_row_5 j

  · exact k7t4p3_local_9_eq_row_6 j

private theorem k7t4p3_local_9_paths : ∀ p ∈ k7t4p3_step_9_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_9_data.i k7t4p3_step_9_data.j) 7 := by decide

private theorem k7t4p3_local_9_bad : k7t4p3_step_9_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_9_data.i k7t4p3_step_9_data.j) k7t4p3_local_9 7 4 := by decide

private theorem k7t4p3_step_9_check : k7t4p3_step_9.Check k7t4p3.graph k7t4p3_state_9 7 4 := by
  change k7t4p3_step_9_data.Check k7t4p3.graph k7t4p3_state_9 7 4
  refine ⟨k7t4p3_local_9_paths, ?_⟩
  rw [k7t4p3_local_9_eq]
  exact k7t4p3_local_9_bad

private theorem k7t4p3_update_9 : k7t4p3_step_9.apply k7t4p3_state_9 = k7t4p3_state_10 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_9.apply k7t4p3_state_9 i j = k7t4p3_state_10 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_11 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {0}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_10 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, Finset.Icc 1 6, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[Finset.Icc 1 6, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, Finset.Icc 1 5, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, ∅],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, Finset.Icc 1 5, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, ∅, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_10_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 0 j = k7t4p3_local_10 0 j := by decide

private theorem k7t4p3_local_10_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 1 j = k7t4p3_local_10 1 j := by decide

private theorem k7t4p3_local_10_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 2 j = k7t4p3_local_10 2 j := by decide

private theorem k7t4p3_local_10_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 3 j = k7t4p3_local_10 3 j := by decide

private theorem k7t4p3_local_10_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 4 j = k7t4p3_local_10 4 j := by decide

private theorem k7t4p3_local_10_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 5 j = k7t4p3_local_10 5 j := by decide

private theorem k7t4p3_local_10_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) 6 j = k7t4p3_local_10 6 j := by decide

private theorem k7t4p3_local_10_eq : (fun a b => k7t4p3_state_10 a b ∪ requiredMatrix 7 k7t4p3_step_10_data.required a b) = k7t4p3_local_10 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_10_eq_row_0 j

  · exact k7t4p3_local_10_eq_row_1 j

  · exact k7t4p3_local_10_eq_row_2 j

  · exact k7t4p3_local_10_eq_row_3 j

  · exact k7t4p3_local_10_eq_row_4 j

  · exact k7t4p3_local_10_eq_row_5 j

  · exact k7t4p3_local_10_eq_row_6 j

private theorem k7t4p3_local_10_paths : ∀ p ∈ k7t4p3_step_10_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_10_data.i k7t4p3_step_10_data.j) 7 := by decide

private theorem k7t4p3_local_10_bad : k7t4p3_step_10_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_10_data.i k7t4p3_step_10_data.j) k7t4p3_local_10 7 4 := by decide

private theorem k7t4p3_step_10_check : k7t4p3_step_10.Check k7t4p3.graph k7t4p3_state_10 7 4 := by
  change k7t4p3_step_10_data.Check k7t4p3.graph k7t4p3_state_10 7 4
  refine ⟨k7t4p3_local_10_paths, ?_⟩
  rw [k7t4p3_local_10_eq]
  exact k7t4p3_local_10_bad

private theorem k7t4p3_update_10 : k7t4p3_step_10.apply k7t4p3_state_10 = k7t4p3_state_11 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_10.apply k7t4p3_state_10 i j = k7t4p3_state_11 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_12 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {0}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0}],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0}, {0}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_11 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5, {0}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0}, ∅, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_11_eq_row_0 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 0 j = k7t4p3_local_11 0 j := by decide

private theorem k7t4p3_local_11_eq_row_1 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 1 j = k7t4p3_local_11 1 j := by decide

private theorem k7t4p3_local_11_eq_row_2 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 2 j = k7t4p3_local_11 2 j := by decide

private theorem k7t4p3_local_11_eq_row_3 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 3 j = k7t4p3_local_11 3 j := by decide

private theorem k7t4p3_local_11_eq_row_4 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 4 j = k7t4p3_local_11 4 j := by decide

private theorem k7t4p3_local_11_eq_row_5 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 5 j = k7t4p3_local_11 5 j := by decide

private theorem k7t4p3_local_11_eq_row_6 : ∀ j : Fin 7, (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) 6 j = k7t4p3_local_11 6 j := by decide

private theorem k7t4p3_local_11_eq : (fun a b => k7t4p3_state_11 a b ∪ requiredMatrix 7 k7t4p3_step_11_data.required a b) = k7t4p3_local_11 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_11_eq_row_0 j

  · exact k7t4p3_local_11_eq_row_1 j

  · exact k7t4p3_local_11_eq_row_2 j

  · exact k7t4p3_local_11_eq_row_3 j

  · exact k7t4p3_local_11_eq_row_4 j

  · exact k7t4p3_local_11_eq_row_5 j

  · exact k7t4p3_local_11_eq_row_6 j

private theorem k7t4p3_local_11_paths : ∀ p ∈ k7t4p3_step_11_data.required, p.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_11_data.i k7t4p3_step_11_data.j) 7 := by decide

private theorem k7t4p3_local_11_bad : k7t4p3_step_11_data.bad.Check (addedEdgeGraph k7t4p3.graph k7t4p3_step_11_data.i k7t4p3_step_11_data.j) k7t4p3_local_11 7 4 := by decide

private theorem k7t4p3_step_11_check : k7t4p3_step_11.Check k7t4p3.graph k7t4p3_state_11 7 4 := by
  change k7t4p3_step_11_data.Check k7t4p3.graph k7t4p3_state_11 7 4
  refine ⟨k7t4p3_local_11_paths, ?_⟩
  rw [k7t4p3_local_11_eq]
  exact k7t4p3_local_11_bad

private theorem k7t4p3_update_11 : k7t4p3_step_11.apply k7t4p3_state_11 = k7t4p3_state_12 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_11.apply k7t4p3_state_11 i j = k7t4p3_state_12 i j := by decide
  exact funext (fun i => funext (h i))

private def k7t4p3_state_13 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[{1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, {1, 2, 3}, {1, 2, 4, 5, 6}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {3, 4, 5}, ∅],
    #[Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, {0, 2, 3, 4, 5}, {0}],
    #[Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0, 1}],
    #[Finset.Icc 0 5, {1, 2, 3}, {3, 4, 5}, {0, 2, 3, 4, 5}, {1, 2, 3}, ∅, {1, 2, 3}],
    #[{1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0}, {0, 1}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private def k7t4p3_local_12 : ForbiddenMatrix 8 :=
  fun i j => ((#[#[∅, {0, 1}, ∅, ∅, {0, 1, 2}, ∅, {0, 1}, ∅],
    #[{0, 1}, ∅, {1, 4, 5, 6}, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 5, {1, 2, 4, 5, 6}],
    #[∅, {1, 4, 5, 6}, ∅, {1, 2, 4, 5, 6}, Finset.Icc 0 5, Finset.Icc 0 4, Finset.Icc 0 3, {1, 2, 4, 5, 6}],
    #[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {1, 2, 3}, Finset.Icc 0 4, {1, 3, 4, 5}, ∅],
    #[{0, 1, 2}, Finset.Icc 0 5, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 0 5, {0}],
    #[∅, Finset.Icc 0 4, Finset.Icc 0 4, Finset.Icc 0 4, {1, 2, 3}, ∅, {1, 2, 3}, {0}],
    #[{0, 1}, Finset.Icc 0 5, Finset.Icc 0 3, {1, 3, 4, 5}, Finset.Icc 0 5, {1, 2, 3}, ∅, {1, 2, 3}],
    #[∅, {1, 2, 4, 5, 6}, {1, 2, 4, 5, 6}, ∅, {0}, {0}, {1, 2, 3}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p3_local_12_eq_row_0 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 0 j = k7t4p3_local_12 0 j := by decide

private theorem k7t4p3_local_12_eq_row_1 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 1 j = k7t4p3_local_12 1 j := by decide

private theorem k7t4p3_local_12_eq_row_2 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 2 j = k7t4p3_local_12 2 j := by decide

private theorem k7t4p3_local_12_eq_row_3 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 3 j = k7t4p3_local_12 3 j := by decide

private theorem k7t4p3_local_12_eq_row_4 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 4 j = k7t4p3_local_12 4 j := by decide

private theorem k7t4p3_local_12_eq_row_5 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 5 j = k7t4p3_local_12 5 j := by decide

private theorem k7t4p3_local_12_eq_row_6 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 6 j = k7t4p3_local_12 6 j := by decide

private theorem k7t4p3_local_12_eq_row_7 : ∀ j : Fin 8, (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) 7 j = k7t4p3_local_12 7 j := by decide

private theorem k7t4p3_local_12_eq : (fun a b => freshMatrix k7t4p3_state_12 a b ∪ requiredMatrix 7 k7t4p3_step_12_data.required a b) = k7t4p3_local_12 := by
  funext i j
  fin_cases i

  · exact k7t4p3_local_12_eq_row_0 j

  · exact k7t4p3_local_12_eq_row_1 j

  · exact k7t4p3_local_12_eq_row_2 j

  · exact k7t4p3_local_12_eq_row_3 j

  · exact k7t4p3_local_12_eq_row_4 j

  · exact k7t4p3_local_12_eq_row_5 j

  · exact k7t4p3_local_12_eq_row_6 j

  · exact k7t4p3_local_12_eq_row_7 j

private theorem k7t4p3_local_12_paths : ∀ p ∈ k7t4p3_step_12_data.required, p.Check (freshGraph k7t4p3.graph k7t4p3_step_12_data.i k7t4p3_step_12_data.j) 7 := by decide

private theorem k7t4p3_local_12_bad : k7t4p3_step_12_data.bad.Check (freshGraph k7t4p3.graph k7t4p3_step_12_data.i k7t4p3_step_12_data.j) k7t4p3_local_12 7 4 := by decide

private theorem k7t4p3_step_12_check : k7t4p3_step_12.Check k7t4p3.graph k7t4p3_state_12 7 4 := by
  change k7t4p3_step_12_data.Check k7t4p3.graph k7t4p3_state_12 7 4
  refine ⟨by decide, k7t4p3_local_12_paths, ?_⟩
  rw [k7t4p3_local_12_eq]
  exact k7t4p3_local_12_bad

private theorem k7t4p3_update_12 : k7t4p3_step_12.apply k7t4p3_state_12 = k7t4p3_state_13 := by
  have h : ∀ i j : Fin 7, k7t4p3_step_12.apply k7t4p3_state_12 i j = k7t4p3_state_13 i j := by decide
  exact funext (fun i => funext (h i))

private theorem k7t4p3_closure_13 : ClosureCheck k7t4p3.graph k7t4p3_state_13 7 4 [] := by trivial

private theorem k7t4p3_closure_12 : ClosureCheck k7t4p3.graph k7t4p3_state_12 7 4 [k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_12_check
  · rw [k7t4p3_update_12]
    exact k7t4p3_closure_13

private theorem k7t4p3_closure_11 : ClosureCheck k7t4p3.graph k7t4p3_state_11 7 4 [k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_11_check
  · rw [k7t4p3_update_11]
    exact k7t4p3_closure_12

private theorem k7t4p3_closure_10 : ClosureCheck k7t4p3.graph k7t4p3_state_10 7 4 [k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_10_check
  · rw [k7t4p3_update_10]
    exact k7t4p3_closure_11

private theorem k7t4p3_closure_9 : ClosureCheck k7t4p3.graph k7t4p3_state_9 7 4 [k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_9_check
  · rw [k7t4p3_update_9]
    exact k7t4p3_closure_10

private theorem k7t4p3_closure_8 : ClosureCheck k7t4p3.graph k7t4p3_state_8 7 4 [k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_8_check
  · rw [k7t4p3_update_8]
    exact k7t4p3_closure_9

private theorem k7t4p3_closure_7 : ClosureCheck k7t4p3.graph k7t4p3_state_7 7 4 [k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_7_check
  · rw [k7t4p3_update_7]
    exact k7t4p3_closure_8

private theorem k7t4p3_closure_6 : ClosureCheck k7t4p3.graph k7t4p3_state_6 7 4 [k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_6_check
  · rw [k7t4p3_update_6]
    exact k7t4p3_closure_7

private theorem k7t4p3_closure_5 : ClosureCheck k7t4p3.graph k7t4p3_state_5 7 4 [k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_5_check
  · rw [k7t4p3_update_5]
    exact k7t4p3_closure_6

private theorem k7t4p3_closure_4 : ClosureCheck k7t4p3.graph k7t4p3_state_4 7 4 [k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_4_check
  · rw [k7t4p3_update_4]
    exact k7t4p3_closure_5

private theorem k7t4p3_closure_3 : ClosureCheck k7t4p3.graph k7t4p3_state_3 7 4 [k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_3_check
  · rw [k7t4p3_update_3]
    exact k7t4p3_closure_4

private theorem k7t4p3_closure_2 : ClosureCheck k7t4p3.graph k7t4p3_state_2 7 4 [k7t4p3_step_2, k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_2_check
  · rw [k7t4p3_update_2]
    exact k7t4p3_closure_3

private theorem k7t4p3_closure_1 : ClosureCheck k7t4p3.graph k7t4p3_state_1 7 4 [k7t4p3_step_1, k7t4p3_step_2, k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_1_check
  · rw [k7t4p3_update_1]
    exact k7t4p3_closure_2

private theorem k7t4p3_closure_0 : ClosureCheck k7t4p3.graph k7t4p3_state_0 7 4 [k7t4p3_step_0, k7t4p3_step_1, k7t4p3_step_2, k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] := by
  constructor
  · exact k7t4p3_step_0_check
  · rw [k7t4p3_update_0]
    exact k7t4p3_closure_1

private theorem k7t4p3_matrix_eq : k7t4p3.matrix 7 = k7t4p3_state_13 := by
  change closureMatrix (k7t4p3.initialMatrix 7) _ = _
  rw [k7t4p3_initial_eq]
  change closureMatrix k7t4p3_state_0 [k7t4p3_step_0, k7t4p3_step_1, k7t4p3_step_2, k7t4p3_step_3, k7t4p3_step_4, k7t4p3_step_5, k7t4p3_step_6, k7t4p3_step_7, k7t4p3_step_8, k7t4p3_step_9, k7t4p3_step_10, k7t4p3_step_11, k7t4p3_step_12] = _
  simp only [closureMatrix]
  rw [k7t4p3_update_0, k7t4p3_update_1, k7t4p3_update_2, k7t4p3_update_3, k7t4p3_update_4, k7t4p3_update_5, k7t4p3_update_6, k7t4p3_update_7, k7t4p3_update_8, k7t4p3_update_9, k7t4p3_update_10, k7t4p3_update_11, k7t4p3_update_12]

private theorem k7t4p3_part_0 : k7t4p3.chains.flatten = List.finRange _ := by decide

private theorem k7t4p3_part_1 : k7t4p3.chains.map List.length = ([[], [], [3]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p3_part_2 : k7t4p3.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p3.clique))) = ([[], [], [3]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p3_templates_item_0 : (⟨0, 1, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_1 : (⟨0, 1, [[2, 3, 4, 5, 6]], [], [], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_2 : (⟨0, 2, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_4 : (⟨0, 3, [], [], [2], 3, 5⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_5 : (⟨0, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_6 : (⟨0, 4, [], [], [3, 2], 2, 4⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_7 : (⟨0, 5, [], [], [4, 3, 2], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_8 : (⟨0, 5, [], [], [6], 3, 5⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_9 : (⟨0, 6, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_10 : (⟨0, 6, [], [], [5, 4, 3, 2], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_11 : (⟨1, 2, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_12 : (⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_13 : (⟨1, 3, [], [], [2], 3, 5⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_14 : (⟨1, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_15 : (⟨1, 4, [], [], [3, 2], 2, 4⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_16 : (⟨1, 5, [], [], [4, 3, 2], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_17 : (⟨1, 6, [], [], [], 4, 6⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_18 : (⟨1, 6, [], [], [5, 4, 3, 2], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_19 : (⟨2, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_20 : (⟨2, 4, [], [], [5, 6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_21 : (⟨2, 5, [], [], [6], 3, 5⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_22 : (⟨3, 4, [], [2], [5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_23 : (⟨3, 5, [], [2], [6], 2, 4⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_24 : (⟨4, 5, [], [2, 3], [6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_templates_item_25 : (⟨5, 6, [], [2, 3, 4], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p3_part_3 : ∀ T ∈ k7t4p3.templates, T.Check k7t4p3.graph k7t4p3.clique 7 (patternAmount ([[], [], [3]] : List (List ℕ))) (([[], [], [3]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p3_templates_item_0, k7t4p3_templates_item_1, k7t4p3_templates_item_2, k7t4p3_templates_item_3, k7t4p3_templates_item_4, k7t4p3_templates_item_5, k7t4p3_templates_item_6, k7t4p3_templates_item_7, k7t4p3_templates_item_8, k7t4p3_templates_item_9, k7t4p3_templates_item_10, k7t4p3_templates_item_11, k7t4p3_templates_item_12, k7t4p3_templates_item_13, k7t4p3_templates_item_14, k7t4p3_templates_item_15, k7t4p3_templates_item_16, k7t4p3_templates_item_17, k7t4p3_templates_item_18, k7t4p3_templates_item_19, k7t4p3_templates_item_20, k7t4p3_templates_item_21, k7t4p3_templates_item_22, k7t4p3_templates_item_23, k7t4p3_templates_item_24, k7t4p3_templates_item_25⟩

private theorem k7t4p3_required_item_0 : (⟨3, 5, [4]⟩ : RequiredPathData (Fin 7)).Check k7t4p3.graph 7 := by decide

private theorem k7t4p3_part_4 : ∀ p ∈ k7t4p3.required, p.Check k7t4p3.graph 7 := by
  simp only [k7t4p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact k7t4p3_required_item_0

private theorem k7t4p3_part_5 : ClosureCheck k7t4p3.graph (k7t4p3.initialMatrix 7) 7 4 k7t4p3.closure := by
  rw [k7t4p3_initial_eq]
  exact k7t4p3_closure_0

private theorem k7t4p3_part_6 : k7t4p3.bad.Check k7t4p3.graph (k7t4p3.matrix 7) 7 4 := by
  rw [k7t4p3_matrix_eq]
  decide

theorem k7t4p3_check : k7t4p3.Check 7 4 [[], [], [3]] :=
  ⟨k7t4p3_part_0, k7t4p3_part_1, k7t4p3_part_2, k7t4p3_part_3, k7t4p3_part_4, k7t4p3_part_5, k7t4p3_part_6⟩
def k7t4p4 : LayoutCertificate 6 where
  chains := [[0], [1, 2, 3, 4, 5]]
  clique := {0, 1, 3, 5}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩,
    ⟨0, 2, [], [], [1], 1, 5⟩,
    ⟨0, 4, [], [], [3], 1, 5⟩,
    ⟨0, 5, [], [], [], 2, 6⟩,
    ⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩,
    ⟨1, 2, [], [], [3], 1, 5⟩,
    ⟨1, 4, [], [], [3], 1, 5⟩,
    ⟨2, 3, [], [1], [], 1, 5⟩,
    ⟨2, 4, [], [1], [3], 1, 4⟩,
    ⟨2, 5, [], [1], [], 1, 5⟩,
    ⟨3, 4, [], [], [5], 1, 5⟩,
    ⟨4, 5, [], [3], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (2, 2), (4, 2), (1, 3)}⟩


private def k7t4p4_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5, ∅, Finset.Icc 1 5],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p4_initial_eq_row_0 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 0 j = k7t4p4_state_0 0 j := by decide

private theorem k7t4p4_initial_eq_row_1 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 1 j = k7t4p4_state_0 1 j := by decide

private theorem k7t4p4_initial_eq_row_2 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 2 j = k7t4p4_state_0 2 j := by decide

private theorem k7t4p4_initial_eq_row_3 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 3 j = k7t4p4_state_0 3 j := by decide

private theorem k7t4p4_initial_eq_row_4 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 4 j = k7t4p4_state_0 4 j := by decide

private theorem k7t4p4_initial_eq_row_5 : ∀ j : Fin 6, (k7t4p4.initialMatrix 7) 5 j = k7t4p4_state_0 5 j := by decide

private theorem k7t4p4_initial_eq : (k7t4p4.initialMatrix 7) = k7t4p4_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p4_initial_eq_row_0 j

  · exact k7t4p4_initial_eq_row_1 j

  · exact k7t4p4_initial_eq_row_2 j

  · exact k7t4p4_initial_eq_row_3 j

  · exact k7t4p4_initial_eq_row_4 j

  · exact k7t4p4_initial_eq_row_5 j

private theorem k7t4p4_closure_0 : ClosureCheck k7t4p4.graph k7t4p4_state_0 7 4 [] := by trivial

private theorem k7t4p4_matrix_eq : k7t4p4.matrix 7 = k7t4p4_state_0 := by
  change closureMatrix (k7t4p4.initialMatrix 7) _ = _
  rw [k7t4p4_initial_eq]
  change closureMatrix k7t4p4_state_0 [] = _
  rfl

private theorem k7t4p4_part_0 : k7t4p4.chains.flatten = List.finRange _ := by decide

private theorem k7t4p4_part_1 : k7t4p4.chains.map List.length = ([[], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p4_part_2 : k7t4p4.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p4.clique))) = ([[], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p4_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_2 : (⟨0, 2, [], [], [1], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_3 : (⟨0, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_4 : (⟨0, 5, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_5 : (⟨0, 5, [], [], [4, 3, 2, 1], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_6 : (⟨1, 2, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_7 : (⟨1, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_8 : (⟨2, 3, [], [1], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_9 : (⟨2, 4, [], [1], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_10 : (⟨2, 5, [], [1], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_11 : (⟨3, 4, [], [], [5], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_templates_item_12 : (⟨4, 5, [], [3], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p4_part_3 : ∀ T ∈ k7t4p4.templates, T.Check k7t4p4.graph k7t4p4.clique 7 (patternAmount ([[], [1, 1]] : List (List ℕ))) (([[], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p4_templates_item_0, k7t4p4_templates_item_1, k7t4p4_templates_item_2, k7t4p4_templates_item_3, k7t4p4_templates_item_4, k7t4p4_templates_item_5, k7t4p4_templates_item_6, k7t4p4_templates_item_7, k7t4p4_templates_item_8, k7t4p4_templates_item_9, k7t4p4_templates_item_10, k7t4p4_templates_item_11, k7t4p4_templates_item_12⟩

private theorem k7t4p4_part_4 : ∀ p ∈ k7t4p4.required, p.Check k7t4p4.graph 7 := by decide

private theorem k7t4p4_part_5 : ClosureCheck k7t4p4.graph (k7t4p4.initialMatrix 7) 7 4 k7t4p4.closure := by
  rw [k7t4p4_initial_eq]
  exact k7t4p4_closure_0

private theorem k7t4p4_part_6 : k7t4p4.bad.Check k7t4p4.graph (k7t4p4.matrix 7) 7 4 := by
  rw [k7t4p4_matrix_eq]
  decide

theorem k7t4p4_check : k7t4p4.Check 7 4 [[], [1, 1]] :=
  ⟨k7t4p4_part_0, k7t4p4_part_1, k7t4p4_part_2, k7t4p4_part_3, k7t4p4_part_4, k7t4p4_part_5, k7t4p4_part_6⟩
def k7t4p5 : LayoutCertificate 7 where
  chains := [[0], [1, 2, 3, 4, 5, 6]]
  clique := {0, 1, 3, 6}
  templates := [⟨0, 1, [], [], [], 3, 6⟩,
    ⟨0, 1, [[3, 4, 5, 6]], [], [], 2, 2⟩,
    ⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩,
    ⟨0, 2, [], [], [1], 2, 5⟩,
    ⟨0, 2, [[3, 4, 5, 6]], [], [1], 1, 1⟩,
    ⟨0, 4, [], [], [3], 2, 5⟩,
    ⟨0, 4, [], [], [5, 6], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3], 1, 4⟩,
    ⟨0, 6, [], [], [5, 4, 3], 2, 3⟩,
    ⟨0, 6, [], [], [5, 4, 3, 2, 1], 1, 1⟩,
    ⟨1, 2, [], [], [3], 2, 5⟩,
    ⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨1, 4, [], [], [3], 2, 5⟩,
    ⟨1, 4, [], [], [5, 6], 1, 4⟩,
    ⟨1, 5, [], [], [4, 3], 1, 4⟩,
    ⟨2, 3, [], [1], [4, 5, 6], 1, 2⟩,
    ⟨2, 4, [], [1], [3], 1, 4⟩,
    ⟨2, 5, [], [1], [4, 3], 1, 3⟩,
    ⟨2, 6, [], [1], [5, 4, 3], 1, 2⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 2)}⟩


private def k7t4p5_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, {1, 2}, Finset.Icc 1 4, {1, 2, 3}, {1, 2}],
    #[∅, ∅, {1, 2}, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, {1, 2, 3}, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, ∅, {1, 2}, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p5_initial_eq_row_0 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 0 j = k7t4p5_state_0 0 j := by decide

private theorem k7t4p5_initial_eq_row_1 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 1 j = k7t4p5_state_0 1 j := by decide

private theorem k7t4p5_initial_eq_row_2 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 2 j = k7t4p5_state_0 2 j := by decide

private theorem k7t4p5_initial_eq_row_3 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 3 j = k7t4p5_state_0 3 j := by decide

private theorem k7t4p5_initial_eq_row_4 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 4 j = k7t4p5_state_0 4 j := by decide

private theorem k7t4p5_initial_eq_row_5 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 5 j = k7t4p5_state_0 5 j := by decide

private theorem k7t4p5_initial_eq_row_6 : ∀ j : Fin 7, (k7t4p5.initialMatrix 7) 6 j = k7t4p5_state_0 6 j := by decide

private theorem k7t4p5_initial_eq : (k7t4p5.initialMatrix 7) = k7t4p5_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p5_initial_eq_row_0 j

  · exact k7t4p5_initial_eq_row_1 j

  · exact k7t4p5_initial_eq_row_2 j

  · exact k7t4p5_initial_eq_row_3 j

  · exact k7t4p5_initial_eq_row_4 j

  · exact k7t4p5_initial_eq_row_5 j

  · exact k7t4p5_initial_eq_row_6 j

private theorem k7t4p5_closure_0 : ClosureCheck k7t4p5.graph k7t4p5_state_0 7 4 [] := by trivial

private theorem k7t4p5_matrix_eq : k7t4p5.matrix 7 = k7t4p5_state_0 := by
  change closureMatrix (k7t4p5.initialMatrix 7) _ = _
  rw [k7t4p5_initial_eq]
  change closureMatrix k7t4p5_state_0 [] = _
  rfl

private theorem k7t4p5_part_0 : k7t4p5.chains.flatten = List.finRange _ := by decide

private theorem k7t4p5_part_1 : k7t4p5.chains.map List.length = ([[], [1, 2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p5_part_2 : k7t4p5.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p5.clique))) = ([[], [1, 2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p5_templates_item_0 : (⟨0, 1, [], [], [], 3, 6⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_1 : (⟨0, 1, [[3, 4, 5, 6]], [], [], 2, 2⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_2 : (⟨0, 1, [], [], [2, 3, 4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_3 : (⟨0, 2, [], [], [1], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_4 : (⟨0, 2, [[3, 4, 5, 6]], [], [1], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_5 : (⟨0, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_6 : (⟨0, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_7 : (⟨0, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_8 : (⟨0, 6, [], [], [5, 4, 3], 2, 3⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_9 : (⟨0, 6, [], [], [5, 4, 3, 2, 1], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_10 : (⟨1, 2, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_11 : (⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_12 : (⟨1, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_13 : (⟨1, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_14 : (⟨1, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_15 : (⟨2, 3, [], [1], [4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_16 : (⟨2, 4, [], [1], [3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_17 : (⟨2, 5, [], [1], [4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_templates_item_18 : (⟨2, 6, [], [1], [5, 4, 3], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p5_part_3 : ∀ T ∈ k7t4p5.templates, T.Check k7t4p5.graph k7t4p5.clique 7 (patternAmount ([[], [1, 2]] : List (List ℕ))) (([[], [1, 2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p5_templates_item_0, k7t4p5_templates_item_1, k7t4p5_templates_item_2, k7t4p5_templates_item_3, k7t4p5_templates_item_4, k7t4p5_templates_item_5, k7t4p5_templates_item_6, k7t4p5_templates_item_7, k7t4p5_templates_item_8, k7t4p5_templates_item_9, k7t4p5_templates_item_10, k7t4p5_templates_item_11, k7t4p5_templates_item_12, k7t4p5_templates_item_13, k7t4p5_templates_item_14, k7t4p5_templates_item_15, k7t4p5_templates_item_16, k7t4p5_templates_item_17, k7t4p5_templates_item_18⟩

private theorem k7t4p5_part_4 : ∀ p ∈ k7t4p5.required, p.Check k7t4p5.graph 7 := by decide

private theorem k7t4p5_part_5 : ClosureCheck k7t4p5.graph (k7t4p5.initialMatrix 7) 7 4 k7t4p5.closure := by
  rw [k7t4p5_initial_eq]
  exact k7t4p5_closure_0

private theorem k7t4p5_part_6 : k7t4p5.bad.Check k7t4p5.graph (k7t4p5.matrix 7) 7 4 := by
  rw [k7t4p5_matrix_eq]
  decide

theorem k7t4p5_check : k7t4p5.Check 7 4 [[], [1, 2]] :=
  ⟨k7t4p5_part_0, k7t4p5_part_1, k7t4p5_part_2, k7t4p5_part_3, k7t4p5_part_4, k7t4p5_part_5, k7t4p5_part_6⟩
def k7t4p6 : LayoutCertificate 6 where
  chains := [[0, 1, 2], [3, 4, 5]]
  clique := {0, 2, 3, 5}
  templates := [⟨0, 1, [], [], [2], 1, 5⟩,
    ⟨0, 3, [], [], [], 2, 6⟩,
    ⟨0, 3, [], [2, 1], [4, 5], 1, 2⟩,
    ⟨0, 4, [], [], [3], 1, 5⟩,
    ⟨0, 5, [], [], [], 2, 6⟩,
    ⟨0, 5, [], [2, 1], [4, 3], 1, 2⟩,
    ⟨1, 2, [], [0], [], 1, 5⟩,
    ⟨1, 3, [], [0], [], 1, 5⟩,
    ⟨1, 4, [], [0], [3], 1, 4⟩,
    ⟨1, 5, [], [0], [], 1, 5⟩,
    ⟨2, 3, [], [], [], 2, 6⟩,
    ⟨2, 3, [], [0, 1], [4, 5], 1, 2⟩,
    ⟨3, 4, [], [], [5], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (3, 3), (1, 2)}⟩


private def k7t4p6_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 6, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 5, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p6_initial_eq_row_0 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 0 j = k7t4p6_state_0 0 j := by decide

private theorem k7t4p6_initial_eq_row_1 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 1 j = k7t4p6_state_0 1 j := by decide

private theorem k7t4p6_initial_eq_row_2 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 2 j = k7t4p6_state_0 2 j := by decide

private theorem k7t4p6_initial_eq_row_3 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 3 j = k7t4p6_state_0 3 j := by decide

private theorem k7t4p6_initial_eq_row_4 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 4 j = k7t4p6_state_0 4 j := by decide

private theorem k7t4p6_initial_eq_row_5 : ∀ j : Fin 6, (k7t4p6.initialMatrix 7) 5 j = k7t4p6_state_0 5 j := by decide

private theorem k7t4p6_initial_eq : (k7t4p6.initialMatrix 7) = k7t4p6_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p6_initial_eq_row_0 j

  · exact k7t4p6_initial_eq_row_1 j

  · exact k7t4p6_initial_eq_row_2 j

  · exact k7t4p6_initial_eq_row_3 j

  · exact k7t4p6_initial_eq_row_4 j

  · exact k7t4p6_initial_eq_row_5 j

private theorem k7t4p6_closure_0 : ClosureCheck k7t4p6.graph k7t4p6_state_0 7 4 [] := by trivial

private theorem k7t4p6_matrix_eq : k7t4p6.matrix 7 = k7t4p6_state_0 := by
  change closureMatrix (k7t4p6.initialMatrix 7) _ = _
  rw [k7t4p6_initial_eq]
  change closureMatrix k7t4p6_state_0 [] = _
  rfl

private theorem k7t4p6_part_0 : k7t4p6.chains.flatten = List.finRange _ := by decide

private theorem k7t4p6_part_1 : k7t4p6.chains.map List.length = ([[1], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p6_part_2 : k7t4p6.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p6.clique))) = ([[1], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p6_templates_item_0 : (⟨0, 1, [], [], [2], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_1 : (⟨0, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_2 : (⟨0, 3, [], [2, 1], [4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_3 : (⟨0, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_4 : (⟨0, 5, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_5 : (⟨0, 5, [], [2, 1], [4, 3], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_6 : (⟨1, 2, [], [0], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_7 : (⟨1, 3, [], [0], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_8 : (⟨1, 4, [], [0], [3], 1, 4⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_9 : (⟨1, 5, [], [0], [], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_10 : (⟨2, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_11 : (⟨2, 3, [], [0, 1], [4, 5], 1, 2⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_templates_item_12 : (⟨3, 4, [], [], [5], 1, 5⟩ : TemplateData (Fin 6)).Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p6_part_3 : ∀ T ∈ k7t4p6.templates, T.Check k7t4p6.graph k7t4p6.clique 7 (patternAmount ([[1], [1]] : List (List ℕ))) (([[1], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p6_templates_item_0, k7t4p6_templates_item_1, k7t4p6_templates_item_2, k7t4p6_templates_item_3, k7t4p6_templates_item_4, k7t4p6_templates_item_5, k7t4p6_templates_item_6, k7t4p6_templates_item_7, k7t4p6_templates_item_8, k7t4p6_templates_item_9, k7t4p6_templates_item_10, k7t4p6_templates_item_11, k7t4p6_templates_item_12⟩

private theorem k7t4p6_part_4 : ∀ p ∈ k7t4p6.required, p.Check k7t4p6.graph 7 := by decide

private theorem k7t4p6_part_5 : ClosureCheck k7t4p6.graph (k7t4p6.initialMatrix 7) 7 4 k7t4p6.closure := by
  rw [k7t4p6_initial_eq]
  exact k7t4p6_closure_0

private theorem k7t4p6_part_6 : k7t4p6.bad.Check k7t4p6.graph (k7t4p6.matrix 7) 7 4 := by
  rw [k7t4p6_matrix_eq]
  decide

theorem k7t4p6_check : k7t4p6.Check 7 4 [[1], [1]] :=
  ⟨k7t4p6_part_0, k7t4p6_part_1, k7t4p6_part_2, k7t4p6_part_3, k7t4p6_part_4, k7t4p6_part_5, k7t4p6_part_6⟩
def k7t4p7 : LayoutCertificate 7 where
  chains := [[0, 1, 2], [3, 4, 5, 6]]
  clique := {0, 2, 3, 6}
  templates := [⟨0, 1, [], [], [2], 2, 5⟩,
    ⟨0, 1, [[3, 4, 5, 6]], [], [2], 1, 1⟩,
    ⟨0, 3, [], [], [], 3, 6⟩,
    ⟨0, 3, [], [], [4, 5, 6], 2, 3⟩,
    ⟨0, 3, [], [2, 1], [4, 5, 6], 1, 1⟩,
    ⟨0, 4, [], [], [3], 2, 5⟩,
    ⟨0, 4, [], [], [5, 6], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3], 1, 4⟩,
    ⟨0, 6, [], [], [5, 4, 3], 2, 3⟩,
    ⟨0, 6, [], [2, 1], [5, 4, 3], 1, 1⟩,
    ⟨1, 2, [[3, 4, 5, 6]], [0], [], 1, 1⟩,
    ⟨1, 3, [], [0], [], 2, 5⟩,
    ⟨1, 3, [], [0], [4, 5, 6], 1, 2⟩,
    ⟨1, 4, [], [0], [3], 1, 4⟩,
    ⟨1, 5, [], [0], [4, 3], 1, 3⟩,
    ⟨1, 6, [], [0], [5, 4, 3], 1, 2⟩,
    ⟨2, 3, [], [], [4, 5, 6], 2, 3⟩,
    ⟨2, 3, [], [0, 1], [4, 5, 6], 1, 1⟩,
    ⟨3, 4, [], [], [5, 6], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 2), (3, 3)}⟩


private def k7t4p7_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 5, ∅, {1}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, {1, 2}],
    #[∅, {1}, ∅, {1, 2, 3}, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 5, {1, 2, 3}, ∅, Finset.Icc 1 4, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, ∅, Finset.Icc 1 4, ∅, ∅, ∅],
    #[Finset.Icc 1 4, {1, 2, 3}, ∅, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2}, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p7_initial_eq_row_0 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 0 j = k7t4p7_state_0 0 j := by decide

private theorem k7t4p7_initial_eq_row_1 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 1 j = k7t4p7_state_0 1 j := by decide

private theorem k7t4p7_initial_eq_row_2 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 2 j = k7t4p7_state_0 2 j := by decide

private theorem k7t4p7_initial_eq_row_3 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 3 j = k7t4p7_state_0 3 j := by decide

private theorem k7t4p7_initial_eq_row_4 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 4 j = k7t4p7_state_0 4 j := by decide

private theorem k7t4p7_initial_eq_row_5 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 5 j = k7t4p7_state_0 5 j := by decide

private theorem k7t4p7_initial_eq_row_6 : ∀ j : Fin 7, (k7t4p7.initialMatrix 7) 6 j = k7t4p7_state_0 6 j := by decide

private theorem k7t4p7_initial_eq : (k7t4p7.initialMatrix 7) = k7t4p7_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p7_initial_eq_row_0 j

  · exact k7t4p7_initial_eq_row_1 j

  · exact k7t4p7_initial_eq_row_2 j

  · exact k7t4p7_initial_eq_row_3 j

  · exact k7t4p7_initial_eq_row_4 j

  · exact k7t4p7_initial_eq_row_5 j

  · exact k7t4p7_initial_eq_row_6 j

private theorem k7t4p7_closure_0 : ClosureCheck k7t4p7.graph k7t4p7_state_0 7 4 [] := by trivial

private theorem k7t4p7_matrix_eq : k7t4p7.matrix 7 = k7t4p7_state_0 := by
  change closureMatrix (k7t4p7.initialMatrix 7) _ = _
  rw [k7t4p7_initial_eq]
  change closureMatrix k7t4p7_state_0 [] = _
  rfl

private theorem k7t4p7_part_0 : k7t4p7.chains.flatten = List.finRange _ := by decide

private theorem k7t4p7_part_1 : k7t4p7.chains.map List.length = ([[1], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p7_part_2 : k7t4p7.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p7.clique))) = ([[1], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p7_templates_item_0 : (⟨0, 1, [], [], [2], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_1 : (⟨0, 1, [[3, 4, 5, 6]], [], [2], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_2 : (⟨0, 3, [], [], [], 3, 6⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_3 : (⟨0, 3, [], [], [4, 5, 6], 2, 3⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_4 : (⟨0, 3, [], [2, 1], [4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_5 : (⟨0, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_6 : (⟨0, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_7 : (⟨0, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_8 : (⟨0, 6, [], [], [5, 4, 3], 2, 3⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_9 : (⟨0, 6, [], [2, 1], [5, 4, 3], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_10 : (⟨1, 2, [[3, 4, 5, 6]], [0], [], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_11 : (⟨1, 3, [], [0], [], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_12 : (⟨1, 3, [], [0], [4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_13 : (⟨1, 4, [], [0], [3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_14 : (⟨1, 5, [], [0], [4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_15 : (⟨1, 6, [], [0], [5, 4, 3], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_16 : (⟨2, 3, [], [], [4, 5, 6], 2, 3⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_17 : (⟨2, 3, [], [0, 1], [4, 5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_templates_item_18 : (⟨3, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p7_part_3 : ∀ T ∈ k7t4p7.templates, T.Check k7t4p7.graph k7t4p7.clique 7 (patternAmount ([[1], [2]] : List (List ℕ))) (([[1], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p7_templates_item_0, k7t4p7_templates_item_1, k7t4p7_templates_item_2, k7t4p7_templates_item_3, k7t4p7_templates_item_4, k7t4p7_templates_item_5, k7t4p7_templates_item_6, k7t4p7_templates_item_7, k7t4p7_templates_item_8, k7t4p7_templates_item_9, k7t4p7_templates_item_10, k7t4p7_templates_item_11, k7t4p7_templates_item_12, k7t4p7_templates_item_13, k7t4p7_templates_item_14, k7t4p7_templates_item_15, k7t4p7_templates_item_16, k7t4p7_templates_item_17, k7t4p7_templates_item_18⟩

private theorem k7t4p7_part_4 : ∀ p ∈ k7t4p7.required, p.Check k7t4p7.graph 7 := by decide

private theorem k7t4p7_part_5 : ClosureCheck k7t4p7.graph (k7t4p7.initialMatrix 7) 7 4 k7t4p7.closure := by
  rw [k7t4p7_initial_eq]
  exact k7t4p7_closure_0

private theorem k7t4p7_part_6 : k7t4p7.bad.Check k7t4p7.graph (k7t4p7.matrix 7) 7 4 := by
  rw [k7t4p7_matrix_eq]
  decide

theorem k7t4p7_check : k7t4p7.Check 7 4 [[1], [2]] :=
  ⟨k7t4p7_part_0, k7t4p7_part_1, k7t4p7_part_2, k7t4p7_part_3, k7t4p7_part_4, k7t4p7_part_5, k7t4p7_part_6⟩
def k7t4p8 : LayoutCertificate 7 where
  chains := [[0, 1, 2, 3, 4, 5, 6]]
  clique := {0, 2, 4, 6}
  templates := [⟨0, 1, [], [], [2], 2, 5⟩,
    ⟨0, 1, [], [], [2, 3, 4], 1, 3⟩,
    ⟨0, 3, [], [], [2], 2, 5⟩,
    ⟨0, 3, [], [2, 1], [4], 1, 3⟩,
    ⟨0, 5, [], [], [4], 2, 5⟩,
    ⟨0, 5, [], [2, 1], [4], 1, 3⟩,
    ⟨1, 2, [], [0], [3, 4], 1, 3⟩,
    ⟨1, 3, [], [0], [2], 1, 4⟩,
    ⟨1, 4, [], [0], [3, 2], 1, 3⟩,
    ⟨1, 5, [], [0], [4], 1, 4⟩,
    ⟨1, 6, [[2, 3, 4]], [0], [], 1, 2⟩,
    ⟨2, 3, [], [0, 1], [4], 1, 3⟩,
    ⟨2, 5, [], [0, 1], [4], 1, 3⟩,
    ⟨3, 4, [], [0, 1, 2], [], 1, 3⟩,
    ⟨3, 5, [], [2], [4], 1, 4⟩,
    ⟨3, 6, [], [0, 1, 2], [], 1, 3⟩,
    ⟨4, 5, [[0, 1, 2]], [], [6], 1, 2⟩,
    ⟨5, 6, [[0, 1, 2]], [4], [], 1, 2⟩]
  required := []
  closure := []
  bad := ⟨none, {(1, 2), (3, 2), (5, 2), (0, 3)}⟩


private def k7t4p8_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, ∅, {1, 2, 3}, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 4, {1, 2}],
    #[∅, {1, 2, 3}, ∅, {1, 2, 3}, ∅, {1, 2, 3}, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, ∅, {1, 2, 3}, Finset.Icc 1 4, {1, 2, 3}],
    #[∅, {1, 2, 3}, ∅, {1, 2, 3}, ∅, {1, 2}, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}, Finset.Icc 1 4, {1, 2}, ∅, {1, 2}],
    #[∅, {1, 2}, ∅, {1, 2, 3}, ∅, {1, 2}, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t4p8_initial_eq_row_0 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 0 j = k7t4p8_state_0 0 j := by decide

private theorem k7t4p8_initial_eq_row_1 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 1 j = k7t4p8_state_0 1 j := by decide

private theorem k7t4p8_initial_eq_row_2 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 2 j = k7t4p8_state_0 2 j := by decide

private theorem k7t4p8_initial_eq_row_3 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 3 j = k7t4p8_state_0 3 j := by decide

private theorem k7t4p8_initial_eq_row_4 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 4 j = k7t4p8_state_0 4 j := by decide

private theorem k7t4p8_initial_eq_row_5 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 5 j = k7t4p8_state_0 5 j := by decide

private theorem k7t4p8_initial_eq_row_6 : ∀ j : Fin 7, (k7t4p8.initialMatrix 7) 6 j = k7t4p8_state_0 6 j := by decide

private theorem k7t4p8_initial_eq : (k7t4p8.initialMatrix 7) = k7t4p8_state_0 := by
  funext i j
  fin_cases i

  · exact k7t4p8_initial_eq_row_0 j

  · exact k7t4p8_initial_eq_row_1 j

  · exact k7t4p8_initial_eq_row_2 j

  · exact k7t4p8_initial_eq_row_3 j

  · exact k7t4p8_initial_eq_row_4 j

  · exact k7t4p8_initial_eq_row_5 j

  · exact k7t4p8_initial_eq_row_6 j

private theorem k7t4p8_closure_0 : ClosureCheck k7t4p8.graph k7t4p8_state_0 7 4 [] := by trivial

private theorem k7t4p8_matrix_eq : k7t4p8.matrix 7 = k7t4p8_state_0 := by
  change closureMatrix (k7t4p8.initialMatrix 7) _ = _
  rw [k7t4p8_initial_eq]
  change closureMatrix k7t4p8_state_0 [] = _
  rfl

private theorem k7t4p8_part_0 : k7t4p8.chains.flatten = List.finRange _ := by decide

private theorem k7t4p8_part_1 : k7t4p8.chains.map List.length = ([[1, 1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t4p8_part_2 : k7t4p8.chains.map (fun l => l.map (fun i => decide (i ∈ k7t4p8.clique))) = ([[1, 1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t4p8_templates_item_0 : (⟨0, 1, [], [], [2], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_1 : (⟨0, 1, [], [], [2, 3, 4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_2 : (⟨0, 3, [], [], [2], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_3 : (⟨0, 3, [], [2, 1], [4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_4 : (⟨0, 5, [], [], [4], 2, 5⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_5 : (⟨0, 5, [], [2, 1], [4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_6 : (⟨1, 2, [], [0], [3, 4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_7 : (⟨1, 3, [], [0], [2], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_8 : (⟨1, 4, [], [0], [3, 2], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_9 : (⟨1, 5, [], [0], [4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_10 : (⟨1, 6, [[2, 3, 4]], [0], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_11 : (⟨2, 3, [], [0, 1], [4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_12 : (⟨2, 5, [], [0, 1], [4], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_13 : (⟨3, 4, [], [0, 1, 2], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_14 : (⟨3, 5, [], [2], [4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_15 : (⟨3, 6, [], [0, 1, 2], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_16 : (⟨4, 5, [[0, 1, 2]], [], [6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_templates_item_17 : (⟨5, 6, [[0, 1, 2]], [4], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t4p8_part_3 : ∀ T ∈ k7t4p8.templates, T.Check k7t4p8.graph k7t4p8.clique 7 (patternAmount ([[1, 1, 1]] : List (List ℕ))) (([[1, 1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t4p8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t4p8_templates_item_0, k7t4p8_templates_item_1, k7t4p8_templates_item_2, k7t4p8_templates_item_3, k7t4p8_templates_item_4, k7t4p8_templates_item_5, k7t4p8_templates_item_6, k7t4p8_templates_item_7, k7t4p8_templates_item_8, k7t4p8_templates_item_9, k7t4p8_templates_item_10, k7t4p8_templates_item_11, k7t4p8_templates_item_12, k7t4p8_templates_item_13, k7t4p8_templates_item_14, k7t4p8_templates_item_15, k7t4p8_templates_item_16, k7t4p8_templates_item_17⟩

private theorem k7t4p8_part_4 : ∀ p ∈ k7t4p8.required, p.Check k7t4p8.graph 7 := by decide

private theorem k7t4p8_part_5 : ClosureCheck k7t4p8.graph (k7t4p8.initialMatrix 7) 7 4 k7t4p8.closure := by
  rw [k7t4p8_initial_eq]
  exact k7t4p8_closure_0

private theorem k7t4p8_part_6 : k7t4p8.bad.Check k7t4p8.graph (k7t4p8.matrix 7) 7 4 := by
  rw [k7t4p8_matrix_eq]
  decide

theorem k7t4p8_check : k7t4p8.Check 7 4 [[1, 1, 1]] :=
  ⟨k7t4p8_part_0, k7t4p8_part_1, k7t4p8_part_2, k7t4p8_part_3, k7t4p8_part_4, k7t4p8_part_5, k7t4p8_part_6⟩
def k7t5p0 : LayoutCertificate 5 where
  chains := [[0], [1], [2], [3], [4]]
  clique := {0, 1, 2, 3, 4}
  templates := [⟨0, 1, [], [], [], 1, 6⟩,
    ⟨0, 2, [], [], [], 1, 6⟩,
    ⟨0, 3, [], [], [], 1, 6⟩,
    ⟨0, 4, [], [], [], 1, 6⟩,
    ⟨1, 2, [], [], [], 1, 6⟩,
    ⟨1, 3, [], [], [], 1, 6⟩,
    ⟨1, 4, [], [], [], 1, 6⟩,
    ⟨2, 3, [], [], [], 1, 6⟩,
    ⟨2, 4, [], [], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t5p0_state_0 : ForbiddenMatrix 5 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t5p0_initial_eq_row_0 : ∀ j : Fin 5, (k7t5p0.initialMatrix 7) 0 j = k7t5p0_state_0 0 j := by decide

private theorem k7t5p0_initial_eq_row_1 : ∀ j : Fin 5, (k7t5p0.initialMatrix 7) 1 j = k7t5p0_state_0 1 j := by decide

private theorem k7t5p0_initial_eq_row_2 : ∀ j : Fin 5, (k7t5p0.initialMatrix 7) 2 j = k7t5p0_state_0 2 j := by decide

private theorem k7t5p0_initial_eq_row_3 : ∀ j : Fin 5, (k7t5p0.initialMatrix 7) 3 j = k7t5p0_state_0 3 j := by decide

private theorem k7t5p0_initial_eq_row_4 : ∀ j : Fin 5, (k7t5p0.initialMatrix 7) 4 j = k7t5p0_state_0 4 j := by decide

private theorem k7t5p0_initial_eq : (k7t5p0.initialMatrix 7) = k7t5p0_state_0 := by
  funext i j
  fin_cases i

  · exact k7t5p0_initial_eq_row_0 j

  · exact k7t5p0_initial_eq_row_1 j

  · exact k7t5p0_initial_eq_row_2 j

  · exact k7t5p0_initial_eq_row_3 j

  · exact k7t5p0_initial_eq_row_4 j

private theorem k7t5p0_closure_0 : ClosureCheck k7t5p0.graph k7t5p0_state_0 7 5 [] := by trivial

private theorem k7t5p0_matrix_eq : k7t5p0.matrix 7 = k7t5p0_state_0 := by
  change closureMatrix (k7t5p0.initialMatrix 7) _ = _
  rw [k7t5p0_initial_eq]
  change closureMatrix k7t5p0_state_0 [] = _
  rfl

private theorem k7t5p0_part_0 : k7t5p0.chains.flatten = List.finRange _ := by decide

private theorem k7t5p0_part_1 : k7t5p0.chains.map List.length = ([[], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t5p0_part_2 : k7t5p0.chains.map (fun l => l.map (fun i => decide (i ∈ k7t5p0.clique))) = ([[], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k7t5p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_4 : (⟨1, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_5 : (⟨1, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_6 : (⟨1, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_7 : (⟨2, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_templates_item_8 : (⟨2, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 5)).Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p0_part_3 : ∀ T ∈ k7t5p0.templates, T.Check k7t5p0.graph k7t5p0.clique 7 (patternAmount ([[], [], [], [], []] : List (List ℕ))) (([[], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k7t5p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t5p0_templates_item_0, k7t5p0_templates_item_1, k7t5p0_templates_item_2, k7t5p0_templates_item_3, k7t5p0_templates_item_4, k7t5p0_templates_item_5, k7t5p0_templates_item_6, k7t5p0_templates_item_7, k7t5p0_templates_item_8⟩

private theorem k7t5p0_part_4 : ∀ p ∈ k7t5p0.required, p.Check k7t5p0.graph 7 := by decide

private theorem k7t5p0_part_5 : ClosureCheck k7t5p0.graph (k7t5p0.initialMatrix 7) 7 5 k7t5p0.closure := by
  rw [k7t5p0_initial_eq]
  exact k7t5p0_closure_0

private theorem k7t5p0_part_6 : k7t5p0.bad.Check k7t5p0.graph (k7t5p0.matrix 7) 7 5 := by
  rw [k7t5p0_matrix_eq]
  decide

theorem k7t5p0_check : k7t5p0.Check 7 5 [[], [], [], [], []] :=
  ⟨k7t5p0_part_0, k7t5p0_part_1, k7t5p0_part_2, k7t5p0_part_3, k7t5p0_part_4, k7t5p0_part_5, k7t5p0_part_6⟩
def k7t5p1 : LayoutCertificate 6 where
  chains := [[0], [1], [2], [3, 4, 5]]
  clique := {0, 1, 2, 3, 5}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [[3, 4, 5]], [], [], 1, 3⟩,
    ⟨0, 2, [], [], [], 2, 6⟩,
    ⟨0, 2, [[3, 4, 5]], [], [], 1, 3⟩,
    ⟨0, 3, [], [], [], 2, 6⟩,
    ⟨0, 3, [], [], [4, 5], 1, 4⟩,
    ⟨0, 4, [], [], [3], 1, 5⟩,
    ⟨0, 5, [], [], [], 2, 6⟩,
    ⟨0, 5, [], [], [4, 3], 1, 4⟩,
    ⟨1, 2, [], [], [], 2, 6⟩,
    ⟨1, 2, [[3, 4, 5]], [], [], 1, 3⟩,
    ⟨1, 3, [], [], [], 2, 6⟩,
    ⟨1, 3, [], [], [4, 5], 1, 4⟩,
    ⟨1, 4, [], [], [3], 1, 5⟩,
    ⟨1, 5, [], [], [], 2, 6⟩,
    ⟨1, 5, [], [], [4, 3], 1, 4⟩,
    ⟨2, 3, [], [], [], 2, 6⟩,
    ⟨2, 3, [], [], [4, 5], 1, 4⟩,
    ⟨2, 4, [], [], [3], 1, 5⟩,
    ⟨2, 5, [], [], [], 2, 6⟩,
    ⟨2, 5, [], [], [4, 3], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t5p1_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t5p1_initial_eq_row_0 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 0 j = k7t5p1_state_0 0 j := by decide

private theorem k7t5p1_initial_eq_row_1 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 1 j = k7t5p1_state_0 1 j := by decide

private theorem k7t5p1_initial_eq_row_2 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 2 j = k7t5p1_state_0 2 j := by decide

private theorem k7t5p1_initial_eq_row_3 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 3 j = k7t5p1_state_0 3 j := by decide

private theorem k7t5p1_initial_eq_row_4 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 4 j = k7t5p1_state_0 4 j := by decide

private theorem k7t5p1_initial_eq_row_5 : ∀ j : Fin 6, (k7t5p1.initialMatrix 7) 5 j = k7t5p1_state_0 5 j := by decide

private theorem k7t5p1_initial_eq : (k7t5p1.initialMatrix 7) = k7t5p1_state_0 := by
  funext i j
  fin_cases i

  · exact k7t5p1_initial_eq_row_0 j

  · exact k7t5p1_initial_eq_row_1 j

  · exact k7t5p1_initial_eq_row_2 j

  · exact k7t5p1_initial_eq_row_3 j

  · exact k7t5p1_initial_eq_row_4 j

  · exact k7t5p1_initial_eq_row_5 j

private theorem k7t5p1_closure_0 : ClosureCheck k7t5p1.graph k7t5p1_state_0 7 5 [] := by trivial

private theorem k7t5p1_matrix_eq : k7t5p1.matrix 7 = k7t5p1_state_0 := by
  change closureMatrix (k7t5p1.initialMatrix 7) _ = _
  rw [k7t5p1_initial_eq]
  change closureMatrix k7t5p1_state_0 [] = _
  rfl

private theorem k7t5p1_part_0 : k7t5p1.chains.flatten = List.finRange _ := by decide

private theorem k7t5p1_part_1 : k7t5p1.chains.map List.length = ([[], [], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t5p1_part_2 : k7t5p1.chains.map (fun l => l.map (fun i => decide (i ∈ k7t5p1.clique))) = ([[], [], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t5p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_1 : (⟨0, 1, [[3, 4, 5]], [], [], 1, 3⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_3 : (⟨0, 2, [[3, 4, 5]], [], [], 1, 3⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_4 : (⟨0, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_5 : (⟨0, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_6 : (⟨0, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_7 : (⟨0, 5, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_8 : (⟨0, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_9 : (⟨1, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_10 : (⟨1, 2, [[3, 4, 5]], [], [], 1, 3⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_11 : (⟨1, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_12 : (⟨1, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_13 : (⟨1, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_14 : (⟨1, 5, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_15 : (⟨1, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_16 : (⟨2, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_17 : (⟨2, 3, [], [], [4, 5], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_18 : (⟨2, 4, [], [], [3], 1, 5⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_19 : (⟨2, 5, [], [], [], 2, 6⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_templates_item_20 : (⟨2, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 6)).Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p1_part_3 : ∀ T ∈ k7t5p1.templates, T.Check k7t5p1.graph k7t5p1.clique 7 (patternAmount ([[], [], [], [1]] : List (List ℕ))) (([[], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t5p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t5p1_templates_item_0, k7t5p1_templates_item_1, k7t5p1_templates_item_2, k7t5p1_templates_item_3, k7t5p1_templates_item_4, k7t5p1_templates_item_5, k7t5p1_templates_item_6, k7t5p1_templates_item_7, k7t5p1_templates_item_8, k7t5p1_templates_item_9, k7t5p1_templates_item_10, k7t5p1_templates_item_11, k7t5p1_templates_item_12, k7t5p1_templates_item_13, k7t5p1_templates_item_14, k7t5p1_templates_item_15, k7t5p1_templates_item_16, k7t5p1_templates_item_17, k7t5p1_templates_item_18, k7t5p1_templates_item_19, k7t5p1_templates_item_20⟩

private theorem k7t5p1_part_4 : ∀ p ∈ k7t5p1.required, p.Check k7t5p1.graph 7 := by decide

private theorem k7t5p1_part_5 : ClosureCheck k7t5p1.graph (k7t5p1.initialMatrix 7) 7 5 k7t5p1.closure := by
  rw [k7t5p1_initial_eq]
  exact k7t5p1_closure_0

private theorem k7t5p1_part_6 : k7t5p1.bad.Check k7t5p1.graph (k7t5p1.matrix 7) 7 5 := by
  rw [k7t5p1_matrix_eq]
  decide

theorem k7t5p1_check : k7t5p1.Check 7 5 [[], [], [], [1]] :=
  ⟨k7t5p1_part_0, k7t5p1_part_1, k7t5p1_part_2, k7t5p1_part_3, k7t5p1_part_4, k7t5p1_part_5, k7t5p1_part_6⟩
def k7t5p2 : LayoutCertificate 7 where
  chains := [[0], [1], [2], [3, 4, 5, 6]]
  clique := {0, 1, 2, 3, 6}
  templates := [⟨0, 1, [], [], [], 3, 6⟩,
    ⟨0, 1, [[3, 4, 5, 6]], [], [], 1, 2⟩,
    ⟨0, 2, [], [], [], 3, 6⟩,
    ⟨0, 2, [[3, 4, 5, 6]], [], [], 1, 2⟩,
    ⟨0, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨0, 4, [], [], [3], 2, 5⟩,
    ⟨0, 4, [], [], [5, 6], 1, 4⟩,
    ⟨0, 5, [], [], [4, 3], 1, 4⟩,
    ⟨0, 6, [], [], [5, 4, 3], 1, 3⟩,
    ⟨1, 2, [], [], [], 3, 6⟩,
    ⟨1, 2, [[3, 4, 5, 6]], [], [], 1, 2⟩,
    ⟨1, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨1, 4, [], [], [3], 2, 5⟩,
    ⟨1, 4, [], [], [5, 6], 1, 4⟩,
    ⟨1, 5, [], [], [4, 3], 1, 4⟩,
    ⟨1, 6, [], [], [5, 4, 3], 1, 3⟩,
    ⟨2, 3, [], [], [4, 5, 6], 1, 3⟩,
    ⟨2, 4, [], [], [3], 2, 5⟩,
    ⟨2, 4, [], [], [5, 6], 1, 4⟩,
    ⟨2, 5, [], [], [4, 3], 1, 4⟩,
    ⟨2, 6, [], [], [5, 4, 3], 1, 3⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t5p2_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, {1, 2, 3}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, {1, 2, 3}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, {1, 2, 3}, Finset.Icc 1 5, Finset.Icc 1 4, {1, 2, 3}],
    #[{1, 2, 3}, {1, 2, 3}, {1, 2, 3}, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 4, Finset.Icc 1 4, Finset.Icc 1 4, ∅, ∅, ∅, ∅],
    #[{1, 2, 3}, {1, 2, 3}, {1, 2, 3}, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t5p2_initial_eq_row_0 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 0 j = k7t5p2_state_0 0 j := by decide

private theorem k7t5p2_initial_eq_row_1 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 1 j = k7t5p2_state_0 1 j := by decide

private theorem k7t5p2_initial_eq_row_2 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 2 j = k7t5p2_state_0 2 j := by decide

private theorem k7t5p2_initial_eq_row_3 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 3 j = k7t5p2_state_0 3 j := by decide

private theorem k7t5p2_initial_eq_row_4 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 4 j = k7t5p2_state_0 4 j := by decide

private theorem k7t5p2_initial_eq_row_5 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 5 j = k7t5p2_state_0 5 j := by decide

private theorem k7t5p2_initial_eq_row_6 : ∀ j : Fin 7, (k7t5p2.initialMatrix 7) 6 j = k7t5p2_state_0 6 j := by decide

private theorem k7t5p2_initial_eq : (k7t5p2.initialMatrix 7) = k7t5p2_state_0 := by
  funext i j
  fin_cases i

  · exact k7t5p2_initial_eq_row_0 j

  · exact k7t5p2_initial_eq_row_1 j

  · exact k7t5p2_initial_eq_row_2 j

  · exact k7t5p2_initial_eq_row_3 j

  · exact k7t5p2_initial_eq_row_4 j

  · exact k7t5p2_initial_eq_row_5 j

  · exact k7t5p2_initial_eq_row_6 j

private theorem k7t5p2_closure_0 : ClosureCheck k7t5p2.graph k7t5p2_state_0 7 5 [] := by trivial

private theorem k7t5p2_matrix_eq : k7t5p2.matrix 7 = k7t5p2_state_0 := by
  change closureMatrix (k7t5p2.initialMatrix 7) _ = _
  rw [k7t5p2_initial_eq]
  change closureMatrix k7t5p2_state_0 [] = _
  rfl

private theorem k7t5p2_part_0 : k7t5p2.chains.flatten = List.finRange _ := by decide

private theorem k7t5p2_part_1 : k7t5p2.chains.map List.length = ([[], [], [], [2]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t5p2_part_2 : k7t5p2.chains.map (fun l => l.map (fun i => decide (i ∈ k7t5p2.clique))) = ([[], [], [], [2]] : List (List ℕ)).map profileMask := by decide

private theorem k7t5p2_templates_item_0 : (⟨0, 1, [], [], [], 3, 6⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_1 : (⟨0, 1, [[3, 4, 5, 6]], [], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_2 : (⟨0, 2, [], [], [], 3, 6⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_3 : (⟨0, 2, [[3, 4, 5, 6]], [], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_4 : (⟨0, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_5 : (⟨0, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_6 : (⟨0, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_7 : (⟨0, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_8 : (⟨0, 6, [], [], [5, 4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_9 : (⟨1, 2, [], [], [], 3, 6⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_10 : (⟨1, 2, [[3, 4, 5, 6]], [], [], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_11 : (⟨1, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_12 : (⟨1, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_13 : (⟨1, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_14 : (⟨1, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_15 : (⟨1, 6, [], [], [5, 4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_16 : (⟨2, 3, [], [], [4, 5, 6], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_17 : (⟨2, 4, [], [], [3], 2, 5⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_18 : (⟨2, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_19 : (⟨2, 5, [], [], [4, 3], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_templates_item_20 : (⟨2, 6, [], [], [5, 4, 3], 1, 3⟩ : TemplateData (Fin 7)).Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p2_part_3 : ∀ T ∈ k7t5p2.templates, T.Check k7t5p2.graph k7t5p2.clique 7 (patternAmount ([[], [], [], [2]] : List (List ℕ))) (([[], [], [], [2]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t5p2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t5p2_templates_item_0, k7t5p2_templates_item_1, k7t5p2_templates_item_2, k7t5p2_templates_item_3, k7t5p2_templates_item_4, k7t5p2_templates_item_5, k7t5p2_templates_item_6, k7t5p2_templates_item_7, k7t5p2_templates_item_8, k7t5p2_templates_item_9, k7t5p2_templates_item_10, k7t5p2_templates_item_11, k7t5p2_templates_item_12, k7t5p2_templates_item_13, k7t5p2_templates_item_14, k7t5p2_templates_item_15, k7t5p2_templates_item_16, k7t5p2_templates_item_17, k7t5p2_templates_item_18, k7t5p2_templates_item_19, k7t5p2_templates_item_20⟩

private theorem k7t5p2_part_4 : ∀ p ∈ k7t5p2.required, p.Check k7t5p2.graph 7 := by decide

private theorem k7t5p2_part_5 : ClosureCheck k7t5p2.graph (k7t5p2.initialMatrix 7) 7 5 k7t5p2.closure := by
  rw [k7t5p2_initial_eq]
  exact k7t5p2_closure_0

private theorem k7t5p2_part_6 : k7t5p2.bad.Check k7t5p2.graph (k7t5p2.matrix 7) 7 5 := by
  rw [k7t5p2_matrix_eq]
  decide

theorem k7t5p2_check : k7t5p2.Check 7 5 [[], [], [], [2]] :=
  ⟨k7t5p2_part_0, k7t5p2_part_1, k7t5p2_part_2, k7t5p2_part_3, k7t5p2_part_4, k7t5p2_part_5, k7t5p2_part_6⟩
def k7t5p3 : LayoutCertificate 7 where
  chains := [[0], [1], [2, 3, 4, 5, 6]]
  clique := {0, 1, 2, 4, 6}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [[2, 3, 4, 5, 6]], [], [], 1, 1⟩,
    ⟨0, 2, [], [], [], 2, 6⟩,
    ⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨0, 3, [], [], [2], 1, 5⟩,
    ⟨0, 5, [], [], [4], 1, 5⟩,
    ⟨0, 6, [], [], [], 2, 6⟩,
    ⟨0, 6, [], [], [5, 4, 3, 2], 1, 2⟩,
    ⟨1, 2, [], [], [], 2, 6⟩,
    ⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩,
    ⟨1, 3, [], [], [2], 1, 5⟩,
    ⟨1, 5, [], [], [4], 1, 5⟩,
    ⟨1, 6, [], [], [], 2, 6⟩,
    ⟨1, 6, [], [], [5, 4, 3, 2], 1, 2⟩,
    ⟨2, 3, [], [], [4], 1, 5⟩,
    ⟨3, 4, [], [2], [], 1, 5⟩,
    ⟨3, 5, [], [2], [4], 1, 4⟩,
    ⟨3, 6, [], [2], [], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (3, 2)}⟩


private def k7t5p3_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 5, Finset.Icc 1 4, Finset.Icc 1 5],
    #[∅, ∅, ∅, Finset.Icc 1 5, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, Finset.Icc 1 4, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t5p3_initial_eq_row_0 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 0 j = k7t5p3_state_0 0 j := by decide

private theorem k7t5p3_initial_eq_row_1 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 1 j = k7t5p3_state_0 1 j := by decide

private theorem k7t5p3_initial_eq_row_2 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 2 j = k7t5p3_state_0 2 j := by decide

private theorem k7t5p3_initial_eq_row_3 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 3 j = k7t5p3_state_0 3 j := by decide

private theorem k7t5p3_initial_eq_row_4 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 4 j = k7t5p3_state_0 4 j := by decide

private theorem k7t5p3_initial_eq_row_5 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 5 j = k7t5p3_state_0 5 j := by decide

private theorem k7t5p3_initial_eq_row_6 : ∀ j : Fin 7, (k7t5p3.initialMatrix 7) 6 j = k7t5p3_state_0 6 j := by decide

private theorem k7t5p3_initial_eq : (k7t5p3.initialMatrix 7) = k7t5p3_state_0 := by
  funext i j
  fin_cases i

  · exact k7t5p3_initial_eq_row_0 j

  · exact k7t5p3_initial_eq_row_1 j

  · exact k7t5p3_initial_eq_row_2 j

  · exact k7t5p3_initial_eq_row_3 j

  · exact k7t5p3_initial_eq_row_4 j

  · exact k7t5p3_initial_eq_row_5 j

  · exact k7t5p3_initial_eq_row_6 j

private theorem k7t5p3_closure_0 : ClosureCheck k7t5p3.graph k7t5p3_state_0 7 5 [] := by trivial

private theorem k7t5p3_matrix_eq : k7t5p3.matrix 7 = k7t5p3_state_0 := by
  change closureMatrix (k7t5p3.initialMatrix 7) _ = _
  rw [k7t5p3_initial_eq]
  change closureMatrix k7t5p3_state_0 [] = _
  rfl

private theorem k7t5p3_part_0 : k7t5p3.chains.flatten = List.finRange _ := by decide

private theorem k7t5p3_part_1 : k7t5p3.chains.map List.length = ([[], [], [1, 1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t5p3_part_2 : k7t5p3.chains.map (fun l => l.map (fun i => decide (i ∈ k7t5p3.clique))) = ([[], [], [1, 1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t5p3_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_1 : (⟨0, 1, [[2, 3, 4, 5, 6]], [], [], 1, 1⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_2 : (⟨0, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_3 : (⟨0, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_4 : (⟨0, 3, [], [], [2], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_5 : (⟨0, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_6 : (⟨0, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_7 : (⟨0, 6, [], [], [5, 4, 3, 2], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_8 : (⟨1, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_9 : (⟨1, 2, [], [], [3, 4, 5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_10 : (⟨1, 3, [], [], [2], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_11 : (⟨1, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_12 : (⟨1, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_13 : (⟨1, 6, [], [], [5, 4, 3, 2], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_14 : (⟨2, 3, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_15 : (⟨3, 4, [], [2], [], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_16 : (⟨3, 5, [], [2], [4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_templates_item_17 : (⟨3, 6, [], [2], [], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p3_part_3 : ∀ T ∈ k7t5p3.templates, T.Check k7t5p3.graph k7t5p3.clique 7 (patternAmount ([[], [], [1, 1]] : List (List ℕ))) (([[], [], [1, 1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t5p3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t5p3_templates_item_0, k7t5p3_templates_item_1, k7t5p3_templates_item_2, k7t5p3_templates_item_3, k7t5p3_templates_item_4, k7t5p3_templates_item_5, k7t5p3_templates_item_6, k7t5p3_templates_item_7, k7t5p3_templates_item_8, k7t5p3_templates_item_9, k7t5p3_templates_item_10, k7t5p3_templates_item_11, k7t5p3_templates_item_12, k7t5p3_templates_item_13, k7t5p3_templates_item_14, k7t5p3_templates_item_15, k7t5p3_templates_item_16, k7t5p3_templates_item_17⟩

private theorem k7t5p3_part_4 : ∀ p ∈ k7t5p3.required, p.Check k7t5p3.graph 7 := by decide

private theorem k7t5p3_part_5 : ClosureCheck k7t5p3.graph (k7t5p3.initialMatrix 7) 7 5 k7t5p3.closure := by
  rw [k7t5p3_initial_eq]
  exact k7t5p3_closure_0

private theorem k7t5p3_part_6 : k7t5p3.bad.Check k7t5p3.graph (k7t5p3.matrix 7) 7 5 := by
  rw [k7t5p3_matrix_eq]
  decide

theorem k7t5p3_check : k7t5p3.Check 7 5 [[], [], [1, 1]] :=
  ⟨k7t5p3_part_0, k7t5p3_part_1, k7t5p3_part_2, k7t5p3_part_3, k7t5p3_part_4, k7t5p3_part_5, k7t5p3_part_6⟩
def k7t5p4 : LayoutCertificate 7 where
  chains := [[0], [1, 2, 3], [4, 5, 6]]
  clique := {0, 1, 3, 4, 6}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [[4, 5, 6]], [], [2, 3], 1, 1⟩,
    ⟨0, 2, [], [], [1], 1, 5⟩,
    ⟨0, 3, [], [], [], 2, 6⟩,
    ⟨0, 3, [[4, 5, 6]], [], [2, 1], 1, 1⟩,
    ⟨0, 4, [], [], [], 2, 6⟩,
    ⟨0, 4, [[1, 2, 3]], [], [5, 6], 1, 1⟩,
    ⟨0, 5, [], [], [4], 1, 5⟩,
    ⟨0, 6, [], [], [], 2, 6⟩,
    ⟨0, 6, [[1, 2, 3]], [], [5, 4], 1, 1⟩,
    ⟨1, 2, [], [], [3], 1, 5⟩,
    ⟨1, 4, [], [], [], 2, 6⟩,
    ⟨1, 4, [], [3, 2], [5, 6], 1, 2⟩,
    ⟨1, 5, [], [], [4], 1, 5⟩,
    ⟨1, 6, [], [], [], 2, 6⟩,
    ⟨1, 6, [], [3, 2], [5, 4], 1, 2⟩,
    ⟨2, 4, [], [1], [], 1, 5⟩,
    ⟨3, 4, [], [], [], 2, 6⟩,
    ⟨3, 4, [], [1, 2], [5, 6], 1, 2⟩,
    ⟨4, 5, [], [], [6], 1, 5⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (4, 3)}⟩


private def k7t5p4_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 6, ∅, ∅, ∅, Finset.Icc 1 6, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6, ∅, Finset.Icc 1 5, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, Finset.Icc 1 5, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t5p4_initial_eq_row_0 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 0 j = k7t5p4_state_0 0 j := by decide

private theorem k7t5p4_initial_eq_row_1 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 1 j = k7t5p4_state_0 1 j := by decide

private theorem k7t5p4_initial_eq_row_2 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 2 j = k7t5p4_state_0 2 j := by decide

private theorem k7t5p4_initial_eq_row_3 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 3 j = k7t5p4_state_0 3 j := by decide

private theorem k7t5p4_initial_eq_row_4 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 4 j = k7t5p4_state_0 4 j := by decide

private theorem k7t5p4_initial_eq_row_5 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 5 j = k7t5p4_state_0 5 j := by decide

private theorem k7t5p4_initial_eq_row_6 : ∀ j : Fin 7, (k7t5p4.initialMatrix 7) 6 j = k7t5p4_state_0 6 j := by decide

private theorem k7t5p4_initial_eq : (k7t5p4.initialMatrix 7) = k7t5p4_state_0 := by
  funext i j
  fin_cases i

  · exact k7t5p4_initial_eq_row_0 j

  · exact k7t5p4_initial_eq_row_1 j

  · exact k7t5p4_initial_eq_row_2 j

  · exact k7t5p4_initial_eq_row_3 j

  · exact k7t5p4_initial_eq_row_4 j

  · exact k7t5p4_initial_eq_row_5 j

  · exact k7t5p4_initial_eq_row_6 j

private theorem k7t5p4_closure_0 : ClosureCheck k7t5p4.graph k7t5p4_state_0 7 5 [] := by trivial

private theorem k7t5p4_matrix_eq : k7t5p4.matrix 7 = k7t5p4_state_0 := by
  change closureMatrix (k7t5p4.initialMatrix 7) _ = _
  rw [k7t5p4_initial_eq]
  change closureMatrix k7t5p4_state_0 [] = _
  rfl

private theorem k7t5p4_part_0 : k7t5p4.chains.flatten = List.finRange _ := by decide

private theorem k7t5p4_part_1 : k7t5p4.chains.map List.length = ([[], [1], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t5p4_part_2 : k7t5p4.chains.map (fun l => l.map (fun i => decide (i ∈ k7t5p4.clique))) = ([[], [1], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t5p4_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_1 : (⟨0, 1, [[4, 5, 6]], [], [2, 3], 1, 1⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_2 : (⟨0, 2, [], [], [1], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_3 : (⟨0, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_4 : (⟨0, 3, [[4, 5, 6]], [], [2, 1], 1, 1⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_5 : (⟨0, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_6 : (⟨0, 4, [[1, 2, 3]], [], [5, 6], 1, 1⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_7 : (⟨0, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_8 : (⟨0, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_9 : (⟨0, 6, [[1, 2, 3]], [], [5, 4], 1, 1⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_10 : (⟨1, 2, [], [], [3], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_11 : (⟨1, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_12 : (⟨1, 4, [], [3, 2], [5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_13 : (⟨1, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_14 : (⟨1, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_15 : (⟨1, 6, [], [3, 2], [5, 4], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_16 : (⟨2, 4, [], [1], [], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_17 : (⟨3, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_18 : (⟨3, 4, [], [1, 2], [5, 6], 1, 2⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_templates_item_19 : (⟨4, 5, [], [], [6], 1, 5⟩ : TemplateData (Fin 7)).Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t5p4_part_3 : ∀ T ∈ k7t5p4.templates, T.Check k7t5p4.graph k7t5p4.clique 7 (patternAmount ([[], [1], [1]] : List (List ℕ))) (([[], [1], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t5p4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t5p4_templates_item_0, k7t5p4_templates_item_1, k7t5p4_templates_item_2, k7t5p4_templates_item_3, k7t5p4_templates_item_4, k7t5p4_templates_item_5, k7t5p4_templates_item_6, k7t5p4_templates_item_7, k7t5p4_templates_item_8, k7t5p4_templates_item_9, k7t5p4_templates_item_10, k7t5p4_templates_item_11, k7t5p4_templates_item_12, k7t5p4_templates_item_13, k7t5p4_templates_item_14, k7t5p4_templates_item_15, k7t5p4_templates_item_16, k7t5p4_templates_item_17, k7t5p4_templates_item_18, k7t5p4_templates_item_19⟩

private theorem k7t5p4_part_4 : ∀ p ∈ k7t5p4.required, p.Check k7t5p4.graph 7 := by decide

private theorem k7t5p4_part_5 : ClosureCheck k7t5p4.graph (k7t5p4.initialMatrix 7) 7 5 k7t5p4.closure := by
  rw [k7t5p4_initial_eq]
  exact k7t5p4_closure_0

private theorem k7t5p4_part_6 : k7t5p4.bad.Check k7t5p4.graph (k7t5p4.matrix 7) 7 5 := by
  rw [k7t5p4_matrix_eq]
  decide

theorem k7t5p4_check : k7t5p4.Check 7 5 [[], [1], [1]] :=
  ⟨k7t5p4_part_0, k7t5p4_part_1, k7t5p4_part_2, k7t5p4_part_3, k7t5p4_part_4, k7t5p4_part_5, k7t5p4_part_6⟩
def k7t6p0 : LayoutCertificate 6 where
  chains := [[0], [1], [2], [3], [4], [5]]
  clique := {0, 1, 2, 3, 4, 5}
  templates := [⟨0, 1, [], [], [], 1, 6⟩,
    ⟨0, 2, [], [], [], 1, 6⟩,
    ⟨0, 3, [], [], [], 1, 6⟩,
    ⟨0, 4, [], [], [], 1, 6⟩,
    ⟨0, 5, [], [], [], 1, 6⟩,
    ⟨1, 2, [], [], [], 1, 6⟩,
    ⟨1, 3, [], [], [], 1, 6⟩,
    ⟨1, 4, [], [], [], 1, 6⟩,
    ⟨1, 5, [], [], [], 1, 6⟩,
    ⟨2, 3, [], [], [], 1, 6⟩,
    ⟨2, 4, [], [], [], 1, 6⟩,
    ⟨2, 5, [], [], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t6p0_state_0 : ForbiddenMatrix 6 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t6p0_initial_eq_row_0 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 0 j = k7t6p0_state_0 0 j := by decide

private theorem k7t6p0_initial_eq_row_1 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 1 j = k7t6p0_state_0 1 j := by decide

private theorem k7t6p0_initial_eq_row_2 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 2 j = k7t6p0_state_0 2 j := by decide

private theorem k7t6p0_initial_eq_row_3 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 3 j = k7t6p0_state_0 3 j := by decide

private theorem k7t6p0_initial_eq_row_4 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 4 j = k7t6p0_state_0 4 j := by decide

private theorem k7t6p0_initial_eq_row_5 : ∀ j : Fin 6, (k7t6p0.initialMatrix 7) 5 j = k7t6p0_state_0 5 j := by decide

private theorem k7t6p0_initial_eq : (k7t6p0.initialMatrix 7) = k7t6p0_state_0 := by
  funext i j
  fin_cases i

  · exact k7t6p0_initial_eq_row_0 j

  · exact k7t6p0_initial_eq_row_1 j

  · exact k7t6p0_initial_eq_row_2 j

  · exact k7t6p0_initial_eq_row_3 j

  · exact k7t6p0_initial_eq_row_4 j

  · exact k7t6p0_initial_eq_row_5 j

private theorem k7t6p0_closure_0 : ClosureCheck k7t6p0.graph k7t6p0_state_0 7 6 [] := by trivial

private theorem k7t6p0_matrix_eq : k7t6p0.matrix 7 = k7t6p0_state_0 := by
  change closureMatrix (k7t6p0.initialMatrix 7) _ = _
  rw [k7t6p0_initial_eq]
  change closureMatrix k7t6p0_state_0 [] = _
  rfl

private theorem k7t6p0_part_0 : k7t6p0.chains.flatten = List.finRange _ := by decide

private theorem k7t6p0_part_1 : k7t6p0.chains.map List.length = ([[], [], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t6p0_part_2 : k7t6p0.chains.map (fun l => l.map (fun i => decide (i ∈ k7t6p0.clique))) = ([[], [], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k7t6p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_4 : (⟨0, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_5 : (⟨1, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_6 : (⟨1, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_7 : (⟨1, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_8 : (⟨1, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_9 : (⟨2, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_10 : (⟨2, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_templates_item_11 : (⟨2, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 6)).Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p0_part_3 : ∀ T ∈ k7t6p0.templates, T.Check k7t6p0.graph k7t6p0.clique 7 (patternAmount ([[], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k7t6p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t6p0_templates_item_0, k7t6p0_templates_item_1, k7t6p0_templates_item_2, k7t6p0_templates_item_3, k7t6p0_templates_item_4, k7t6p0_templates_item_5, k7t6p0_templates_item_6, k7t6p0_templates_item_7, k7t6p0_templates_item_8, k7t6p0_templates_item_9, k7t6p0_templates_item_10, k7t6p0_templates_item_11⟩

private theorem k7t6p0_part_4 : ∀ p ∈ k7t6p0.required, p.Check k7t6p0.graph 7 := by decide

private theorem k7t6p0_part_5 : ClosureCheck k7t6p0.graph (k7t6p0.initialMatrix 7) 7 6 k7t6p0.closure := by
  rw [k7t6p0_initial_eq]
  exact k7t6p0_closure_0

private theorem k7t6p0_part_6 : k7t6p0.bad.Check k7t6p0.graph (k7t6p0.matrix 7) 7 6 := by
  rw [k7t6p0_matrix_eq]
  decide

theorem k7t6p0_check : k7t6p0.Check 7 6 [[], [], [], [], [], []] :=
  ⟨k7t6p0_part_0, k7t6p0_part_1, k7t6p0_part_2, k7t6p0_part_3, k7t6p0_part_4, k7t6p0_part_5, k7t6p0_part_6⟩
def k7t6p1 : LayoutCertificate 7 where
  chains := [[0], [1], [2], [3], [4, 5, 6]]
  clique := {0, 1, 2, 3, 4, 6}
  templates := [⟨0, 1, [], [], [], 2, 6⟩,
    ⟨0, 1, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨0, 2, [], [], [], 2, 6⟩,
    ⟨0, 2, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨0, 3, [], [], [], 2, 6⟩,
    ⟨0, 3, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨0, 4, [], [], [], 2, 6⟩,
    ⟨0, 4, [], [], [5, 6], 1, 4⟩,
    ⟨0, 5, [], [], [4], 1, 5⟩,
    ⟨0, 6, [], [], [], 2, 6⟩,
    ⟨0, 6, [], [], [5, 4], 1, 4⟩,
    ⟨1, 2, [], [], [], 2, 6⟩,
    ⟨1, 2, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨1, 3, [], [], [], 2, 6⟩,
    ⟨1, 3, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨1, 4, [], [], [], 2, 6⟩,
    ⟨1, 4, [], [], [5, 6], 1, 4⟩,
    ⟨1, 5, [], [], [4], 1, 5⟩,
    ⟨1, 6, [], [], [], 2, 6⟩,
    ⟨1, 6, [], [], [5, 4], 1, 4⟩,
    ⟨2, 3, [], [], [], 2, 6⟩,
    ⟨2, 3, [[4, 5, 6]], [], [], 1, 3⟩,
    ⟨2, 4, [], [], [], 2, 6⟩,
    ⟨2, 4, [], [], [5, 6], 1, 4⟩,
    ⟨2, 5, [], [], [4], 1, 5⟩,
    ⟨2, 6, [], [], [], 2, 6⟩,
    ⟨2, 6, [], [], [5, 4], 1, 4⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3)}⟩


private def k7t6p1_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 5, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 5, Finset.Icc 1 5, Finset.Icc 1 5, ∅, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t6p1_initial_eq_row_0 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 0 j = k7t6p1_state_0 0 j := by decide

private theorem k7t6p1_initial_eq_row_1 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 1 j = k7t6p1_state_0 1 j := by decide

private theorem k7t6p1_initial_eq_row_2 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 2 j = k7t6p1_state_0 2 j := by decide

private theorem k7t6p1_initial_eq_row_3 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 3 j = k7t6p1_state_0 3 j := by decide

private theorem k7t6p1_initial_eq_row_4 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 4 j = k7t6p1_state_0 4 j := by decide

private theorem k7t6p1_initial_eq_row_5 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 5 j = k7t6p1_state_0 5 j := by decide

private theorem k7t6p1_initial_eq_row_6 : ∀ j : Fin 7, (k7t6p1.initialMatrix 7) 6 j = k7t6p1_state_0 6 j := by decide

private theorem k7t6p1_initial_eq : (k7t6p1.initialMatrix 7) = k7t6p1_state_0 := by
  funext i j
  fin_cases i

  · exact k7t6p1_initial_eq_row_0 j

  · exact k7t6p1_initial_eq_row_1 j

  · exact k7t6p1_initial_eq_row_2 j

  · exact k7t6p1_initial_eq_row_3 j

  · exact k7t6p1_initial_eq_row_4 j

  · exact k7t6p1_initial_eq_row_5 j

  · exact k7t6p1_initial_eq_row_6 j

private theorem k7t6p1_closure_0 : ClosureCheck k7t6p1.graph k7t6p1_state_0 7 6 [] := by trivial

private theorem k7t6p1_matrix_eq : k7t6p1.matrix 7 = k7t6p1_state_0 := by
  change closureMatrix (k7t6p1.initialMatrix 7) _ = _
  rw [k7t6p1_initial_eq]
  change closureMatrix k7t6p1_state_0 [] = _
  rfl

private theorem k7t6p1_part_0 : k7t6p1.chains.flatten = List.finRange _ := by decide

private theorem k7t6p1_part_1 : k7t6p1.chains.map List.length = ([[], [], [], [], [1]] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t6p1_part_2 : k7t6p1.chains.map (fun l => l.map (fun i => decide (i ∈ k7t6p1.clique))) = ([[], [], [], [], [1]] : List (List ℕ)).map profileMask := by decide

private theorem k7t6p1_templates_item_0 : (⟨0, 1, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_1 : (⟨0, 1, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_2 : (⟨0, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_3 : (⟨0, 2, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_4 : (⟨0, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_5 : (⟨0, 3, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_6 : (⟨0, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_7 : (⟨0, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_8 : (⟨0, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_9 : (⟨0, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_10 : (⟨0, 6, [], [], [5, 4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_11 : (⟨1, 2, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_12 : (⟨1, 2, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_13 : (⟨1, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_14 : (⟨1, 3, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_15 : (⟨1, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_16 : (⟨1, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_17 : (⟨1, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_18 : (⟨1, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_19 : (⟨1, 6, [], [], [5, 4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_20 : (⟨2, 3, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_21 : (⟨2, 3, [[4, 5, 6]], [], [], 1, 3⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_22 : (⟨2, 4, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_23 : (⟨2, 4, [], [], [5, 6], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_24 : (⟨2, 5, [], [], [4], 1, 5⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_25 : (⟨2, 6, [], [], [], 2, 6⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_templates_item_26 : (⟨2, 6, [], [], [5, 4], 1, 4⟩ : TemplateData (Fin 7)).Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t6p1_part_3 : ∀ T ∈ k7t6p1.templates, T.Check k7t6p1.graph k7t6p1.clique 7 (patternAmount ([[], [], [], [], [1]] : List (List ℕ))) (([[], [], [], [], [1]] : List (List ℕ)).map List.length).sum := by
  simp only [k7t6p1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t6p1_templates_item_0, k7t6p1_templates_item_1, k7t6p1_templates_item_2, k7t6p1_templates_item_3, k7t6p1_templates_item_4, k7t6p1_templates_item_5, k7t6p1_templates_item_6, k7t6p1_templates_item_7, k7t6p1_templates_item_8, k7t6p1_templates_item_9, k7t6p1_templates_item_10, k7t6p1_templates_item_11, k7t6p1_templates_item_12, k7t6p1_templates_item_13, k7t6p1_templates_item_14, k7t6p1_templates_item_15, k7t6p1_templates_item_16, k7t6p1_templates_item_17, k7t6p1_templates_item_18, k7t6p1_templates_item_19, k7t6p1_templates_item_20, k7t6p1_templates_item_21, k7t6p1_templates_item_22, k7t6p1_templates_item_23, k7t6p1_templates_item_24, k7t6p1_templates_item_25, k7t6p1_templates_item_26⟩

private theorem k7t6p1_part_4 : ∀ p ∈ k7t6p1.required, p.Check k7t6p1.graph 7 := by decide

private theorem k7t6p1_part_5 : ClosureCheck k7t6p1.graph (k7t6p1.initialMatrix 7) 7 6 k7t6p1.closure := by
  rw [k7t6p1_initial_eq]
  exact k7t6p1_closure_0

private theorem k7t6p1_part_6 : k7t6p1.bad.Check k7t6p1.graph (k7t6p1.matrix 7) 7 6 := by
  rw [k7t6p1_matrix_eq]
  decide

theorem k7t6p1_check : k7t6p1.Check 7 6 [[], [], [], [], [1]] :=
  ⟨k7t6p1_part_0, k7t6p1_part_1, k7t6p1_part_2, k7t6p1_part_3, k7t6p1_part_4, k7t6p1_part_5, k7t6p1_part_6⟩
def k7t7p0 : LayoutCertificate 7 where
  chains := [[0], [1], [2], [3], [4], [5], [6]]
  clique := {0, 1, 2, 3, 4, 5, 6}
  templates := [⟨0, 1, [], [], [], 1, 6⟩,
    ⟨0, 2, [], [], [], 1, 6⟩,
    ⟨0, 3, [], [], [], 1, 6⟩,
    ⟨0, 4, [], [], [], 1, 6⟩,
    ⟨0, 5, [], [], [], 1, 6⟩,
    ⟨0, 6, [], [], [], 1, 6⟩,
    ⟨1, 2, [], [], [], 1, 6⟩,
    ⟨1, 3, [], [], [], 1, 6⟩,
    ⟨1, 4, [], [], [], 1, 6⟩,
    ⟨1, 5, [], [], [], 1, 6⟩,
    ⟨1, 6, [], [], [], 1, 6⟩,
    ⟨2, 3, [], [], [], 1, 6⟩,
    ⟨2, 4, [], [], [], 1, 6⟩,
    ⟨2, 5, [], [], [], 1, 6⟩,
    ⟨2, 6, [], [], [], 1, 6⟩,
    ⟨3, 4, [], [], [], 1, 6⟩,
    ⟨3, 5, [], [], [], 1, 6⟩,
    ⟨3, 6, [], [], [], 1, 6⟩]
  required := []
  closure := []
  bad := ⟨none, {(0, 3), (1, 3), (2, 3), (3, 3)}⟩


private def k7t7p0_state_0 : ForbiddenMatrix 7 :=
  fun i j => ((#[#[∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅],
    #[Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, Finset.Icc 1 6, ∅, ∅, ∅]] : Array (Array (Finset ℕ))).getD i.val #[]).getD j.val ∅

private theorem k7t7p0_initial_eq_row_0 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 0 j = k7t7p0_state_0 0 j := by decide

private theorem k7t7p0_initial_eq_row_1 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 1 j = k7t7p0_state_0 1 j := by decide

private theorem k7t7p0_initial_eq_row_2 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 2 j = k7t7p0_state_0 2 j := by decide

private theorem k7t7p0_initial_eq_row_3 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 3 j = k7t7p0_state_0 3 j := by decide

private theorem k7t7p0_initial_eq_row_4 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 4 j = k7t7p0_state_0 4 j := by decide

private theorem k7t7p0_initial_eq_row_5 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 5 j = k7t7p0_state_0 5 j := by decide

private theorem k7t7p0_initial_eq_row_6 : ∀ j : Fin 7, (k7t7p0.initialMatrix 7) 6 j = k7t7p0_state_0 6 j := by decide

private theorem k7t7p0_initial_eq : (k7t7p0.initialMatrix 7) = k7t7p0_state_0 := by
  funext i j
  fin_cases i

  · exact k7t7p0_initial_eq_row_0 j

  · exact k7t7p0_initial_eq_row_1 j

  · exact k7t7p0_initial_eq_row_2 j

  · exact k7t7p0_initial_eq_row_3 j

  · exact k7t7p0_initial_eq_row_4 j

  · exact k7t7p0_initial_eq_row_5 j

  · exact k7t7p0_initial_eq_row_6 j

private theorem k7t7p0_closure_0 : ClosureCheck k7t7p0.graph k7t7p0_state_0 7 7 [] := by trivial

private theorem k7t7p0_matrix_eq : k7t7p0.matrix 7 = k7t7p0_state_0 := by
  change closureMatrix (k7t7p0.initialMatrix 7) _ = _
  rw [k7t7p0_initial_eq]
  change closureMatrix k7t7p0_state_0 [] = _
  rfl

private theorem k7t7p0_part_0 : k7t7p0.chains.flatten = List.finRange _ := by decide

private theorem k7t7p0_part_1 : k7t7p0.chains.map List.length = ([[], [], [], [], [], [], []] : List (List ℕ)).map (fun w => w.sum + w.length + 1) := by decide

private theorem k7t7p0_part_2 : k7t7p0.chains.map (fun l => l.map (fun i => decide (i ∈ k7t7p0.clique))) = ([[], [], [], [], [], [], []] : List (List ℕ)).map profileMask := by decide

private theorem k7t7p0_templates_item_0 : (⟨0, 1, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_1 : (⟨0, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_2 : (⟨0, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_3 : (⟨0, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_4 : (⟨0, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_5 : (⟨0, 6, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_6 : (⟨1, 2, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_7 : (⟨1, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_8 : (⟨1, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_9 : (⟨1, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_10 : (⟨1, 6, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_11 : (⟨2, 3, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_12 : (⟨2, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_13 : (⟨2, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_14 : (⟨2, 6, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_15 : (⟨3, 4, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_16 : (⟨3, 5, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_templates_item_17 : (⟨3, 6, [], [], [], 1, 6⟩ : TemplateData (Fin 7)).Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by decide

private theorem k7t7p0_part_3 : ∀ T ∈ k7t7p0.templates, T.Check k7t7p0.graph k7t7p0.clique 7 (patternAmount ([[], [], [], [], [], [], []] : List (List ℕ))) (([[], [], [], [], [], [], []] : List (List ℕ)).map List.length).sum := by
  simp only [k7t7p0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  exact ⟨k7t7p0_templates_item_0, k7t7p0_templates_item_1, k7t7p0_templates_item_2, k7t7p0_templates_item_3, k7t7p0_templates_item_4, k7t7p0_templates_item_5, k7t7p0_templates_item_6, k7t7p0_templates_item_7, k7t7p0_templates_item_8, k7t7p0_templates_item_9, k7t7p0_templates_item_10, k7t7p0_templates_item_11, k7t7p0_templates_item_12, k7t7p0_templates_item_13, k7t7p0_templates_item_14, k7t7p0_templates_item_15, k7t7p0_templates_item_16, k7t7p0_templates_item_17⟩

private theorem k7t7p0_part_4 : ∀ p ∈ k7t7p0.required, p.Check k7t7p0.graph 7 := by decide

private theorem k7t7p0_part_5 : ClosureCheck k7t7p0.graph (k7t7p0.initialMatrix 7) 7 7 k7t7p0.closure := by
  rw [k7t7p0_initial_eq]
  exact k7t7p0_closure_0

private theorem k7t7p0_part_6 : k7t7p0.bad.Check k7t7p0.graph (k7t7p0.matrix 7) 7 7 := by
  rw [k7t7p0_matrix_eq]
  decide

theorem k7t7p0_check : k7t7p0.Check 7 7 [[], [], [], [], [], [], []] :=
  ⟨k7t7p0_part_0, k7t7p0_part_1, k7t7p0_part_2, k7t7p0_part_3, k7t7p0_part_4, k7t7p0_part_5, k7t7p0_part_6⟩
end CycleClique.Construction.Certificates

end OAI
