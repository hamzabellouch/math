import OAI.InformationTheory.QuantumCircuit.RegularApproximation

namespace OAI

/-! Asymptotic error budgets for low-degree approximations. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

lemma act_smul {N : ℕ} (c : ℂ) (A : Operator N) (ψ : State N) :
    act (c • A) ψ = c • act A ψ := by simp [act]

lemma act_sub_state {N : ℕ} (A : Operator N) (ψ ξ : State N) :
    act A (ψ - ξ) = act A ψ - act A ξ := by simp [act]

lemma act_real_smul {N : ℕ} (c : ℝ) (A : Operator N) (ψ : State N) :
    act (c • A) ψ = c • act A ψ := by
  change act ((c : ℂ) • A) ψ = (c : ℂ) • act A ψ
  exact act_smul _ _ _

def ApproxOn {N : ℕ} (ψ : State N) (r C δ : ℝ) (E : Operator N) : Prop :=
  ∃ E' : Operator N, HasDegreeLE E' r ∧ ‖E'‖ ≤ C ∧ ‖act (E - E') ψ‖ ≤ δ

lemma ApproxOn.exact {N : ℕ} (ψ : State N) {r C : ℝ} {E : Operator N}
    (hE : HasDegreeLE E r) (hC : ‖E‖ ≤ C) : ApproxOn ψ r C 0 E :=
  ⟨E, hE, hC, by simp⟩

lemma ApproxOn.mono {N : ℕ} {ψ : State N} {r s C D δ ε : ℝ} {E : Operator N}
    (h : ApproxOn ψ r C δ E) (hrs : r ≤ s) (hCD : C ≤ D) (hδε : δ ≤ ε) :
    ApproxOn ψ s D ε E := by
  obtain ⟨E', hd, hn, he⟩ := h
  exact ⟨E', hd.mono hrs, hn.trans hCD, he.trans hδε⟩

lemma ApproxOn.congr_operator {N : ℕ} {ψ : State N} {r C δ : ℝ}
    {E F : Operator N} (h : ApproxOn ψ r C δ E) (heq : E = F) :
    ApproxOn ψ r C δ F := heq ▸ h

lemma ApproxOn.add {N : ℕ} {ψ : State N} {r C D δ ε : ℝ} {E F : Operator N}
    (hE : ApproxOn ψ r C δ E) (hF : ApproxOn ψ r D ε F) :
    ApproxOn ψ r (C + D) (δ + ε) (E + F) := by
  obtain ⟨E', hdE, hnE, heE⟩ := hE
  obtain ⟨F', hdF, hnF, heF⟩ := hF
  refine ⟨E' + F', hdE.add hdF, (norm_add_le _ _).trans (add_le_add hnE hnF), ?_⟩
  rw [show E + F - (E' + F') = (E - E') + (F - F') by abel, act_add]
  exact (norm_add_le _ _).trans (add_le_add heE heF)

lemma ApproxOn.smul {N : ℕ} {ψ : State N} {r C δ : ℝ} {E : Operator N}
    (hE : ApproxOn ψ r C δ E) (c : ℂ) :
    ApproxOn ψ r (‖c‖ * C) (‖c‖ * δ) (c • E) := by
  obtain ⟨E', hd, hn, he⟩ := hE
  refine ⟨c • E', hd.smul c, ?_, ?_⟩
  · rw [norm_smul]; exact mul_le_mul_of_nonneg_left hn (norm_nonneg c)
  · rw [← smul_sub, act_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg c)

lemma ApproxOn.real_smul {N : ℕ} {ψ : State N} {r C δ : ℝ} {E : Operator N}
    (hE : ApproxOn ψ r C δ E) (c : ℝ) :
    ApproxOn ψ r (|c| * C) (|c| * δ) (c • E) := by
  obtain ⟨E', hd, hn, he⟩ := hE
  refine ⟨c • E', ?_, ?_, ?_⟩
  · have hscalar : (c : ℂ) • E' = c • E' := by ext i j; rfl
    rw [← hscalar]
    exact hd.smul (c : ℂ)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hn (abs_nonneg c)
  · rw [← smul_sub, act_real_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg c)

lemma approx_list_sum {N : ℕ} {ι : Type*} (ψ : State N) (l : List ι)
    (c : ι → ℂ) (E : ι → Operator N) (r C δ : ℝ)
    (h : ∀ i ∈ l, ApproxOn ψ r C δ (E i)) :
    ApproxOn ψ r ((l.map (fun i => ‖c i‖)).sum * C)
      ((l.map (fun i => ‖c i‖)).sum * δ) (l.map (fun i => c i • E i)).sum := by
  induction l with
  | nil => exact ⟨0, degree_zero r, by simp, by simp⟩
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons, add_mul] using
      ((h i (List.mem_cons_self ..)).smul (c i)).add
        (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma approx_real_list_sum {N : ℕ} {ι : Type*} (ψ : State N) (l : List ι)
    (c : ι → ℝ) (E : ι → Operator N) (r C δ : ℝ)
    (h : ∀ i ∈ l, ApproxOn ψ r C δ (E i)) :
    ApproxOn ψ r ((l.map (fun i => |c i|)).sum * C)
      ((l.map (fun i => |c i|)).sum * δ) (l.map (fun i => c i • E i)).sum := by
  induction l with
  | nil => exact ⟨0, degree_zero r, by simp, by simp⟩
  | cons i l ih =>
    simpa only [List.map_cons, List.sum_cons, add_mul] using
      ((h i (List.mem_cons_self ..)).real_smul (c i)).add
        (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

lemma reflection_double_expansion {N : ℕ} (l : List (Count N))
    (hl : l.Pairwise (fun A B => Disjoint A.support B.support)) (D : Operator N) :
    conjugate (reflectList l) D =
      ((reflectionTerms l).map (fun p => p.1 •
        ((reflectionTerms l).map (fun q => q.1 • (p.2.zero * D * q.2.zero))).sum)).sum := by
  unfold conjugate
  rw [reflectList_selfAdjoint l hl, ← reflectionTerms_sum l hl]
  calc
    _ = ((reflectionTerms l).map (fun a => (a.1 • a.2.zero) * D *
        ((reflectionTerms l).map (fun b => b.1 • b.2.zero)).sum)).sum := by
      rw [← List.sum_map_mul_right, ← List.sum_map_mul_right]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro a _
      rw [← List.sum_map_mul_left]
      simp only [List.map_map, smul_mul_assoc, mul_smul_comm, List.smul_sum]
      congr 1
      apply List.map_congr_left
      intro b _
      exact smul_comm b.1 a.1 _

lemma sandwich_approximation {N : ℕ} (ψ : State N) (M : Count N)
    (J S T : Finset (Fin N)) (D : Operator N) (hD : TensorSupported J D)
    (hDn : ‖D‖ ≤ 1) (p : Polynomial ℝ) (r δ τ : ℝ)
    (hδ : 0 ≤ δ) (hψ : ‖ψ‖ ≤ 1) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k : ℝ) < r → |p.eval (k : ℝ)| ≤ δ)
    (htail : ‖act ((M.restrict ((S ∪ T) \ J)).high r) ψ‖ ≤ τ) :
    ApproxOn ψ ((J.card : ℝ) + p.natDegree) (weight N p)
      (δ + (1 + weight N p) * τ)
      ((M.restrict S).zero * D * (M.restrict T).zero) := by
  let Q := M.restrict ((S ∪ T) \ J)
  let I := interiorTerm M J S T D
  refine ⟨I * Q.polynomial p, ?_, ?_, ?_⟩
  · exact (tensor_hasDegreeLE J I (interiorTerm_supported M J S T D hD) le_rfl).mul
      (Q.polynomial_degree p)
  · exact (norm_mul_le_right _ _ (interiorTerm_norm M J S T D hDn)).trans
      (Q.polynomial_norm_le p)
  · rw [sandwich_factor M J S T D hD]
    change ‖act (I * Q.zero - I * Q.polynomial p) ψ‖ ≤ _
    rw [← mul_sub, act_mul]
    exact (act_norm_le_of_contraction I (interiorTerm_norm M J S T D hDn) _).trans
      (Q.polynomial_action_error p ψ r δ τ hδ hψ hp0 hp htail)

end QAC

end

end OAI
