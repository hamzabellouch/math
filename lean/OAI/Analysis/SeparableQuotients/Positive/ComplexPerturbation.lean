import OAI.Analysis.SeparableQuotients.Positive.SeparatedWitness

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Scalar
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

def imagCoordinate (f : ℕ → V) (n : ℕ) : StrongDual ℝ (ClosedSpan ℂ f) :=
  Complex.imCLM.comp ((prefixCoord ℂ f n).restrictScalars ℝ)

def perturbTerm (f g : ℕ → V) (n : ℕ) : ClosedSpan ℂ f →L[ℝ] V :=
  (imagCoordinate f n).smulRight (g n - Complex.I • f n)

lemma imagCoordinate_norm (f : ℕ → V) (h : PrefixBoundTwo ℂ f) (hv : ∀ n, ‖f n‖ = 1)
    (n : ℕ) : ‖imagCoordinate f n‖ ≤ 4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change |(prefixCoord ℂ f n x).im| ≤ 4 * ‖x‖
  exact (Complex.abs_im_le_norm _).trans (by
    simpa using prefixCoord_bound ℂ f h (a := 1) (by norm_num) (fun i => (hv i).ge) x n)

lemma summable_perturbTerm [CompleteSpace V] (f g : ℕ → V)
    (h : PrefixBoundTwo ℂ f) (hv : ∀ n, ‖f n‖ = 1)
    (hfg : ∀ n, ‖g n - Complex.I • f n‖ ≤ (1/2:ℝ)^n) :
    Summable (perturbTerm f g) := by
  apply Summable.of_norm_bounded ((summable_geometric_of_lt_one
    (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)).mul_left 4)
  intro n
  rw [perturbTerm, ContinuousLinearMap.norm_smulRight_apply]
  exact mul_le_mul (imagCoordinate_norm f h hv n) (hfg n) (norm_nonneg _) (by norm_num)

def perturbation (f g : ℕ → V) : ClosedSpan ℂ f →L[ℝ] V := ∑' n, perturbTerm f g n

lemma perturbation_combination [CompleteSpace V] (f g : ℕ → V)
    (h : PrefixBoundTwo ℂ f) (hv : ∀ n, ‖f n‖ = 1)
    (hfg : ∀ n, ‖g n - Complex.I • f n‖ ≤ (1/2:ℝ)^n) (c : ℕ →₀ ℂ) :
    perturbation f g (spanCombination ℂ f c) =
      ∑ n ∈ c.support, (c n).im • (g n - Complex.I • f n) := by
  have hs := summable_perturbTerm f g h hv hfg
  change (ContinuousLinearMap.apply ℝ V (spanCombination ℂ f c)) (∑' n, perturbTerm f g n) = _
  rw [ContinuousLinearMap.map_tsum _ hs]
  simp only [ContinuousLinearMap.apply_apply, perturbTerm, ContinuousLinearMap.smulRight_apply,
    imagCoordinate, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  change (∑' n, (prefixCoord ℂ f n (spanCombination ℂ f c)).im •
    (g n - Complex.I • f n)) = _
  simp only [prefixCoord_combination ℂ f h (a := 1) (by norm_num) (fun i => (hv i).ge)]
  apply tsum_eq_sum
  intro n hn
  simp [Finsupp.notMem_support_iff.mp hn]

lemma real_imag_perturbed (z : ℂ) (u v : V) :
    z • u + z.im • (v - Complex.I • u) = z.re • u + z.im • v := by
  have hz : z • u = z.re • u + z.im • (Complex.I • u) := by
    conv_lhs => rw [← Complex.re_add_im z, add_smul, mul_smul]
    rw [show (z.re:ℂ) • u = z.re • u from algebraMap_smul ℂ z.re u,
      show (z.im:ℂ) • (Complex.I • u) = z.im • (Complex.I • u) from
        algebraMap_smul ℂ z.im (Complex.I • u)]
  rw [hz, smul_sub]
  abel



theorem perturbation_maps_into_real [CompleteSpace V]
    (E : Submodule ℝ V) (hEcl : IsClosed (E : Set V)) (f g : ℕ → E)
    (h : PrefixBoundTwo ℂ (fun n => (f n : V))) (hv : ∀ n, ‖f n‖ = 1)
    (hfg : ∀ n, ‖(g n : V) - Complex.I • (f n : V)‖ ≤ (1/2:ℝ)^n) :
    ∀ x : ClosedSpan ℂ (fun n => (f n : V)),
      (x : V) + perturbation (fun n => (f n : V)) (fun n => (g n : V)) x ∈ E := by
  intro x
  refine (denseRange_spanCombination ℂ (fun n => (f n : V))).induction_on x (p := fun x =>
    (x : V) + perturbation (fun n => (f n : V)) (fun n => (g n : V)) x ∈ E) ?_ ?_
  · exact hEcl.preimage (by fun_prop)
  · intro c
    rw [spanCombination_coe, perturbation_combination _ _ h hv hfg c]
    change (∑ n ∈ c.support, c n • (f n : V)) +
      (∑ n ∈ c.support, (c n).im • ((g n : V) - Complex.I • (f n : V))) ∈ E
    rw [← Finset.sum_add_distrib]
    apply E.sum_mem
    intro n hn
    rw [real_imag_perturbed]
    exact E.add_mem (E.smul_mem _ (f n).property) (E.smul_mem _ (g n).property)

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Fields.ComplexTransfer
open Set TopologicalSpace Scalar
attribute [local instance] Scalar.dualSubmoduleNormedGroup Scalar.dualSubmoduleNormedSpace
attribute [local instance] realDualSubmoduleNormedGroup realDualSubmoduleNormedSpace
attribute [local instance] complexDualSubmoduleRealNormedSpace complexRealOperatorNormedGroup
  complexRealOperatorMetric complexRealOperatorNormedSpace complexRealOperatorAdd
  complexRealOperatorSMul complexRealOperatorT2
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]




lemma perturbation_separable_eval (f g : ℕ → StrongDual ℂ X)
    (h : PrefixBoundTwo ℂ f) (hv : ∀ n, ‖f n‖ = 1)
    (hfg : ∀ n, ‖g n - Complex.I • f n‖ ≤ (1/2:ℝ)^n) :
    IsSeparable (Set.range (fun x : X =>
      ((ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ).flip x).comp (perturbation f g))) := by
  let : ContinuousAdd (ClosedSpan ℂ f →L[ℝ] ℂ) := complexRealOperatorAdd _
  let : ContinuousSMul ℂ (ClosedSpan ℂ f →L[ℝ] ℂ) := complexRealOperatorSMul _
  let a (n : ℕ) : ClosedSpan ℂ f →L[ℝ] ℂ := Complex.ofRealCLM.comp (imagCoordinate f n)
  let S := ClosedSpan ℂ a
  have hSsep : IsSeparable (S : Set (ClosedSpan ℂ f →L[ℝ] ℂ)) :=
    ((Set.countable_range a).isSeparable.span (R := ℂ)).closure
  apply hSsep.mono
  rintro _ ⟨x, rfl⟩
  let ex : StrongDual ℂ X →L[ℝ] ℂ :=
    (ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ).flip x
  have he (n : ℕ) : ex.comp (perturbTerm f g n) =
      (g n x - Complex.I * f n x) • a n := by
    ext z
    change (imagCoordinate f n z) • ((g n - Complex.I • f n) x) =
      (g n x - Complex.I * f n x) * (imagCoordinate f n z : ℂ)
    simp [smul_eq_mul, mul_comm]
  have ht := summable_perturbTerm f g h hv hfg
  change (ex.postcomp (ClosedSpan ℂ f)) (∑' n, perturbTerm f g n) ∈ S
  rw [ContinuousLinearMap.map_tsum _ ht]
  have hSclosed : IsClosed (S : Set (ClosedSpan ℂ f →L[ℝ] ℂ)) := isClosed_closure
  apply tsum_mem hSclosed
  intro n
  change ex.comp (perturbTerm f g n) ∈ S
  rw [he n]
  exact S.smul_mem _ (spanVector ℂ a n).property

lemma perturbation_witness
    (E : Submodule ℝ (StrongDual ℂ X)) (hEcl : IsClosed (E : Set (StrongDual ℂ X)))
    (hEsep : IsSeparable (Set.range (realEvaluation E))) (f g : ℕ → E)
    (h : PrefixBoundTwo ℂ (fun n => (f n : StrongDual ℂ X))) (hv : ∀ n, ‖f n‖ = 1)
    (hfg : ∀ n, ‖(g n : StrongDual ℂ X) - Complex.I • (f n : StrongDual ℂ X)‖ ≤ (1/2:ℝ)^n) :
    ∃ H : Submodule ℂ (StrongDual ℂ X), IsClosed (H : Set (StrongDual ℂ X)) ∧
      ¬ FiniteDimensional ℂ H ∧ IsSeparable (Set.range (Scalar.evaluation H)) := by
  let u : ℕ → StrongDual ℂ X := fun n => f n
  let v : ℕ → StrongDual ℂ X := fun n => g n
  let H := ClosedSpan ℂ u
  let K := perturbation u v
  let L₀ : H →L[ℝ] StrongDual ℂ X := H.subtypeL.restrictScalars ℝ + K
  let L : H →L[ℝ] E := L₀.codRestrict E (perturbation_maps_into_real E hEcl f g h hv hfg)
  have hHinf : ¬ FiniteDimensional ℂ H := by
    intro hh
    let := hh
    have hi := (basisOfPrefix ℂ u h (a := 1) (by norm_num) (fun n => (hv n).ge)).linearIndependent
    have hh := hi.lt_aleph0_of_finiteDimensional
    simp at hh
  refine ⟨H, Submodule.isClosed_topologicalClosure _, hHinf, ?_⟩
  apply complex_eval_separable_of_real
  let evK : X → (H →L[ℝ] ℂ) := fun x =>
    ((ContinuousLinearMap.restrictScalarsL ℂ X ℂ ℝ ℝ).flip x).comp K
  have hKsep : IsSeparable (Set.range evK) := perturbation_separable_eval u v h hv hfg
  let φ : (E →L[ℝ] ℂ) × (H →L[ℝ] ℂ) → (H →L[ℝ] ℂ) := fun p => p.1.comp L - p.2
  have hφ : Continuous φ := by
    let : IsTopologicalAddGroup (H →L[ℝ] ℂ) := ContinuousLinearMap.isTopologicalAddGroup
    let : ContinuousSub (H →L[ℝ] ℂ) := IsTopologicalAddGroup.to_continuousSub
    fun_prop
  apply ((hEsep.prod hKsep).image hφ).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨(realEvaluation E x, evK x), ⟨Set.mem_range_self _, Set.mem_range_self _⟩, ?_⟩
  ext z
  change ((z : StrongDual ℂ X) + K z) x - (K z) x = (z : StrongDual ℂ X) x
  simp

end SeparableQuotient.Positive.Fields.ComplexTransfer

end

end

end OAI
