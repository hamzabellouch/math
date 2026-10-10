import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverRootDistortion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNMetric

namespace OAI

/-! # Linear metric radius of exponential boxes in the Cartan cover -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra
open scoped Manifold BigOperators

attribute [local instance] semidirectProductTopology
  rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))

include T hExp in
theorem semidirect_root_generators_linear_metric_bound
    {B S : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) :
    letI := dS.compatibleMetric
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ (s : Fin M.letterCount → ℝ), (∀ i, s i ≤ S) →
      ∀ (i : Fin M.letterCount) (t : ℝ), |t| ≤ B →
      dist 1 (SemidirectProduct.inl (F.ExpN (F.N.equiv
        (t • (Real.exp (r * s i) • M.letter i)))) : F.N.carrier ⋊[F.action] F.D.carrier) ≤
        C * (1 + r) := by
  let := dS.compatibleMetric
  let v := fun i => (⟨M.letter i, M.letter_root i⟩ : LieAlgebra.rootSpace H (M.weight i))
  choose D hD hd using fun i => F.semidirect_root_logarithmic_distortion T hExp dS
    (M.weight i) (M.weight_nonzero i)
  let A := fun i => B * ‖v i‖
  let C := fun i => D i * (Real.log (2 + A i) + S)
  have hA : ∀ i, 0 ≤ A i := fun i => mul_nonneg hB (norm_nonneg _)
  have hC : ∀ i, 0 ≤ C i := fun i => mul_nonneg (hD i).le
    (add_nonneg (Real.log_nonneg (by linarith [hA i])) hS)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro r hr s hs i t ht
  have harg : ‖t • (Real.exp (r * s i) • v i)‖ ≤ A i * Real.exp (r * S) := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ B * (Real.exp (r * S) * ‖v i‖) := by
        gcongr
        exact hs i
      _ = _ := by dsimp [A]; ring
  have hdist := hd i (t • (Real.exp (r * s i) • v i))
  change dist 1 (SemidirectProduct.inl (F.ExpN (F.N.equiv
    (t • (Real.exp (r * s i) • M.letter i)))) : F.N.carrier ⋊[F.action] F.D.carrier) ≤ _ at hdist
  have hstep : dist 1 (SemidirectProduct.inl (F.ExpN (F.N.equiv
      (t • (Real.exp (r * s i) • M.letter i)))) : F.N.carrier ⋊[F.action] F.D.carrier) ≤
      C i * (1 + r) := by
    apply hdist.trans
    calc
      _ ≤ D i * Real.log (2 + A i * Real.exp (r * S)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) (hD i).le
      _ ≤ D i * (Real.log (2 + A i) + r * S) :=
        mul_le_mul_of_nonneg_left (log_two_add_exp_le (hA i) hS hr) (hD i).le
      _ ≤ C i * (1 + r) := by
        dsimp [C]
        have hlog : 0 ≤ Real.log (2 + A i) := Real.log_nonneg (by linarith [hA i])
        calc
          _ ≤ D i * ((Real.log (2 + A i) + S) * (1 + r)) :=
            mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hr hlog]) (hD i).le
          _ = _ := by ring
  exact hstep.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) (by linarith))

include T hExp in
theorem exists_semidirect_box_metric_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) {S : ℝ} (hS : 0 ≤ S) :
    letI := dS.compatibleMetric
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Fin M.letterCount → ℝ), (∀ i, s i ≤ S) →
      ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ R →
      dist 1 (SemidirectProduct.inl (F.ExpN (F.N.equiv v)) :
        F.N.carrier ⋊[F.action] F.D.carrier) ≤ C * (1 + r) := by
  let := dS.compatibleMetric
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  obtain ⟨k, B, hB, hgen⟩ := M.exists_uniform_cartan_rescaled_generator_words T F
    hExp exponentialLinearRealizationInput_intrinsic (nilpotentPublishedInputs.haar _ F.N)
    (nilpotentPublishedInputs.dynkin _ F.N) b₀ R
  obtain ⟨C, hC, hstep⟩ := semidirect_root_generators_linear_metric_bound T F M hExp dS
    (le_trans zero_le_one hB) hS
  refine ⟨(k : ℝ) * C, by positivity, ?_⟩
  intro s hs β hβ r hr v hv
  obtain ⟨u, hu, hub, hue⟩ := hgen s β hβ r hr v hv
  let E : cartanRootIdeal H → F.N.carrier ⋊[F.action] F.D.carrier :=
    fun v => SemidirectProduct.inl (F.ExpN (F.N.equiv v))
  have he : generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i) E u = E v := by
    simpa only [E, generatorGroupWord, map_list_prod, List.map_map, Function.comp_def] using
      congrArg (SemidirectProduct.inl : F.N.carrier →* F.N.carrier ⋊[F.action] F.D.carrier) hue
  change dist 1 (E v) ≤ _
  rw [← he]
  calc
    _ ≤ (u.length : ℝ) * (C * (1 + r)) :=
      dist_generatorGroupWord_le _ E u hub (fun i t ht => hstep r hr s hs i t ht)
    _ ≤ (k : ℝ) * (C * (1 + r)) := by gcongr
    _ = _ := by ring

end PolycyclicRecognition

end

end OAI
