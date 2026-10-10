import OAI.Probability.InvariantIsing.Cavity.CavityResidualReplica

namespace OAI

/-! One sampled innovation path has independent Gaussian increments.
This is the marginal needed by the remaining linear-tilt moment bound. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

lemma cavity_replica_one_marginal {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Kernel Ω X) [IsMarkovKernel ν] :
    (probabilityReplicaKernel ν ν.measurable ∘ₘ P).map (fun σ => σ 0) = ν ∘ₘ P := by
  rw [Measure.map_comp P _ (measurable_pi_apply 0)]
  congr 1
  ext ω : 1
  rw [Kernel.map_apply _ (measurable_pi_apply 0)]
  exact Measure.infinitePi_map_eval _ 0

lemma cavity_edgeAt_injective (n : ℕ) (γ : LabeledLeaf n) :
    Function.Injective (edgeAt n γ) := by
  intro i j hij
  apply Fin.ext
  simpa only [forestVertexDepth_edgeAt] using congrArg (forestVertexDepth n) hij

lemma cavity_selected_path_law {A : Type} [MeasurableSpace A]
    (n : ℕ) (μ : ℕ → ProbabilityMeasure A) (γ : LabeledLeaf n) :
    (Measure.infinitePi (fun v : ForestVertex n =>
      (μ (forestVertexDepth n v) : Measure A))).map (fun g i => g (edgeAt n γ i)) =
      Measure.pi (fun i : Fin n => (μ i : Measure A)) := by
  have hi : iIndepFun (fun v (g : ForestVertex n → A) => g v)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hs := hi.precomp (cavity_edgeAt_injective n γ)
  have he := hs.map_fun_eq_pi_map (fun i => (measurable_pi_apply (edgeAt n γ i)).aemeasurable)
  simpa only [Measure.infinitePi_map_eval, forestVertexDepth_edgeAt] using he

lemma cavity_coordinate_one_path_law {A : Type} [MeasurableSpace A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    ((cascadeReplicaLaw n b).prod (Measure.infinitePi
      (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map
      (fun p => coordinateMarkPath n p 0) = Measure.pi (fun i : Fin n => (μ i : Measure A)) := by
  have hm : Measurable (fun p : (ℕ → LabeledLeaf n) × (ForestVertex n → A) =>
      coordinateMarkPath n p 0) :=
    (measurable_pi_apply 0).comp (measurable_coordinateMarkPath n)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  rw [lintegral_prod _ (show AEMeasurable (fun p => F (coordinateMarkPath n p 0)) _ from
    (hF.comp hm).aemeasurable)]
  have hinner (σ : ℕ → LabeledLeaf n) :
      (∫⁻ g, F (coordinateMarkPath n (σ, g) 0)
        ∂Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))) =
      ∫⁻ x, F x ∂Measure.pi (fun i : Fin n => (μ i : Measure A)) := by
    rw [← cavity_selected_path_law n μ (σ 0), lintegral_map hF (by fun_prop)]
    rfl
  simp_rw [hinner]
  simp

theorem cavity_marked_one_path_law {A : Type} [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b) (μ : ℕ → ProbabilityMeasure A) :
    (markedReplicaLaw n b μ).map (fun σ => noiseLeafMark n (σ 0)) =
      Measure.pi (fun i : Fin n => (μ i : Measure A)) := by
  have hpath := congrArg (fun P : Measure (ℕ → Fin n → A) => P.map (fun x => x 0))
    (marked_path_law n b hb μ)
  rw [Measure.map_map (measurable_pi_apply 0) (measurable_replicaMarkPath n),
    Measure.map_map (measurable_pi_apply 0) (measurable_coordinateMarkPath n)] at hpath
  exact hpath.trans (cavity_coordinate_one_path_law n b μ)

lemma cavityLeafSum_eq_mark_sum {d : ℕ} (n : ℕ) (s : EuclideanSpace ℝ (Fin d))
    (v : NoiseLeaf (EuclideanSpace ℝ (Fin d)) n) :
    cavityLeafSum n s v = s + ∑ i : Fin n, noiseLeafMark n v i := by
  induction n generalizing s with
  | zero => simp [cavityLeafSum]
  | succ n ih =>
    rw [cavityLeafSum, ih, Fin.sum_univ_succ]
    simp only [noiseLeafMark, Fin.cases_zero, Fin.cases_succ]
    abel

end InvariantIsing

end

end OAI
