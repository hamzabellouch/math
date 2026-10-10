import OAI.Probability.PosteriorReplicas.Information.RandomCorrelation
import OAI.Probability.PosteriorReplicas.Kernels.LiftedReplica
import OAI.Probability.PosteriorReplicas.Kernels.ReplicaTupleMarginals

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma observe_law {d ℓ k m : ℕ} (μ : Measure (EqualSpace d k m)) [SFinite μ] :
    (μ.prod (auxLaw d ℓ k)).map observe =
      ((auxLaw d ℓ k).prod (μ.map (fun z => z.2.2))).map
        (fun z => (z.1,projectedTuple z.1.1 z.2)) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH (by fun_prop),lintegral_map hH (by fun_prop),
    lintegral_prod _ (by fun_prop),lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ b, ∫⁻ z, H (b,projectedTuple b.1 z.2.2) ∂μ ∂auxLaw d ℓ k :=
      lintegral_lintegral_swap (by fun_prop)
    _ = _ := by
      apply lintegral_congr
      intro b
      rw [lintegral_map (by fun_prop) (by fun_prop)]

lemma totalCorrelation_projectedTuple {d ℓ m : ℕ} (Q : Measure (Tuple d m)) [IsProbabilityMeasure Q]
    (B : Rows d ℓ) : totalCorrelation (Q.map (projectedTuple B)) =
      totalCorrelation (Q.map (fun u i => labels B (u i))) := by
  let h : (Fin (m+1) → Labels ℓ) → Tuple ℓ m := fun y i => WithLp.toLp 2 (y i)
  let h' : Tuple ℓ m → (Fin (m+1) → Labels ℓ) := fun y i => WithLp.ofLp (y i)
  have hh : Measurable h := by unfold h; fun_prop
  have hh' : Measurable h' := by unfold h'; fun_prop
  have he : Q.map (projectedTuple B) = (Q.map (fun u i => labels B (u i))).map h := by
    rw [Measure.map_map hh (by unfold labels; fun_prop)]
    rfl
  rw [he]
  change totalCorrelation ((Q.map (fun u i => labels B (u i))).map (fun y i => WithLp.toLp 2 (y i))) = _
  simp only [totalCorrelation]
  have : IsProbabilityMeasure (Q.map (fun u i => labels B (u i))) := by infer_instance
  rw [marginalProduct_map (ν := Q.map (fun u i => labels B (u i))) (g := WithLp.toLp 2) (by fun_prop)]
  exact klDiv_map_leftInverse _ _ hh hh' (fun _ => rfl)

lemma observe_klDiv_eq_correlation {d ℓ k m : ℕ} (μ ν : Measure (EqualSpace d k m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hν : ν.map (fun z => z.2.2) = marginalProduct (μ.map (fun z => z.2.2))) :
    klDiv ((μ.prod (auxLaw d ℓ k)).map observe) ((ν.prod (auxLaw d ℓ k)).map observe) =
      ∫⁻ B, totalCorrelation ((μ.map (fun z => z.2.2)).map (fun u i => labels B (u i))) ∂gaussianRows d ℓ := by
  have : IsProbabilityMeasure (μ.map (fun z => z.2.2)) := by infer_instance
  rw [observe_law,observe_law,hν]
  change klDiv (((auxLaw d ℓ k).prod (μ.map (fun z => z.2.2))).map
      (fun z => (z.1,fun i => WithLp.toLp 2 (labels z.1.1 (z.2 i)))))
    (((auxLaw d ℓ k).prod (marginalProduct (μ.map (fun z => z.2.2)))).map
      (fun z => (z.1,fun i => WithLp.toLp 2 (labels z.1.1 (z.2 i))))) = _
  rw [klDiv_random_tuple_observation (auxLaw d ℓ k) (μ.map (fun z => z.2.2)) (g := fun z : AuxSpace d ℓ k × Vec d => WithLp.toLp 2 (labels z.1.1 z.2)) (by unfold labels; fun_prop)]
  have he (b : AuxSpace d ℓ k) : totalCorrelation ((μ.map (fun z => z.2.2)).map
      (fun u i => WithLp.toLp 2 (labels b.1 (u i)))) =
      totalCorrelation ((μ.map (fun z => z.2.2)).map (fun u i => labels b.1 (u i))) :=
    totalCorrelation_projectedTuple _ b.1
  simp_rw [he]
  rw [auxLaw,lintegral_prod _ (by
    exact ((measurable_projected_totalCorrelation (μ.map (fun z => z.2.2)) measurable_labels).comp measurable_fst).aemeasurable)]
  simp only [lintegral_const,measure_univ,mul_one]

lemma replica_tuple_klDiv_le {d k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    totalCorrelation (posteriorMessageLaw (m := m) .spherical hf κ).fst ≤
      klDiv (replicaLaw (k := k) (m := m) .spherical f) (equalReference ((sphereLaw d).withDensity f)) := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [totalCorrelation,posteriorMessageLaw_marginalProduct (by omega) (by omega) .spherical hf hLt hfL κ,
    posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ]
  change klDiv _ (Measure.pi (fun _ => (sphereLaw d).withDensity f)) ≤ _
  rw [← equalReference_tuple (k := k) ((sphereLaw d).withDensity f)]
  exact klDiv_map_le _ _ (by fun_prop)

lemma replica_observe_klDiv_eq {d ℓ k m N : ℕ} (hd : k+m+2 ≤ d) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {f : Vec d → ℝ≥0∞} (hf : Measurable f) {L : ℝ≥0∞} (hLt : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    [IsProbabilityMeasure ((sphereLaw d).withDensity f)]
    (κ : Kernel (Data d k) (Fin N)) [IsMarkovKernel κ] :
    klDiv (((replicaLaw (k := k) (m := m) .spherical f).prod (auxLaw d ℓ k)).map observe)
      (((equalReference ((sphereLaw d).withDensity f)).prod (auxLaw d ℓ k)).map observe) =
      ∫⁻ B, totalCorrelation ((posteriorMessageLaw (m := m) .spherical hf κ).fst.map
        (fun u i => labels B (u i))) ∂gaussianRows d ℓ := by
  have : IsProbabilityMeasure ((BaseLaw.spherical.measure d).withDensity f) := by
    change IsProbabilityMeasure ((sphereLaw d).withDensity f); infer_instance
  have := posteriorMessageLaw_probability (m := m) .spherical hf hLt hfL κ
  have := replicaLaw_probability hd hk hm .spherical hf hLt hfL
  rw [posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ]
  apply observe_klDiv_eq_correlation
  rw [← posteriorMessageLaw_tuple hd hk hm .spherical hf hLt hfL κ,
    posteriorMessageLaw_marginalProduct (by omega) (by omega) .spherical hf hLt hfL κ,
    equalReference_tuple]
  rfl

end PosteriorReplicas
end

end OAI
