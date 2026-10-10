import OAI.Probability.InvariantIsing.Cavity.CavityFrameLimit

namespace OAI

/-! Exact finite-dimensional laws of the independent Gaussian array used
in the fresh-frame construction. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

lemma cavityGaussianRows_coordinate_law {q : ℕ} (k : ℕ) (i : Fin q) :
    HasLaw (fun x : ℕ → Fin q → ℝ => x k i) (gaussianReal 0 1)
      (cavityGaussianRows q) :=
  (cavityGaussianRow_eval_law i).fun_comp (cavityGaussianRows_eval_law q k)

lemma cavityGaussianRows_coordinates_independent (q : ℕ) :
    iIndepFun (fun p : ℕ × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := by
  simpa only [cavityGaussianRows, cavityGaussianRow, Measure.infinitePi_eq_pi] using
    iIndepFun_uncurry_infinitePi' (fun (_ : ℕ) (_ : Fin q) => gaussianReal 0 1)
      (X := fun _ _ x => x) (fun _ _ => measurable_id)

lemma cavityGaussianRows_finite_array_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ => fun p : Fin n × Fin q => x p.1 p.2)
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1))
      (cavityGaussianRows q) := by
  have hinj : Function.Injective (fun p : Fin n × Fin q => ((p.1 : ℕ), p.2)) := by
    intro p r h
    exact Prod.ext (Fin.ext (congrArg (fun z : ℕ × Fin q => z.1) h))
      (congrArg (fun z : ℕ × Fin q => z.2) h)
  have hind : iIndepFun
      (fun p : Fin n × Fin q => fun x : ℕ → Fin q → ℝ => x p.1 p.2)
      (cavityGaussianRows q) := (cavityGaussianRows_coordinates_independent q).precomp hinj
  refine ⟨(measurable_pi_iff.mpr (fun p =>
    (measurable_pi_apply p.2).comp (measurable_pi_apply (p.1 : ℕ)))).aemeasurable, ?_⟩
  have hm := hind.map_fun_eq_pi_map (fun (p : Fin n × Fin q) =>
    (cavityGaussianRows_coordinate_law (p.1 : ℕ) p.2).aemeasurable)
  simpa only [(cavityGaussianRows_coordinate_law _ _).map_eq] using hm

theorem cavityGaussianRows_finite_standard_law (n q : ℕ) :
    HasLaw (fun x : ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : Fin n × Fin q => x p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin q)))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q))) (cavityGaussianRows q) := by
  have ht : HasLaw (WithLp.toLp 2 : (Fin n × Fin q → ℝ) →
      EuclideanSpace ℝ (Fin n × Fin q))
      (stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)))
      (Measure.pi (fun _ : Fin n × Fin q => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact ht.fun_comp (cavityGaussianRows_finite_array_law n q)

end InvariantIsing

end

end OAI
