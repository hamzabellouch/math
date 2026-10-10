import OAI.Probability.InvariantIsing.Cavity.CavityFiniteGaussian

namespace OAI

/-! Independent Gaussian arrays for the finitely many spectral groups.
The finite restrictions are exactly standard Gaussian vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InvariantIsing

def cavityGroupGaussianRows (m q : ℕ) : Measure (Fin m → ℕ → Fin q → ℝ) :=
  Measure.pi (fun _ : Fin m => cavityGaussianRows q)

instance (m q : ℕ) : IsProbabilityMeasure (cavityGroupGaussianRows m q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin m => cavityGaussianRows q)))

lemma cavityGroupGaussian_eval_law {m q : ℕ} (a : Fin m) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a) (cavityGaussianRows q)
      (cavityGroupGaussianRows m q) :=
  ⟨(measurable_pi_apply a).aemeasurable,
    (measurePreserving_eval (fun _ : Fin m => cavityGaussianRows q) a).map_eq⟩

lemma cavityGroupGaussian_row_law {m q : ℕ} (a : Fin m) (k : ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a k) (cavityGaussianRow q)
      (cavityGroupGaussianRows m q) :=
  (cavityGaussianRows_eval_law q k).fun_comp (cavityGroupGaussian_eval_law a)

lemma cavityGroupGaussian_coordinate_law {m q : ℕ} (a : Fin m) (k : ℕ) (j : Fin q) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ => x a k j) (gaussianReal 0 1)
      (cavityGroupGaussianRows m q) :=
  (cavityGaussianRow_eval_law j).fun_comp (cavityGroupGaussian_row_law a k)

lemma cavityGroupGaussian_coordinates_independent (m q : ℕ) :
    iIndepFun (fun p : (Fin m × ℕ) × Fin q =>
      fun x : Fin m → ℕ → Fin q → ℝ => x p.1.1 p.1.2 p.2)
      (cavityGroupGaussianRows m q) := by
  have hrows : iIndepFun (fun p : Fin m × ℕ =>
      fun x : Fin m → ℕ → Fin q → ℝ => x p.1 p.2) (cavityGroupGaussianRows m q) := by
    simpa only [cavityGroupGaussianRows, cavityGaussianRows, Measure.infinitePi_eq_pi] using
      iIndepFun_uncurry_infinitePi' (fun (_ : Fin m) (_ : ℕ) => cavityGaussianRow q)
        (X := fun _ _ x => x) (fun _ _ => measurable_id)
  apply iIndepFun_uncurry' (fun _ _ => by fun_prop) hrows
  intro p
  exact (iIndepFun_iff_hasLaw_pi_pi
    (fun j => cavityGroupGaussian_coordinate_law p.1 p.2 j)).mpr
      (cavityGroupGaussian_row_law p.1 p.2)

lemma cavityGroupGaussian_finite_array_law {m q : ℕ} (N : Fin m → ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ =>
      fun p : (a : Fin m) × (Fin (N a) × Fin q) => x p.1 p.2.1 p.2.2)
      (Measure.pi (fun _ : (a : Fin m) × (Fin (N a) × Fin q) => gaussianReal 0 1))
      (cavityGroupGaussianRows m q) := by
  have hinj : Function.Injective (fun p : (a : Fin m) × (Fin (N a) × Fin q) =>
      ((p.1, (p.2.1 : ℕ)), p.2.2)) := by
    intro p r h
    cases p with | mk a p =>
      cases r with | mk b r =>
        have hab : a = b := congrArg (fun z : (Fin m × ℕ) × Fin q => z.1.1) h
        subst b
        congr 1
        exact Prod.ext (Fin.ext (congrArg (fun z : (Fin m × ℕ) × Fin q => z.1.2) h))
          (congrArg (fun z : (Fin m × ℕ) × Fin q => z.2) h)
  exact iIndepFun.hasLaw_pi
    (fun p => cavityGroupGaussian_coordinate_law p.1 p.2.1 p.2.2)
    ((cavityGroupGaussian_coordinates_independent m q).precomp hinj)

theorem cavityGroupGaussian_finite_standard_law {m q : ℕ} (N : Fin m → ℕ) :
    HasLaw (fun x : Fin m → ℕ → Fin q → ℝ =>
      (WithLp.toLp 2 (fun p : (a : Fin m) × (Fin (N a) × Fin q) =>
        x p.1 p.2.1 p.2.2) : EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (cavityGroupGaussianRows m q) := by
  have h : HasLaw (WithLp.toLp 2 : (((a : Fin m) × (Fin (N a) × Fin q)) → ℝ) →
      EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q)))
      (stdGaussian (EuclideanSpace ℝ ((a : Fin m) × (Fin (N a) × Fin q))))
      (Measure.pi (fun _ : (a : Fin m) × (Fin (N a) × Fin q) => gaussianReal 0 1)) :=
    ⟨(by fun_prop), map_pi_eq_stdGaussian⟩
  exact h.fun_comp (cavityGroupGaussian_finite_array_law N)

end InvariantIsing

end

end OAI
