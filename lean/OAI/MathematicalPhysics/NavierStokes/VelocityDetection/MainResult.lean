import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.EffectivePrescriptions

namespace OAI

noncomputable section
namespace VelocityDetection
open Set Function MeasureTheory Turing
open scoped ContDiff
open Effective Effective.MachineRecipe

theorem main_result :
    ∃ B : ℕ, 0 < B ∧
      (∀ s : ℝ, |deriv (deriv SmoothBump.profile) s| ≤ (B:ℝ)) ∧
    ∀ (ν : ℝ), 0 < ν → ComputableReal ν →
    ∀ (b N : ℕ) [NeZero b] [NeZero N]
      (M : TM0.Machine (Fin b) (Fin N)) (w : List (Fin b)),
    ∃ (Ftor Fcyl : ℝ → VectorField 3),
      (compile B M w).Represents .torus Ftor ∧
      (compile B M w).Represents .cylinder Fcyl ∧
      (ContDiff ℝ ∞ (uncurry (Ftor ν)) ∧
        (∀ t, FactorsThrough (Ftor ν t) PeriodicSpace.cover) ∧
        (∃ K : Set (Coord 2), IsCompact K ∧ (∀ X ∈ K, ∀ i, X i ∈ Ioo (0:ℝ) 1) ∧
          ∀ t X, PeriodicSpace.cover (horizontal X) ∉ PeriodicSpace.cover '' K → Ftor ν t X = 0) ∧
        (∀ T d, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) T, ∀ X,
          ‖iteratedFDeriv ℝ d (uncurry (Ftor ν)) (t,X)‖ ≤ C) ∧
        ∃ u : VectorField 3,
          ContDiff ℝ ∞ (uncurry u) ∧ TorusClass.ComparisonClass u (fun _ _ => 0) ∧
          NavierStokes ν u (fun _ _ => 0) (Ftor ν) ∧
          (Observation.torusEvent u ↔ (TM0.eval M w).Dom) ∧
          ∀ (v : VectorField 3) (p : ScalarField 3), TorusClass.ComparisonClass v p →
            NavierStokes ν v p (Ftor ν) →
            ∀ t ≥ 0, (∀ X, v t X = u t X) ∧ (∀ X, p t X = 0)) ∧
      (ContDiff ℝ ∞ (uncurry (Fcyl ν)) ∧
        UniformDerivatives.Bounded (fun _ : Unit => uncurry (Fcyl ν)) ∧
        (∀ t X z, Fcyl ν t (update X 2 z) = Fcyl ν t X) ∧
        (∀ T : ℝ, ∃ K : Set (Coord 2), IsCompact K ∧ ∀ t ∈ Icc (0:ℝ) T,
          ∀ X : Coord 3, horizontal X ∉ K → Fcyl ν t X = 0) ∧
        ∃ u : VectorField 3,
          ContDiff ℝ ∞ (uncurry u) ∧
          Cylinder.ComparisonClass (fun t x => u t (Cylinder.join x)) (fun _ _ => 0) ∧
          NavierStokes ν u (fun _ _ => 0) (Fcyl ν) ∧
          (∀ t ≥ 0, (∀ x, 0 ≤ u t (Cylinder.join x) 2) ∧
            Integrable (fun x => u t (Cylinder.join x) 2) Cylinder.measure) ∧
          (Observation.planeEvent u ↔ (TM0.eval M w).Dom) ∧
          ∀ (v : VectorField 3) (p : ScalarField 3),
            Cylinder.ComparisonClass (fun t x => v t (Cylinder.join x))
              (fun t x => p t (Cylinder.join x)) →
            NavierStokes ν v p (Fcyl ν) →
            ∀ t ≥ 0, (∀ X, v t X = u t X) ∧ (∀ X, p t X = 0)) := by
  refine ⟨SmoothBump.bound,SmoothBump.bound_pos,SmoothBump.second_bound,?_⟩
  intro ν hν _hcomputable b N _ _ M w
  exact ⟨(fun μ => MachineTorus.force μ M w), (fun μ => MachineCylinder.force μ M w),
    Program.compile_represents .torus M w, Program.compile_represents .cylinder M w,
    MachineTorus.analytic_result ν hν M w, MachineCylinder.analytic_result ν hν M w⟩

end VelocityDetection
end

end OAI
