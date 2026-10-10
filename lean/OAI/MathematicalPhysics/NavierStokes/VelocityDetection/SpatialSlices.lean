import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.SpatialCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem contDiff_slice {n : ℕ} {v : VectorField n}
    (hv : ContDiff ℝ ∞ (fun q : ℝ × Coord n => v q.1 q.2)) (t : ℝ) :
    ContDiff ℝ ∞ (v t) :=
  hv.comp (show ContDiff ℝ ∞ (fun X : Coord n => (t, X)) from
    contDiff_const.prodMk contDiff_id)

theorem partialD_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Coord n → ℝ)
    (hf : ∀ k ∈ s, Differentiable ℝ (f k)) (i : Fin n) (X : Coord n) :
    partialD i (fun Y => ∑ k ∈ s, f k Y) X = ∑ k ∈ s, partialD i (f k) X := by
  rw [partialD_eq_fderiv i (by fun_prop (disch := aesop)), fderiv_fun_sum]
  · simp only [sum_apply]
    exact Finset.sum_congr rfl (fun k hk => (partialD_eq_fderiv i (hf k hk) X).symm)
  · exact fun k hk => hf k hk X

theorem divergence_congr_at {n : ℕ} {u v : VectorField n} (t : ℝ) (X : Coord n)
    (heq : u t = v t) : divergence u t X = divergence v t X := by
  simp only [divergence, spatialD, heq]

theorem divergence_sum {ι : Type*} (s : Finset ι) (v : ι → VectorField 2)
    (hv : ∀ k ∈ s, ∀ t, ContDiff ℝ ∞ (v k t)) (t : ℝ) (X : Coord 2) :
    divergence (fun t X => ∑ k ∈ s, v k t X) t X = ∑ k ∈ s, divergence (v k) t X := by
  simp only [divergence]
  have h (i : Fin 2) : spatialD i (fun t X => (∑ k ∈ s, v k t X) i) t X =
      ∑ k ∈ s, spatialD i (fun t X => v k t X i) t X := by
    simp only [Finset.sum_apply]
    exact partialD_sum s (fun k X => v k t X i)
      (fun k hk => ((contDiff_apply ℝ ℝ i).comp (hv k hk t)).differentiable (by simp)) i X
  simp_rw [h]
  exact Finset.sum_comm

end VelocityDetection.SpatialCalculus
end

end OAI
