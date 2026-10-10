import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPeriodizationDerivatives
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.CompactRapidDifferential

namespace OAI

/-! Local periodization preserves the full residual equation. A pressure
projection, when supplied by the torus Poisson solver, is a separate algebraic
step and does not change the velocity or its trajectories. -/

noncomputable section
open Set
open scoped BigOperators
namespace RapidForcing.CompactEmbedding

theorem field_chartSupported {u : Field Space} (hu : Supported u)
    (hneg : ∀ t, t < 0 → ∀ x, u t x = 0) : ChartSupported (field u) := by
  intro t x hx
  by_cases ht : 0 ≤ t
  · have hu' : unembed x ∉ K := by
      intro h
      exact hx (by simpa only [embed_unembed] using embed_mem_chart h)
    simp [field, hu.zero_off ht hu']
  · simp [field, hneg t (lt_of_not_ge ht)]

theorem periodic_divergence {u : Field Space} (hu : ChartSupported u) (t : ℝ) (x : Space) :
    divergence (periodic u) t x = divergence u t (representative x) := by
  unfold divergence
  simp_rw [periodic_spatialD hu]
  rfl

theorem periodic_advection {u : Field Space} (hu : ChartSupported u) (t : ℝ) (x : Space) :
    advection (periodic u) t x = advection u t (representative x) := by
  unfold advection
  simp_rw [periodic_spatialD hu]
  rfl

theorem periodic_laplace {u : Field Space} (hu : ChartSupported u) (t : ℝ) (x : Space) :
    laplace (periodic u) t x = laplace u t (representative x) := by
  unfold laplace
  simp_rw [periodic_spatialD hu]
  apply Finset.sum_congr rfl
  intro i _
  rw [periodic_spatialD (hu.spatialD i)]
  rfl

theorem periodic_residual {u : Field Space} (hu : ChartSupported u) (ν t : ℝ) (x : Space) :
    residual ν (periodic u) t x = residual ν u t (representative x) := by
  unfold residual
  rw [periodic_timeD, periodic_advection hu, periodic_laplace hu]
  rfl

theorem periodic_navierStokes {u f : Field Space} {ν : ℝ}
    (hu : ChartSupported u) (hNS : NavierStokes ν f u (fun _ _ => 0)) :
    NavierStokes ν (periodic f) (periodic u) (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht x
    have h := hNS.1 t ht (representative x)
    simp only [gradient, spatialD, fderiv_const_apply, zero_apply,
      zero_smul, Finset.sum_const_zero, neg_zero, zero_add] at h ⊢
    rw [periodic_timeD, periodic_advection hu, periodic_laplace hu]
    exact h
  · intro t ht x
    rw [periodic_divergence hu]
    exact hNS.2.1 t ht (representative x)
  · intro x
    exact hNS.2.2 (representative x)

theorem navierStokes_pressure_projection {u g : Field Space} {ν : ℝ}
    {φ : Field ℝ} (hNS : NavierStokes ν g u (fun _ _ => 0)) :
    NavierStokes ν (fun t x => g t x - gradient φ t x) u (fun t x => -φ t x) := by
  refine ⟨?_, hNS.2⟩
  intro t ht x
  have h := hNS.1 t ht x
  simp only [gradient, spatialD, fderiv_const_apply, zero_apply,
    zero_smul, Finset.sum_const_zero, neg_zero, zero_add] at h
  have hg : gradient (fun t x => -φ t x) t x = -gradient φ t x := by
    unfold gradient spatialD
    change (∑ i, fderiv ℝ (-(φ t)) x (basis i) • basis i) = _
    rw [fderiv_neg]
    simp only [neg_apply, neg_smul, Finset.sum_neg_distrib]
  rw [hg, neg_neg, h]
  module

end RapidForcing.CompactEmbedding

end

end OAI
