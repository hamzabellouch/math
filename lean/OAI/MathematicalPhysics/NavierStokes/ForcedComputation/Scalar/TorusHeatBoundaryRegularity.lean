import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatInitialContinuity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatLaplacianTransfer
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.TangentCone.Prod

namespace OAI

/-! All orders of heat regularity on the closed initial half-cylinder. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows PlanarHamiltonian Set Filter
open scoped ContDiff Topology BigOperators

theorem heatDataLaplacian_smooth {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (scalarLaplacian g) :=
  ContDiff.sum (fun j _ => spatialD_smooth j (spatialD_smooth j hg))

theorem heatDataLaplacian_periodic {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : PlanePeriodic g) : PlanePeriodic (scalarLaplacian g) := by
  intro x n
  apply Finset.sum_congr rfl
  intro j _
  exact spatialD_periodic (spatialD_smooth j hg) (spatialD_periodic hg hp j) j x n

/-- The joint derivative, expressed entirely by evolutions of smooth initial data. -/
def torusHeatDerivative (g : Plane → ℝ) (p : ℝ × Plane) : (ℝ × Plane) →L[ℝ] ℝ :=
  torusHeatEvolution (scalarLaplacian g) p.1 p.2 • ContinuousLinearMap.fst ℝ ℝ Plane +
    ∑ j : Fin 2, torusHeatEvolution (spatialD j g) p.1 p.2 •
      (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℝ Plane)

theorem torusHeatDerivative_apply (g : Plane → ℝ) (p v : ℝ × Plane) :
    torusHeatDerivative g p v =
      v.1 * torusHeatEvolution (scalarLaplacian g) p.1 p.2 +
        ∑ j : Fin 2, v.2 j * torusHeatEvolution (spatialD j g) p.1 p.2 := by
  simp only [torusHeatDerivative, add_apply, smul_apply,
    sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  congr 1
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

theorem torusHeatEvolution_fderiv_positive {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) {t : ℝ} (ht : 0 < t) (x : Plane) :
    fderiv ℝ (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2) (t,x) =
      torusHeatDerivative g (t,x) := by
  let f : ℝ × Plane → ℝ := fun p => torusHeatEvolution g p.1 p.2
  have hmem : (t,x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨ht, mem_univ _⟩
  have hd : HasFDerivAt f (fderiv ℝ f (t,x)) (t,x) :=
    ((torusHeatEvolution_smooth_positive g hg.continuous).differentiableOn (by simp)
      (t,x) hmem).differentiableAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
        |>.hasFDerivAt
  have htime : fderiv ℝ f (t,x) (1,0) =
      torusHeatEvolution (scalarLaplacian g) t x := by
    have h := hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact h.unique (torusHeatEvolution_time_data hg hp ht x)
  have hspace (v : Plane) : fderiv ℝ f (t,x) (0,v) =
      ∑ j : Fin 2, v j * torusHeatEvolution (spatialD j g) t x := by
    have h := (hd.comp x (hasFDerivAt_prodMk_right t x)).fderiv
    have hv := congrArg (fun L : Plane →L[ℝ] ℝ => L v) h
    change fderiv ℝ (torusHeatEvolution g t) x v = fderiv ℝ f (t,x) (0,v) at hv
    rw [← hv, scalar_directional_basis]
    apply Finset.sum_congr rfl
    intro j _
    rw [torusHeatEvolution_spatialD hg hp]
  apply ContinuousLinearMap.ext
  intro v
  rw [torusHeatDerivative_apply]
  have he : v = v.1 • (1, (0 : Plane)) + (0, v.2) := by ext <;> simp
  calc
    _ = fderiv ℝ f (t,x) (v.1 • (1, (0 : Plane)) + (0, v.2)) := congrArg _ he
    _ = _ := by rw [map_add, map_smul, htime, hspace]; rfl

theorem torusHeatDerivative_continuousOn {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) :
    ContinuousOn (torusHeatDerivative g) (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) := by
  apply ContinuousOn.add
  · exact (torusHeatEvolution_continuousOn (heatDataLaplacian_smooth hg |>.of_le (by simp))
      (heatDataLaplacian_periodic hg hp)).smul continuousOn_const
  · exact continuousOn_finsetSum _ (fun j _ =>
      (torusHeatEvolution_continuousOn (spatialD_smooth j hg |>.of_le (by simp))
        (spatialD_periodic hg hp j)).smul continuousOn_const)

theorem torusHeatEvolution_hasFDerivWithinAt {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) {p : ℝ × Plane}
    (hp₀ : p ∈ Ici (0 : ℝ) ×ˢ (univ : Set Plane)) :
    HasFDerivWithinAt (fun q : ℝ × Plane => torusHeatEvolution g q.1 q.2)
      (torusHeatDerivative g p) (Ici (0 : ℝ) ×ˢ univ) p := by
  have hc : closure (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) = Ici (0 : ℝ) ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioi, closure_univ]
  have hcont := torusHeatEvolution_continuousOn (hg.of_le (by simp)) hp
  have hs : Ioi (0 : ℝ) ×ˢ (univ : Set Plane) ⊆ Ici (0 : ℝ) ×ˢ univ := by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    change 0 < s at hs
    change 0 ≤ s ∧ y ∈ (univ : Set Plane)
    exact ⟨hs.le,hy⟩
  have hlim := (torusHeatDerivative_continuousOn hg hp p hp₀).mono
    hs
  have he : (fun q : ℝ × Plane => fderiv ℝ
      (fun r : ℝ × Plane => torusHeatEvolution g r.1 r.2) q) =ᶠ[
        𝓝[Ioi (0 : ℝ) ×ˢ (univ : Set Plane)] p] torusHeatDerivative g := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact torusHeatEvolution_fderiv_positive hg hp hq.1 q.2
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv
    ((torusHeatEvolution_smooth_positive g hg.continuous).differentiableOn (by simp))
    ((convex_Ioi (0 : ℝ)).prod convex_univ) (isOpen_Ioi.prod isOpen_univ)
    (fun q hq => (hcont q (hc ▸ hq)).mono hs)
    (hlim.congr' he.symm)
  rwa [hc] at h

theorem torusHeatEvolution_contDiffOn {g : Plane → ℝ}
    (hg : ContDiff ℝ ∞ g) (hp : PlanePeriodic g) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) := by
  have hi (n : ℕ) : ∀ (g : Plane → ℝ), ContDiff ℝ ∞ g → PlanePeriodic g →
      ContDiffOn ℝ n (fun p : ℝ × Plane => torusHeatEvolution g p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) := by
    induction n with
    | zero =>
      intro g hg hp
      exact contDiffOn_zero.mpr (torusHeatEvolution_continuousOn (hg.of_le (by simp)) hp)
    | succ n ih =>
      intro g hg hp
      rw [Nat.cast_add, Nat.cast_one]
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        ((uniqueDiffOn_Ici (0 : ℝ)).prod uniqueDiffOn_univ)).mpr
      refine ⟨by simp, torusHeatDerivative g, ?_, fun p hp₀ =>
        torusHeatEvolution_hasFDerivWithinAt hg hp hp₀⟩
      exact ((ih _ (heatDataLaplacian_smooth hg) (heatDataLaplacian_periodic hg hp)).smul
        contDiffOn_const).add (ContDiffOn.sum (fun j _ =>
          (ih _ (spatialD_smooth j hg) (spatialD_periodic hg hp j)).smul contDiffOn_const))
  exact contDiffOn_infty.mpr (fun n => hi n g hg hp)

end ForcedComputation.VelocityDetector

end

end OAI
