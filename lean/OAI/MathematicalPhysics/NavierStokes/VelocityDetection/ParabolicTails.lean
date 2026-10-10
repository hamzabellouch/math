import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.ParabolicComparison
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialCalculusPartialDSub

namespace OAI

noncomputable section
namespace VelocityDetection.ParabolicComparison
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped ZeroAtInfty

theorem comparison_C0 {n : ℕ} {ν : ℝ} {a : VectorField n} {g h : ScalarField n}
    (ρ σ : ℝ → C₀(Coord n, ℝ)) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Ici 0)) (hσc : ContinuousOn σ (Ici 0))
    (hρ : ContDiff ℝ 2 (fun q : ℝ × Coord n => ρ q.1 q.2))
    (hσ : ContDiff ℝ 2 (fun q : ℝ × Coord n => σ q.1 q.2))
    (heqρ : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection a (fun s Y => ρ s Y) t X =
        ν * laplacian (fun s Y => ρ s Y) t X + g t X)
    (heqσ : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => σ s X) t + advection a (fun s Y => σ s Y) t X =
        ν * laplacian (fun s Y => σ s Y) t X + h t X)
    (hinit : ∀ X, ρ 0 X ≤ σ 0 X) (hsource : ∀ t, 0 ≤ t → ∀ X, g t X ≤ h t X) :
    ∀ t, 0 ≤ t → ∀ X, ρ t X ≤ σ t X := by
  have hdiff (t : ℝ) (ht : 0 ≤ t) (X : Coord n) :
      deriv (fun s => σ s X - ρ s X) t +
          advection a (fun s Y => σ s Y - ρ s Y) t X =
        ν * laplacian (fun s Y => σ s Y - ρ s Y) t X + (h t X - g t X) := by
    have hσt : ContDiff ℝ 2 (fun s => σ s X) := hσ.comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ 2 (fun s : ℝ => (s, X)))
    have hρt : ContDiff ℝ 2 (fun s => ρ s X) := hρ.comp (contDiff_id.prodMk contDiff_const :
      ContDiff ℝ 2 (fun s : ℝ => (s, X)))
    rw [deriv_fun_sub (hσt.differentiable (by norm_num) t) (hρt.differentiable (by norm_num) t)]
    have hσx : ContDiff ℝ 2 (fun Y => σ t Y) := hσ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ 2 (fun Y : Coord n => (t, Y)))
    have hρx : ContDiff ℝ 2 (fun Y => ρ t Y) := hρ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ 2 (fun Y : Coord n => (t, Y)))
    have hlap := SpatialCalculus.laplacian_sub hσx hρx X
    have hadv : advection a (fun s Y => σ s Y - ρ s Y) t X =
      advection a (fun s Y => σ s Y) t X - advection a (fun s Y => ρ s Y) t X := by
      change (∑ i : Fin n, a t X i *
        SpatialCalculus.partialD i (fun Y => σ t Y - ρ t Y) X) = _
      simp_rw [SpatialCalculus.partialD_sub _ (hσx.differentiable (by norm_num))
        (hρx.differentiable (by norm_num)), mul_sub, Finset.sum_sub_distrib]
      rfl
    rw [hadv]
    change _ = ν * laplacian (fun _ Y => σ t Y - ρ t Y) 0 X + (h t X - g t X)
    rw [hlap]
    have h1 := heqσ t ht X
    have h2 := heqρ t ht X
    change _ + _ = ν * laplacian (fun _ Y => σ t Y) 0 X + _ at h1
    change _ + _ = ν * laplacian (fun _ Y => ρ t Y) 0 X + _ at h2
    linarith
  have hp := nonnegative_of_continuous_C0 (fun t => σ t - ρ t) hν
    (hσc.sub hρc) (hσ.sub hρ) hdiff (fun X => sub_nonneg.mpr (hinit X))
    (fun t ht X => sub_nonneg.mpr (hsource t ht X))
  exact fun t ht X => sub_nonneg.mp (hp t ht X)

theorem uniqueness_C0 {n : ℕ} {ν : ℝ} {a : VectorField n} {g : ScalarField n}
    (ρ σ : ℝ → C₀(Coord n, ℝ)) (hν : 0 ≤ ν)
    (hρc : ContinuousOn ρ (Ici 0)) (hσc : ContinuousOn σ (Ici 0))
    (hρ : ContDiff ℝ 2 (fun q : ℝ × Coord n => ρ q.1 q.2))
    (hσ : ContDiff ℝ 2 (fun q : ℝ × Coord n => σ q.1 q.2))
    (heqρ : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection a (fun s Y => ρ s Y) t X =
        ν * laplacian (fun s Y => ρ s Y) t X + g t X)
    (heqσ : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => σ s X) t + advection a (fun s Y => σ s Y) t X =
        ν * laplacian (fun s Y => σ s Y) t X + g t X)
    (hinit : ∀ X, ρ 0 X = σ 0 X) : ∀ t, 0 ≤ t → ρ t = σ t := by
  have hu := comparison_C0 ρ σ hν hρc hσc hρ hσ heqρ heqσ
    (fun X => (hinit X).le) (fun _ _ _ => le_rfl)
  have hl := comparison_C0 σ ρ hν hσc hρc hσ hρ heqσ heqρ
    (fun X => (hinit X).ge) (fun _ _ _ => le_rfl)
  intro t ht
  ext X
  exact le_antisymm (hu t ht X) (hl t ht X)

end VelocityDetection.ParabolicComparison
end

end OAI
