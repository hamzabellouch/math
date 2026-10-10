import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialIntegration

namespace OAI

noncomputable section
namespace VelocityDetection.ScalarMass
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem integralCLM_eq {n : ℕ} (r : Lp ℝ 1 (volume : Measure (Coord n))) :
    L1.integralCLM r = ∫ X, r X := by
  rw [← L1.integral_eq, L1.integral_eq_integral]

theorem hasDerivWithinAt_integral {n : ℕ} {ρ dρ : ScalarField n} {t : ℝ}
    {r : ℝ → Lp ℝ 1 (volume : Measure (Coord n))}
    {dr : Lp ℝ 1 (volume : Measure (Coord n))}
    (heq : ∀ s, (fun X => r s X) =ᵐ[volume] ρ s)
    (hdeq : (fun X => dr X) =ᵐ[volume] dρ t)
    (hd : HasDerivWithinAt r dr (Ici 0) t) :
    HasDerivWithinAt (fun s => ∫ X, ρ s X) (∫ X, dρ t X) (Ici 0) t := by
  have hh := (L1.integralCLM (α := Coord n) (E := ℝ) (μ := volume)).hasFDerivAt.comp_hasDerivWithinAt t hd
  have hval (s : ℝ) : L1.integralCLM (r s) = ∫ X, ρ s X :=
    (integralCLM_eq (r s)).trans (integral_congr_ae (heq s))
  have hdval : L1.integralCLM dr = ∫ X, dρ t X :=
    (integralCLM_eq dr).trans (integral_congr_ae hdeq)
  simpa only [Function.comp_def, hval, hdval] using hh

theorem mass_eq_primitive {n : ℕ} {ν : ℝ} {a : VectorField n} {g ρ : ScalarField n}
    {r dr : ℝ → Lp ℝ 1 (volume : Measure (Coord n))} {M : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 (uncurry ρ))
    (hi : ∀ t, 0 ≤ t → ∀ i, Integrable (SpatialCalculus.partialD i (ρ t)))
    (hii : ∀ t, 0 ≤ t → ∀ i,
      Integrable (SpatialCalculus.partialD i (SpatialCalculus.partialD i (ρ t))))
    (hg : ∀ t, 0 ≤ t → Integrable (g t))
    (ha : ∀ t, 0 ≤ t → ∀ i, ContDiff ℝ 1 (fun X => a t X i))
    (hac : ∀ t, 0 ≤ t → ∀ i, HasCompactSupport (fun X => a t X i))
    (hdiv : ∀ t, 0 ≤ t → ∀ X, divergence a t X = 0)
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection a ρ t X = ν * laplacian ρ t X + g t X)
    (hrep : ∀ t, (fun X => r t X) =ᵐ[volume] ρ t)
    (hdrep : ∀ t, 0 ≤ t → (fun X => dr t X) =ᵐ[volume] (fun X => deriv (fun s => ρ s X) t))
    (hr : ∀ t, 0 ≤ t → HasDerivWithinAt r (dr t) (Ici 0) t)
    (hM : ∀ t, 0 ≤ t → HasDerivWithinAt M (∫ X, g t X) (Ici 0) t)
    (hzero : (∫ X, ρ 0 X) = M 0) : ∀ t, 0 ≤ t → (∫ X, ρ t X) = M t := by
  have hrate (t : ℝ) (ht : 0 ≤ t) : (∫ X, deriv (fun s => ρ s X) t) = ∫ X, g t X := by
    have hρt : ContDiff ℝ 2 (ρ t) := hρ.comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ 2 (fun X : Coord n => (t, X)))
    exact SpatialCalculus.scalar_mass_rate hρt (hi t ht) (hii t ht) (hg t ht)
      (ha t ht) (hac t ht) (hdiv t ht) (heq t ht)
  have hm (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (fun s => ∫ X, ρ s X) (∫ X, g t X) (Ici 0) t := by
    rw [← hrate t ht]
    exact hasDerivWithinAt_integral (dρ := fun s X => deriv (fun u => ρ u X) s) hrep (hdrep t ht) (hr t ht)
  intro t ht
  apply eq_of_has_deriv_right_eq (f' := fun s => ∫ X, g s X)
      (fun s hs => (hm s hs.1).mono (fun x hx => hs.1.trans hx))
      (fun s hs => (hM s hs.1).mono (fun x hx => hs.1.trans hx))
      (fun s hs => ((hm s hs.1).continuousWithinAt.mono Icc_subset_Ici_self))
      (fun s hs => ((hM s hs.1).continuousWithinAt.mono Icc_subset_Ici_self)) hzero t
  exact ⟨ht, le_rfl⟩

theorem integrable_of_L1_rep {n : ℕ} {f : Coord n → ℝ}
    {r : Lp ℝ 1 (volume : Measure (Coord n))} (heq : (fun X => r X) =ᵐ[volume] f) :
    Integrable f := (L1.integrable_coeFn r).congr heq

end VelocityDetection.ScalarMass
end

end OAI
