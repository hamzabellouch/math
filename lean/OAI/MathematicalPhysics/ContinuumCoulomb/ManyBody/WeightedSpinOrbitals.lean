import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RealSpinOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.FullSpinTensorCoefficients

namespace OAI

/-! Spin lifting of the actual weighted spatial matrix elements. Only
integrability of the spatial product is required, including at nuclear poles. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem weighted_realSpinOrbital_integrable (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ s : Fin 2) :
    Integrable (fun x => (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s)) := by
  by_cases hs : s=σ
  · by_cases ht : s=τ
    · subst s
      subst τ
      have hi : Integrable (fun x => ((F x*f x*g x : ℝ) : ℂ)) := hI.ofReal
      convert hi using 1
      funext x
      simp only [realSpinOrbital,ite_true,Complex.star_def,Complex.conj_ofReal,
        Complex.ofReal_mul]
      ring
    · have ht' : σ ≠ τ := by simpa only [hs] using ht
      simp only [realSpinOrbital,hs,ht',ite_true,ite_false,mul_zero]
      exact integrable_zero _ _ _
  · simp only [realSpinOrbital,hs,ite_false,star_zero,zero_mul,mul_zero]
    exact integrable_zero _ _ _

theorem weighted_realSpinOrbital_inner (F f g : Position → ℝ) (σ τ : Fin 2) :
    (∑ s : Fin 2, ∫ x, (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s)) =
      if σ=τ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
  by_cases h : σ=τ
  · subst τ
    have hp (s : Fin 2) :
        (∫ x, (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g σ x s)) =
          if s=σ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
      by_cases hs : s=σ
      · subst s
        simp only [realSpinOrbital,ite_true,Complex.star_def,Complex.conj_ofReal,
          ← Complex.ofReal_mul,integral_complex_ofReal,mul_assoc]
      · simp [realSpinOrbital,hs]
    simp only [hp,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  · have hz (s : Fin 2) (x : Position) :
        (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s) = 0 := by
      by_cases hs : s=σ
      · subst s
        simp [realSpinOrbital,h]
      · simp [realSpinOrbital,hs]
    simp only [hz,integral_zero,Finset.sum_const_zero,h,ite_false]

theorem flatWeighted_realSpinOrbital_integrable (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ : Fin 2) :
    Integrable (fun z : Fin 2 × (Fin 3 → ℝ) => (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*
        Coulomb.flatSpinOrbital (realSpinOrbital g τ) z)) Coulomb.spinSpaceMeasure := by
  apply Coulomb.integrable_finite_count_prod
  intro s
  exact (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_of_integrable
    (weighted_realSpinOrbital_integrable F f g hI σ τ s)

theorem flatWeighted_realSpinOrbital_inner (F f g : Position → ℝ)
    (hI : Integrable (fun x => F x*f x*g x)) (σ τ : Fin 2) :
    (∫ z : Fin 2 × (Fin 3 → ℝ), (F (WithLp.toLp 2 z.2):ℂ)*
      (star (Coulomb.flatSpinOrbital (realSpinOrbital f σ) z)*
        Coulomb.flatSpinOrbital (realSpinOrbital g τ) z) ∂Coulomb.spinSpaceMeasure) =
      if σ=τ then (↑(∫ x, F x*f x*g x):ℂ) else 0 := by
  unfold Coulomb.spinSpaceMeasure
  rw [Coulomb.integral_finite_count_prod _ (fun s =>
    (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_of_integrable
      (weighted_realSpinOrbital_integrable F f g hI σ τ s))]
  rw [← weighted_realSpinOrbital_inner F f g σ τ]
  apply Finset.sum_congr rfl
  intro s _
  have hm : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (Fin 3)
  exact hm.integral_comp'
    (fun x => (F x:ℂ)*(star (realSpinOrbital f σ x s)*realSpinOrbital g τ x s))

end ContinuumCoulomb

end

end OAI
