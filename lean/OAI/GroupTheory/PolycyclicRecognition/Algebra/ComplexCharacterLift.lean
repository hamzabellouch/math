import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Topology.Algebra.Group.Units

namespace OAI

/-! # Additive lifts of complex characters

Rotational diagonal characters in a simply connected solvable group have
continuous logarithms. Uniqueness of covering lifts makes the normalized
logarithm additive; its value on an exponential curve is the prescribed
linear weight, with no choice of a global principal logarithm.
-/

noncomputable section
namespace PolycyclicRecognition

open Function

/-- Two continuous lifts through the complex exponential agree everywhere
when they agree at one point of a connected domain. -/
theorem eq_of_continuous_complex_exp_eq
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ x, Complex.exp (f x) = Complex.exp (g x))
    (x₀ : X) (h₀ : f x₀ = g x₀) : f = g := by
  apply Complex.isCoveringMap_exp.eq_of_comp_eq hf hg _ x₀ h₀
  funext x
  exact Subtype.ext (he x)

/-- A continuous character into the nonzero complex numbers has a
normalized additive lift on a simply connected group. -/
theorem exists_additive_lift_complex_character
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SimplyConnectedSpace G] [LocallyPathConnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ π : G →* Multiplicative ℂ, Continuous (fun g => (π g).toAdd) ∧
      ∀ g, Complex.exp (π g).toAdd = (χ g : ℂ) := by
  let c : C(G, ℂ) := ⟨fun g => (χ g : ℂ), hχ⟩
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts c
      (a₀ := 1) (e₀ := 0) (by simp [c]) (fun g => (χ g).ne_zero)
  have he (g : G) : Complex.exp (F g) = (χ g : ℂ) := congrFun hFexp g
  have hmul (g h : G) : F (g * h) = F g + F h := by
    have heq : (fun h : G => F (g * h) - F g) = F := by
      refine eq_of_continuous_complex_exp_eq
        ((F.continuous.comp (continuous_const.mul continuous_id)).sub continuous_const)
        F.continuous (fun h => ?_) 1 (by simp [hF0])
      rw [Complex.exp_sub, he, he, he, map_mul, Units.val_mul]
      exact mul_div_cancel_left₀ _ (χ g).ne_zero
    have hv := congrFun heq h
    exact (sub_eq_iff_eq_add.mp hv).trans (add_comm _ _)
  refine ⟨{
    toFun := fun g => Multiplicative.ofAdd (F g)
    map_one' := hF0
    map_mul' := hmul }, F.continuous, he⟩

/-- The additive lift recovers the exact weight along a continuous
one-parameter curve starting at the identity. -/
theorem additive_lift_complex_character_on_curve
    {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →* ℂˣ) (π : G →* Multiplicative ℂ)
    (hπ : Continuous (fun g => (π g).toAdd))
    (he : ∀ g, Complex.exp (π g).toAdd = (χ g : ℂ))
    (γ : ℝ → G) (hγ : Continuous γ) (hγ0 : γ 0 = 1)
    (z : ℂ) (hz : ∀ t, (χ (γ t) : ℂ) = Complex.exp ((t : ℂ) * z)) :
    ∀ t, (π (γ t)).toAdd = (t : ℂ) * z := by
  have hf : (fun t => (π (γ t)).toAdd) = (fun t : ℝ => (t : ℂ) * z) := by
    exact eq_of_continuous_complex_exp_eq (hπ.comp hγ)
      (Complex.continuous_ofReal.mul continuous_const)
      (fun t => (he (γ t)).trans (hz t)) 0 (by simp [hγ0])
  exact congrFun hf

end PolycyclicRecognition

end

end OAI
