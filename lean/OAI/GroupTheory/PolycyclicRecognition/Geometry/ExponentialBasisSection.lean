import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProduct
import Mathlib.Topology.Maps.Basic

namespace OAI

/-! # A global section for a linear exponential quotient

A product of lifted basis one-parameter subgroups is a continuous global
section. Only the individual exponential curves are used; the exponential
map need not be globally invertible or even be supplied as a continuous map.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff BigOperators

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem exponentialProduct_linear_quotient
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G}
    (d : E →ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπ : ∀ x, (π (Exp x)).toAdd = d x)
    {n : ℕ} (v : Fin n → E) (t : Fin n → ℝ) :
    (π (exponentialProduct Exp v t)).toAdd = ∑ i, t i • d (v i) := by
  induction n with
  | zero => simp [exponentialProduct]
  | succ n ih =>
    change (π (Exp (t 0 • v 0) *
      exponentialProduct Exp (v ∘ Fin.succ) (t ∘ Fin.succ))).toAdd = _
    rw [map_mul, toAdd_mul]
    have hhead : (π (Exp (t 0 • v 0))).toAdd = t 0 • d (v 0) :=
      (hπ _).trans (d.map_smul _ _)
    exact (congrArg₂ (· + ·) hhead (ih (v ∘ Fin.succ) (t ∘ Fin.succ))).trans
      (Fin.sum_univ_succ (fun i => t i • d (v i))).symm

theorem exists_smooth_section_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ (s : W → G) (l : W →L[ℝ] E),
      ContMDiff (𝓘(ℝ, W)) (𝓘(ℝ, E)) ∞ s ∧ s 0 = 1 ∧
      (∀ w, (π (s w)).toAdd = w) ∧
      HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, E)) s 0 l ∧
      d.comp l.toLinearMap = LinearMap.id := by
  let b := Module.finBasis ℝ W
  choose v hv using fun i => hd (b i)
  let c : W →L[ℝ] (Fin (Module.finrank ℝ W) → ℝ) :=
    b.equivFun.toLinearMap.toContinuousLinearMap
  let s : W → G := fun w => exponentialProduct Exp v (c w)
  let l : W →L[ℝ] E := (tangentCombination v).comp c
  refine ⟨s, l, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hExp.contMDiff_exponentialProduct v).comp c.contDiff.contMDiff
  · change exponentialProduct Exp v (c 0) = 1
    rw [map_zero]
    exact hExp.exponentialProduct_zero v
  · intro w
    rw [show s w = exponentialProduct Exp v (c w) from rfl,
      exponentialProduct_linear_quotient d π hπ]
    simp only [hv]
    exact b.sum_repr w
  · have hc : HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, Fin (Module.finrank ℝ W) → ℝ))
        c 0 c := c.hasFDerivAt.hasMFDerivAt
    have hp := hExp.hasMFDerivAt_exponentialProduct_zero v
    have hzero : c 0 = 0 := map_zero c
    rw [← hzero] at hp
    exact hp.comp 0 hc
  · ext w
    change d ((tangentCombination v) (c w)) = w
    rw [tangentCombination_apply, map_sum]
    simp only [map_smul, hv]
    exact b.sum_repr w

theorem exists_continuous_section_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x) :
    ∃ s : W → G, Continuous s ∧ s 0 = 1 ∧ ∀ w, (π (s w)).toAdd = w := by
  obtain ⟨s, _, hs, hs0, hsπ, _⟩ :=
    exists_smooth_section_of_exponential_linear_quotient hExp d hd π hπ
  exact ⟨s, hs.continuous, hs0, hsπ⟩

theorem isQuotientMap_of_exponential_linear_quotient
    [FiniteDimensional ℝ W]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (d : E →ₗ[ℝ] W) (hd : Function.Surjective d)
    (π : G →* Multiplicative W) (hπ : ∀ x, (π (Exp x)).toAdd = d x)
    (hc : Continuous (fun g => (π g).toAdd)) :
    Topology.IsQuotientMap (fun g => (π g).toAdd) := by
  obtain ⟨s, hs, _, hright⟩ :=
    exists_continuous_section_of_exponential_linear_quotient hExp d hd π hπ
  exact Topology.IsQuotientMap.of_inverse hs hc hright

end PolycyclicRecognition

end

end OAI
