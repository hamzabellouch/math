import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearOrbitSpan
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixGenericPosition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SeparateIrreducibleComponent

namespace OAI

/-! # A conjugator in simultaneous transverse position

Irreducibility makes every nonzero orbit span. In the polynomial topology,
a single element can therefore place a finite family of lines outside all
specified repelling hyperplanes and attracting lines, in both directions.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

variable {K G : Type*} [Field K] [Group G] [TopologicalSpace G]
    [PreirreducibleSpace G] [ContinuousInv G] {n : ℕ}

theorem exists_irreducible_forward_inverse_avoidance
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction.toMonoidHom.comp ι))]
    {I : Type*} [Finite I] (v : I → Fin n → K) (hv : ∀ i, v i ≠ 0)
    (W : I → Submodule K (Fin n → K)) (hW : ∀ i, W i ≠ ⊤) :
    ∃ g : G, ∀ i, linearAction (ι g) (v i) ∉ W i ∧
      linearAction (ι g⁻¹) (v i) ∉ W i := by
  apply exists_simultaneous_forward_inverse_avoidance ι hι v W
  · intro i
    exact irreducible_linear_orbit_span
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction.toMonoidHom.comp ι))
      (hv i)
  · exact hW

theorem exists_irreducible_transverse_conjugator
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    [Representation.IsIrreducible (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction.toMonoidHom.comp ι))]
    {I : Type*} [Finite I] (v : I → Fin n → K)
    (φ : I → Module.Dual K (Fin n → K)) (hφv : ∀ i, φ i (v i) = 1)
    (hline : ∀ i, Submodule.span K ({v i} : Set (Fin n → K)) ≠ ⊤) :
    ∃ g : G, ∀ i j,
      φ i (linearAction (ι g) (v j)) ≠ 0 ∧
      φ i (linearAction (ι g⁻¹) (v j)) ≠ 0 ∧
      linearAction (ι g) (v j) ∉ Submodule.span K ({v i} : Set (Fin n → K)) ∧
      linearAction (ι g⁻¹) (v j) ∉ Submodule.span K ({v i} : Set (Fin n → K)) := by
  classical
  let W (p : (I × I) × Bool) : Submodule K (Fin n → K) :=
    if p.2 then Submodule.span K ({v p.1.1} : Set (Fin n → K)) else (φ p.1.1).ker
  have hv (i : I) : v i ≠ 0 := by
    intro h
    have he := hφv i
    rw [h, map_zero] at he
    exact zero_ne_one he
  have hW (p : (I × I) × Bool) : W p ≠ ⊤ := by
    cases p with
    | mk ij b =>
      cases b
      · intro he
        have hm : v ij.1 ∈ (φ ij.1).ker := by
          change v ij.1 ∈ W (ij, false)
          rw [he]
          trivial
        have hz : φ ij.1 (v ij.1) = 0 := hm
        rw [hφv] at hz
        exact one_ne_zero hz
      · exact hline ij.1
  obtain ⟨g, hg⟩ := exists_irreducible_forward_inverse_avoidance ι hι
    (fun p : (I × I) × Bool => v p.1.2) (fun p => hv p.1.2) W hW
  refine ⟨g, fun i j => ?_⟩
  have hk := hg ((i, j), false)
  have hl := hg ((i, j), true)
  exact ⟨hk.1, hk.2, hl.1, hl.2⟩

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
