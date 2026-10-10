import OAI.Analysis.KadisonKastler.II1CoreCenter
import OAI.Analysis.KadisonKastler.NormalCyclicRealization

namespace OAI

/-! # Realizing the finite-factor trace by a vector in the given representation -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem exists_tracial_vector_of_II1_cyclic
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    ∃ η : H, ‖η‖ = 1 ∧ Function.Injective (algebraVectorMap M η) ∧
      ∀ a b : Algebra M, inner ℂ η ((a.val * b.val) η) =
        inner ℂ η ((b.val * a.val) η) := by
  let hf := traceHilbert_factor hM
  let hu := traceHilbert_nonzero hM
  let K := TraceFreeHilbert hf hM.diffuse hM.finite hu
  let N := traceFreeHilbertClosure hf hM.diffuse hM.finite hu
  let τ := traceFreeHilbertClosureTrace hf hM.diffuse hM.finite hu
  let e := traceFreeHilbertEquiv hf hM.diffuse hM.finite hu
  let : TopologicalSpace.SeparableSpace K := concreteTraceHilbert_separable hM
  have hc : DenseRange (algebraVectorMap N τ.vector) :=
    traceFreeHilbertClosureTrace_cyclic hf hM.diffuse hM.finite hu
  have hs : Function.Injective (algebraVectorMap N τ.vector) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply τ.separating
    change a.val τ.vector - b.val τ.vector = 0
    exact sub_eq_zero.mpr hab
  obtain ⟨W, hW⟩ := exists_spatial_of_normal_cyclic_separating e
    (traceFreeHilbertEquiv_boundedWeakNormal hM) Ω τ.vector hcyc hc hsep hs
  refine ⟨W.symm τ.vector, ?_, spatialVectorTransport_separating e W hW τ.vector hs, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    exact τ.norm_vector
  · intro a b
    have hab := spatialVectorTransport_state e W hW τ.vector (a * b)
    have hba := spatialVectorTransport_state e W hW τ.vector (b * a)
    change inner ℂ (W.symm τ.vector) ((a * b).val (W.symm τ.vector)) =
      inner ℂ (W.symm τ.vector) ((b * a).val (W.symm τ.vector))
    rw [hab, hba, map_mul, map_mul]
    exact τ.cyclic (e a) (e b)

theorem exists_tracial_vector_of_II1_separating
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) :
    ∃ η : H, ‖η‖ = 1 ∧ Function.Injective (algebraVectorMap M η) ∧
      ∀ a b : Algebra M, inner ℂ η ((a.val * b.val) η) =
        inner ℂ η ((b.val * a.val) η) := by
  let φ := M.toStarSubalgebra.subtype
  have hs : Function.Injective (fun a : Algebra M => φ a Ω) := hsep
  have hφ : BoundedWeakNormal M φ := by
    intro ι l a b C ha hb
    exact hb
  let e := normalCyclicEquiv M φ Ω hs hφ
  let N := normalCyclicAlgebra M φ Ω
  have hN : Generator.IsII1Factor N.toStarSubalgebra :=
    Generator.isII1Factor_of_starAlgEquiv e hM (vonNeumann_wotClosed N)
  obtain ⟨η, hηn, hηs, hηt⟩ := exists_tracial_vector_of_II1_cyclic hN
    (normalCyclicVector M φ Ω) (normalCyclicAlgebra_separating M φ Ω hs hφ)
    (normalCyclicAlgebra_cyclic M φ Ω)
  refine ⟨η.val, hηn, ?_, ?_⟩
  · intro a b hab
    apply e.injective
    apply hηs
    apply Subtype.ext
    change (normalCyclicHom M φ Ω a η : H) = (normalCyclicHom M φ Ω b η : H)
    rw [normalCyclicHom_apply, normalCyclicHom_apply]
    exact hab
  · intro a b
    have hh := hηt (e a) (e b)
    change inner ℂ η (((e a) * (e b)).val η) =
      inner ℂ η (((e b) * (e a)).val η) at hh
    rw [← map_mul, ← map_mul] at hh
    change inner ℂ η (normalCyclicHom M φ Ω (a * b) η) =
      inner ℂ η (normalCyclicHom M φ Ω (b * a) η) at hh
    simp only [Submodule.coe_inner, normalCyclicHom_apply] at hh
    exact hh

end

end KadisonKastler

end OAI
