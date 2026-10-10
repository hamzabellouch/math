import OAI.Analysis.KadisonKastler.ReducingCommutantCorner
import OAI.Analysis.KadisonKastler.FactorSpatialSplit
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert

namespace OAI

/-! # Faithful normal restriction of a factor to a nonzero reducing subspace -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial Filter
open scoped Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (M : VonNeumannAlgebra H) (hE : E.starProjection ∈ M.commutant)
  (hE0 : E.starProjection ≠ 0) (hM : ScalarCenter M)

def reducingFactorEquiv : Algebra M ≃⋆ₐ[ℂ]
    Algebra (generatedVonNeumannAlgebra (commutantReducingHom E M hE).range) :=
  boundedWeakNormalEquiv M (commutantReducingHom E M hE)
    (commutantReducingHom_injective E M hE hE0 (scalarCenter_commutant M hM))
    (commutantReducingHom_boundedWeakNormal E M hE)

theorem reducingFactorEquiv_apply (a : Algebra M) :
    (reducingFactorEquiv E M hE hE0 hM a).val = cornerCompression E a.val := rfl

theorem reducingFactorEquiv_tendsto_weak {ι : Type u} {l : Filter ι}
    (a : ι → Algebra M) (b : Algebra M) (C : ℝ)
    (hn : ∀ᶠ i in l, ‖a i‖ ≤ C)
    (hw : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) (x y : E) :
    Tendsto (fun i => inner ℂ y ((reducingFactorEquiv E M hE hE0 hM (a i)).val x)) l
      (𝓝 (inner ℂ y ((reducingFactorEquiv E M hE hE0 hM b).val x))) := by
  simp only [reducingFactorEquiv_apply]
  exact commutantReducingHom_boundedWeakNormal E M hE a b C hn hw x y

omit hE0 hM in
theorem reducingRepresentation_comparison (N : VonNeumannAlgebra H)
    (hEN : E.starProjection ∈ N.commutant) (a : Algebra M) (b : Algebra N) :
    ‖commutantReducingHom E M hE a - commutantReducingHom E N hEN b‖ ≤
      ‖a.val - b.val‖ := by
  change ‖cornerCompression E a.val - cornerCompression E b.val‖ ≤ _
  rw [← map_sub]
  exact norm_cornerCompression_le E (a.val - b.val)

omit E hE hE0 hM in
theorem scalarCenter_of_isII1 (h : IsII1Factor M.toStarSubalgebra) : ScalarCenter M := by
  intro T hT hc
  obtain ⟨z, hz⟩ := traceHilbert_factor h ⟨T, hT⟩
    (fun a => Subtype.ext (hc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
