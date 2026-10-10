import OAI.Analysis.KadisonKastler.ReducingCommutantCorner

namespace OAI

/-! # Faithful cyclic restriction to a vector orbit

A separating vector remains separating after restriction to its closed
orbit, where it is cyclic by construction. The concrete reducing map
retains the commutant-corner identification.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (ξ : H)

abbrev cyclicOrbitSpace := vectorOrbitClosure M.toStarSubalgebra ξ

def cyclicOrbitVector : cyclicOrbitSpace M ξ := ⟨ξ, mem_vectorOrbitClosure _ _⟩

theorem cyclicOrbitProjection_mem : (cyclicOrbitSpace M ξ).starProjection ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  exact (vectorOrbitProjection_commutes M.toStarSubalgebra ξ ⟨a,ha⟩).symm

abbrev cyclicOrbitHom : Algebra M →⋆ₐ[ℂ]
    (cyclicOrbitSpace M ξ →L[ℂ] cyclicOrbitSpace M ξ) :=
  commutantReducingHom (cyclicOrbitSpace M ξ) M (cyclicOrbitProjection_mem M ξ)

@[simp] theorem cyclicOrbitHom_apply (a : Algebra M) (x : cyclicOrbitSpace M ξ) :
    (cyclicOrbitHom M ξ a x : H) = a.val x :=
  reducingRestriction_coe_apply _ _ _ a x

theorem cyclicOrbitHom_separating (hs : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (fun a : Algebra M => cyclicOrbitHom M ξ a (cyclicOrbitVector M ξ)) := by
  intro a b hab
  apply hs
  change a.val ξ = b.val ξ
  have he := congrArg (fun x : cyclicOrbitSpace M ξ => (x : H)) hab
  simpa only [cyclicOrbitHom_apply,cyclicOrbitVector] using he

theorem cyclicOrbitHom_injective (hs : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (cyclicOrbitHom M ξ) := by
  intro a b hab
  exact cyclicOrbitHom_separating M ξ hs
    (congrArg (fun T => T (cyclicOrbitVector M ξ)) hab)

def cyclicOrbitAlgebra : VonNeumannAlgebra (cyclicOrbitSpace M ξ) :=
  generatedVonNeumannAlgebra (cyclicOrbitHom M ξ).range

def cyclicOrbitEquiv (hs : Function.Injective (algebraVectorMap M ξ)) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (cyclicOrbitAlgebra M ξ) :=
  boundedWeakNormalEquiv M (cyclicOrbitHom M ξ) (cyclicOrbitHom_injective M ξ hs)
    (commutantReducingHom_boundedWeakNormal _ _ _)

@[simp] theorem cyclicOrbitEquiv_val (hs : Function.Injective (algebraVectorMap M ξ))
    (a : Algebra M) : (cyclicOrbitEquiv M ξ hs a).val = cyclicOrbitHom M ξ a := rfl

theorem cyclicOrbitAlgebra_separating (hs : Function.Injective (algebraVectorMap M ξ)) :
    Function.Injective (algebraVectorMap (cyclicOrbitAlgebra M ξ) (cyclicOrbitVector M ξ)) := by
  intro a b hab
  let e := cyclicOrbitEquiv M ξ hs
  apply e.symm.injective
  apply cyclicOrbitHom_separating M ξ hs
  change (e (e.symm a)).val (cyclicOrbitVector M ξ) =
    (e (e.symm b)).val (cyclicOrbitVector M ξ)
  rw [e.apply_symm_apply, e.apply_symm_apply]
  exact hab

theorem cyclicOrbitAlgebra_cyclic :
    DenseRange (algebraVectorMap (cyclicOrbitAlgebra M ξ) (cyclicOrbitVector M ξ)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  let b : Algebra (cyclicOrbitAlgebra M ξ) :=
    ⟨cyclicOrbitHom M ξ a, subset_generatedVonNeumannAlgebra _ ⟨a,rfl⟩⟩
  refine ⟨algebraVectorMap (cyclicOrbitAlgebra M ξ) (cyclicOrbitVector M ξ) b,
    ⟨b,rfl⟩, ?_⟩
  change dist y.val (↑(cyclicOrbitHom M ξ a (cyclicOrbitVector M ξ)) : H) < ε
  change dist y.val (a.val ξ) < ε at ha
  simpa only [cyclicOrbitHom_apply, cyclicOrbitVector] using ha

theorem cyclicOrbitAlgebra_commutant :
    (cyclicOrbitAlgebra M ξ).commutant =
      representedCorner (cyclicOrbitSpace M ξ) M.commutant (cyclicOrbitProjection_mem M ξ) :=
  commutant_reducingClosure _ _ _

end

end KadisonKastler

end OAI
