import OAI.Analysis.KadisonKastler.NormalEquivOnto
import OAI.Analysis.KadisonKastler.ProductStateCentralizer

namespace OAI

/-! # The normal cyclic restriction of a specified separating vector -/

namespace KadisonKastler

open Filter Generator
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (M : VonNeumannAlgebra H) (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (ξ : K)

abbrev normalCyclicSpace := vectorOrbitClosure φ.range ξ

def normalCyclicVector : normalCyclicSpace M φ ξ := ⟨ξ, mem_vectorOrbitClosure _ _⟩

def normalCyclicHom : Algebra M →⋆ₐ[ℂ]
    (normalCyclicSpace M φ ξ →L[ℂ] normalCyclicSpace M φ ξ) :=
  (reducingRestriction (normalCyclicSpace M φ ξ) φ.range
    (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)).comp φ.rangeRestrict

@[simp] theorem normalCyclicHom_apply (a : Algebra M) (x : normalCyclicSpace M φ ξ) :
    (normalCyclicHom M φ ξ a x : K) = φ a x :=
  reducingRestriction_coe_apply _ _ (fun a _ hy => vectorOrbitClosure_invariant _ _ a hy)
    (φ.rangeRestrict a) x

theorem normalCyclicHom_separating
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) :
    Function.Injective (fun a : Algebra M => normalCyclicHom M φ ξ a (normalCyclicVector M φ ξ)) := by
  intro a b hab
  apply hs
  simpa only [normalCyclicHom_apply, normalCyclicVector] using
    congrArg (fun x : normalCyclicSpace M φ ξ => (x : K)) hab

theorem normalCyclicHom_injective
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) :
    Function.Injective (normalCyclicHom M φ ξ) := by
  intro a b hab
  exact normalCyclicHom_separating M φ ξ hs
    (congrArg (fun T => T (normalCyclicVector M φ ξ)) hab)

theorem normalCyclicHom_normal (hφ : BoundedWeakNormal M φ) :
    BoundedWeakNormal M (normalCyclicHom M φ ξ) := by
  intro ι l a b C ha hb x y
  simpa only [Submodule.coe_inner, normalCyclicHom_apply] using
    hφ a b C ha hb x.val y.val

theorem normalCyclicHom_cyclic :
    DenseRange (fun a : Algebra M => normalCyclicHom M φ ξ a (normalCyclicVector M φ ξ)) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z, ⟨b, rfl⟩, hb⟩ := Metric.mem_closure_iff.mp y.property ε hε
  obtain ⟨a, ha⟩ := b.property
  refine ⟨normalCyclicHom M φ ξ a (normalCyclicVector M φ ξ), ⟨a, rfl⟩, ?_⟩
  change dist y.val (↑(normalCyclicHom M φ ξ a (normalCyclicVector M φ ξ)) : K) < ε
  rw [normalCyclicHom_apply]
  change dist y.val (b.val ξ) < ε at hb
  change φ a = b.val at ha
  rwa [ha]

def normalCyclicAlgebra : VonNeumannAlgebra (normalCyclicSpace M φ ξ) :=
  generatedVonNeumannAlgebra (normalCyclicHom M φ ξ).range

def normalCyclicEquiv
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ) :
    Algebra M ≃⋆ₐ[ℂ] Algebra (normalCyclicAlgebra M φ ξ) :=
  boundedWeakNormalEquiv M (normalCyclicHom M φ ξ)
    (normalCyclicHom_injective M φ ξ hs) (normalCyclicHom_normal M φ ξ hφ)

@[simp] theorem normalCyclicEquiv_val
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ)
    (a : Algebra M) : (normalCyclicEquiv M φ ξ hs hφ a).val = normalCyclicHom M φ ξ a := rfl

theorem normalCyclicEquiv_coefficient
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ)
    (a : Algebra M) :
    inner ℂ (normalCyclicVector M φ ξ)
        ((normalCyclicEquiv M φ ξ hs hφ a).val (normalCyclicVector M φ ξ)) =
      inner ℂ ξ (φ a ξ) := by
  rw [normalCyclicEquiv_val]
  change inner ℂ ξ (↑(normalCyclicHom M φ ξ a (normalCyclicVector M φ ξ)) : K) = _
  rw [normalCyclicHom_apply]
  rfl

theorem normalCyclicEquiv_normal
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ) :
    BoundedWeakNormal M ((normalCyclicAlgebra M φ ξ).toStarSubalgebra.subtype.comp
      (normalCyclicEquiv M φ ξ hs hφ).toStarAlgHom) := normalCyclicHom_normal M φ ξ hφ

theorem normalCyclicEquiv_centralizes
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ)
    (a : Algebra M)
    (hc : ∀ b : Algebra M, inner ℂ ξ (φ (a * b) ξ) = inner ℂ ξ (φ (b * a) ξ)) :
    ProductStateCentralizes (normalCyclicAlgebra M φ ξ) (normalCyclicVector M φ ξ)
      (normalCyclicEquiv M φ ξ hs hφ a).val := by
  let e := normalCyclicEquiv M φ ξ hs hφ
  intro c hcN
  let b := e.symm ⟨c, hcN⟩
  have hcb : (e b).val = c := congrArg Subtype.val (e.apply_symm_apply ⟨c, hcN⟩)
  have hmul (x y : Algebra M) : (e x).val * (e y).val = (e (x * y)).val :=
    congrArg Subtype.val (map_mul e x y).symm
  change inner ℂ (normalCyclicVector M φ ξ) (((e a).val * c) (normalCyclicVector M φ ξ)) =
    inner ℂ (normalCyclicVector M φ ξ) ((c * (e a).val) (normalCyclicVector M φ ξ))
  rw [← hcb, hmul, hmul]
  rw [normalCyclicEquiv_coefficient, normalCyclicEquiv_coefficient]
  exact hc b

theorem normalCyclicAlgebra_separating
    (hs : Function.Injective (fun a : Algebra M => φ a ξ)) (hφ : BoundedWeakNormal M φ) :
    Function.Injective (algebraVectorMap (normalCyclicAlgebra M φ ξ) (normalCyclicVector M φ ξ)) := by
  intro a b hab
  let e := normalCyclicEquiv M φ ξ hs hφ
  have he : e.symm a = e.symm b := by
    apply normalCyclicHom_separating M φ ξ hs
    change (e (e.symm a)).val (normalCyclicVector M φ ξ) =
      (e (e.symm b)).val (normalCyclicVector M φ ξ)
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact hab
  exact e.symm.injective he

theorem normalCyclicAlgebra_cyclic :
    DenseRange (algebraVectorMap (normalCyclicAlgebra M φ ξ) (normalCyclicVector M φ ξ)) := by
  apply (normalCyclicHom_cyclic M φ ξ).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨normalCyclicHom M φ ξ a,
    subset_generatedVonNeumannAlgebra _ ⟨a, rfl⟩⟩, rfl⟩

end

end KadisonKastler

end OAI
