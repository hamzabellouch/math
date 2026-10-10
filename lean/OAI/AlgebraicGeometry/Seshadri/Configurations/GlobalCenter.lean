import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.CenteredSections
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticSubsystem
import OAI.AlgebraicGeometry.Seshadri.Configurations.AffineCenter

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.PointCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [Fintype σ] {X : Scheme}

theorem centeredOpen_complement_singleton {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (p : Γ((SectionOpens.isoOpen (s none)).toScheme, ⊤) →+* K)
    (hp : p.comp ((SectionOpens.isoOpen (s none)).ι.appTop.hom.comp k) = RingHom.id K) :
    let U := SectionOpens.isoOpen (s none)
    let a := fun i => coefficient (sectionFrame (s none)) (restrictSection U.ι (s i))
    let t := shiftedSections k s (fun i => -p (a (some i)))
    ∃ y : X, ∀ x : X, x ∉ centeredOpen t ↔ x = y := by
  let U := SectionOpens.isoOpen (s none)
  let a := fun i => coefficient (sectionFrame (s none)) (restrictSection U.ι (s i))
  let kU := U.ι.appTop.hom.comp k
  let t := shiftedSections k s (fun i => -p (a (some i)))
  obtain ⟨hUa, hgen⟩ := sectionsMorphism_chart_generators k s hs none
  let : IsAffine U.toScheme := hUa
  let : Algebra K Γ(U.toScheme, ⊤) := kU.toAlgebra
  let p' : Γ(U.toScheme, ⊤) →ₐ[K] K :=
    { p with commutes' := fun c => RingHom.congr_fun hp c }
  have ha : Function.Surjective (MvPolynomial.aeval (R := K) a) := hgen
  have hnorm : a none = 1 := sectionFrame_normalized _
  have ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤ := shiftedSections_cover k s hs _
  have heq : U.ι ⁻¹ᵁ centeredOpen t =
      ⨆ i, U.toScheme.basicOpen (a i - algebraMap K Γ(U.toScheme, ⊤) (p' (a i))) := by
    rw [iSup_option]
    simp only [hnorm, map_one, sub_self, Scheme.basicOpen_zero, bot_sup_eq]
    unfold centeredOpen
    rw [Scheme.Hom.preimage_iSup]
    congr 1
    funext i
    rw [preimage_isoOpen _ U.ι (sectionFrame (s none)), coefficient_shiftedSections]
    simp only [shiftedVariable, map_add, eval₂Hom_X', map_mul, eval₂Hom_C]
    change U.toScheme.basicOpen (a (some i) + kU (-p (a (some i))) * a none) = _
    simp only [hnorm, mul_one, map_neg, sub_eq_add_neg]
    rfl
  let y : X := U.ι (affineCenter p)
  refine ⟨y, fun x => ?_⟩
  constructor
  · intro hx
    have hxU : x ∈ U := by
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (ht.ge (Set.mem_univ x))
      cases j with
      | none => simpa only [t, shiftedSections_none] using hj
      | some i => exact False.elim (hx (Opens.mem_iSup.mpr ⟨i, hj⟩))
    have hx' : (⟨x, hxU⟩ : U) ∉ U.ι ⁻¹ᵁ centeredOpen t := hx
    rw [heq] at hx'
    have hh := (affine_center_cutout a ha p' (⟨x, hxU⟩ : U)).mp hx'
    exact congrArg U.ι hh
  · rintro rfl hx
    have hh : affineCenter p ∈ U.ι ⁻¹ᵁ centeredOpen t := hx
    rw [heq] at hh
    exact ((affine_center_cutout a ha p' (affineCenter p)).mpr rfl) hh

end
end MaximalSeshadri.Projective
end


end
end

end OAI
