import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem affine_scalar_regular_on_open [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) (U : X.Opens) :
    Function.Injective (fun a : Γ(X, U) =>
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf U a b
  intro x hx
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have hreg : X.presheaf.germ ⊤ x trivial r ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap
      (((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl) (X.presheaf.stalk x) hr
  have h := congrArg (fun v : Γ(X, U) => X.presheaf.germ U x hx v) hab
  simp only [map_mul, TopCat.Presheaf.germ_res_apply] at h
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left h

theorem scalarEnd_mono_of_regular [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) : Mono (scalarEnd r) := by
  have hm : Mono (scalarEnd r).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact affine_scalar_regular_on_open r hr U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

theorem framed_section_mono_of_regular [IsAffine X] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M)
    (hr : coefficient e s ∈ nonZeroDivisors Γ(X, ⊤)) : Mono s := by
  have he : s ≫ e.hom = scalarEnd (coefficient e s) := by
    apply endValue_injective
    rw [endValue_scalarEnd]
    rfl
  have hm : Mono (s ≫ e.hom) := by
    rw [he]
    exact scalarEnd_mono_of_regular _ hr
  exact (mono_comp_iff_of_mono s e.hom).mp hm

theorem section_mono_of_regular_affine_frames (L : LineBundle X)
    (s : GlobalSections X L.sheaf)
    (H : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        coefficient e (restrictSection U.1.ι s) ∈
          nonZeroDivisors Γ(U.1.toScheme, ⊤)) : Mono s := by
  apply CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, e, he⟩ := H x
  have : IsAffine U.1.toScheme := U.2
  have hm : Mono (restrictSection U.1.ι s) := framed_section_mono_of_regular e _ he
  refine ⟨U.1, hx, ?_⟩
  let : IsIso (Scheme.Modules.restrictUnitIso U.1.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
  exact (mono_comp_iff_of_isIso (Scheme.Modules.restrictUnitIso U.1.ι).inv _).mp hm

end
end PiExponent.NumericalAmpleness

end OAI
