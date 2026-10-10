import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealLocal
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
open scoped nonZeroDivisors

theorem dimension_le_of_local_bound {T : Type*} [TopologicalSpace T] (d : ℕ)
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [← ENat.WithBot.lt_add_one_iff]
  suffices topologicalKrullDim T < ((d+1 : ℕ) : WithBot ℕ∞) by
    simpa only [Nat.cast_add, Nat.cast_one] using this
  apply Order.krullDim_lt_coe_iff.mpr
  intro c
  obtain ⟨x, hx⟩ := c.head.isIrreducible.nonempty
  obtain ⟨U, hxU, hU⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → T) U.isOpen.isOpenEmbedding_subtypeVal
  have hm (i : Fin (c.length + 1)) :
      ((Subtype.val : U → T) ⁻¹' (c i : Set T)).Nonempty := by
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact c.strictMono.monotone (Fin.zero_le i) hx
  let c' : LTSeries {Z : IrreducibleCloseds T |
      ((Subtype.val : U → T) ⁻¹' (Z : Set T)).Nonempty} :=
    ⟨c.length, fun i => ⟨c i, hm i⟩, fun i => c.step i⟩
  have hc := (Order.LTSeries.length_le_krullDim (c'.map e.symm e.symm.strictMono)).trans hU
  have hc' : c.length ≤ d := by exact_mod_cast hc
  omega

variable {X : Scheme.{0}}

private theorem mono_comp_iso {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ B) (e : B ≅ D) (hg : Mono g) : Mono (g ≫ e.hom) := by
  let : Mono g := hg
  infer_instance

private theorem mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) (hg : Mono g) : Mono (e.inv ≫ g) := by
  let : Mono g := hg
  infer_instance

theorem section_coefficient_regular (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsRegular (coefficient e (restrictSection U.ι s)) := by
  let g : PiExponentSeshadri.UnitEndomorphism.unit U.toScheme ⟶
      PiExponentSeshadri.UnitEndomorphism.unit U.toScheme := restrictSection U.ι s ≫ e.hom
  have hmap : Mono ((Scheme.Modules.restrictFunctor U.ι).map s) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.restrictFunctor U.ι)
      inferInstance _ _ s ‹Mono s›
  have hrestrict : Mono (restrictSection U.ι s) :=
    mono_iso_inv_comp (C := U.toScheme.Modules) (Scheme.Modules.restrictUnitIso U.ι)
      ((Scheme.Modules.restrictFunctor U.ι).map s) hmap
  have : Mono g := mono_comp_iso (C := U.toScheme.Modules) (restrictSection U.ι s) e hrestrict
  exact PiExponentSeshadri.UnitEndomorphism.equation_regular g ⊤

theorem section_affine_coefficient_nonZeroDivisor (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ (Γ(X, U))⁰ := by
  let f := U.1.topIso.commRingCatIsoToRingEquiv
  rw [← MulEquivClass.map_nonZeroDivisors f]
  exact Submonoid.mem_map.mpr ⟨_,
    isRegular_iff_mem_nonZeroDivisors.mp (section_coefficient_regular L s U.1 e), rfl⟩

theorem regular_sectionZero_dimension_le (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d + 1) :
    topologicalKrullDim (zeroIdeal L s).subscheme ≤ d := by
  let I := zeroIdeal L s
  apply dimension_le_of_local_bound d
  intro y
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne (I.subschemeι y)
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  let f := I.subschemeCover.f U
  refine ⟨f.opensRange, ?_, ?_⟩
  · change y ∈ (I.subschemeCover.f U).opensRange
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
    exact hxW
  · have hr := section_affine_coefficient_nonZeroDivisor L s U e
    have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    rw [← zeroIdeal_on_frame L s U e] at hdrop
    have hring : ringKrullDim Γ(X,U) ≤ d + 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      change topologicalKrullDim (Spec Γ(X,U)) ≤ d+1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hdim
    have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤ d := by
      have hbound := hdrop.trans hring
      exact ENat.WithBot.add_le_add_one_right_iff.mp hbound
    have hsource : topologicalKrullDim (Spec (I.subschemeCover.X U)) ≤ d := by
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hquot
    change topologicalKrullDim f.opensRange.toScheme ≤ d
    exact (IsHomeomorph.topologicalKrullDim_eq _
      f.isoOpensRange.hom.homeomorph.isHomeomorph).symm.le.trans hsource

end
end PiExponent.NumericalAmpleness

end OAI
