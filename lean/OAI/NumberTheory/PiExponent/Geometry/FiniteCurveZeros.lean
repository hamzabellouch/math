import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.FiniteZeroEuler
import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_scheme_isFinite (f : X ⟶ Y) [IsProper f] [Finite X] : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact .of_isProper_of_locallyQuasiFinite f

lemma proper_finite_scheme_isAffine (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] : IsAffine X := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  exact isAffine_of_isAffineHom f

lemma proper_finite_functions (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    FiniteDimensional K Γ(X,⊤) := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  dsimp only
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (by
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

lemma proper_finite_germ_surjective (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    Function.Surjective (X.presheaf.germ ⊤ x trivial) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let p : PrimeSpectrum Γ(X,⊤) := (isAffineOpen_top X).isoSpec.hom ⟨x,trivial⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact IsArtinianRing.localization_surjective p.asIdeal.primeCompl (X.presheaf.stalk x)

theorem proper_finite_stalk_finrank_le (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    let _ : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
    let _ : Algebra K (X.presheaf.stalk x) :=
      ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    FiniteDimensional K (X.presheaf.stalk x) ∧
      Module.finrank K (X.presheaf.stalk x) ≤ Module.finrank K Γ(X,⊤) := by
  dsimp only
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) :=
    ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom K Γ(X,⊤) (X.presheaf.stalk x)).toLinearMap
  have hφ : Function.Surjective φ := proper_finite_germ_surjective f x
  exact ⟨Module.Finite.of_surjective φ hφ, φ.finrank_le_finrank_of_surjective hφ⟩

end

section
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]

lemma proper_irreducible_closed_subsingleton
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hi : IsIrreducible Z) (hp : Z ≠ Set.univ) : Z.Subsingleton := by
  let C : IrreducibleCloseds X := ⟨Z, hi, hZ⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin C := by
    rcases Order.krullDim_le_one_iff.mp hd C with hm | hm
    · exact hm
    · have he : C = T := le_antisymm (Set.subset_univ _) (hm (Set.subset_univ _))
      exact (hp (congrArg SetLike.coe he)).elim
  have hg (x : X) (hx : x ∈ Z) : IsGenericPoint x Z := by
    let D : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : D ≤ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
    have he : D = C := le_antisymm hle (hmin hle)
    exact congrArg SetLike.coe he
  intro x hx y hy
  exact (hg x hx).eq (hg y hy)

theorem proper_closed_finite_of_dimension_one [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hp : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨F, hF, hFc, hFi, hZF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZF]
  apply hF.sUnion
  intro C hC
  apply Set.Subsingleton.finite
  apply proper_irreducible_closed_subsingleton hd (hFc C hC) (hFi C hC)
  intro hc
  apply hp
  apply Set.eq_univ_of_univ_subset
  rw [hZF]
  exact hc ▸ Set.subset_sUnion_of_mem hC

open AlgebraicGeometry in

theorem integral_curve_proper_closed_finite (C : Scheme)
    [IsIntegral C] [IsNoetherian C] (hd : topologicalKrullDim C = 1)
    {Z : Set C} (hZ : IsClosed Z) (hp : Z ≠ Set.univ) : Z.Finite :=
  proper_closed_finite_of_dimension_one hd.le hZ hp

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

theorem finite_subscheme_of_curve [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Finite I.subscheme := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  have hp : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI
    exact Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he)
  have hf := proper_closed_finite_of_dimension_one hd I.support.isClosed hp
  have hr : (Set.range I.subschemeι).Finite := I.range_subschemeι ▸ hf
  let : Finite (Set.range I.subschemeι) := hr.to_subtype
  exact Finite.of_injective (fun x : I.subscheme =>
    (⟨I.subschemeι x, ⟨x,rfl⟩⟩ : Set.range I.subschemeι))
    (fun a b h => I.subschemeι.isEmbedding.injective (congrArg (fun z : Set.range I.subschemeι => (z : X)) h))

theorem curve_subscheme_isFinite [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsFinite (I.subschemeι ≫ f) := by
  let : Finite I.subscheme := finite_subscheme_of_curve f hd I hI
  exact proper_finite_scheme_isFinite (I.subschemeι ≫ f)

abbrev structuralStalkAlgebra (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

theorem proper_finite_finrank_eq_sum_stalks (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Fintype X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = ∑ x : X,
      let _ := structuralStalkAlgebra f x
      Module.finrank K (X.presheaf.stalk x) := by
  classical
  dsimp only
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Fintype (MaximalSpectrum Γ(X,⊤)) := Fintype.ofFinite _
  let e : X ≃ MaximalSpectrum Γ(X,⊤) :=
    (Equiv.Set.univ X).symm.trans ((isAffineOpen_top X).isoSpec.hom.homeomorph.toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum)
  rw [PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations Γ(X,⊤) K, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (e x).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact ((IsLocalization.algEquiv (e x).asIdeal.primeCompl
    (Localization.AtPrime (e x).asIdeal) (X.presheaf.stalk x)).restrictScalars K).toLinearEquiv.finrank_eq

end

open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}}

theorem proper_finite_euler (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper f] [Finite X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars f).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  let L : LineBundle X := ⟨structureSheaf X, fun x =>
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (structureSheaf X).IsQuasicoherent :=
    PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent L 0
  exact affine_eulerCharacteristic f (structureSheaf X) d

theorem proper_finite_euler_eq_sum_stalk_finrank
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      letI := structuralStalkAlgebra f x
      (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [proper_finite_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks f
  dsimp only at h
  exact_mod_cast h

theorem proper_finite_euler_eq_sum_stalk_lengths
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  rw [proper_finite_euler_eq_sum_stalk_finrank]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars f).toAlgebra
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  let : Algebra ℂ (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower ℂ Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite ℂ Γ(X, ⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom ℂ Γ(X, ⊤) (X.presheaf.stalk x)).toLinearMap
  let : Module.Finite ℂ (X.presheaf.stalk x) :=
    Module.Finite.of_surjective φ (proper_finite_germ_surjective f x)
  have h := PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (PiExponent.CurveLocalOrder.residueAugmentation ℂ (X.presheaf.stalk x))
    (PiExponent.CurveLocalOrder.residueAugmentation_algebraMap ℂ (X.presheaf.stalk x))
  rw [h]
  simp

end PiExponentSeshadri.Geometry

end

end OAI
