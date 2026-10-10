import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.Adjunction
import OAI.AlgebraicGeometry.LogKodaira.BaseChange

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.RelativeCanonical
open scoped TensorProduct
open CanonicalAdjunction DifferentialBaseChange

 

def relativeCanonicalEquiv
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (n r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    [Algebra.IsStandardSmoothOfRelativeDimension r A B]
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    Canonical R B (n + r) ≃ₗ[B] Canonical A B r :=
  (Classical.choose (smooth_canonical_adjunction R A B n r)).symm.trans
    ((TensorProduct.congr (determinantCoordinate (b.baseChange B))
      (LinearEquiv.refl B (Canonical A B r))).trans
        (TensorProduct.lid B (Canonical A B r)))

lemma relativeCanonicalEquiv_wedge
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (n r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    [Algebra.IsStandardSmoothOfRelativeDimension r A B]
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (z : Fin r → KaehlerDifferential R B) :
    relativeCanonicalEquiv R A B n r b
      (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z)) =
      exteriorPower.ιMulti B r (KaehlerDifferential.map R A B B ∘ z) := by
  have hb : KaehlerDifferential.mapBaseChange R A B ∘ (b.baseChange B) =
      KaehlerDifferential.map R R A B ∘ b := by
    funext i
    simp [Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul]
  rw [← hb, ← Classical.choose_spec (smooth_canonical_adjunction R A B n r)
    (b.baseChange B) z]
  simp [relativeCanonicalEquiv, determinantCoordinate_wedge, Module.Basis.det_self]

 

lemma relative_canonical_ext
    (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module B M]
    (n r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    [Algebra.IsStandardSmoothOfRelativeDimension r A B]
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (l₁ l₂ : Canonical R B (n + r) →ₗ[B] M)
    (h : ∀ z : Fin r → KaehlerDifferential R B,
      l₁ (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z)) =
      l₂ (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z))) : l₁ = l₂ := by
  classical
  let e := relativeCanonicalEquiv R A B n r b
  have hcomp : l₁.comp e.symm.toLinearMap = l₂.comp e.symm.toLinearMap := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
    rintro _ ⟨v, rfl⟩
    choose z hz using fun i => KaehlerDifferential.map_surjective R A B (v i)
    have hv : KaehlerDifferential.map R A B B ∘ z = v := funext hz
    have he : e.symm (exteriorPower.ιMulti B r v) =
        exteriorPower.ιMulti B (n + r)
          (Fin.append (KaehlerDifferential.map R R A B ∘ b) z) := by
      apply e.injective
      rw [e.apply_symm_apply, relativeCanonicalEquiv_wedge, hv]
    change l₁ (e.symm _) = l₂ (e.symm _)
    rw [he]
    exact h z
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomp (e x)
  simpa using hx

lemma differential_map_tower
    (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra B C] [IsScalarTower A B C] [IsScalarTower R B C]
    (x : KaehlerDifferential R A) :
    KaehlerDifferential.map R R B C (KaehlerDifferential.map R R A B x) =
      KaehlerDifferential.map R R A C x := by
  have he : ((KaehlerDifferential.map R R B C).restrictScalars A).comp
      (KaehlerDifferential.map R R A B) = KaehlerDifferential.map R R A C := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R A)
    rintro _ ⟨a, rfl⟩
    simp [IsScalarTower.algebraMap_apply A B C]
  exact LinearMap.congr_fun he x

lemma differential_map_relative
    (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra B C] [IsScalarTower A B C] [IsScalarTower R B C]
    (x : KaehlerDifferential R B) :
    KaehlerDifferential.map R A C C (KaehlerDifferential.map R R B C x) =
      KaehlerDifferential.map A A B C (KaehlerDifferential.map R A B B x) := by
  have he : ((KaehlerDifferential.map R A C C).restrictScalars B).comp
      (KaehlerDifferential.map R R B C) =
      (KaehlerDifferential.map A A B C).comp (KaehlerDifferential.map R A B B) := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation R B)
    rintro _ ⟨a, rfl⟩
    simp
  exact LinearMap.congr_fun he x

 

theorem relative_canonical_naturality
    (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Nontrivial B] [Nontrivial C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra B C] [IsScalarTower A B C] [IsScalarTower R B C]
    (n r : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A]
    [Algebra.IsStandardSmoothOfRelativeDimension r A B]
    [Algebra.IsStandardSmoothOfRelativeDimension r A C]
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A)) :
    ((relativeCanonicalEquiv R A C n r b).toLinearMap.restrictScalars B).comp
        (exteriorDifferentialMap R R B C (n + r)) =
      (exteriorDifferentialMap A A B C r).comp
        (relativeCanonicalEquiv R A B n r b).toLinearMap := by
  apply relative_canonical_ext R A B _ n r b
  intro z
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, exteriorDifferentialMap, exteriorScalarMap_wedge]
  have hv : KaehlerDifferential.map R R B C ∘
      Fin.append (KaehlerDifferential.map R R A B ∘ b) z =
      Fin.append (KaehlerDifferential.map R R A C ∘ b)
        (KaehlerDifferential.map R R B C ∘ z) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [differential_map_tower]
    | right i => simp
  rw [hv, relativeCanonicalEquiv_wedge, relativeCanonicalEquiv_wedge,
    exteriorScalarMap_wedge]
  congr 1
  funext i
  exact differential_map_relative R A B C (z i)

end ReverseLogKodaira.RelativeCanonical

namespace ReverseLogKodaira.BasedRelativeCanonical
open CanonicalAdjunction DifferentialBaseChange RelativeCanonical

lemma formallySmooth_mapBaseChange_injective
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B x).mp hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0, map_zero] at hy
  exact hy.symm

 

def basedAdjunction
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    (⋀[B]^n (BaseDifferentials R A B)) ⊗[B] Canonical A B r ≃ₗ[B]
      Canonical R B (n + r) :=
  (exact_canonical_adjunction (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) (formallySmooth_mapBaseChange_injective R A B)
    (KaehlerDifferential.exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B) (b.baseChange B) c).choose

 
def basedRelativeCanonicalEquiv
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Canonical R B (n + r) ≃ₗ[B] Canonical A B r :=
  (basedAdjunction R A B n r b c).symm.trans
    ((TensorProduct.congr (determinantCoordinate (b.baseChange B))
      (LinearEquiv.refl B (Canonical A B r))).trans
        (TensorProduct.lid B (Canonical A B r)))

end ReverseLogKodaira.BasedRelativeCanonical

namespace ReverseLogKodaira.BasedRelativeCanonical
open CanonicalAdjunction DifferentialBaseChange RelativeCanonical

lemma basedAdjunction_wedge
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (v : Fin n → BaseDifferentials R A B) (z : Fin r → KaehlerDifferential R B) :
    basedAdjunction R A B n r b c
      (exteriorPower.ιMulti B n v ⊗ₜ[B]
        exteriorPower.ιMulti B r (KaehlerDifferential.map R A B B ∘ z)) =
      exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.mapBaseChange R A B ∘ v) z) :=
  (exact_canonical_adjunction (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) (formallySmooth_mapBaseChange_injective R A B)
    (KaehlerDifferential.exact_mapBaseChange_map R A B)
    (KaehlerDifferential.map_surjective R A B) (b.baseChange B) c).choose_spec v z

lemma basedRelativeCanonicalEquiv_general_wedge
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (v : Fin n → BaseDifferentials R A B) (z : Fin r → KaehlerDifferential R B) :
    basedRelativeCanonicalEquiv R A B n r b c
      (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.mapBaseChange R A B ∘ v) z)) =
      (b.baseChange B).det v •
        exteriorPower.ιMulti B r (KaehlerDifferential.map R A B B ∘ z) := by
  rw [← basedAdjunction_wedge R A B n r b c v z]
  simp [basedRelativeCanonicalEquiv, determinantCoordinate_wedge]

lemma basedRelativeCanonicalEquiv_wedge
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (z : Fin r → KaehlerDifferential R B) :
    basedRelativeCanonicalEquiv R A B n r b c
      (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z)) =
      exteriorPower.ιMulti B r (KaehlerDifferential.map R A B B ∘ z) := by
  have hb : KaehlerDifferential.mapBaseChange R A B ∘ (b.baseChange B) =
      KaehlerDifferential.map R R A B ∘ b := by
    funext i
    simp [Module.Basis.baseChange_apply, KaehlerDifferential.mapBaseChange_tmul]
  rw [← hb, basedRelativeCanonicalEquiv_general_wedge]
  simp [Module.Basis.det_self]

lemma based_relative_canonical_ext
    (R A B M : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] [AddCommGroup M] [Module B M]
    (n r : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (l₁ l₂ : Canonical R B (n + r) →ₗ[B] M)
    (h : ∀ z : Fin r → KaehlerDifferential R B,
      l₁ (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z)) =
      l₂ (exteriorPower.ιMulti B (n + r)
        (Fin.append (KaehlerDifferential.map R R A B ∘ b) z))) : l₁ = l₂ := by
  classical
  let e := basedRelativeCanonicalEquiv R A B n r b c
  have hcomp : l₁.comp e.symm.toLinearMap = l₂.comp e.symm.toLinearMap := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
    rintro _ ⟨v, rfl⟩
    choose z hz using fun i => KaehlerDifferential.map_surjective R A B (v i)
    have hv : KaehlerDifferential.map R A B B ∘ z = v := funext hz
    have he : e.symm (exteriorPower.ιMulti B r v) =
        exteriorPower.ιMulti B (n + r)
          (Fin.append (KaehlerDifferential.map R R A B ∘ b) z) := by
      apply e.injective
      rw [e.apply_symm_apply, basedRelativeCanonicalEquiv_wedge, hv]
    change l₁ (e.symm _) = l₂ (e.symm _)
    rw [he]
    exact h z
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hcomp (e x)
  simpa using hx

 

theorem based_relative_canonical_naturality
    (R A B C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A C] [Algebra R C] [IsScalarTower R A C]
    [Algebra B C] [IsScalarTower A B C] [IsScalarTower R B C]
    [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A C]
    (n r : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (d : Module.Basis (Fin r) C (KaehlerDifferential A C)) :
    ((basedRelativeCanonicalEquiv R A C n r b d).toLinearMap.restrictScalars B).comp
        (exteriorDifferentialMap R R B C (n + r)) =
      (exteriorDifferentialMap A A B C r).comp
        (basedRelativeCanonicalEquiv R A B n r b c).toLinearMap := by
  apply based_relative_canonical_ext R A B _ n r b c
  intro z
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, exteriorDifferentialMap, exteriorScalarMap_wedge]
  have hv : KaehlerDifferential.map R R B C ∘
      Fin.append (KaehlerDifferential.map R R A B ∘ b) z =
      Fin.append (KaehlerDifferential.map R R A C ∘ b)
        (KaehlerDifferential.map R R B C ∘ z) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [differential_map_tower]
    | right i => simp
  rw [hv, basedRelativeCanonicalEquiv_wedge, basedRelativeCanonicalEquiv_wedge,
    exteriorScalarMap_wedge]
  congr 1
  funext i
  exact differential_map_relative R A B C (z i)

end ReverseLogKodaira.BasedRelativeCanonical

end

end OAI
