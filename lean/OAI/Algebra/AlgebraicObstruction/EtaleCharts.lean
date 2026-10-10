import Mathlib
import OAI.Algebra.FrobeniusObstruction.Obstruction
import OAI.Algebra.AlgebraicObstruction.EtaleCoefficients

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
open scoped TensorProduct

structure AffineEtaleChart (K α : Type) [CommRing K] where
  S : Type
  ringS : CommRing S
  baseS : Algebra (MvPolynomial α K) S
  etale : Algebra.Etale (MvPolynomial α K) S
  expansion : S →ₐ[MvPolynomial α K] MvPowerSeries α K

attribute [instance] AffineEtaleChart.ringS AffineEtaleChart.baseS AffineEtaleChart.etale

variable {K α : Type} [CommRing K]

noncomputable def AffineEtaleChart.base : AffineEtaleChart K α where
  S := MvPolynomial α K
  ringS := inferInstance
  baseS := inferInstance
  etale := inferInstance
  expansion := Algebra.ofId _ _

noncomputable def AffineEtaleChart.prod (E F : AffineEtaleChart K α) :
    AffineEtaleChart K α where
  S := E.S ⊗[MvPolynomial α K] F.S
  ringS := inferInstance
  baseS := inferInstance
  etale := Algebra.Etale.comp (MvPolynomial α K) E.S _
  expansion := Algebra.TensorProduct.lift E.expansion F.expansion
    (fun _ _ ↦ Commute.all _ _)

lemma AffineEtaleChart.range_left (E F : AffineEtaleChart K α) (x : E.S) :
    E.expansion x ∈ (E.prod F).expansion.range := by
  refine ⟨(Algebra.TensorProduct.includeLeft : E.S →ₐ[MvPolynomial α K] E.S ⊗[MvPolynomial α K] F.S) x, ?_⟩
  change E.expansion x * F.expansion 1 = E.expansion x
  simp

lemma AffineEtaleChart.range_right (E F : AffineEtaleChart K α) (x : F.S) :
    F.expansion x ∈ (E.prod F).expansion.range := by
  refine ⟨Algebra.TensorProduct.includeRight x, ?_⟩
  change E.expansion 1 * F.expansion x = F.expansion x
  simp

theorem LocalEtaleExpansion.affine {φ : MvPowerSeries α K} (E : LocalEtaleExpansion φ) :
    ∃ F : AffineEtaleChart K α, φ ∈ F.expansion.range := by
  obtain ⟨x,y,hy⟩ := IsLocalization.exists_mk'_eq E.denominators E.germ
  let T := Localization.Away (y : E.S)
  let g := E.expansion.comp (algebraMap E.S E.L)
  have hu : IsUnit (g y) := (IsLocalization.map_units E.L y).map E.expansion
  let H : T →+* MvPowerSeries α K := IsLocalization.Away.lift (y : E.S) hu
  let y' : Submonoid.powers (y : E.S) := ⟨y,⟨1,by simp⟩⟩
  let s' : T := IsLocalization.mk' T x y'
  let : Algebra.Etale (MvPolynomial α K) T := Algebra.Etale.comp _ E.S _
  have hH (p : MvPolynomial α K) : H (algebraMap _ T p) = algebraMap _ _ p := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial α K) E.S T,
      IsLocalization.Away.lift_eq]
    change E.expansion (algebraMap E.S E.L (algebraMap (MvPolynomial α K) E.S p)) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact E.coordinates p
  let F : AffineEtaleChart K α :=
    ⟨T, inferInstance, inferInstance, inferInstance, ⟨H,hH⟩⟩
  refine ⟨F, s', ?_⟩
  change H s' = φ
  apply Eq.trans _ E.represents
  rw [← hy]
  apply hu.mul_right_cancel
  have h₁ := congrArg H (IsLocalization.mk'_spec T x y')
  have h₂ := congrArg E.expansion (IsLocalization.mk'_spec E.L x y)
  simp only [map_mul,IsLocalization.Away.lift_eq,H,y'] at h₁
  simpa only [map_mul,g,RingHom.comp_apply] using h₁.trans h₂.symm

theorem common_affine_chart (s : Finset (MvPowerSeries α K))
    (hs : ∀ φ ∈ s, Nonempty (LocalEtaleExpansion φ)) :
    ∃ E : AffineEtaleChart K α, ∀ φ ∈ s, φ ∈ E.expansion.range := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨AffineEtaleChart.base, by simp⟩
  | @insert φ s hφ ih =>
      obtain ⟨E,hE⟩ := ih (fun ψ hψ ↦ hs ψ (Finset.mem_insert_of_mem hψ))
      obtain ⟨F,hF⟩ := (hs φ (Finset.mem_insert_self _ _)).some.affine
      refine ⟨E.prod F, ?_⟩
      intro ψ hψ
      rcases Finset.mem_insert.mp hψ with rfl | hψ
      · obtain ⟨x,hx⟩ := hF
        rw [← hx]
        exact E.range_right F x
      · obtain ⟨x,hx⟩ := hE ψ hψ
        rw [← hx]
        exact E.range_left F x

end BoundaryOnly.FormalObstruction.FormalCorrection

namespace BoundaryOnly.FormalObstruction.AlgebraicReplacement

theorem coordinate_series_flat {K α : Type*} [Field K] [Finite α] :
    Module.Flat (MvPolynomial α K) (MvPowerSeries α K) := by
  exact Module.Flat.of_linearEquiv
    (MvPowerSeries.toAdicCompletionAlgEquiv α K).toLinearEquiv

theorem etale_expansion_faithfullyFlat
    {K α E : Type*} [Field K] [Finite α] [CommRing E]
    [Algebra (MvPolynomial α K) E]
    [Algebra.FormallyUnramified (MvPolynomial α K) E]
    [Algebra.EssFiniteType (MvPolynomial α K) E]
    [Algebra E (MvPowerSeries α K)]
    [IsScalarTower (MvPolynomial α K) E (MvPowerSeries α K)]
    [IsLocalRing E] [IsLocalHom (algebraMap E (MvPowerSeries α K))] :
    Module.FaithfullyFlat E (MvPowerSeries α K) := by
  let := coordinate_series_flat (K := K) (α := α)
  let : Module.Flat E (MvPowerSeries α K) :=
    Algebra.FormallyUnramified.flat_of_restrictScalars
      (MvPolynomial α K) E (MvPowerSeries α K)
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem etale_expansion_mem_iff
    {K α E : Type*} [Field K] [Finite α] [CommRing E]
    [Algebra (MvPolynomial α K) E]
    [Algebra.FormallyUnramified (MvPolynomial α K) E]
    [Algebra.EssFiniteType (MvPolynomial α K) E]
    [Algebra E (MvPowerSeries α K)]
    [IsScalarTower (MvPolynomial α K) E (MvPowerSeries α K)]
    [IsLocalRing E] [IsLocalHom (algebraMap E (MvPowerSeries α K))]
    (I : Ideal E) (x : E) :
    algebraMap E (MvPowerSeries α K) x ∈ I.map (algebraMap E (MvPowerSeries α K)) ↔
      x ∈ I := by
  let := etale_expansion_faithfullyFlat (K := K) (α := α) (E := E)
  change x ∈ (I.map (algebraMap E (MvPowerSeries α K))).comap
    (algebraMap E (MvPowerSeries α K)) ↔ _
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

end BoundaryOnly.FormalObstruction.AlgebraicReplacement

namespace BoundaryOnly.FormalObstruction.FormalCorrection
open MvPowerSeries
variable {K α : Type} [Field K] [Finite α]

namespace AffineEtaleChart

def point (E : AffineEtaleChart K α) : Ideal E.S :=
  RingHom.ker ((constantCoeff : MvPowerSeries α K →+* K).comp E.expansion.toRingHom)

instance (E : AffineEtaleChart K α) : (point E).IsPrime := RingHom.ker_isPrime _

abbrev LocalRing (E : AffineEtaleChart K α) := Localization.AtPrime E.point

omit [Finite α] in
lemma outside_point_unit [Finite α] (E : AffineEtaleChart K α) (y : E.point.primeCompl) :
    IsUnit (E.expansion y) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  exact y.property

noncomputable def localExpansion (E : AffineEtaleChart K α) :
    E.LocalRing →ₐ[MvPolynomial α K] MvPowerSeries α K :=
  IsLocalization.liftAlgHom E.outside_point_unit

@[simp] lemma localExpansion_map (E : AffineEtaleChart K α) (x : E.S) :
    E.localExpansion (algebraMap E.S E.LocalRing x) = E.expansion x :=
  IsLocalization.lift_eq E.outside_point_unit x

instance localExpansion_isLocalHom (E : AffineEtaleChart K α) :
    IsLocalHom E.localExpansion := by
  constructor
  intro z hz
  obtain ⟨x,y,rfl⟩ := IsLocalization.exists_mk'_eq E.point.primeCompl z
  apply (IsLocalization.AtPrime.isUnit_mk'_iff E.LocalRing E.point x y).mpr
  have hxy := congrArg E.localExpansion (IsLocalization.mk'_spec E.LocalRing x y)
  simp only [map_mul, localExpansion_map] at hxy
  have hu : IsUnit (E.expansion x) := hxy ▸ (hz.mul (E.outside_point_unit y))
  exact (MvPowerSeries.isUnit_iff_constantCoeff.mp hu).ne_zero

noncomputable instance localAlgebra (E : AffineEtaleChart K α) :
    Algebra E.LocalRing (MvPowerSeries α K) := E.localExpansion.toRingHom.toAlgebra

instance localTower (E : AffineEtaleChart K α) :
    IsScalarTower (MvPolynomial α K) E.LocalRing (MvPowerSeries α K) :=
  IsScalarTower.of_algebraMap_eq (fun p ↦ (E.localExpansion.commutes p).symm)

instance localAlgebra_isLocalHom (E : AffineEtaleChart K α) :
    IsLocalHom (algebraMap E.LocalRing (MvPowerSeries α K)) :=
  ⟨fun x hx ↦ isUnit_of_map_unit E.localExpansion x hx⟩

instance localEssFiniteType (E : AffineEtaleChart K α) :
    Algebra.EssFiniteType (MvPolynomial α K) E.LocalRing :=
  Algebra.EssFiniteType.comp (MvPolynomial α K) E.S E.LocalRing

instance localFormallyEtale (E : AffineEtaleChart K α) :
    Algebra.FormallyEtale (MvPolynomial α K) E.LocalRing := inferInstance

theorem localFaithfullyFlat (E : AffineEtaleChart K α) :
    Module.FaithfullyFlat E.LocalRing (MvPowerSeries α K) :=
  BoundaryOnly.FormalObstruction.AlgebraicReplacement.etale_expansion_faithfullyFlat

lemma localRange (E : AffineEtaleChart K α) {φ : MvPowerSeries α K}
    (h : φ ∈ E.expansion.range) : φ ∈ E.localExpansion.range := by
  obtain ⟨x,rfl⟩ := h
  exact ⟨algebraMap E.S E.LocalRing x,E.localExpansion_map x⟩

noncomputable def localGerm (E : AffineEtaleChart K α) (x : E.LocalRing) :
    LocalEtaleExpansion (E.localExpansion x) where
  S := E.S
  L := E.LocalRing
  ringS := inferInstance
  baseS := inferInstance
  etale := inferInstance
  ringL := inferInstance
  fromS := inferInstance
  baseL := inferInstance
  tower := inferInstance
  denominators := E.point.primeCompl
  localization := inferInstance
  expansion := E.localExpansion.toRingHom
  coordinates p := E.localExpansion.commutes p
  germ := x
  represents := rfl

end AffineEtaleChart
end BoundaryOnly.FormalObstruction.FormalCorrection

end

end OAI
