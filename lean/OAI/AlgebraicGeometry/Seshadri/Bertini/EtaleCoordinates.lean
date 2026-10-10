import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Bertini.HyperplaneFamilies

namespace OAI

section
noncomputable section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open Polynomial RingTheory
open scoped Pointwise

lemma mem_principal_smul_top_iff_dvd {R : Type*} [CommRing R] (a r : R) :
    r ∈ a • (⊤ : Submodule R R) ↔ a ∣ r := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  simp [dvd_def, eq_comm]

lemma weaklyRegular_pair_iff {R : Type*} [CommRing R] (a b : R) :
    Sequence.IsWeaklyRegular R [a, b] ↔
      IsSMulRegular R a ∧ ∀ r : R, a ∣ b * r → a ∣ r := by
  rw [Sequence.isWeaklyRegular_cons_iff, Sequence.isWeaklyRegular_singleton_iff]
  change (IsSMulRegular R a ∧ IsSMulRegular (R ⧸ (a • (⊤ : Submodule R R))) b) ↔ _
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
  simp only [smul_eq_mul, mem_principal_smul_top_iff_dvd]

theorem flat_regular_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (a b : R) (ha : IsSMulRegular R a)
    (hab : ∀ r : R, a ∣ b * r → a ∣ r) :
    IsSMulRegular S (algebraMap R S a) ∧
      ∀ s : S, algebraMap R S a ∣ algebraMap R S b * s → algebraMap R S a ∣ s := by
  have h := ((weaklyRegular_pair_iff a b).mpr ⟨ha, hab⟩).of_flat (S := S)
  simp only [List.map_cons, List.map_nil] at h
  exact (weaklyRegular_pair_iff _ _).mp h

theorem flat_plane_coordinates {K S : Type*} [CommRing K] [CommRing S]
    [Algebra K[X][X] S] [Module.Flat K[X][X] S] :
    IsSMulRegular S (algebraMap K[X][X] S (C X)) ∧
      ∀ s : S, algebraMap K[X][X] S (C X) ∣ algebraMap K[X][X] S X * s →
        algebraMap K[X][X] S (C X) ∣ s := by
  apply flat_regular_pair
  · intro p q hpq
    apply Polynomial.ext
    intro n
    apply Polynomial.isRegular_X.left
    have h := congrArg (fun p : K[X][X] => p.coeff n) hpq
    simpa only [smul_eq_mul, coeff_C_mul] using h
  · intro p hp
    rw [C_dvd_iff_dvd_coeff] at hp ⊢
    intro n
    simpa only [coeff_X_mul] using hp (n + 1)

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {K σ : Type*} [CommRing K]

abbrev coordinateDifference : MvPolynomial σ K →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  aeval fun i => (X i : MvPolynomial σ K) ⊗ₜ[K] (1 : MvPolynomial σ K) -
    (1 : MvPolynomial σ K) ⊗ₜ[K] (X i : MvPolynomial σ K)

abbrev coordinateSum : MvPolynomial σ K →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  aeval fun i => (X i : MvPolynomial σ K) ⊗ₜ[K] (1 : MvPolynomial σ K) +
    (1 : MvPolynomial σ K) ⊗ₜ[K] (X i : MvPolynomial σ K)

abbrev shearMinus : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  Algebra.TensorProduct.lift coordinateDifference Algebra.TensorProduct.includeRight
    (fun _ _ => Commute.all _ _)

abbrev shearPlus : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) →ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  Algebra.TensorProduct.lift coordinateSum Algebra.TensorProduct.includeRight
    (fun _ _ => Commute.all _ _)

lemma shearMinus_plus : (shearMinus (K := K) (σ := σ)).comp shearPlus = .id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference,
      ← Algebra.TensorProduct.one_def]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference]

lemma shearPlus_minus : (shearPlus (K := K) (σ := σ)).comp shearMinus = .id _ _ := by
  apply Algebra.TensorProduct.ext
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference,
      ← Algebra.TensorProduct.one_def]
  · apply MvPolynomial.algHom_ext
    intro i
    simp [AlgHom.comp_apply, shearMinus, shearPlus, coordinateSum, coordinateDifference]

def shearEquiv : (MvPolynomial σ K ⊗[K] MvPolynomial σ K) ≃ₐ[K]
    MvPolynomial σ K ⊗[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom shearMinus shearPlus shearMinus_plus shearPlus_minus

theorem coordinateDifference_flat :
    (coordinateDifference (K := K) (σ := σ)).Flat := by
  have hl : (Algebra.TensorProduct.includeLeft : MvPolynomial σ K →ₐ[K]
      MvPolynomial σ K ⊗[K] MvPolynomial σ K).Flat := by
    change (algebraMap (MvPolynomial σ K)
      (MvPolynomial σ K ⊗[K] MvPolynomial σ K)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hs : (shearMinus (K := K) (σ := σ)).Flat :=
    RingHom.Flat.of_bijective (shearEquiv (K := K) (σ := σ)).bijective
  have hc := hl.comp hs
  change ((shearMinus (K := K) (σ := σ)).comp
    Algebra.TensorProduct.includeLeft).Flat at hc
  simpa only [Algebra.TensorProduct.lift_comp_includeLeft] using hc

def chartDifference {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) : MvPolynomial σ K →ₐ[K] A ⊗[K] A :=
  (Algebra.TensorProduct.map φ φ).comp coordinateDifference

@[simp] lemma chartDifference_X {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (i : σ) :
    chartDifference φ (X i) = φ (X i) ⊗ₜ[K] (1 : A) -
      (1 : A) ⊗ₜ[K] φ (X i) := by
  simp [chartDifference]

theorem chartDifference_flat {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : φ.Flat) : (chartDifference φ).Flat := by
  exact coordinateDifference_flat.comp (RingHom.Flat.tensorProductMap hφ hφ)

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct

theorem chartDifference_regular_pair {K A σ : Type*} [Field K]
    [CommRing A] [Algebra K A] (φ : MvPolynomial σ K →ₐ[K] A)
    (hφ : φ.Flat) (i j : σ) (hij : i ≠ j) :
    IsSMulRegular (A ⊗[K] A) (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) -
      (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∧
    ∀ s : A ⊗[K] A,
      (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∣
        (φ (MvPolynomial.X j) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X j)) * s →
      (φ (MvPolynomial.X i) ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] φ (MvPolynomial.X i)) ∣ s := by
  let : Algebra (MvPolynomial σ K) (A ⊗[K] A) := (chartDifference φ).toRingHom.toAlgebra
  let : Module.Flat (MvPolynomial σ K) (A ⊗[K] A) := chartDifference_flat φ hφ
  have hab : ∀ p : MvPolynomial σ K,
      MvPolynomial.X i ∣ MvPolynomial.X j * p → MvPolynomial.X i ∣ p := by
    intro p hp
    exact (MvPolynomial.X_dvd_mul_iff.mp hp).resolve_left (by simpa using hij)
  have hr := flat_regular_pair (S := A ⊗[K] A) (MvPolynomial.X i) (MvPolynomial.X j)
    (show IsSMulRegular (MvPolynomial σ K) (MvPolynomial.X i) from
      MvPolynomial.isRegular_X.left) hab
  change IsSMulRegular _ (chartDifference φ (MvPolynomial.X i)) ∧
    ∀ s, chartDifference φ (MvPolynomial.X i) ∣ chartDifference φ (MvPolynomial.X j) * s →
      chartDifference φ (MvPolynomial.X i) ∣ s at hr
  simpa only [chartDifference_X] using hr

end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open KaehlerDifferential
open scoped TensorProduct

variable {K A σ : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [Algebra (MvPolynomial σ K) A] [IsScalarTower K (MvPolynomial σ K) A]
  [Algebra.FormallyEtale (MvPolynomial σ K) A]

def etaleCotangentCoordinate (j : σ) : Ω[A⁄K] →ₗ[A] A :=
  (((mvPolynomialBasis K σ).baseChange A).coord j).comp
    (tensorKaehlerEquivOfFormallyEtale K (MvPolynomial σ K) A).symm.toLinearMap

@[simp] theorem etaleCotangentCoordinate_X [DecidableEq σ] (i j : σ) :
    etaleCotangentCoordinate (K := K) (A := A) j
      (D K A (algebraMap (MvPolynomial σ K) A (MvPolynomial.X i))) =
        if i = j then 1 else 0 := by
  rw [etaleCotangentCoordinate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  rw [← mvPolynomialBasis_apply, ← Module.Basis.baseChange_apply]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]
end
end MaximalSeshadri.BertiniIntegral

namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open scoped TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem etale_hyperplane_geometricGeneric {K A E σ ι : Type} [Field K] [CharZero K]
    [IsAlgClosed K] [CommRing A] [IsDomain A] [Algebra K A] [Fintype σ]
    [Algebra (MvPolynomial ι K) A] [IsScalarTower K (MvPolynomial ι K) A]
    [Algebra.Etale (MvPolynomial ι K) A]
    [Field E] [Algebra (FractionRing (Polynomial (MvPolynomial σ K))) E]
    (v : σ → A) (i j : σ) (a b : ι) (hab : a ≠ b)
    (hvi : v i = algebraMap (MvPolynomial ι K) A (MvPolynomial.X a))
    (hvj : v j = algebraMap (MvPolynomial ι K) A (MvPolynomial.X b)) :
    let := hyperplaneFamilyAlgebra (K := K) v
    IsDomain ((FractionRing (Polynomial (MvPolynomial σ K)) ⊗[Polynomial (MvPolynomial σ K)]
      MvPolynomial σ A) ⊗[FractionRing (Polynomial (MvPolynomial σ K))] E) := by
  classical
  let : IsDomain (A ⊗[K] A) := tensorProduct_isDomain_general
  let φ : MvPolynomial ι K →ₐ[K] A := IsScalarTower.toAlgHom K (MvPolynomial ι K) A
  have hφ : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨hr, hreg⟩ := chartDifference_regular_pair φ hφ a b hab
  let δ : Derivation K A A :=
    (etaleCotangentCoordinate (K := K) (A := A) a).compDer (KaehlerDifferential.D K A)
  have hδi : δ (v i) = 1 := by
    rw [hvi]
    simp [δ]
  have hδj : δ (v j) = 0 := by
    rw [hvj]
    change etaleCotangentCoordinate a
      (KaehlerDifferential.D K A (algebraMap (MvPolynomial ι K) A (MvPolynomial.X b))) = 0
    simp [hab.symm]
  have hji : j ≠ i := by
    rintro rfl
    exact one_ne_zero (hδi.symm.trans hδj)
  apply hyperplaneFamily_geometricGeneric v δ i (hδi ▸ one_ne_zero) i j hji
  · rw [hvi]
    intro hz
    have hz' : φ (MvPolynomial.X a) ⊗ₜ[K] (1 : A) -
        (1 : A) ⊗ₜ[K] φ (MvPolynomial.X a) = 0 := hz
    have : (1 : A ⊗[K] A) = 0 := hr (by rw [hz']; simp)
    exact one_ne_zero this
  · simpa only [hvi, hvj, φ, IsScalarTower.coe_toAlgHom'] using hreg
end
end MaximalSeshadri.BertiniIntegral


end
end

end OAI
