import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import OAI.NumberTheory.SiegelZeros.Determinants.NormalSelection
import OAI.NumberTheory.SiegelZeros.Selection.Directions
import OAI.NumberTheory.SiegelZeros.Structure.OmegaIndependence

namespace OAI

noncomputable section

namespace SiegelZeros

namespace WeightedTorusJets.ResidueDirectionBasis

section
open SiegelZeros.W58 NormalExactness ActualNormalSelection

theorem localization_derivation_ext_module
    {K A S M : Type*} [CommRing K] [CommRing A] [CommRing S]
    [AddCommGroup M] [Algebra K A] [Algebra K S] [Algebra A S]
    [Module K M] [Module A M] [Module S M]
    [IsScalarTower K A S] [IsScalarTower K A M] [IsScalarTower K S M]
    [IsScalarTower A S M] (P : Submonoid A) [IsLocalization P S]
    (D E : Derivation K S M)
    (h : ∀ a : A, D (algebraMap A S a) = E (algebraMap A S a)) : D = E := by
  apply Derivation.ext
  intro s
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective P s
  apply (IsLocalization.map_units S m).smul_left_cancel.mp
  have hD := congrArg D (IsLocalization.mk'_spec' S a m)
  have hE := congrArg E (IsLocalization.mk'_spec' S a m)
  rw [D.leibniz] at hD
  rw [E.leibniz] at hE
  simp only [h] at hD hE
  exact add_right_cancel (hD.trans hE.symm)

theorem kernel_finrank_three_of_finrank_four
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : V →ₗ[F] F) (hf : f ≠ 0) (hd : Module.finrank F V = 4) :
    Module.finrank F f.ker = 3 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [hd] at h
  omega

def basisOfIndependentTriple
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {v : Fin 3 → V} (hv : LinearIndependent F v) (hd : Module.finrank F V = 3) :=
  basisOfLinearIndependentOfCardEqFinrank
    (K := F) (V := V) (ι := Fin 3) (b := v) hv (by simpa using hd.symm)

@[simp] theorem basisOfIndependentTriple_apply
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {v : Fin 3 → V} (hv : LinearIndependent F v) (hd : Module.finrank F V = 3)
    (i : Fin 3) : basisOfIndependentTriple hv hd i = v i := by
  simp [basisOfIndependentTriple]

variable (K : Type*) [Field K] (p : Ideal (TorusRing K)) [p.IsPrime]

abbrev Local := GenericLocalRing K p

@[reducible] local instance localCommSemiring : CommSemiring (Local K p) :=
  (inferInstance : CommRing (Local K p)).toCommSemiring

abbrev Residue := GenericResidue K p

@[reducible] local instance residueCommRing : CommRing (Residue K p) :=
  (inferInstance : Field (Residue K p)).toCommRing

@[reducible] local instance residueCommSemiring : CommSemiring (Residue K p) :=
  (inferInstance : Field (Residue K p)).toCommSemiring

abbrev Maximal := GenericMaximal K p

@[reducible] local instance residueLocalModule : Module (Local K p) (Residue K p) :=
  inferInstanceAs (Module (Local K p) ((Local K p) ⧸ Maximal K p))

@[reducible] local instance residueSelfModule : Module (Residue K p) (Residue K p) :=
  Semiring.toModule

local instance residueQuotientScalarTower
    (R₀ R₁ : Type*) [CommRing R₀] [CommRing R₁]
    [Algebra R₀ (Local K p)] [Algebra R₁ (Local K p)]
    [SMul R₀ R₁] [IsScalarTower R₀ R₁ (Local K p)] :
    IsScalarTower R₀ R₁ (Residue K p) :=
  Ideal.Quotient.isScalarTower R₀ R₁ (Maximal K p)

abbrev ResidueDerivation := Derivation K (Local K p) (Residue K p)

@[reducible] local instance residueDerivationAddCommGroup :
    AddCommGroup (ResidueDerivation K p) :=
  Derivation.instAddCommGroup (R := K) (A := Local K p) (M := Residue K p)

@[reducible] local instance residueDerivationModule :
    Module (Residue K p) (ResidueDerivation K p) :=
  Derivation.instModule (R := K) (A := Local K p) (M := Residue K p)
    (S := Residue K p)

def originalDerivation (v : Fin 4 → K) : ResidueDerivation K p :=
  reducedDerivation (Maximal K p) (W18.localTorusDerivation K p v)

def residueCoordinate (j : Fin 4) : Residue K p :=
  IsLocalRing.residue (Local K p) (genericCoordinates K p j)

theorem residueCoordinate_ne_zero (j : Fin 4) : residueCoordinate K p j ≠ 0 := by
  exact ((coordinate_isUnit K j).map
    ((IsLocalRing.residue (Local K p)).comp
      (algebraMap (TorusRing K) (Local K p)))).ne_zero

theorem originalDerivation_coordinate (v : Fin 4 → K) (j : Fin 4) :
    originalDerivation K p v (genericCoordinates K p j) =
      algebraMap K (Residue K p) (v j) * residueCoordinate K p j := by
  change IsLocalRing.residue (Local K p)
    (W18.localTorusDerivation K p v
      (algebraMap (TorusRing K) (Local K p) (coordinate K j))) = _
  rw [W18.localTorusDerivation_algebraMap]
  change IsLocalRing.residue (Local K p)
    (algebraMap (TorusRing K) (Local K p)
      (W18.torusDerivation K v
        (algebraMap (AmbientPolynomial K) (TorusRing K) (MvPolynomial.X j)))) = _
  rw [W18.torusDerivation_polynomial, IdentityCotangentRank.invariantDerivation_X,
    map_mul, map_mul, map_mul]
  rfl

theorem residue_derivation_ext (D E : ResidueDerivation K p)
    (h : ∀ j, D (genericCoordinates K p j) = E (genericCoordinates K p j)) : D = E := by
  apply localization_derivation_ext_module (K := K) (A := TorusRing K)
    (S := Local K p) (M := Residue K p) p.primeCompl D E
  intro f
  have htorus : D.compAlgebraMap (TorusRing K) = E.compAlgebraMap (TorusRing K) := by
    apply localization_derivation_ext_module (K := K) (A := AmbientPolynomial K)
      (S := TorusRing K) (M := Residue K p)
      (Submonoid.powers (coordinateProduct K))
      (D.compAlgebraMap (TorusRing K)) (E.compAlgebraMap (TorusRing K))
    intro g
    have hpoly : (D.compAlgebraMap (TorusRing K)).compAlgebraMap (AmbientPolynomial K) =
        (E.compAlgebraMap (TorusRing K)).compAlgebraMap (AmbientPolynomial K) := by
      apply MvPolynomial.derivation_ext
      exact h
    exact congrArg (fun d : Derivation K (AmbientPolynomial K) (Residue K p) => d g) hpoly
  exact congrArg (fun d : Derivation K (TorusRing K) (Residue K p) => d f) htorus

def coefficientMap : ResidueDerivation K p →ₗ[Residue K p] (Fin 4 → Residue K p) where
  toFun D j := (residueCoordinate K p j)⁻¹ * D (genericCoordinates K p j)
  map_add' D E := by ext j; simp [mul_add]
  map_smul' a D := by ext j; simp [mul_left_comm, smul_eq_mul]

@[simp] theorem coefficientMap_original (v : Fin 4 → K) :
    coefficientMap K p (originalDerivation K p v) = algebraMap K (Residue K p) ∘ v := by
  funext j
  change (residueCoordinate K p j)⁻¹ *
    originalDerivation K p v (genericCoordinates K p j) =
      algebraMap K (Residue K p) (v j)
  rw [originalDerivation_coordinate]
  calc
    _ = algebraMap K (Residue K p) (v j) *
        ((residueCoordinate K p j)⁻¹ * residueCoordinate K p j) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (residueCoordinate_ne_zero K p j), mul_one]

theorem coefficientMap_injective : Function.Injective (coefficientMap K p) := by
  intro D E h
  apply residue_derivation_ext K p
  intro j
  have hj := congrFun h j
  exact mul_left_cancel₀ (inv_ne_zero (residueCoordinate_ne_zero K p j)) hj

def residueInvariant : (Fin 4 → Residue K p) →ₗ[Residue K p] ResidueDerivation K p where
  toFun w := ∑ j : Fin 4, w j • originalDerivation K p (Pi.single j 1)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

@[simp] theorem coefficientMap_residueInvariant (w : Fin 4 → Residue K p) :
    coefficientMap K p (residueInvariant K p w) = w := by
  classical
  ext j
  simp [residueInvariant, map_sum, map_smul, coefficientMap_original,
    Finset.sum_apply, Pi.single_apply, Function.comp_def]

def residueCoefficientEquiv : ResidueDerivation K p ≃ₗ[Residue K p] (Fin 4 → Residue K p) :=
  { coefficientMap K p with
    invFun := residueInvariant K p
    left_inv derivation := coefficientMap_injective K p
      (coefficientMap_residueInvariant K p (coefficientMap K p derivation))
    right_inv := coefficientMap_residueInvariant K p }

def coefficientForm (c : Fin 4 → K) : (Fin 4 → K) →ₗ[K] K where
  toFun v := ∑ j, c j * v j
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.mul_sum, mul_left_comm, smul_eq_mul]

def localLogForm (c : Fin 4 → K) : ResidueDerivation K p →ₗ[Residue K p] Residue K p :=
  logFormOnDerivations (K := K) (Maximal K p)
    (algebraMap K (Residue K p) ∘ c) (genericCoordinates K p)

@[reducible] local instance localLogKernelModule (c : Fin 4 → K) :
    Module (Residue K p) (localLogForm K p c).ker :=
  Submodule.module (localLogForm K p c).ker

theorem localLogForm_eq (c : Fin 4 → K) (D : ResidueDerivation K p) :
    localLogForm K p c D =
      ∑ j, algebraMap K (Residue K p) (c j) * coefficientMap K p D j := by
  change (∑ j : Fin 4, (algebraMap K (Residue K p) (c j) *
      (residueCoordinate K p j)⁻¹) * D (genericCoordinates K p j)) =
    ∑ j : Fin 4, algebraMap K (Residue K p) (c j) *
      ((residueCoordinate K p j)⁻¹ * D (genericCoordinates K p j))
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem localLogForm_original (c v : Fin 4 → K) :
    localLogForm K p c (originalDerivation K p v) =
      algebraMap K (Residue K p) (coefficientForm K c v) := by
  rw [localLogForm_eq, coefficientMap_original]
  simp [coefficientForm, map_sum, map_mul]

theorem localLogForm_ne_zero (c : Fin 4 → K) (hc : c ≠ 0) :
    localLogForm K p c ≠ 0 := by
  classical
  intro h
  apply hc
  funext j
  have hj := LinearMap.congr_fun h (originalDerivation K p (Pi.single j 1))
  simpa [localLogForm_original, coefficientForm, Pi.single_apply] using hj

instance residueDerivation_finite : Module.Finite (Residue K p) (ResidueDerivation K p) :=
  Module.Finite.of_injective (coefficientMap K p) (coefficientMap_injective K p)
theorem localLogForm_kernel_finrank (c : Fin 4 → K) (hc : c ≠ 0) :
    Module.finrank (Residue K p) (localLogForm K p c).ker = 3 := by
  have hd : Module.finrank (Residue K p) (ResidueDerivation K p) = 4 :=
    (residueCoefficientEquiv K p).finrank_eq.trans (by simp)
  have h := @kernel_finrank_three_of_finrank_four
    (Residue K p) (ResidueDerivation K p)
    (inferInstance : Field (Residue K p))
    (residueDerivationAddCommGroup K p)
    (residueDerivationModule K p) (residueDerivation_finite K p)
    (localLogForm K p c) (localLogForm_ne_zero K p c hc) hd
  exact h

def originalKernelVectors (c : Fin 4 → K)
    (b : Module.Basis (Fin 3) K (coefficientForm K c).ker) :
    Fin 3 → (localLogForm K p c).ker :=
  fun i => ⟨originalDerivation K p (b i).val, by
    change localLogForm K p c (originalDerivation K p (b i).val) = 0
    rw [localLogForm_original, (b i).property, map_zero]⟩

theorem originalKernelVectors_linearIndependent (c : Fin 4 → K)
    (b : Module.Basis (Fin 3) K (coefficientForm K c).ker) :
    LinearIndependent (Residue K p) (originalKernelVectors K p c b) := by
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map_injOn (coefficientForm K c).ker.subtype
      (fun _ _ _ _ h => Subtype.ext h)
  have hext : LinearIndependent (Residue K p)
      (fun i => algebraMap K (Residue K p) ∘ (b i).val) :=
    linearIndependent_algebraMap_comp_iff.mpr hb
  apply LinearIndependent.of_comp ((coefficientMap K p).comp (localLogForm K p c).ker.subtype)
  simpa only [Function.comp_def, LinearMap.comp_apply, Submodule.subtype_apply,
    originalKernelVectors, coefficientMap_original] using hext

def originalResidueBasis (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (coefficientForm K c).ker) :=
  basisOfIndependentTriple (originalKernelVectors_linearIndependent K p c b)
    (localLogForm_kernel_finrank K p c hc)

@[simp] theorem originalResidueBasis_apply (c : Fin 4 → K) (hc : c ≠ 0)
    (b : Module.Basis (Fin 3) K (coefficientForm K c).ker) (i : Fin 3) :
    (originalResidueBasis K p c hc b i).val =
      reducedDerivation (Maximal K p) (W18.localTorusDerivation K p (b i).val) := by
  simp [originalResidueBasis, originalKernelVectors, originalDerivation]
  rfl

end

open SiegelZeros.W58 NormalExactness ActualNormalSelection

attribute [local instance] localCommSemiring residueCommRing residueCommSemiring
  residueLocalModule residueSelfModule residueQuotientScalarTower
  residueDerivationAddCommGroup residueDerivationModule localLogKernelModule

attribute [local instance] ActualNormalSelection.genericNormalDualModule
  ActualNormalSelection.genericQuotientNormalDualModule

variable (K : Type*) [Field K] (p : Ideal (TorusRing K)) [p.IsPrime]

theorem original_basis_selected_normals [PerfectField K]
    (h : ℕ) (hp : p.height = h) (c : Fin 4 → K) (hc : c ≠ 0)
    (hω : residueLogForm (K := K) (Maximal K p)
      (algebraMap K (Residue K p) ∘ c) (genericCoordinates K p) ≠ 0)
    (b : Module.Basis (Fin 3) K (coefficientForm K c).ker) :
    ∃ T : Set (Fin 3), Nat.card T = h ∧
      LinearIndependent (Residue K p)
        (fun i : T => derivationNormal (Maximal K p)
          (W18.localTorusDerivation K p (b i).val)) ∧
      Function.Surjective
        (fun x : Maximal K p => fun i : T =>
          IsLocalRing.residue (Local K p)
            (W18.localTorusDerivation K p (b i).val x)) := by
  exact generic_original_direction_selection K p h hp
    (algebraMap K (Residue K p) ∘ c) hω (fun i => (b i).val)
    (originalResidueBasis K p c hc b)
    (fun i => originalResidueBasis_apply K p c hc b i)

variable [CharZero K]

theorem coefficientForm_omega (a b : K) :
    coefficientForm K (W13.omegaCoefficients a b) = W12.omega a b := by
  ext x
  simp [coefficientForm, W13.omegaCoefficients, W12.omega, Fin.sum_univ_succ]
  ring

theorem omegaCoefficients_ne_zero (a b : K) : W13.omegaCoefficients a b ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [W13.omegaCoefficients] at h0

def biquadraticKernelVectors (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Fin 3 → (coefficientForm K (W13.omegaCoefficients a b)).ker :=
  fun i => ⟨W12.directions a b i, by
    change coefficientForm K (W13.omegaCoefficients a b) (W12.directions a b i) = 0
    rw [coefficientForm_omega]
    exact W12.omega_direction a b ha hb i⟩

theorem biquadraticKernelVectors_linearIndependent (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (biquadraticKernelVectors K a b ha hb) := by
  apply LinearIndependent.of_comp (coefficientForm K (W13.omegaCoefficients a b)).ker.subtype
  exact W12.directions_linearIndependent a b ha hb

def biquadraticCoordinateBasis (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) K (coefficientForm K (W13.omegaCoefficients a b)).ker :=
  basisOfLinearIndependentOfCardEqFinrank
    (biquadraticKernelVectors_linearIndependent K a b ha hb)
    (by rw [coefficientForm_omega, W12.finrank_kernel_omega a b ha hb]; rfl)

@[simp] theorem biquadraticCoordinateBasis_apply (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticCoordinateBasis K a b ha hb i).val = W12.directions a b i := by
  simp [biquadraticCoordinateBasis, biquadraticKernelVectors]

def biquadraticResidueBasis (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Basis (Fin 3) (Residue K p)
      (localLogForm K p (W13.omegaCoefficients a b)).ker :=
  originalResidueBasis K p (W13.omegaCoefficients a b) (omegaCoefficients_ne_zero K a b)
    (biquadraticCoordinateBasis K a b ha hb)

@[simp] theorem biquadraticResidueBasis_apply (a b : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    (biquadraticResidueBasis K p a b ha hb i).val =
      reducedDerivation (Maximal K p) (W18.localTorusDerivation K p (W12.directions a b i)) := by
  simp [biquadraticResidueBasis, originalResidueBasis_apply]
  rfl

end WeightedTorusJets.ResidueDirectionBasis

end SiegelZeros

end

end OAI
