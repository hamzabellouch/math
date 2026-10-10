import OAI.Combinatorics.Progressions.Estimates.AllocatedActualHaarComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (x : G → IntegerScalarCubeBox (Fin 1) S.value)
variable (u : PrincipalAxisTuples (α := Fin 1) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree grid
local notation "Endpoint" => OneCubeActiveEndpoint (B := B) degree grid
local notation "Row" => OneCubeActiveRow grid
local notation "Output" => (Σ _e : Row, Unit)

local notation "Jet" => (Σ _a : {a // ¬grid a}, Finset (Fin 1))
local notation "jetRows" => (fun _ : Fin m => Finset (Fin 1))

theorem allocatedSlicedLongReference_uniform_l1 [DecidableEq G]
    (hR : ∀ j, 0 < R j) (hσpos : ∀ j, 0 < σ j)
    (s : ∀ j : Fin m, Finset (Fin 1) ↪ BoundedIntegerExponent G (j.val + 1))
    (hKernel : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) id).submatrix id (s j)).det ≠ 0)
    (N O : ℕ) (hN : Fintype.card Endpoint ≤ N) (hO : Fintype.card Row ≤ O)
    (hB : ∀ a : {a // ¬grid a}, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : {a // ¬grid a}, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hx : ∀ g, IntegerScalarCube S.value (fun j => (x g j : ℤ)))
    (hu : ∀ j, IntegerScalarCube (principalAxisLength grid (allocatedPrincipalSides B U basis S) j)
      (fun a => (u j a : ℤ)))
    {a δ η : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η)
    (hprincipal : ∀ j : {a // ¬grid a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hσ : ∀ j, |σ j| ≤ slicedPolynomialScale N O N m m 1 1 a δ A η)
    {Mk : ℕ} (hMk : 0 < Mk)
    (hinv : ∀ j : Fin m, fixedKernelInverseBound (O := Finset (Fin 1)) S.positive x (j.val + 1) id (s j) (hKernel j) (1 / (Mk : ℝ)))
    {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (Finset (Fin 1)) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {mesh Cmask : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (hCmask : 1 ≤ Cmask)
    (hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x (fun _ => id) j modulus (residue j) z ≤ Cmask) :
    let radius := max (4 * Real.exp P) (Real.exp (allocatedJetSupportLog (G := G) B (Fin 1) jetRows P))
    let densityBound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B (Fin 1) jetRows P), Real.exp_nonneg _⟩
    let Kp := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * densityBound *
      densityBound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := (‖(∏ o : Output, R o.1.2.val.1)⁻¹‖₊ *
      (NNReal.mk (Real.exp (slicedJointDensityLogBudget O m P)) (Real.exp_nonneg _) *
        NNReal.mk (Real.exp P) (Real.exp_nonneg _))) * 2
    let select := allocatedLongIntegerSelect B U basis S (O := jetRows)
    (∫ z, |allocatedLongProfileDensity B U basis S x (fun _ => id) modulus residue
        (allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width) z -
      allocatedLongProfileDensity B U basis S x (fun _ => id) modulus residue
        (allocatedSlicedLongJetProxy B U basis S x u s hKernel lower width) z|
      ∂allocatedLongJetReference B U basis S jetRows) ≤
      Cmask ^ Fintype.card (LayerSamplerAxis I n) *
        (η + (2 * radius) ^ Fintype.card (UnselectedColumn select) *
          ((2 * radius + 2) ^ Fintype.card {o : Jet // allocatedLongIntegerCoordinate B U basis S (O := jetRows) o} *
            ((Ki : ℝ) + Kp) * mesh)) := by
  intro radius densityBound Kp Ki select
  let ideal := allocatedSlicedPhysicalJetIdeal B U basis S hR hB lower width
  let proxy := allocatedSlicedLongJetProxy B U basis S x u s hKernel lower width
  have ht := slicedEndpointUniformScale_spec N O m ha hδ A.coe_nonneg hη
  have hσ1 (j) : σ j ≤ 1 := (le_abs_self _).trans ((hσ j).trans ht.2.1)
  have he := allocatedSlicedLongJetProxy_uniform_l1 B U basis S x u hR hσpos s hKernel
    N O hN hO hB lower width hwidth hx hu ha hδ hδone hη hprincipal hw hl A hA hσ
  have hIi := (allocatedSlicedPhysicalJetIdeal_probability B U basis S hR hB lower width
    ha hδ hprincipal hw hl).2.1
  have hPi := (allocatedSlicedLongJetProxy_probability B U basis S x u s hKernel lower width hR hσpos hσ1).2.1
  have hIb := allocatedSlicedPhysicalJetIdeal_uniform_bounds B U basis S hR hB lower width
    O hO ha hδ hP haP hδP hprincipal hw hl ⟨Real.exp P, Real.exp_nonneg _⟩ hRi
  have hPb := allocatedSlicedLongJetProxy_output_bounds B U basis S x u s hKernel lower width
    hR hσpos hMk hinv hP hMkP hRP hRi hσi hcount hσ1
  have hIs (z : Jet → ℝ) (hz : radius < ‖z‖) : ideal z = 0 :=
    allocatedSlicedPhysicalJetIdeal_zero_off_ball B U basis S hR hB lower width hwidth
      ha hδ hprincipal hw hl ⟨Real.exp P, Real.exp_nonneg _⟩ hRP z ((le_max_left _ _).trans_lt hz)
  have hPs (z : Jet → ℝ) (hz : radius < ‖z‖) : proxy z = 0 :=
    allocatedSlicedLongJetProxy_zero_off_ball B U basis S x u s hKernel lower width
      hR hσpos hMk hinv hP hMkP hRP hRi hσi hcount hσ1 hwidth z ((le_max_right _ _).trans_lt hz)
  have hbox : 0 ≤ radius := (Real.exp_pos _).le.trans (le_max_right _ _)
  have hcap (z : Jet → ℝ) : |proxy z| ≤ (densityBound ^ Fintype.card (LayerSamplerAxis I n) : ℝ≥0) := by
    rw [abs_of_nonneg (hPb.1 z).1]
    exact (hPb.1 z).2
  exact allocatedLongReference_l1_comparison B U basis S x (fun _ => id) modulus residue
    ideal proxy ⟨radius, hbox⟩ hIb.2 hPb.2 hIs hPs (mul_nonneg (NNReal.coe_nonneg _) (Real.exp_nonneg _)) (NNReal.coe_nonneg _)
    hIb.1 hcap (hIi.sub hPi) he hmesh0 hmesh1 hmesh hCmask hmask

end Erdos3.VectorPolynomial

end

end OAI
