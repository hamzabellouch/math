import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyL1Averaging
import OAI.Combinatorics.Progressions.Geometry.AllocatedProxyOutputSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal Classical ContDiff

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable {M : ℕ} (hM : 0 < M)
variable (hi : ∀ j : Fin m,
  fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
variable {P : ℝ} (hP : 0 ≤ P) (hMP : (M : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "sets" => (fun a : {a // ¬grid a} => rows (Sigma.fst (Subtype.val a)))
local notation "ideal" => physicalActiveProfileIdeal (G := G) (B := B) (G × Option α)
  (layerSamplerDegree I n) grid sets (fun a => R (Sigma.fst a)) (fun a => hR (Sigma.fst a))
local notation "proxy" => allocatedContinuousLongJetProxy B U basis S x u rows s hA
local notation "expP" => NNReal.mk (Real.exp P) (le_of_lt (Real.exp_pos P))
local notation "bound" => NNReal.mk (Real.exp (allocatedDensityLog (G := G) B α O P))
  (le_of_lt (Real.exp_pos _))
local notation "lipProxy" => (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
  bound ^ Fintype.card (LayerSamplerAxis I n)
local notation "jacobian" => (∏ o : output, R (Sigma.fst (Subtype.val (Sigma.fst o))))⁻¹
local notation "lipIdeal" δ => ‖jacobian‖₊ * (affineProductProfileLip output δ * expP)
local notation "boxRadius" => max (Real.exp P * (partitionedIdealRadius α m + 1))
  (Real.exp (allocatedJetSupportLog (G := G) B α O P))

include hσ hM hi hP hMP hRP hRi hσi hcount in
theorem allocatedProxy_mixed_grid_error (hσ1 : ∀ j, σ j ≤ 1)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ}
    (he : (∫ v, |ideal δ v - proxy v|) ≤ ε)
    {W K : Type*} [MeasurableSpace W] [Fintype K]
    (select : K ↪ output) (μ : Measure W) [IsProbabilityMeasure μ]
    (a T : W × (UnselectedColumn select → ℝ) → K → ℝ)
    (hT : ∀ p k, 0 < T p k) {mesh H : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p k, 1 / T p k ≤ mesh)
    (samples : W × (UnselectedColumn select → ℝ) → Finset (K → ℤ))
    (mask : W × (UnselectedColumn select → ℝ) → (K → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (K → ℤ) → ℂ)
    (hH : 0 ≤ H) (hmask : ∀ p k, k ∈ samples p → |mask p k| ≤ H)
    (hφ : ∀ p k, k ∈ samples p → ‖φ p k‖ ≤ 1) :
    ‖∫ p : W × (UnselectedColumn select → ℝ),
      gridDensityTest (selectedOutputSlice select (ideal δ) p.2) (a p) (T p) (samples p) (mask p) (φ p) -
      gridDensityTest (selectedOutputSlice select proxy p.2) (a p) (T p) (samples p) (mask p) (φ p)
      ∂μ.prod volume‖ ≤
    H * (ε + (2 * boxRadius) ^ Fintype.card (UnselectedColumn select) *
      ((2 * boxRadius + 2) ^ Fintype.card K * ((lipIdeal δ : ℝ) + lipProxy) * mesh)) := by
  have hIi := (physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid sets (fun a => R a.1) (fun a => hR a.1) δ hδ).2.1
  have hPi := (allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1).2.1
  have hIlip := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    (layerSamplerDegree I n) grid sets (fun a => R a.1) (fun a => hR a.1) δ hδ expP
    (fun a => hRi a.1)
  have hPlip := (allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1).2
  have hIs (v : output → ℝ) (hv : boxRadius < ‖v‖) : ideal δ v = 0 :=
    physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      (layerSamplerDegree I n) grid sets (fun a => R a.1) (fun a => hR a.1)
      (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1 expP (fun a => hRP a.1) v
      ((le_max_left _ _).trans_lt hv)
  have hPs (v : output → ℝ) (hv : boxRadius < ‖v‖) : proxy v = 0 :=
    allocatedContinuousLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 v ((le_max_right _ _).trans_lt hv)
  have hbox : 0 ≤ boxRadius := (Real.exp_pos _).le.trans (le_max_right _ _)
  have hfg := integrable_snd_probability μ volume (fun v => ideal δ v - proxy v) (hIi.sub hPi)
  have he' : (∫ p : W × (output → ℝ), |ideal δ p.2 - proxy p.2| ∂μ.prod volume) ≤ ε := by
    rw [integral_snd_probability μ volume (fun v : output → ℝ => |ideal δ v - proxy v|)
      (hIi.sub hPi).abs]
    exact he
  exact mixed_output_grid_error select μ (fun _ => ideal δ) (fun _ => proxy)
    ⟨boxRadius, hbox⟩ (Filter.Eventually.of_forall (fun _ => ⟨hIlip, hPlip, hIs, hPs⟩))
    hfg he' a T hT hmesh0 hmesh1 hmesh samples mask φ hH hmask hφ

include hσ hM hi hP hMP hRP hRi hσi hcount in
theorem exists_allocated_proxy_mixed_grid_error [∀ j, Nonempty (O j)]
    (hrows : ∀ j, Function.Injective (rows j))
    (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
    (block : ∀ a : {a // ¬grid a}, O a.val.1 ↪ B a.val)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A Q : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith Q Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε)
    {W K : Type*} [MeasurableSpace W] [Fintype K]
    (select : K ↪ output) (μ : Measure W) [IsProbabilityMeasure μ]
    (a scales : W × (UnselectedColumn select → ℝ) → K → ℝ)
    (hscales : ∀ p k, 0 < scales p k) {mesh H : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p k, 1 / scales p k ≤ mesh)
    (samples : W × (UnselectedColumn select → ℝ) → Finset (K → ℤ))
    (mask : W × (UnselectedColumn select → ℝ) → (K → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (K → ℤ) → ℂ)
    (hH : 0 ≤ H) (hmask : ∀ p k, k ∈ samples p → |mask p k| ≤ H)
    (hφ : ∀ p k, k ∈ samples p → ‖φ p k‖ ≤ 1) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) (layerSamplerDegree I n)
        (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
        A Q (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
        (layerSamplerDegree I n) (unitProfilePrincipalSize (B := B))
        (fun a => 2 * unitProfilePrincipalSize (B := B) a) A Q m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧ ((∀ j, σ j ≤ t) →
      ‖∫ p : W × (UnselectedColumn select → ℝ),
        gridDensityTest (selectedOutputSlice select (ideal δ) p.2)
          (a p) (scales p) (samples p) (mask p) (φ p) -
        gridDensityTest (selectedOutputSlice select proxy p.2)
          (a p) (scales p) (samples p) (mask p) (φ p) ∂μ.prod volume‖ ≤
      H * (ε + (2 * boxRadius) ^ Fintype.card (UnselectedColumn select) *
        ((2 * boxRadius + 2) ^ Fintype.card K * ((lipIdeal δ : ℝ) + lipProxy) * mesh))) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcomp⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A Q hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro hsmall
  exact allocatedProxy_mixed_grid_error B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u (fun j => (hsmall j).trans ht1) δ hδ hδ1
    (hcomp U basis hR hσ hsmall S x u rows hrows hcard block s hA).1
    select μ a scales hscales hmesh0 hmesh1 hmesh samples mask φ hH hmask hφ

end Erdos3.VectorPolynomial

end

end OAI
