import OAI.Combinatorics.Progressions.Estimates.AllocatedComparisonScale

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedSpatialDataBudget {T : Type*} [Semiring T] (m A : ℕ) (p : T) : T :=
  (p+2)^A+(p+2)^allocatedComparisonExponent m (A+3)+(m+2 : ℕ)+comparisonProfileBound+1

theorem allocatedSpatialDataBudget_bounds (m A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let Z := allocatedSpatialDataBudget m A p
    0 ≤ Z ∧ (p+2)^A ≤ Z ∧ (p+2)^allocatedComparisonExponent m (A+3) ≤ Z ∧
    ((m+1 : ℕ) : ℝ) ≤ Z ∧ (probabilityProfileLipschitz : ℝ) ≤ Z := by
  have hP : 0 ≤ (p+2)^A := by positivity
  have hL : 0 ≤ (p+2)^allocatedComparisonExponent m (A+3) := by positivity
  have hf : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  have hf0 : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  dsimp only [allocatedSpatialDataBudget]
  push_cast
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith [Nat.cast_nonneg (α := ℝ) m]

theorem exists_allocatedSpatial_polynomial_bound (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      spatialParameterEnvelope (allocatedSpatialDataBudget m A p) ≤ (p+2)^C := by
  let P : Polynomial ℕ := spatialParameterEnvelope (allocatedSpatialDataBudget m A Polynomial.X)
  obtain ⟨C, hC, hb⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [P, allocatedSpatialDataBudget, spatialParameterEnvelope, spatialHeightEnvelope,
    spatialRadiusEnvelope, spatialChoiceEnvelope, spatialProfileEnvelope, spatialPointEnvelope,
    spatialCapEnvelope, spatialLipEnvelope, Polynomial.eval₂_pow] using hb p hp

noncomputable def allocatedSpatialParameterExponent (m A : ℕ) : ℕ :=
  (exists_allocatedSpatial_polynomial_bound m A).choose

theorem allocatedSpatialParameterExponent_two_le (m A : ℕ) :
    2 ≤ allocatedSpatialParameterExponent m A :=
  (exists_allocatedSpatial_polynomial_bound m A).choose_spec.1

theorem allocatedSpatialEnvelope_le_power (m A : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    spatialParameterEnvelope (allocatedSpatialDataBudget m A p) ≤
      (p+2)^allocatedSpatialParameterExponent m A :=
  (exists_allocatedSpatial_polynomial_bound m A).choose_spec.2 p hp

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (A : ℕ) {p : ℝ} {α D N : Type*} [Fintype α] [Fintype D] [Fintype N]
variable (c : D → N → ℤ) (index : D → N → PrincipalTupleIndex B (layerSamplerDegree I n))
variable (selection : α ↪ G) (M : ℕ) {τ : ℝ}

local notation "P₀" => (p+2)^A
local notation "L" => (p+2)^allocatedComparisonExponent m (A+3)
local notation "S" => allocatedComparisonScale (G := G) B U basis hR hσ ((p+2)^(A+3))

theorem allocatedSpatialParameters_polynomial (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P₀)
    (hn : ∀ j, (n j : ℝ) ≤ P₀) (hD : (Fintype.card D : ℝ) ≤ P₀)
    (hN : (Fintype.card N : ℝ) ≤ P₀) (hq : Fintype.card α ≤ m+1)
    (hMP : (M : ℝ) ≤ Real.exp P₀) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P₀)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P₀) (hτ : 0 < τ) (hτP : τ⁻¹ ≤ Real.exp P₀)
    (hc : ∀ d j, |(c d j : ℝ)| ≤ Real.exp P₀) :
    let K := Real.exp ((p+2)^allocatedSpatialParameterExponent m A)
    (∀ d, allocatedSpatialHeight B U basis S c index selection M τ d ≤ K) ∧
    smoothJointResolution N (Fintype.card D) selection M (LayerSamplerScale.value S) (m+1) τ ≤ K ∧
    (smoothJointWidth N (Fintype.card D) selection M (m+1) τ)⁻¹ ≤ K ∧
    (smoothJointRadius (Fintype.card D) selection M (m+1) τ)⁻¹ ≤ K := by
  have hP0 : 0 ≤ P₀ := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hBudget : P₀ ≤ (p+2)^(A+3) := by linarith [polynomialBudget_four_slack A hp]
  have hExp := Real.exp_le_exp.mpr hBudget
  have hS := allocatedComparisonScale_polynomial_upper (G := G) B U basis hR hσ (A+3) hp
    (hK.trans hBudget) (fun j => (hn j).trans hBudget) (fun j => (hRi j).trans hExp)
    (fun j => (hσi j).trans hExp)
  let Z := allocatedSpatialDataBudget m A p
  obtain ⟨hZ, hPZ, hLZ, hmZ, hprofile⟩ := allocatedSpatialDataBudget_bounds m A hp
  have haZ : (Fintype.card α : ℝ) ≤ Z := (Nat.cast_le.mpr hq).trans hmZ
  have hgZ : (Fintype.card G : ℝ) ≤ Z :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hK.trans hPZ)
  have heZ : (Fintype.card (UnselectedColumn selection) : ℝ) ≤ Z :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hgZ
  have hnZ := hN.trans hPZ
  have hdZ := hD.trans hPZ
  have hchoice := spatialChoiceLog_le_envelope hP0 hL0 hP0 hZ haZ hgZ hnZ hdZ heZ hmZ hPZ hLZ hPZ hprofile
  have hheight := spatialChosenHeightLog_le_envelope selection hP0 hL0 hP0 hZ
    haZ hgZ hnZ hdZ heZ hmZ hPZ hLZ hPZ hprofile
  have hradius := spatialRadiusLog_le_envelope hP0 hP0 hZ hdZ haZ heZ hmZ hPZ hPZ hprofile
  obtain ⟨_, _, _, _, hChoice0, hHeight0, hRadius0⟩ := spatialEnvelopes_nonneg hZ
  have hAll := allocatedSpatialEnvelope_le_power m A hp
  have hHeightAll : spatialHeightEnvelope Z ≤ spatialParameterEnvelope Z := by
    unfold spatialParameterEnvelope
    linarith
  have hChoiceAll : 2*spatialChoiceEnvelope Z+4 ≤ spatialParameterEnvelope Z := by
    unfold spatialParameterEnvelope
    linarith
  have hRadiusAll : spatialRadiusEnvelope Z ≤ spatialParameterEnvelope Z := by
    unfold spatialParameterEnvelope
    linarith
  have hlog : 2*spatialChoiceLog (Fintype.card α) (Fintype.card G) (Fintype.card N)
      (Fintype.card D) (Fintype.card (UnselectedColumn selection)) (m+1) P₀ L P₀+4 ≤
      (p+2)^allocatedSpatialParameterExponent m A := by
    apply le_trans _ (hChoiceAll.trans hAll)
    linarith
  have hparams := smoothJointResolution_width_le_exp N (Fintype.card D) selection (m+1)
    hP0 hL0 hP0 hMP hS hτ hτP
  refine ⟨?_, hparams.1.trans (Real.exp_le_exp.mpr hlog),
    hparams.2.trans (Real.exp_le_exp.mpr hlog), ?_⟩
  · intro d
    exact (allocatedSpatialHeight_le_exp B U basis S c index selection M τ hP0 hL0 hP0 hMP hS hτ hτP hc d).trans
      (Real.exp_le_exp.mpr (hheight.trans (hHeightAll.trans hAll)))
  · have hr := smoothJointRadius_inverse_le_exp (Fintype.card D) selection (m+1) hP0 hP0 hMP hτ hτP
    simp only [Fintype.card_sum, Fintype.card_unit, Nat.add_comm 1] at hr
    exact hr.trans (Real.exp_le_exp.mpr (hradius.trans (hRadiusAll.trans hAll)))

end Erdos3.VectorPolynomial

end

end OAI
