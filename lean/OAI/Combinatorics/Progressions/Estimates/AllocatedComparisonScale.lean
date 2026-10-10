import OAI.Combinatorics.Progressions.Polynomial.AllocatedComparisonPolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedComparisonInitialScale (m : ℕ) (p : ℝ) : ℕ :=
  ⌈Real.exp (allocatedComparisonInitialLog m p)⌉₊

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedComparisonScale (p : ℝ) : LayerSamplerScale (G := G) B U basis R σ :=
  selectedLayerSamplerScale (G := G) B U basis R σ hR hσ (allocatedComparisonInitialScale m p)

theorem allocatedComparisonScale_lower (p : ℝ) :
    Real.exp (allocatedComparisonInitialLog m p) ≤
      (allocatedComparisonScale (G := G) B U basis hR hσ p).value :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (selectedLayerSamplerScale_bounds (G := G) B U basis R σ hR hσ (allocatedComparisonInitialScale m p)).1)

theorem allocatedComparisonScale_upper {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ((allocatedComparisonScale (G := G) B U basis hR hσ p).value : ℝ) ≤
      Real.exp (allocatedComparisonScaleLog m p) := by
  obtain ⟨hD, hm, hpD, _, hCD, _, _, _, hfD⟩ := allocatedComparisonDimension_bounds m hp
  have hE := allocatedComparisonInitialLog_nonneg m hp
  let T := allocatedComparisonDimension m p+allocatedComparisonInitialLog m p+1
  have hDT : allocatedComparisonDimension m p ≤ T := by dsimp [T]; linarith
  have hpT : p ≤ T := hpD.trans hDT
  have hT : 0 ≤ T := hp.trans hpT
  have hmT : (m : ℝ) ≤ T := (Nat.cast_le.mpr (Nat.le_succ m)).trans (hm.trans hDT)
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ comparisonProfileBound :=
    (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp T :=
    (hprofile.trans (hfD.trans hDT)).trans (by linarith [Real.add_one_le_exp T])
  have hL : (allocatedComparisonInitialScale m p : ℝ) ≤ Real.exp T := by
    apply (natCeil_le_exp_succ_of_le hE le_rfl).trans
    apply Real.exp_le_exp.mpr
    dsimp [T]
    linarith
  change ((selectedLayerSamplerScale (G := G) B U basis R σ hR hσ (allocatedComparisonInitialScale m p)).value : ℝ) ≤
    Real.exp (allocatedScaleLog T)
  apply selectedLayerSamplerScale_exp_bound (G := G) B U basis R σ hR hσ _ hT hmT
    (fun j => (hn j).trans hpT)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpT))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpT)) _ hA hL
  intro j
  exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
    (Nat.succ_le_of_lt j.isLt) hp hK).trans (hCD.trans hDT)

theorem allocatedComparisonScale_ready
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    let D := allocatedComparisonDimension m p
    Real.exp (allocatedJointLengthLog (G := G) B α O D (allocatedJetTestLog (G := G) B α O D D)) ≤
      (allocatedComparisonScale (G := G) B U basis hR hσ p).value := by
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hK hI hn
  exact (Real.exp_le_exp.mpr (allocatedTestLengthLog_le_envelope B hd hd.nonneg hd.nonneg)).trans
    (allocatedComparisonScale_lower (G := G) B U basis hR hσ p)

theorem allocatedComparisonScale_polynomial_upper (A : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (p+2)^A)
    (hn : ∀ j, (n j : ℝ) ≤ (p+2)^A)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp ((p+2)^A))
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp ((p+2)^A)) :
    ((allocatedComparisonScale (G := G) B U basis hR hσ ((p+2)^A)).value : ℝ) ≤
      Real.exp ((p+2)^allocatedComparisonExponent m A) :=
  (allocatedComparisonScale_upper (G := G) B U basis hR hσ (by positivity) hK hn hRi hσi).trans
    (Real.exp_le_exp.mpr (allocatedComparisonScaleLog_le_power m A hp))

end Erdos3.VectorPolynomial

end

end OAI
