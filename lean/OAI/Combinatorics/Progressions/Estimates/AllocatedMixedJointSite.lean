import OAI.Combinatorics.Progressions.Dynamics.AllocatedMixedSiteBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))

local notation "rows" => fun a : A => rowSets (Sigma.fst (selected a))
local notation "axisN" => fun a : A => allocatedPrincipalGridScale (G := G) B U b (R := R)
  (Sigma.fst (selected a)) (Sigma.snd (selected a))

include hq in
theorem exists_allocated_mixed_joint_site_expansion
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hselected : Function.Injective selected)
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hgamma : ∀ a, principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)) ≤ 1)
    (hgrid : ∀ a, allocatedGridAxis (I := I) U b S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ a t, t ∈ (rows) a → t.card ≤ (selected a).1.val + 1)
    (hB : ∀ a, max
      (positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
        ((layerTailDegree m + 2) * ((rows) a).card))
      (uniformSpectrumBlockCount (selected a).1.val ((rows) a).card
        (((selected a).1.val + 1) * ((rows) a).card)) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) :
    let O := allocatedMixedJointSiteLog m D p v E
    ∃ e : A → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp O)) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → A → ℤ),
        (∀ a t, t ∉ (rows) a → booleanCoefficient (fun s => y s a) t = 0) →
        ‖(((∏ a, ((axisN) a : ℝ) ^ ((rows) a).card) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell selected (rows) x
            (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
          siteFamilyEval e y (fun s a => (y s a : ℝ) / (axisN) a)‖ ≤ δ := by
  let C := Real.exp (allocatedMixedPointCapLog m D p v)
  let τ := uniformProductAccuracy (Fintype.card A) C δ
  let O := allocatedMixedJointSiteLog m D p v E
  have hC : 0 ≤ C := (Real.exp_pos _).le
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) hC hδ
  have hε : 0 < τ / 2 := half_pos hτ
  have hε1 : τ / 2 ≤ 1 := by linarith only [hτ1]
  have hcount : (Fintype.card A : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective selected hselected)).trans
      (allocatedIntegerAxes_card_le B rowSets hD)
  obtain ⟨hcapLog, hcapA, hcapI⟩ := allocatedMixedPointCapLog_bounds m hD.nonneg hp hv
  have hτinv := uniformProductAccuracy_inverse_exp_bound (Fintype.card A) hC hδ hD.nonneg hcapLog hE
    hcount (le_refl C) hδE
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hεinv : (τ / 2)⁻¹ ≤ Real.exp (allocatedMixedAccuracyLog m D p v E) := by
    rw [inv_div, div_eq_mul_inv]
    have hb := (mul_le_mul htwo hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hb.trans_eq (by unfold allocatedMixedAccuracyLog; congr 1; ring)
  have haccuracy := (allocatedMixedJointLogs_nonneg m hD.nonneg hp hv hE).1
  obtain ⟨_, houtA, houtI⟩ := allocatedMixedSiteOutputLog_bounds m hD.nonneg hp hv haccuracy
  have hAout : Real.exp (allocatedActiveSiteOutputLog m D p (allocatedMixedAccuracyLog m D p v E)) ≤
      Real.exp O := Real.exp_le_exp.mpr houtA
  have hIout : Real.exp (allocatedInactiveSiteOutputLog m D p v (allocatedMixedAccuracyLog m D p v E)) ≤
      Real.exp O := Real.exp_le_exp.mpr houtI
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hBa (a : A) : positiveModerateSpectrumBlockCount (selected a).1.val ((rows) a).card
      ((layerTailDegree m + 2) * ((rows) a).card) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) :=
    (le_max_left _ _).trans (hB a)
  have hBi (a : A) : uniformSpectrumBlockCount (selected a).1.val ((rows) a).card
      (((selected a).1.val + 1) * ((rows) a).card) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) :=
    (le_max_right _ _).trans (hB a)
  have hnonempty (a : A) : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := by
    have hi := hBi a
    unfold uniformSpectrumBlockCount at hi
    exact Fintype.card_pos_iff.mp (by omega)
  have heach (a : A) : ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp O) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ (rows) a, booleanCoefficient y t = 0) →
        ‖((((axisN) a : ℝ) ^ ((rows) a).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell (selected a).1 (selected a).2
            ((rows) a) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
          e.integerEval ((axisN) a) y‖ ≤ 2 * (τ / 2) := by
    by_cases ha : S.value ^ ((selected a).1.val + 1) < basisAxisScale (b (selected a).1) (selected a).2
    · obtain ⟨e, he, herr⟩ := exists_allocated_active_budgeted_site_expansion
        B U b S hR hσ rowSets (selected a).1 (selected a).2 q hq r hD hα hP hp hPp
        hε hε1 haccuracy hεinv ha hsize ((hgamma a).trans hS1) hcell (hgrid a) L hL hcP hsP
        (hrows a) (hBa a)
      exact ⟨e, he.mono hAout hAout hAout (by exact_mod_cast hAout) hAout, herr⟩
    · let : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := hnonempty a
      obtain ⟨e, he, herr⟩ := exists_allocated_inactive_budgeted_site_expansion
        B U b S hR hσ rowSets (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv
        hε hε1 haccuracy hεinv hsize (hgamma a) (le_of_not_gt ha) hcell (hgrid a) (hσ1 a) L hL hsP
        (hrows a) (hBi a)
      exact ⟨e, he.mono hIout hIout hIout (by exact_mod_cast hIout) hIout, herr⟩
  choose e hb he using heach
  refine ⟨e, hb, ?_⟩
  apply allocatedJointGrid_site_approximation B U b hR hσ S q r hcell selected (rows)
    hselected hgrid (axisN) e hC hδ
  · intro a x z
    by_cases ha : S.value ^ ((selected a).1.val + 1) < basisAxisScale (b (selected a).1) (selected a).2
    · exact (allocatedActiveGrid_norm_exp_bound B U b S hR hσ rowSets
        (selected a).1 (selected a).2 q hq r hD hα hP hp hPp ha hsize ((hgamma a).trans hS1)
        hcell (hgrid a) L hL hcP hsP (hrows a) (hBa a) x z).trans (Real.exp_le_exp.mpr hcapA)
    · let : Nonempty (B ⟨(selected a).1, Sum.inr (selected a).2⟩) := hnonempty a
      exact (allocatedInactiveGrid_norm_exp_bound B U b S hR hσ rowSets
        (selected a).1 (selected a).2 q hq r hD hα hP hp hv hPp hqv hsize (hgamma a) (le_of_not_gt ha)
        hcell (hgrid a) L hL hsP (hrows a) (hBi a) x z).trans (Real.exp_le_exp.mpr hcapI)
  · intro a x y hy
    have herr := he a x y hy
    have hcancel : (2 : ℝ) * (τ / 2) = τ := by ring
    simpa only [hcancel] using herr

end Erdos3.VectorPolynomial

end

end OAI
