import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveSupport

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

variable (rows : Finset (Finset α)) (P ε : ℝ)

local notation "bias" => uniformBlockRetainedBias (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) ε
local notation "sizeBound" => uniformSpectrumSizeConstant (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) /
  ε ^ max (majorArcSpectrumExponent (Fin.val j) (Finset.card rows)) (majorArcLengthExponent (Fin.val j) * (degree * Finset.card rows))
local notation "cap" => uniformSpectrumAbsoluteCap (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows)
local notation "periodBound" => uniformCharacterDenominatorBound (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) bias
local notation "frequencyBound" => 2 * majorArcCoverConstant (Fin.val j) (Finset.card rows) P ((torus : ℝ) * cost) /
  bias ^ majorArcCoverExponent (Fin.val j) (Finset.card rows)
local notation "freq" => Real.toNNReal frequencyBound
local notation "supportRadius" => (Finset.card rows : ℝ) * (radius + R j / 4)

include hq hsize in
theorem exists_allocated_inactive_scalar_site_expansion
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : supportRadius + 1 / 4 ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        periodBound
        (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (supportRadius + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + δ := by
  let : NeZero height := ⟨(basisAxisScale_pos (b j) i).ne'⟩
  obtain ⟨F, hcard, hcap, hchar, hpoint⟩ := exists_allocated_inactive_plateau_spectrum
    B U b S j i q hq r hsize hR hσ hsmall hlarge hcell hgrid A hA P ε hP hε hε1 rows hrows hB
  have hmodes : ∀ k : rows → Fin (torus * height), ∃ (d : ℕ) (a : rows → ℤ) (ω : rows → ℝ),
      0 < d ∧ (k ∈ F → (d : ℝ) ≤ periodBound ∧ (∀ t, |ω t| ≤ frequencyBound) ∧
        ∀ t, ((k t).val : ℝ) / (torus * height) = (a t : ℝ) / d + ω t / height) := by
    intro k
    by_cases hk : k ∈ F
    · obtain ⟨d, hd, hdb, a, ω, hω, he⟩ := hchar k hk
      exact ⟨d, a, ω, hd, fun _ => ⟨hdb, hω, he⟩⟩
    · exact ⟨1, fun _ => 0, fun _ => 0, zero_lt_one, fun h => False.elim (hk h)⟩
  choose D a ω hD hmodes using hmodes
  let : ∀ k, NeZero (D k) := fun k => ⟨(hD k).ne'⟩
  have hscale : ((height : ℝ) / (torus * height)) ^ rows.card ≤ 1 :=
    grid_scale_factor_le_one _ _ _ (blockTorusFactor_pos _ _ _ _) (basisAxisScale_pos (b j) i)
  have hsupport : 0 ≤ supportRadius := mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (blockJetScaleBound_nonneg _ _ _ zero_le_one) (div_nonneg (hR j).le (by norm_num)))
  obtain ⟨N, _, hNcard, β, f, hβ, hf, hLf, he⟩ := exists_weightedCube_plateau_site_approximation source
    constantLaw (basisAxisScale_pos (b j) i) radius rows F D a ω
    (fun k hk => by simpa only [Nat.cast_mul] using (hmodes k hk).2.2)
    (fun c t => booleanCoefficient (fun _ : Finset α => c) t)
    (by simpa only [Nat.cast_mul] using hscale) hcap freq
    (fun k hk t => ((hmodes k hk).2.1 t).trans (Real.le_coe_toNNReal _))
    (show 0 < supportRadius + 1 / 4 by linarith only [hsupport]) hδ hQ hHQ hδQ hLQ
  let e : ScalarSiteExpansion.{uα,uα} (Finset α) :=
    { Term := PlateauSiteIndex α F N
      period := fun k => D k.1
      coefficient := β
      factor := fun k u v z => scalarSupportPlateau supportRadius z * f k u v z }
  refine ⟨e, ⟨?_, ?_, ?_, hβ, ?_, ?_, ?_⟩, ?_⟩
  · exact hNcard.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))
  · exact fun k => hD k.1
  · exact fun k => (hmodes k.1 k.1.property).1
  · intro k u v z
    change ‖scalarSupportPlateau supportRadius z * f k u v z‖ ≤ 1
    rw [norm_mul]
    exact (mul_le_mul (scalarSupportPlateau_norm _ _) (hf k u v z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro k u v
    exact scalarSupportPlateau_mul_lipschitz supportRadius (f k u v) (hLf k u v) (hf k u v)
  · intro k u v z hz
    change scalarSupportPlateau supportRadius z * f k u v z = 0
    rw [scalarSupportPlateau_zero hz, zero_mul]
  · intro x y hy
    let target : ℂ := (((height : ℝ) ^ rows.card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
        (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ)
    have hkeep : target ≠ 0 → ∀ u, scalarSupportPlateau supportRadius ((y u : ℝ) / height) = 1 := by
      intro htarget u
      have hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
          (fun t => booleanCoefficient y t) ≠ 0 := by
        intro hz
        apply htarget
        simp only [target, hz, ENNReal.toReal_zero, mul_zero, Complex.ofReal_zero]
      exact scalarSupportPlateau_one hsupport
        (allocatedInactivePhysicalSites_bound B U b S j i q hq r hsize hR hσ
          hsmall hlarge hcell hgrid rows hrows x y hy hmass u)
    apply finite_site_cutoff_error target β
      (fun k u => f k u (y u : ZMod (D k.1)) ((y u : ℝ) / height))
      (fun u => scalarSupportPlateau supportRadius ((y u : ℝ) / height))
      (show 0 ≤ ε + δ by positivity) (fun u => scalarSupportPlateau_norm _ _) hkeep
    intro hcut
    have hsite := he y (fun u => (scalarSupportPlateau_support _ _ (hcut u)).le)
    have hp := hpoint x (fun t => booleanCoefficient y t)
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hp hsite)

end Erdos3.VectorPolynomial

end

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 2
local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

variable (rows : Finset (Finset α)) (P ε : ℝ)

local notation "bias" => uniformBlockRetainedBias (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) ε
local notation "sizeBound" => uniformSpectrumSizeConstant (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) /
  ε ^ max (majorArcSpectrumExponent (Fin.val j) (Finset.card rows)) (majorArcLengthExponent (Fin.val j) * (degree * Finset.card rows))
local notation "cap" => uniformSpectrumAbsoluteCap (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows)
local notation "periodBound" => uniformCharacterDenominatorBound (Fin.val j) (Finset.card rows) (degree * Finset.card rows) P
  ((torus : ℝ) * cost) (((torus : ℝ) * cost) ^ Finset.card rows) bias
local notation "frequencyBound" => 2 * majorArcCoverConstant (Fin.val j) (Finset.card rows) P ((torus : ℝ) * cost) /
  bias ^ majorArcCoverExponent (Fin.val j) (Finset.card rows)
local notation "freq" => Real.toNNReal frequencyBound
local notation "supportRadius" => (Finset.card rows : ℝ) * (radius + R j / 4)

local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "smallHeight" => (max (2 * denom)
  (integerAxisShortBound degree ((Fintype.card α + 1) * q) gamma) : ℕ)
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "shortRadius" => (Finset.card rows : ℝ) * ((Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
local notation "commonRadius" => max supportRadius shortRadius + 1 / 4

include hq in
theorem exists_allocated_inactive_site_expansion_all_cases
    [Nonempty (B ⟨j, Sum.inr i⟩)]
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hsmall : height ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    {δ Q : ℝ} (hδ : 0 < δ) (hQ : 0 ≤ Q)
    (hHQ : commonRadius ≤ Real.exp Q) (hδQ : (δ / (cap + 1))⁻¹ ≤ Real.exp Q)
    (hLQ : ((CircleFourier.characterLipConstant * (rows.card * freq) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortCap : (smallHeight : ℝ) ^ rows.card ≤ Real.exp Q)
    (hshortLip : ((rows.card * (2 * (smallHeight : ℝ≥0) ^ 2) * (smallHeight : ℝ≥0) ^ rows.card) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q)
    (hshortError : δ⁻¹ ≤ Real.exp Q) :
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max (sizeBound * Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8))))
        (max periodBound 1)
        (max (cap * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
          (Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q)))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) commonRadius ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ ε + δ := by
  rcases allocatedGridSide_normalizable_or_bounded B U b S q j i hq hsize with hl | hs
  · obtain ⟨e, he, herr⟩ := exists_allocated_inactive_scalar_site_expansion B U b S j i q hq r hl.2
      hR hσ rows P ε hsmall hl.1 hcell hgrid A hA hP hε hε1 hrows hB hδ hQ
      ((add_le_add (le_max_left supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ) hδQ hLQ
    exact ⟨e, he.mono (le_max_left _ _) (le_max_left _ _) (le_max_left _ _) le_rfl
      (add_le_add (le_max_left _ _) (le_refl (1 / 4 : ℝ))), herr⟩
  · obtain ⟨e, he, herr⟩ := exists_allocated_bounded_grid_site_expansion B U b hR hσ S q r hcell j i
      hσ1 hgrid rows hs hδ hQ
      ((add_le_add (le_max_right supportRadius shortRadius) (le_refl (1 / 4 : ℝ))).trans hHQ)
      hshortCap hshortLip hshortError
    refine ⟨e, he.mono (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) le_rfl
      (add_le_add (le_max_right _ _) (le_refl (1 / 4 : ℝ))), ?_⟩
    intro x y hy
    exact (herr x y hy).trans (le_add_of_nonneg_left hε.le)

end Erdos3.VectorPolynomial

end

end OAI
