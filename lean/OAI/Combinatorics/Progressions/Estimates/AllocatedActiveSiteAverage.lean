import OAI.Combinatorics.Progressions.Estimates.AllocatedActivePlateauAverage

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ) [NeZero q]
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B α (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "labelType" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

include hf hT hs hC hCf hfb hm hq hsize in
theorem exists_allocatedActiveSite_residue_approximation
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Λ) :
    ∃ A : labelType → EuclideanJetLayers U O → ℂ,
      (∀ r, Measurable (A r)) ∧
      (∀ r, 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) →
        ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
        ∃ hy₀ : 0 < (tuples).mass
          (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)),
        ∃ e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
          principalResidueLabel q y₀ = r ∧
          allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
          A r = allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hy₀ f e) ∧
      Integrable (fun z => ((tuples).mean (fun y =>
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => A r z)) haar ∧
      (∫ z, ‖((tuples).mean (fun y =>
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => A r z)‖ ∂haar) ≤ δ * longBound := by
  let p := principalTupleWeights (α := α) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
  let Spec (r : labelType) (A : EuclideanJetLayers U O → ℂ) : Prop :=
    ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
    ∃ hy₀ : 0 < p.mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)),
    ∃ e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      principalResidueLabel q y₀ = r ∧ allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      A = allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hy₀ f e
  have hlocal (r : labelType) (hr : 0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
      ∃ A : EuclideanJetLayers U O → ℂ, Spec r A ∧ Measurable A ∧
        Integrable (fun z => (p.condition _ hr).complexMean (fun y =>
          (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ)) - A z) haar ∧
        (∫ z, ‖(p.condition _ hr).complexMean (fun y =>
          (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ)) - A z‖ ∂haar) ≤
          δ * longBound := by
    obtain ⟨y₀, hy₀⟩ := p.exists_mem_positive_fiber (principalResidueLabel q) r hr
    subst r
    obtain ⟨e, hbE, hi, he⟩ := exists_allocated_active_site_haar_error B U b hR hσ S rowSets x hb o bW d ν q y₀ hr
      f hf hT hs hC hCf hfb (hm y₀) hq hsize P δ Λ M hperiod hP hδ hΛ hgamma L hL hcP hsP hM hrows hB hHΛ hδΛ hLΛ
    refine ⟨allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hr f e,
      ⟨y₀, hr, e, rfl, hbE, rfl⟩,
      allocatedActiveSiteProfile_measurable B U b hR hσ S rowSets x hb o bW d q y₀ hr f e hf, ?_⟩
    simpa only [FiniteProbabilityWeights.complexMean_ofReal,
      ← allocatedActiveSiteProfile_error B U b hR hσ S rowSets x hb o bW d q y₀ hr f e] using And.intro hi he
  obtain ⟨A, hAm, hAs, hAi, hAe⟩ := p.exists_supported_fiber_l1_approximation
    (principalResidueLabel q) haar
    (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ))
    (fun _ => δ * longBound) Spec hlocal
  refine ⟨A, hAm, hAs, ?_, ?_⟩
  · simpa only [FiniteProbabilityWeights.complexMean_ofReal] using hAi
  · simpa only [FiniteProbabilityWeights.complexMean_ofReal, (p.fiberLaw (principalResidueLabel q)).mean_const] using hAe

end Erdos3.VectorPolynomial

end

end OAI
