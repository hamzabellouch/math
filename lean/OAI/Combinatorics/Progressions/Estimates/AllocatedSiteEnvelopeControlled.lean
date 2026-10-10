import OAI.Combinatorics.Progressions.Probability.AllocatedSiteBufferSampledMass

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_site_envelope_controlled_mass (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (cells : Finset (ColumnResiduePattern (Option (Fin q)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin q) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    {D pNum pKernel sLog : ℝ}
    (_hdims : AllocatedComparisonDimensions (G := G) B (Fin q)
      (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) D)
    (_hpNum : 0 ≤ pNum) (_hpKernel : 0 ≤ pKernel) (_hsLog : 0 ≤ sLog)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (_hRi : ∀ j, (R₀ j)⁻¹ ≤ Real.exp pNum)
    (_hSlog : (S.value : ℝ) ≤ Real.exp sLog)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (u : PrincipalAxisTuples (α := Fin q) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := Fin q) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (_hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (_bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (Mkernel : ℕ) (_hM : 0 < Mkernel) (_hMp : (Mkernel : ℝ) ≤ Real.exp pKernel)
    (selection : Fin q ↪ G) (_hx : GoodScalarKernelTuple selection (1 / (Mkernel : ℝ)) Mkernel x)
    (_hq : q ≤ m + 1)
    (period : ℕ) [NeZero period]
    (_hperiod : ∀ j : Fin m, integerScalarLattice (BoundedBooleanJet (Fin q) (j.val + 1)) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q))).mulVecLin.range)
    (_hperiod_size : period ≤ Mkernel ^ (m + 1))
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin q) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hClog : ∀ j, (C j : ℝ) ≤ Real.exp pNum) (_hVlog : ∀ j, (V j : ℝ) ≤ Real.exp pNum),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin q))
    let gain := allocatedSiteEnvelopeGain m D pKernel
    let T := allocatedSiteBufferInput m D pNum gain sLog (normalizedSiteCutoffBound : ℝ)
    let budget := allocatedProfileFourierOutput T
    budget ≤ P →
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => |allocatedCoveredProfileDensity B U b hR₀ hσ S x u v rows _hb o _bW d
          (fun j _ => standardLatticeClosedQuarterBox (J j))
          (allocatedMaskedSiteEnvelope B U b S x modulus residue)
          (physicalCubeEuclideanSample U d p hm (standardPhysicalCubeOutput z))|) ≤
            Real.exp (allocatedSiteEnvelopeMassLog m D pKernel) := by
  obtain ⟨K, hK, htest⟩ := exists_allocated_site_envelope_sampled_mass m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ
    hS hSP hρ hρP hstride H hsize hrank hR cells hcells W hW hwidth
    G _ I _ n B _ b R₀ σ S D pNum pKernel sLog hdims hpNum hpKernel hsLog hJ hRi hSlog
    o hR₀ hσ hσ1 x u v _ hb Q _ bW Mkernel hM hMp selection hx hq period _ hperiod hperiod_size
    modulus residue C V hC hV hClog hVlog O rows gain T budget hbudget
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * pKernel
  let Cm : ℝ≥0 := ⟨Real.exp w, (Real.exp_pos w).le⟩
  let A : ℝ≥0 := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
    Cm ^ Fintype.card (LayerSamplerAxis I n)
  have hQ (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)
  have hkernel := allocatedSiteEnvelope_kernel_gain B U b S x u v rows hdims hQ hpKernel hM hMp
    selection hx (by simpa only [Fintype.card_fin] using hq)
    (fun _ => Subtype.val_injective) (fun _ z => z.property) period hperiod hperiod_size d modulus residue
  have hAg : (A : ℝ) ≤ Real.exp gain := hkernel.1
  have hg : 0 ≤ gain := allocatedSiteEnvelopeGain_nonneg m hdims.nonneg hpKernel
  obtain ⟨hL, h4Q, _hpQ, _hDQ, hamb, hδ, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteBuffer_fourier_budget (α := Fin q) B U b S hdims hpNum hg hsLog hJ
      (fun j => (hR₀ j).le) hRi A hAg hSlog C V hClog hVlog
  have hquarterP : 1 / (1 / 4 : ℝ) ≤ Real.exp P := by
    norm_num
    exact (h4Q.trans hbudget).trans (by linarith [Real.add_one_le_exp P])
  obtain ⟨hZ, _hmajorant, hactual⟩ := htest (ε := (1 / 4 : ℝ))
    hP hn hdim U μ ν p hp hm d stride hs hS hSP hρ (by norm_num) hρP hquarterP
    hstride H hsize hrank hR cells hcells W hW hwidth
    B b S o hR₀ hσ hσ1 x u v hb bW A ⟨Real.exp pNum, (Real.exp_pos pNum).le⟩ hRi
    modulus residue C V hC hV (δ := (1 / 4 : ℝ)) (L := allocatedProfileFourierInput T)
    (by norm_num) hL hamb hδ hkernel.2 hLip
    (hfreq.trans (Real.exp_le_exp.mpr hbudget))
    (hcoeff.trans (Real.exp_le_exp.mpr hbudget))
  refine ⟨hZ, hactual.trans ?_⟩
  exact allocatedSiteEnvelope_sample_mass_le m hdims.nonneg hpKernel hdims.outputs hdims.cube hAg

end Erdos3.BooleanCubeKernel

end

end OAI
