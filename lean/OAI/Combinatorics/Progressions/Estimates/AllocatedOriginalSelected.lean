import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonWeightedOriginal

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))

theorem allocatedReferenceSelectedIdealAt_original
    {D Psp E e t : ℝ} {δ : ℝ≥0} {Kideal : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) (he : 0 ≤ e) (ht1 : t ≤ 1) (hKideal : 2 ≤ Kideal)
    (hselected : AllocatedReferenceSelectedIdealAt.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B D Psp (E + 4) e t δ Kideal) :
    ∃ A T Kproj : ℕ, 2 ≤ A ∧ 2 ≤ T ∧ 2 ≤ Kproj ∧
      AllocatedOriginalSelectedAt.{uG, uI, uB, uGeom, uCover, uSpace}
        (G := G) (dim := dim) B D Psp E e t δ A T Kproj Kideal := by
  obtain ⟨A, T, Kproj, hAconst, hT, hKproj, hfamily⟩ :=
    exists_allocated_ideal_density_source_family.{uSpace, uG, uI, uB, uGeom} m dim
  refine ⟨A, T, Kproj, hAconst, hT, hKproj, ?_⟩
  unfold AllocatedOriginalSelectedAt
  intro w error gainLog hmPsp hdimPsp hGPsp hvarsGrowth J _ U b R σ hR hσ hσt
    pNum hPspNum hcount herrorNum hRefineNum hRP hRi hσi S lengthLog Pbase l F Q K
  have hpNum : 0 ≤ pNum := hPsp.trans hPspNum
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have herror : 0 ≤ error := allocatedReferenceIdealError_nonneg m hdim.nonneg hPsp (by linarith)
  have hgain : 0 ≤ gainLog := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have hlength : 0 ≤ lengthLog := by
    have h := allocatedIdealScaleInput_bounds m hdim.nonneg hpNum he hw herror
    exact h.2.1.trans h.2.2.2.2.2
  have hinput := (allocatedActualProfileInput_bounds m hdim.nonneg hpNum he hgain hlength).1
  have hF : 0 ≤ F := by
    have hlog := allocatedProfileErrorLog_nonneg hinput
    dsimp only [F, allocatedProfileFourierOutput, allocatedProfileFourierInput]
    positivity
  obtain ⟨_hPbase1, _hDPbase, hpBase, _hLBase, _hWBase⟩ :=
    allocatedIdealSourceBudget_bounds m hdim.nonneg hpNum he hw herror
  have hPspBase : Psp ≤ Pbase := hPspNum.trans hpBase
  obtain ⟨hS, hselected⟩ := hselected hmPsp hdimPsp hGPsp U b hR hσ hσt
    hPspNum hcount herrorNum hRefineNum hRP hRi hσi
  obtain ⟨_hSfamily, hfamily⟩ := hfamily B U b hR hσ hdim hpNum he hw herror hRi hσi
  refine ⟨hS, ?_⟩
  intro x Mk hMk selection hx hqDim hMkPsp
  obtain ⟨d, hd, hdb, hfamily⟩ := hfamily x hx.2
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨modulus, hmodulus, hselected⟩ := hselected x hMk selection hx hqDim hMkPsp
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmodulusSize, hspatialPeriod, hcoefficientPeriod, s, hA, hinverse, hselected⟩ := hselected
  refine ⟨d, hd, hdb, modulus, hmodulus, hmodulusSize, hspatialPeriod, hcoefficientPeriod,
    s, hA, hinverse, ?_⟩
  intro block _ _ _ _ _ _ hb o Kcov _ bW C V hC hV hCp hVp Cinv hCinv hchart hsmall μ _ _ ν _ _
    X _ _ hXPsp q hq hqPsp refined
  have hσ1 (j) : σ j ≤ 1 := (hσt j).trans ht1
  have hjet := allocatedPhysicalChartRadius_bound (G := G) B (Fin dim) Cinv hCinv
    (le_refl 1) (fun j => (hR j).le) hsmall (le_refl 1) (le_refl 1)
  have hsmallDensity := allocatedJetRadius_implies_chartRadius (B := B) (hR := hR)
    (le_refl 1) Cinv hCinv hjet
  obtain ⟨hnum, g, hgc, hgb, _hgi, _hgm, hglaw, _hproject, horiginal, hdata⟩ :=
    hfamily hb o C V hC hV hCp hVp hσ1 Cinv hCinv hchart hsmallDensity μ ν
  obtain ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, _hpointwise,
    hsource, hideal⟩ := hselected block hb o bW d C V hC hV ν hXPsp q hq hqPsp
  let : NeZero (residueRefinedPeriod modulus q) := ⟨hRefined.ne'⟩
  refine ⟨hRefined, hdiv, hRefinedBound, hsize, reference, residue, href, hresidue, ?_⟩
  intro W hW indices ξ hξ mesh τ hτ hτP N hN hsizeN poly hpoly hmem rank hrank hRank
    base cells hcells test htest Z hZ
  let C₀ : ℝ := 1 + (S.value : ℝ) + W
  let cap : ℝ := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
    Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
  let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
  let ρ := normalizedTupleResolution X indices selection Mk Psp (E + 2) C₀ W cap Centry
  have hcap : 0 ≤ cap := pow_nonneg (NNReal.coe_nonneg _) _
  obtain ⟨_hW, hl, hBaseL, hC₀, hLC, hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    AllocatedSourceNumerics.late_bounds B U b S C V hnum hR hσ
  have hWscale : W ≤ (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hPspL : Psp ≤ l := hPspBase.trans hBaseL
  have hql (a : X) : (q a : ℝ) ≤ Real.exp l := (hqPsp a).trans (Real.exp_le_exp.mpr hPspL)
  have hτl : τ⁻¹ ≤ Real.exp l := by
    simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseL))
  have hE2 : 0 ≤ E + 2 := by linarith
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast Nat.succ_le_iff.mpr S.positive
  have hentry : 0 ≤ Centry := zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  obtain ⟨_hξ, hξ1, _hξlog, hchoices⟩ := normalizedTupleSpatialChoices
    (N := indices) (X := X) (m := m) selection hMk hPsp hE2 hmPsp hdimPsp hGPsp hXPsp hMkPsp
  obtain ⟨_hδ, _hδ1, hmesh, hρ, _hmeshSize, hρ8, hshift, _hmove, _hboundary, _hspatial⟩ :=
    hchoices (zero_le_one.trans hC₀) hW hS1 hcap hentry hvarsGrowth hWscale
  have hqdimBase : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using
      hdimPsp.trans hPspBase
  have hXBase : (Fintype.card X : ℝ) ≤ Pbase := hXPsp.trans hPspBase
  obtain ⟨_hQ1, hBaseQ, hE1Q, hlQ, _hFQ, hJetQ, hProdQ, _hWidthQ, _hSideQ⟩ :=
    allocatedSourceSamplingBudget_bounds m dim A hnum.nonneg hE hl hF
  obtain ⟨hwidthQ, hsideQ, hdimQ⟩ := allocatedSourceSamplingBudget_spatial m A X indices selection
    hPsp hE hl hF hPspBase hqdimBase hnum.variable_count hXBase
  have hXQ := hXBase.trans hBaseQ
  have hOptionBase : (Fintype.card (Option (Fin dim)) : ℝ) ≤ Pbase := by
    simpa only [Fintype.card_option, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit, Nat.add_comm 1]
      using hqdimBase
  have hsmallDim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ Q := by
    calc
      _ = (Fintype.card (Option (Fin dim)) : ℝ) * Fintype.card X := by
        simp only [Fintype.card_prod, Nat.cast_mul]
      _ ≤ Pbase * Pbase := mul_le_mul hOptionBase hXBase (Nat.cast_nonneg _) hnum.nonneg
      _ ≤ (Pbase + 1) * Pbase := mul_le_mul_of_nonneg_right (by linarith) hnum.nonneg
      _ ≤ Q := hProdQ
  obtain ⟨hQcut, hMassCut, hProjCut, hIdealCut⟩ := allocatedSourceSamplingBudget_cutoffs m dim A
    hnum.nonneg hE hl hF T Kproj Kideal (Nat.le_trans (by decide) hT)
      (Nat.le_trans (by decide) hKproj) (Nat.le_trans (by decide) hKideal)
  have hside (a : X) : Real.exp (normalizedTupleSideLog X indices selection Psp (E + 2) l) ≤ (N a : ℝ) :=
    (Real.exp_le_exp.mpr (hsideQ.trans hQcut)).trans (hsizeN a)
  have hphysical (a : X) : 8 * (1 + W) * (q a : ℝ) * ρ ≤ (ξ * τ) * (N a : ℝ) :=
    normalizedTupleSpatialSize X indices selection hPsp hE2 hl hMk hmPsp hdimPsp hGPsp hXPsp hMkPsp
      (zero_le_one.trans hC₀) hW hcap hentry hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _) (hql a)
      hτ hτl (hside a)
  have hshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hshift
  obtain ⟨hmass, _hphysicalCap⟩ := exists_selectedResidue_physical_cap
    (fun _ : LayerSamplerVariables G I n B => 0) q hq cells hcells
    (narrowTrimmedSpatialWidths (G := G) (J := indices) W τ ξ N)
    (narrowTrimmedSpatialWidths_pos hW hτ hξ N hN)
    (fun z => hρ8.trans (narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N q hN hq hphysical z))
  refine ⟨hmass, ?_⟩
  have hmassReference := fun y y₀ a => (hdata y).2 hJetQ hXQ hsmallDim poly hpoly hmem N q hq
    hW hτ hξ1 hρ (hτP.trans (Real.exp_le_exp.mpr (hpBase.trans hBaseQ)))
    (fun a => (hqPsp a).trans (Real.exp_le_exp.mpr (hPspBase.trans hBaseQ)))
    (fun a => (Real.exp_le_exp.mpr hMassCut).trans (hsizeN a)) hrank
    ((Real.exp_le_exp.mpr hMassCut).trans hRank) hphysical hρ8 hshift' y₀ base a
  have htest' := physicalCubeSiteTest_norm_le test htest
  have htailIdeal := hideal N hN hW hτ hξ hξ1 hρ hphysical hρ8 hshift' le_rfl base cells hmass
    poly hpoly hmem hCp hVp hτP mesh hmesh hvarsGrowth hWscale
    (fun a => (Real.exp_le_exp.mpr hIdealCut).trans (hsizeN a)) hrank
    ((Real.exp_le_exp.mpr hIdealCut).trans hRank) (physicalCubeSiteTest test) htest' Z hZ
  have hcomparison := allocatedFixedData_chosen_original_ideal B U b hR hσ S x X hMk selection hx
    modulus s hA q reference residue hb o bW d (Pbase := Pbase) (Kproj := Kproj) (P := Psp) (E := E) δ hsource
  obtain ⟨_hξ1', _hξlog', hcomparison⟩ :=
    hcomparison hPsp hE hmPsp hdimPsp hGPsp hXPsp hMkPsp hmodulusSize hq hσ1
  obtain ⟨_hδ', _hmesh', _hρ', _hδlog, _hmeshlog, _hρlog, hcomparison⟩ :=
    hcomparison Cinv hCinv hchart hsmall μ ν g hgc (fun y z => (hgb y z).1) hglaw horiginal
      hW hτ le_rfl hC₀ hLC hWC hcap hZ hvarsGrowth hWscale hl hC₀l hWl hcapl hentryl hprofilel hql hτl
  exact hcomparison hBaseQ hlQ hE1Q hwidthQ hXQ hdimQ N hN hside
    (fun a => (Real.exp_le_exp.mpr hProjCut).trans (hsizeN a)) poly hpoly hmem hrank
    ((Real.exp_le_exp.mpr hProjCut).trans hRank) base cells hcells hmass test htest
    (fun y v => (hgb y (physicalCubeEuclideanSample U d poly hmem v)).2)
    hmassReference htailIdeal.1 htailIdeal.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

universe uG uI uB uGeom uCover uSpace

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped ContDiff BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {dim : ℕ}

local notation "jets" => (fun j : Fin m => BoundedBooleanJet (Fin dim) ((j : ℕ) + 1))
local notation "jetRows" => (fun j : Fin m => (Subtype.val : BoundedBooleanJet (Fin dim) ((j : ℕ) + 1) → Finset (Fin dim)))
local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_original_selected_ideal
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {D Psp E : ℝ} (hdim : AllocatedComparisonDimensions (G := G) B (Fin dim) jets D)
    (hPsp : 0 ≤ Psp) (hE : 0 ≤ E) :
    ∃ K : ℕ, 2 ≤ K ∧
      let target := profileReferenceErrorLog Psp (E + 4)
      let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
      let gainLog := allocatedProfileGainLog m D Psp w
      let ε := physicalIdealErrorShare target gainLog
      let e := physicalIdealSmoothingLog (B := B) (O := fun a : LayerSamplerAxis I n => jets a.1)
        (α := Fin dim) hLayer A T target gainLog
      ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
        (δ : ℝ) = booleanRegularizationRadius (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T (ε / 2) ∧ (δ : ℝ)⁻¹ ≤ Real.exp e ∧
        let t := booleanMassPerturbationScale (B := B)
          (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
          ((G × Option (Fin dim)) ⊕ (Σ a, SamplerCoefficientSlot G B hLayer a)) hLayer
          (unitProfilePrincipalSize (B := B)) (fun a => 2 * unitProfilePrincipalSize (B := B) a)
          A T m 1 (ε / 2)
        0 < t ∧ t ≤ 1 ∧
          ∃ A₀ T₀ Kproj : ℕ, 2 ≤ A₀ ∧ 2 ≤ T₀ ∧ 2 ≤ Kproj ∧
            AllocatedOriginalSelectedAt.{_, _, _, uGeom, uCover, uSpace}
              (G := G) (dim := dim) B D Psp E e t δ A₀ T₀ Kproj K := by
  have hE4 : 0 ≤ E + 4 := by linarith
  let target := profileReferenceErrorLog Psp (E + 4)
  have htarget : 0 ≤ target := by
    have hs := coefficientErrorSpatialLog_nonneg hPsp
    dsimp [target, profileReferenceErrorLog]
    linarith
  let w : ℝ := (m * 2 ^ (m + 1) : ℕ) * Psp
  have hw : 0 ≤ w := mul_nonneg (Nat.cast_nonneg _) hPsp
  have hgain := allocatedProfileGainLog_nonneg m hdim.nonneg hPsp hw
  have he : 0 ≤ physicalIdealSmoothingLog (B := B)
      (O := fun a : LayerSamplerAxis I n => jets a.1) (α := Fin dim)
      hLayer A T target (allocatedProfileGainLog m D Psp w) :=
    physicalIdealSmoothingLog_nonneg hLayer A T htarget hgain
  obtain ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1, hselected⟩ :=
    exists_allocated_reference_selected_ideal.{uG, uI, uB, uGeom, uCover, uSpace}
      (G := G) (dim := dim) B ψ hψ hrange hzero hone A T hLip hTransition hdim hPsp hE4
  exact ⟨K, hK, δ, hδ, hδ1, hδeq, hδe, ht, ht1,
    allocatedReferenceSelectedIdealAt_original B hdim hPsp hE he ht1 hK hselected⟩

end Erdos3.VectorPolynomial

end

end OAI
