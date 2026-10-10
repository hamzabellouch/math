import OAI.Combinatorics.Progressions.Estimates.AllocatedCenteredJointStatement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedCenteredChosenTupleComparison (m dim : ℕ) :
    allocatedCenteredChosenTupleStatement m dim := by
  obtain ⟨A, a, hA, ha, hcomparison⟩ := allocatedOriginalChosenTupleComparison m dim
  unfold allocatedCenteredChosenTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc L₀
  obtain ⟨S, hS, hSbound, hkernel⟩ := hcomparison B U b hR hσ hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp
  have hselected : S = selectedLayerSamplerScale B U b R σ hR hσ L₀ := hS
  refine ⟨S, hS, hSbound, ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank base cells hcells bases hbases test htest Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hpoly' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1) (centeredPoly j) :=
    (hpoly j).subtractConstant (c j).val
  have hrank' (j : Fin m) :
      HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (centeredPoly j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) _ _ (U j)
      (c j).val (poly j)).mpr (hrank j)
  have hdensity : (fun (a : X → ℤ) z => density (affineSampleCoefficientTorus U
      (fun j => translate (fun t => (a t : ℝ)) (centeredPoly j))
      (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ))
        (centeredPoly j) (centeredMem j)) (fun k t => (z (k, t) : ℝ)))) = baseDensity := by
    funext a z
    exact allocatedJointDensity_subtractConstant B U b hb o R σ hR hσ L₀ S hselected
      poly hmem center c hc a z
  have hnormalizer := congrArg (selectedJointDensityMass bases stride cells widths) hdensity
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ :=
    hdata hCp hVp hXp centeredPoly hpoly' centeredMem N stride hs hτ hτp hstrideT
      hsize hrank' hRank base cells hcells bases hbases test htest bW
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  rw [hnormalizer] at hnormal hcompare
  exact ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedCenteredJointComparison (m dim : ℕ) :
    allocatedCenteredJointStatement m dim := by
  obtain ⟨A, a, hA, ha, hcomparison⟩ := allocatedCenteredChosenTupleComparison m dim
  unfold allocatedCenteredJointStatement
  refine ⟨A, a, hA, ha, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ hR hσ p Etarget T hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp P Pc L₀
  obtain ⟨S, hS, hSbound, hkernel⟩ := hcomparison B U b hR hσ hp hE hT
    hvars hI hn hJ hRup hRi hσi hmsp
  have hselected : S = selectedLayerSamplerScale B U b R σ hR hσ L₀ := hS
  refine ⟨S, hS, hSbound, ?_⟩
  intro x M hM hMp selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hkernel x hM hMp selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, hdata⟩ :=
    hconstruct hb o C Vcap hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hgproj, ?_⟩
  intro hCp hVp X _ _ hXp ξ₀ hξ W hW Pmass poly hpoly hmem center c hc N stride hs Rrank τ hτ
    δ mesh hτp hstrideT hsize hrank hRank cells hcells bases hbases test htest Kcov _ bW
    centeredPoly centeredMem widths baseDensity Z
  have hbase (base : X → ℤ) := hdata hCp hVp hXp poly hpoly hmem center c hc N stride hs hτ
    hτp hstrideT hsize hrank hRank base cells hcells bases hbases test htest bW
  obtain ⟨hmass, hnormal, hN, _⟩ := hbase (fun _ => 0)
  have hZ : 0 < Z := hnormal.2.2.1
  let source := fun base => allocatedOriginalTupleSource B U b hR hσ S x X stride hb o
    N hN hW hτ hξ base cells hmass (physicalCubeSiteTest test) Z centeredPoly centeredMem
  let represents := fun base value => allocatedRefinedReferenceValue (τ := τ) (ξ := ξ₀)
    B U b hR hσ S x rows X hM selection hx stride hb o bW d N hW mesh base cells
    (physicalCubeEuclideanSample U d centeredPoly centeredMem) (physicalCubeSiteTest test) Z Pc T value
  have hperBase (base : X → ℤ) :
      ∃ value : ℂ, represents base value ∧ ‖source base - value‖ ≤ Real.exp (-Etarget) := by
    obtain ⟨_, _, _, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
      s, hsA, hi, hRefined, hdiv, hbound, hlengths, tupleRef, residue, href, hr, hcompare⟩ := hbase base
    let : NeZero modulus := ⟨hmodulus.ne'⟩
    let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
    let value := allocatedRefinedTupleReference (τ := τ) (ξ := ξ₀) B U b hR hσ S x rows X
      hM selection hx modulus s hsA stride tupleRef residue hb o bW d N hW mesh base cells
      (physicalCubeEuclideanSample U d centeredPoly centeredMem) (physicalCubeSiteTest test) Z
    refine ⟨value, ?_, ?_⟩
    · exact ⟨modulus, hmodulus, hmod, hspatialPeriod, hperiod, s, hsA, hi,
        hRefined, hdiv, hbound, hlengths, tupleRef, residue, href, hr, rfl⟩
    · exact hcompare
  choose reference hrep herror using hperBase
  refine ⟨hmass, hN, hZ, ⟨hnormal.1, hnormal.2.1, hnormal.2.2.2⟩,
    reference, hrep, herror, ?_⟩
  exact allocatedCenteredJointSource_comparison B U b hR hσ S L₀ hselected x X hb o
    poly hmem center c hc N hN hW hτ hξ stride cells bases hbases hmass hZ
    (physicalCubeSiteTest test) reference (fun base _ => herror base)

end Erdos3.VectorPolynomial

end

end OAI
