import OAI.Geometry.SurfaceImmersion.Correction.PolynomialRealReconstruction

namespace OAI

/-! Quantitative reconstruction bounds for the actual complexified surface
map, derived from real two-jet and inverse denominator bounds. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

theorem polynomial_reconstruction_bound {U : Set Base} {F : RField 4}
    (hF : ContDiff ℝ ∞ F) (hU : RealModeDomain F U) {s C K : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (hb : WeightedBound U s m C (realTwoJet F))
    (hGD : ∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ K)
    (hGN : ∀ x ∈ U, ‖(realSecond F x ⬝ᵥ realSecond F x)⁻¹‖ ≤ K) :
    ReconstructionCoefficientBound (fun p => complexify (F p)) U s m (reconstructionBudget m C K) := by
  let J := realTwoJet F
  have hJ : ContDiff ℝ ∞ J := contDiff_realTwoJet hF
  have hJn : ∀ x ∈ U, realJetNormal (J x) 4 ≠ 0 := hU.good
  obtain ⟨hscalar,hvector⟩ := weighted_realJet_coefficients hU.isOpen.uniqueDiffOn
    hJ hs hC hK hb hU.determinant hJn hGD hGN
  have hmap : MapsTo (complexifyJetCLM ∘ J) U admissibleComplexJets :=
    fun x hx => complexifyJet_mem (hU.determinant x hx) (hU.good x hx)
  have hcoeff := admissibleComplexJets_domain.smoothCoefficients.comp
    (complexifyJetCLM.contDiff.comp hJ).contDiffOn hmap
  have hsc (i : Fin 8) : ContDiffOn ℝ ∞ (fun x => realScalarCoefficients (J x) i) U := by
    have hh := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hcoeff (Sum.inl i))
    apply hh.congr
    intro x hx
    change realScalarCoefficients (J x) i = (LowJet.scalarCoefficients (complexifyJetCLM (J x)) i).re
    rw [scalarCoefficients_complexify,Complex.ofReal_re]
  have hvc (i : Fin 5) : ContDiffOn ℝ ∞ (fun x => realVectorCoefficients (J x) i) U := by
    apply contDiffOn_pi.mpr
    intro a
    have hh := Complex.reCLM.contDiff.comp_contDiffOn (contDiffOn_pi.mp hcoeff (Sum.inr (i,a)))
    apply hh.congr
    intro x hx
    change realVectorCoefficients (J x) i a = (LowJet.vectorCoefficients (complexifyJetCLM (J x)) i a).re
    rw [vectorCoefficients_complexify,Complex.ofReal_re]
  have hcs (i : Fin 8) : WeightedBound U s m (reconstructionBudget m C K)
      (fun p => LowJet.scalarCoefficients (twoJet (fun p => complexify (F p)) p) i) := by
    have hh := weighted_linearIsometry hU.isOpen.uniqueDiffOn (hsc i) (hscalar i) Complex.ofRealLI
    apply hh.congr
    intro p hp
    change LowJet.scalarCoefficients (twoJet (fun p => complexify (F p)) p) i =
      (realScalarCoefficients (J p) i : ℂ)
    rw [show twoJet (fun p => complexify (F p)) p = complexifyJetCLM (J p) from
      congrFun (twoJet_complexify hF) p]
    exact scalarCoefficients_complexify (J p) i
  have hcv (i : Fin 5) : WeightedBound U s m (reconstructionBudget m C K)
      (fun p => LowJet.vectorCoefficients (twoJet (fun p => complexify (F p)) p) i) := by
    have hh := weighted_linearIsometry hU.isOpen.uniqueDiffOn (hvc i) (hvector i) (complexifyLI 4)
    apply hh.congr
    intro p hp
    change LowJet.vectorCoefficients (twoJet (fun p => complexify (F p)) p) i =
      complexify (realVectorCoefficients (J p) i)
    rw [show twoJet (fun p => complexify (F p)) p = complexifyJetCLM (J p) from
      congrFun (twoJet_complexify hF) p]
    ext a
    exact vectorCoefficients_complexify (J p) i a
  exact ⟨⟨⟨hcs 0,hcs 1,hcs 2,hcs 3,hcs 4,hcs 5,hcs 6,hcs 7⟩,hcv 0,hcv 1⟩,
    hcv 2,hcv 3,hcv 4⟩

end ClosedSurfaceR4.SmallModes

end

end OAI
