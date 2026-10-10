import OAI.Geometry.Immersion.ClosedSurface.NormalJets
import OAI.Geometry.Immersion.ClosedSurface.RealBounds

namespace OAI

/-! Uniform reconstruction estimates on a fixed compact set of real two-jets. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SmallModes
open RealModes WeightedEstimates

def admissibleComplexJets : Set (TwoJet 4) :=
  {J | gramDet (J 0) (J 1) ≠ 0 ∧
    normalPart (J 0) (J 1) (J 4) ⬝ᵥ normalPart (J 0) (J 1) (J 4) ≠ 0}

lemma admissibleComplexJets_domain : LowJet.Domain admissibleComplexJets := by
  refine ⟨?_,fun _ h => h.1,fun _ h => h.2⟩
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hs (i : Fin 5) : ContDiffAt ℝ ∞ (fun K : TwoJet 4 => K i) J :=
    (ContinuousLinearMap.proj i : TwoJet 4 →L[ℝ] Ambient 4).contDiff.contDiffAt
  have hd := LowJet.contDiffAt_gramDet (hs 0) (hs 1)
  have hn := LowJet.contDiffAt_normalPart (hs 0) (hs 1) (hs 4) hJ.1
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((LowJet.contDiffAt_dot hn hn).continuousAt.eventually_ne hJ.2)

def complexifyJetCLM : RealTwoJet →L[ℝ] TwoJet 4 :=
  ContinuousLinearMap.pi fun i => (complexifyCLM 4).comp (ContinuousLinearMap.proj i)

def complexifyJetLI : RealTwoJet →ₗᵢ[ℝ] TwoJet 4 where
  toLinearMap := complexifyJetCLM.toLinearMap
  norm_map' J := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg J)).mpr
      intro i
      exact (norm_complexify (J i)).trans_le (norm_le_pi_norm J i)
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (complexifyJetCLM J))).mpr
      intro i
      exact (norm_complexify (J i)).symm.trans_le (norm_le_pi_norm (complexifyJetCLM J) i)

lemma complexifyJet_mem {J : RealTwoJet}
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0)
    (hB : realNormalPart (J 0) (J 1) (J 4) ≠ 0) :
    complexifyJetCLM J ∈ admissibleComplexJets := by
  constructor
  · change gramDet (complexify (J 0)) (complexify (J 1)) ≠ 0
    rw [complexify_gram]
    exact Complex.ofReal_ne_zero.mpr hD
  · change normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ⬝ᵥ
      normalPart (complexify (J 0)) (complexify (J 1)) (complexify (J 4)) ≠ 0
    rw [← complexify_normalPart,complexify_dot]
    exact Complex.ofReal_ne_zero.mpr ((dotProduct_self_eq_zero).not.mpr hB)

lemma twoJet_complexify {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    twoJet (fun p => complexify (F p)) = complexifyJetCLM ∘ realTwoJet F := by
  have hfirst (v : Base) : coordDeriv v (fun p => complexify (F p)) =
      fun p => complexify (coordDeriv v F p) := by
    funext p
    exact coordDeriv_complexify (hF.differentiable (by simp) p) v
  have hsecond (v w : Base) : coordDeriv v (fun p => complexify (coordDeriv w F p)) =
      fun p => complexify (coordDeriv v (coordDeriv w F) p) := by
    funext p
    exact coordDeriv_complexify ((contDiff_real_coordDeriv hF w).differentiable (by simp) p) v
  funext p i
  fin_cases i
  · change coordDeriv dx (fun p => complexify (F p)) p = complexify (coordDeriv dx F p)
    exact congrFun (hfirst dx) p
  · change coordDeriv dy (fun p => complexify (F p)) p = complexify (coordDeriv dy F p)
    exact congrFun (hfirst dy) p
  · change coordDeriv dx (coordDeriv dx (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dx F) p)
    rw [hfirst dx]
    exact congrFun (hsecond dx dx) p
  · change coordDeriv dx (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dx (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dx dy) p
  · change coordDeriv dy (coordDeriv dy (fun p => complexify (F p))) p =
      complexify (coordDeriv dy (coordDeriv dy F) p)
    rw [hfirst dy]
    exact congrFun (hsecond dy dy) p

/-- The constant precedes the map and scale. Its only geometric input is a
fixed compact set of admissible real two-jets; higher bounds enter polynomially. -/
theorem compact_real_reconstruction_bounds {U : Set Base} (hU : IsOpen U)
    {Ω K : Set RealTwoJet} (hΩ : RealJetDomain Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (F : RField 4) (s C : ℝ), 0 < s → 1 ≤ C →
      ContDiff ℝ ∞ F → MapsTo (realTwoJet F) U K →
      WeightedBound U s m C (realTwoJet F) →
      ReconstructionCoefficientBound (fun p => complexify (F p)) U s m
        ((m.factorial : ℝ) * D * C^m) := by
  have hKc : IsCompact (complexifyJetCLM '' K) := hK.image complexifyJetCLM.continuous
  have hKo : complexifyJetCLM '' K ⊆ admissibleComplexJets := by
    rintro _ ⟨J,hJ,rfl⟩
    exact complexifyJet_mem (hΩ.determinant J (hKΩ hJ)) (hΩ.good J (hKΩ hJ))
  obtain ⟨D,hD,hd⟩ := compact_reconstructionCoefficientBound hU
    admissibleComplexJets_domain hKc hKo m
  refine ⟨D,hD,?_⟩
  intro F s C hs hC hF hFK hb
  apply hd (fun p => complexify (F p)) s C hs hC (contDiff_complexify hF).contDiffOn
  · intro p hp
    rw [twoJet_complexify hF]
    exact mem_image_of_mem complexifyJetCLM (hFK hp)
  · rw [twoJet_complexify hF]
    exact weighted_linearIsometry hU.uniqueDiffOn (contDiff_realTwoJet hF).contDiffOn hb complexifyJetLI

end ClosedSurfaceR4.SmallModes

end

end OAI
