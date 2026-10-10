import OAI.NumberTheory.CubicMoment.Theta.CubicThetaC1PairingIntegral

namespace OAI

/-! The scalar Hermitian pairing of two actual automorphic sections
descends to the quotient and agrees with the L2 inner product. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaSectionPairing (F G : CubicThetaSection) (q : CubicThetaQuotient) : ℂ :=
  inner ℂ (F.val (cubicThetaQuotientLift q)) (G.val (cubicThetaQuotientLift q))

lemma cubicThetaSectionPairing_invariant (F G : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    inner ℂ (F.val (g • p)) (G.val (g • p))=inner ℂ (F.val p) (G.val p) := by
  rw [F.property,G.property]
  change inner ℂ (cubicThetaKubotaValue g • F.val p) (cubicThetaKubotaValue g • G.val p)=_
  rw [inner_smul_left,inner_smul_right,← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,cubicThetaKubotaValue_norm]
  simp

lemma cubicThetaSectionPairing_apply (F G : CubicThetaSection) (p : CubicThetaPoint) :
    cubicThetaSectionPairing F G (cubicThetaQuotientMap p)=inner ℂ (F.val p) (G.val p) := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaSectionPairing
  rw [← hg,cubicThetaSectionPairing_invariant]

lemma cubicThetaSectionPairing_continuous (F G : CubicThetaSection) :
    Continuous (cubicThetaSectionPairing F G) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaSectionPairing F G ∘ cubicThetaQuotientMap=
      fun p => inner ℂ (F.val p) (G.val p) := funext (cubicThetaSectionPairing_apply F G)
  rw [he]
  exact F.val.continuous.inner G.val.continuous

lemma cubicThetaSectionPairing_support (F G : CubicThetaSection) :
    tsupport (cubicThetaSectionPairing F G)⊆tsupport (cubicThetaSectionNorm F) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro q hq
  apply subset_tsupport
  intro h
  have hz : F.val (cubicThetaQuotientLift q)=0 := norm_eq_zero.mp h
  exact hq (by simp only [cubicThetaSectionPairing,hz,inner_zero_left])

lemma cubicThetaSectionPairing_L2 (F G : CubicThetaSection)
    (hmF : MemLp (cubicThetaSectionRepresentative F) 2 cubicThetaQuotientMeasure)
    (hmG : MemLp (cubicThetaSectionRepresentative G) 2 cubicThetaQuotientMeasure) :
    inner ℂ (hmF.toLp _) (hmG.toLp _)=∫ q, cubicThetaSectionPairing F G q ∂cubicThetaQuotientMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hmF.coeFn_toLp,hmG.coeFn_toLp] with q hqF hqG
  rw [hqF,hqG]
  have h := cubicThetaSectionPairing_apply F G (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse] at h
  exact h.symm

end CubicFirstMoment

end

end OAI
