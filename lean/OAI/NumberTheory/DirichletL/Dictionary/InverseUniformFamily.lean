import OAI.NumberTheory.DirichletL.Dictionary.InverseUniformLog
import OAI.NumberTheory.DirichletL.Dictionary.InverseUniformScale

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

def inverseLogSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  realInterpolatedLogSchwartz (baseProfile reverse n V W p.2) a b ha
    ((baseProfile_support reverse n V W p.2).trans hs)
    (baseProfile_smooth reverse n V W p.2 a b ha hV hW hs) p

lemma inverseLogSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) (x : ℝ) :
    inverseLogSchwartz reverse n V W a b ha hV hW hs p x=inverseLogFamily reverse n V W p x := by
  rw [inverseLogSchwartz,realInterpolatedLogSchwartz_apply,inverseLogFamily_eq]

def inverseSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (baseProfile reverse n V W R) a b ha
    ((baseProfile_support reverse n V W R).trans hs)
    (baseProfile_smooth reverse n V W R a b ha hV hW hs) σ t

lemma inverseSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t x : ℝ) :
    inverseSchwartz reverse n V W a b ha hV hW hs R σ t x=
      twistProfile (baseProfile reverse n V W R) σ t x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem inverseSchwartz_operator_uniform (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) (Rmax : ℝ)
    (op : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀R∈Icc (0:ℝ) Rmax,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤C*(1+‖t‖)^J := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (op.comp (CompletedHeight.fixedLogReturnCLM a b ha)) S
  obtain ⟨J,B,hB,hbound⟩ := compact_family_frequencyTwist
    (inverseLogFamily reverse n V W) (inverseLogFamily_smooth reverse n V W hV hW)
    (|Real.log a|+|Real.log b|) (by positivity) (inverseLogFamily_support reverse n V W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax) (isCompact_Icc.prod isCompact_Icc)
    (inverseLogSchwartz reverse n V W a b ha hV hW hs)
    (inverseLogSchwartz_apply reverse n V W a b ha hV hW hs) T
  refine ⟨J,A*B,mul_pos hA hB,?_⟩
  intro R hR σ hσ t
  have hp : (σ,R)∈Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax := ⟨hσ,hR⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))≤B*(1+‖t‖)^J :=
    (hbound (σ,R) hp (t/(2*Real.pi))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
