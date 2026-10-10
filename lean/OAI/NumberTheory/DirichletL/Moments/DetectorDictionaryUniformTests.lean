import OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma twistProfile_zero (W : ℝ→ℂ) : twistProfile W 0 0=W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

lemma oriented_detector_log_support (reverse : Bool) (n : ℕ) :
    Function.support (orientedProfile reverse ((logProfile^[n]) positiveAnnular))⊆Icc (1/4) (9/4) := by
  simpa only [twistProfile_zero] using detector_profile_support reverse n 0 0

lemma oriented_detector_log_smooth (reverse : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) := by
  simpa only [twistProfile_zero] using detector_profile_smooth reverse n 0 0

def detectorSchwartz (reverse : Bool) (n : ℕ) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support reverse n) (oriented_detector_log_smooth reverse n) σ
      (orientedFrequency reverse t)

lemma detectorSchwartz_apply (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    detectorSchwartz reverse n σ t x=
      twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ (orientedFrequency reverse t) x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem detectorSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Fin 3=>interpolatedProfile_uniform
    (orientedProfile q.1 ((logProfile^[q.2.val]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support q.1 q.2.val) (oriented_detector_log_smooth q.1 q.2.val) S
  let J := (Finset.univ : Finset (Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Fin 3,C q,by linarith,?_⟩
  intro reverse n hn σ hσ t
  let q : Bool×Fin 3 := (reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q σ hσ (orientedFrequency reverse t)
  have hnorm : ‖orientedFrequency reverse t‖=‖t‖ := by cases reverse <;> simp [orientedFrequency]
  rw [hnorm] at he
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
