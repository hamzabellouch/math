import OAI.NumberTheory.DirichletL.Dictionary.InverseUniformFamily
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicCutoff

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def sourceOperator (scaled : Bool) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  if scaled then scaleCLM else ContinuousLinearMap.id ℝ _

def inverseDetectorSchwartz (reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseSchwartz reverse n cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support R σ t

lemma inverseDetectorSchwartz_apply (reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorSchwartz reverse n R σ t x=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x :=
  inverseSchwartz_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

def inverseDetectorTest (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  sourceOperator scaled (inverseDetectorSchwartz reverse n R σ t)

lemma inverseDetectorTest_apply (scaled reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorTest scaled reverse n R σ t x=
      if scaled then scaleProfile (twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t) x
      else twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x := by
  have he : (inverseDetectorSchwartz reverse n R σ t : ℝ→ℂ)=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t :=
    funext (inverseDetectorSchwartz_apply reverse n R σ t)
  cases scaled
  · exact inverseDetectorSchwartz_apply _ _ _ _ _ _
  · change scaleCLM (inverseDetectorSchwartz reverse n R σ t) x=_
    rw [scaleCLM_apply,he]
    rfl

theorem inverseDetectorTest_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R∈Icc (0:ℝ) 4,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Bool×Fin 3=>inverseSchwartz_operator_uniform
    q.2.1 q.2.2.val cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support 4 (sourceOperator q.1) S
  let J := (Finset.univ : Finset (Bool×Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Bool×Fin 3,C q,by linarith,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  let q : Bool×Bool×Fin 3 := (scaled,reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q R hR σ hσ t
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
