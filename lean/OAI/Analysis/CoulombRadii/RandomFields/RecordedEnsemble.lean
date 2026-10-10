import Mathlib
import OAI.Analysis.CoulombRadii.Localization.RadialAppend

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

structure RecordedEnsemble (n : ℕ) where
  index : Type
  finite : Fintype index
  out : index → ℕ
  core : index → ℕ
  vector : (p : index) → H1Vector (out p+core p)
  labels : (p : index) → Fin (out p+core p) ≃ Fin n
attribute [instance] RecordedEnsemble.finite

namespace RecordedEnsemble
variable {n J : ℕ}

def totalMass (T : RecordedEnsemble n) : ℝ := ∑ p, mass (T.vector p)
def totalForm (T : RecordedEnsemble n) (S : Nuclei J) : ℝ := ∑ p, form S (T.vector p)
def Conserves (T : RecordedEnsemble n) (ψ : H1Vector n) : Prop :=
  ∀ W : Configuration n → ℝ, Measurable W → (∃ B : ℝ, ∀ x, |W x|≤B) →
    (∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p))=potentialForm W ψ

def CoreFermionic (T : RecordedEnsemble n) : Prop :=
  ∀ p, PartlyAntisymmetric (T.vector p) (coreIndexSet (T.out p) (T.core p))
def OutSupported (T : RecordedEnsemble n) (A : Set Space) : Prop :=
  ∀ p, PartlySupported (T.vector p) (outIndexSet (T.out p) (T.core p)) A

def rawSquare (T : RecordedEnsemble n) (S : Nuclei J) (y : Space) (a : ℝ) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    (max (coreConditionalObservable (T.vector p)
      (rawSignedField (attraction S y) {z | 40*a≤‖z-y‖} y) s x) 0)^2)

lemma reindexConfiguration_trans {a b c : ℕ} (e : Fin a ≃ Fin b) (f : Fin b ≃ Fin c) :
    reindexConfiguration (e.trans f)=reindexConfiguration f ∘ reindexConfiguration e := by
  funext x
  ext ⟨i,j⟩
  rfl

lemma Conserves.population {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, expectedPopulation (T.vector p) A)=expectedPopulation ψ A := by
  have H := hT (localCount A) (localCount_measurable hA)
    ⟨n,fun x => by rw [abs_of_nonneg (localCount_nonneg _ _)]; exact localCount_le _ _⟩
  simpa only [Function.comp_def,localCount_reindex,potentialForm,expectedPopulation_eq _ hA] using H

lemma Conserves.secondMoment {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, localCountSecondMoment (T.vector p) A)=localCountSecondMoment ψ A := by
  have hb (x : Configuration n) : |(localCount A x)^2|≤(n:ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (localCount_nonneg _ _) (localCount_le _ _) 2
  have H := hT (fun x => (localCount A x)^2) ((localCount_measurable hA).pow_const 2) ⟨_,hb⟩
  simpa only [Function.comp_def,localCount_reindex,potentialForm,localCountSecondMoment] using H

lemma Conserves.recorded_secondMoment {T : RecordedEnsemble n} {ψ : H1Vector n}
    (hT : T.Conserves ψ) {A : Set Space} (hA : MeasurableSet A) :
    (∑ p, sliceExpectation (T.vector p) (fun _ x => (localCount A x)^2))≤
      localCountSecondMoment ψ A := by
  rw [←hT.secondMoment hA]
  exact Finset.sum_le_sum (fun p _ => sliceExpectation_localCount_sq_le (T.vector p) hA)

theorem append_radial (S : Nuclei J) (ψ : H1Vector n) (T : RecordedEnsemble n)
    (hT : T.Conserves ψ) (hanti : T.CoreFermionic) (A : Set Space) (hsupp : T.OutSupported A)
    {a E : ℝ} (ha : 0<a) (y : Space) (hnuc : ∀ j, 3*a≤‖S.position j-y‖)
    (hE : (E:EReal)≤unrestrictedFormBottom S) :
    ∃ U : RecordedEnsemble n,
      U.Conserves ψ ∧ U.CoreFermionic ∧ U.OutSupported (A∪Metric.closedBall y (80*a)) ∧
      U.totalMass=T.totalMass ∧
      U.totalForm S≤T.totalForm S+3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a)) ∧
      a/(16*ballTrialCoefficient)*T.rawSquare S y a ≤
        T.totalForm S+3*(radialCutCoefficient/(40*a))^2*expectedPopulation ψ (Metric.closedBall y (80*a))-
          (∑ p, conditionalOutCost S (U.vector p))-E*T.totalMass+
            (4*ballTrialCoefficient*(screenBaseMass a)^2/a)*T.totalMass := by
  have H (p : T.index) := radial_append_raw_gain S (T.vector p) (hanti p) A (hsupp p) ha y hnuc hE
  choose q k e hm hanti' hcore hout hcons hgain using H
  let χ := radialCut y (40*a)
  let D := radialCutCoefficient/(40*a)
  have hr : 0<40*a := by positivity
  have hD : 0≤D := div_nonneg radialCutCoefficient_pos.le hr.le
  let v (p : T.index) (l : Fin (T.out p+T.core p) → Fin 2) :=
    (T.vector p).appendCut χ (radialCut_smooth y (40*a)) (radialCut_partition y (40*a))
      D hD (radialCut_derivative_bound y hr) l (e p l)
  let U : RecordedEnsemble n := {
    index := (p : T.index) × (Fin (T.out p+T.core p) → Fin 2)
    finite := inferInstance
    out := fun pl => T.out pl.1+q pl.1 pl.2
    core := fun pl => k pl.1 pl.2
    vector := fun pl => v pl.1 pl.2
    labels := fun pl => (recordAssoc _ _ _).trans ((coreReindex _ (e pl.1 pl.2)).trans (T.labels pl.1)) }
  have hmass : U.totalMass=T.totalMass := by
    dsimp [totalMass,U]
    rw [Fintype.sum_sigma]
    exact Finset.sum_congr rfl (fun p _ => hm p)
  have HC : U.Conserves ψ := by
    intro W hW hB
    change (∑ pl : (p : T.index) × (Fin (T.out p+T.core p) → Fin 2),
      potentialForm (W ∘ reindexConfiguration ((recordAssoc _ _ _).trans
        ((coreReindex _ (e pl.1 pl.2)).trans (T.labels pl.1)))) (v pl.1 pl.2))=_
    rw [Fintype.sum_sigma]
    simp only [reindexConfiguration_trans,←Function.comp_assoc]
    rw [show (∑ p, ∑ l, potentialForm (((W ∘ reindexConfiguration (T.labels p)) ∘
      reindexConfiguration (coreReindex _ (e p l))) ∘ reindexConfiguration (recordAssoc _ _ _)) (v p l))=
        ∑ p, potentialForm (W ∘ reindexConfiguration (T.labels p)) (T.vector p) from ?_]
    · exact hT W hW hB
    · apply Finset.sum_congr rfl
      intro p hp
      exact hcons p _ (hW.comp (reindexConfiguration_continuous _).measurable)
        (hB.imp (fun B hb x => hb _))
  have HI : U.totalForm S≤T.totalForm S+3*D^2*expectedPopulation ψ (Metric.closedBall y (80*a)) := by
    dsimp [totalForm,U]
    rw [Fintype.sum_sigma]
    have HH := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) =>
      form_radial_labelCut S (T.vector p) y hr)
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,show 2*(40*a)=80*a by ring] at HH
    rw [hT.population measurableSet_closedBall] at HH
    simpa only [v,form_appendCut] using HH
  have HG := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgain p)
  change (∑ p, a/(16*ballTrialCoefficient)*_)≤_ at HG
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at HG
  rw [hT.population measurableSet_closedBall] at HG
  refine ⟨U,HC,(fun pl => hanti' pl.1 pl.2),(fun pl => hout pl.1 pl.2),hmass,HI,?_⟩
  change _≤T.totalForm S+3*D^2*expectedPopulation ψ (Metric.closedBall y (80*a))-
    (∑ pl : (p : T.index) × (Fin (T.out p+T.core p) → Fin 2), conditionalOutCost S (v pl.1 pl.2))-
      E*T.totalMass+_
  rw [Fintype.sum_sigma]
  exact HG

end RecordedEnsemble
end Coulomb
end

end
end

end OAI
