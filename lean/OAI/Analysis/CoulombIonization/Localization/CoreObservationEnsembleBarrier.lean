import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryOutMaximumBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.CoupledCoreExcessBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombAtom

structure CoreObservationEnsemble where
  Branch : Type
  finite : Fintype Branch
  graph : Branch → CoreObservationGraph
attribute [instance] CoreObservationEnsemble.finite

namespace CoreObservationEnsemble

def initial {N : ℕ} (ψ : FormVector N) (hψ : SobolevFermion ψ) : CoreObservationEnsemble where
  Branch := Unit
  finite := inferInstance
  graph := fun _ => CoreObservationGraph.initial ψ hψ

def observe (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) : CoreObservationEnsemble where
  Branch := Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2
  finite := inferInstance
  graph := fun ic => (E.graph ic.1).observe p hp ic.2

def mass (E : CoreObservationEnsemble) : ℝ := ∑ i, (E.graph i).mass
def countMoment (E : CoreObservationEnsemble) (y : Space) (R : ℝ) : ℝ :=
  ∑ i, (E.graph i).countMoment y R
def fieldMoment (E : CoreObservationEnsemble) (Z lam : ℝ) (y : Space) : ℝ :=
  ∑ i, (E.graph i).fieldMoment Z lam y
def excess (E : CoreObservationEnsemble) (Z lam : ℝ) : ℝ := ∑ i, (E.graph i).excess Z lam
def outMoment (E : CoreObservationEnsemble) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (Z lam : ℝ) : ℝ := ∑ i, (E.graph i).outMoment y hr hb Z lam

lemma mass_nonneg (E : CoreObservationEnsemble) : 0 ≤ E.mass :=
  Finset.sum_nonneg (fun i _ => (E.graph i).mass_nonneg)
lemma countMoment_nonneg (E : CoreObservationEnsemble) (y : Space) (R : ℝ) : 0 ≤ E.countMoment y R :=
  Finset.sum_nonneg (fun i _ => (E.graph i).countMoment_nonneg y R)
lemma fieldMoment_nonneg (E : CoreObservationEnsemble) (Z lam : ℝ) (y : Space) : 0 ≤ E.fieldMoment Z lam y :=
  Finset.sum_nonneg (fun i _ => (E.graph i).fieldMoment_nonneg Z lam y)
lemma outMoment_nonneg (E : CoreObservationEnsemble) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (Z lam : ℝ) : 0 ≤ E.outMoment y hr hb Z lam :=
  Finset.sum_nonneg (fun i _ => (E.graph i).outMoment_nonneg y hr hb Z lam)

lemma observe_mass (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) : (E.observe p hp).mass = E.mass := by
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2, ((E.graph ic.1).observe p hp ic.2).mass) = _
  rw [Fintype.sum_sigma]
  simp_rw [CoreObservationGraph.observe_mass]
  rfl

lemma observe_countMoment (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (y : Space) (R : ℝ) :
    (E.observe p hp).countMoment y R ≤ E.countMoment y R := by
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
    ((E.graph ic.1).observe p hp ic.2).countMoment y R) ≤ _
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun i _ => (E.graph i).observe_countMoment p hp y R)

lemma fieldMoment_le_nuclear (E : CoreObservationEnsemble) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (y : Space) : E.fieldMoment Z lam y ≤ (Z/‖y‖)^2*E.mass := by
  unfold fieldMoment mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (E.graph i).fieldMoment_le_nuclear hZ hlam y)

lemma fieldMoment_ball_integrable (E : CoreObservationEnsemble) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hs : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (E.fieldMoment Z lam) (closedBall y A) :=
  integrable_finsetSum _ (fun i _ => coreLawAverage_fieldSquare_ball_integrable
    (E.graph i).sobolev y hd hs hZ hlam)

lemma observe_excess_budget (E : CoreObservationEnsemble) (y : Space) {r b R : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖) (hR : r+b < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).excess Z lam ≤
      E.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (E.countMoment y R)*Real.sqrt E.mass)+
        Real.sqrt (E.outMoment y hr hb Z lam)*Real.sqrt (E.countMoment y R) := by
  let K := (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2
  have h1 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i : E.Branch => (E.graph i).countMoment_nonneg y R) (fun i => (E.graph i).mass_nonneg)
  have h2 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (fun i : E.Branch => (E.graph i).outMoment_nonneg y hr hb Z lam)
    (fun i => (E.graph i).countMoment_nonneg y R)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).observe_excess_budget y hr hb hy hR hZ hlam)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hend := hh.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ K))) h2)
  change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
    ((E.graph ic.1).observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) ic.2).excess Z lam) ≤ _
  rw [Fintype.sum_sigma]
  exact hend

lemma fieldMoment_le_observe_excess (E : CoreObservationEnsemble)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hv : ∀ x ∈ ball y (2*B), (p 0).value x = 0)
    (hd : ∀ x ∈ ball y (2*B), ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*E.mass+
      (E.observe p hp).excess Z lam/B) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).fieldMoment_le_observe_excess p hp y hB hnuc hv hd hZ hlam)
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.sum_div] at hh
  change E.fieldMoment Z lam y ≤ 2*packetFieldConstant^2*((1/B^4+1/B)^2*E.mass+
    (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).excess Z lam)/B)
  rw [Fintype.sum_sigma]
  exact hh

lemma outMoment_spatial (E : CoreObservationEnsemble) (y : Space) {r b R B Z lam : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hR : 0 < R) (hsep : r+b+2*R ≤ ‖y‖)
    (hnear : r+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hηr : CoulombAnalysis.IsRadial η) (h1 : ∫ z, η z = 1) :
    E.outMoment y hr hb Z lam ≤ B*∫ z in closedBall y (r+b+R),
      (E.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb)).fieldMoment Z lam z := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (E.graph i).outMoment_spatial y hr hb hR hsep hnear hZ hlam hm hn hs hbound hηr h1)
  rw [←Finset.mul_sum] at hh
  change _ ≤ B*∫ z in closedBall y (r+b+R),
    ∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
      ((E.graph ic.1).observe p hp ic.2).fieldMoment Z lam z
  simp_rw [Fintype.sum_sigma]
  rw [integral_finsetSum]
  · exact hh
  · intro i _
    exact integrable_finsetSum _ (fun c _ => coreLawAverage_fieldSquare_ball_integrable
      ((E.graph i).observe p hp c).sobolev y hR (by linarith) hZ hlam)

end CoreObservationEnsemble
end CoulombAtom

end

end OAI
