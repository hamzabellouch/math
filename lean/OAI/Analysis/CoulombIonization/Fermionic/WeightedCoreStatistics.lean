import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FiniteCellObservation

namespace OAI

open MeasureTheory Filter Set
open scoped BigOperators
noncomputable section
namespace CoulombAtom

def rawWeightedCount {N : ℕ} (f : Space → ℝ) (x : Configuration N) : ℝ := ∑ i, f (x i)
lemma rawWeightedCount_nonneg {N : ℕ} {f : Space → ℝ} (hf : ∀ z, 0 ≤ f z)
    (x : Configuration N) : 0 ≤ rawWeightedCount f x := Finset.sum_nonneg (fun i _ => hf (x i))
lemma rawWeightedCount_le {N : ℕ} {f : Space → ℝ} {A : ℝ} (hf : ∀ z, f z ≤ A)
    (x : Configuration N) : rawWeightedCount f x ≤ N*A := by
  calc _ ≤ ∑ _i : Fin N, A := Finset.sum_le_sum (fun i _ => hf (x i))
       _ = _ := by simp
lemma rawWeightedCount_measurable {N : ℕ} {f : Space → ℝ} (hf : Measurable f) :
    Measurable (rawWeightedCount (N := N) f) :=
  Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))
lemma rawWeightedCount_cutCore_le {N : ℕ} {f : Space → ℝ} (hf : ∀ z, 0 ≤ f z)
    (c : Fin N → Fin 2) (x : Configuration N) :
    rawWeightedCount f (cutCorePositions c x) ≤ rawWeightedCount f x := by
  rw [rawWeightedCount,sum_cutCorePositions c x f]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact hf _

def rawWeightedMoment {N : ℕ} (psi : FormVector N) (f : Space → ℝ) : ℝ :=
  rawFormPair psi (fun x => rawWeightedCount f x^2)
lemma rawWeightedMoment_nonneg {N : ℕ} (psi : FormVector N) (f : Space → ℝ) :
    0 ≤ rawWeightedMoment psi f :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
lemma rawWeightedMoment_eq_integral {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    rawWeightedMoment psi f = ∫ x, rawWeightedCount f x^2 ∂formRawLaw psi :=
  rawFormPair_eq_integral hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))
lemma rawWeightedMoment_coreSlice_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z)
    {A : ℝ} (hb : ∀ z, f z ≤ A) (t : Spins M) :
    Integrable (fun v => rawWeightedMoment (coreSlice psi t v) f) :=
  rawFormPair_coreSlice_integrable hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x)) t

lemma sum_cutCore_weightedMoment_le {N : ℕ} {psi : FormVector N} (hpsi : SobolevVector psi)
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin N → Fin 2, coreLawAverage (orderedCutForm p hp psi c)
      (fun phi => rawWeightedMoment phi f)) ≤ rawWeightedMoment psi f := by
  simp only [rawWeightedMoment]
  simp_rw [cutCore_rawFormPair p hp hpsi _ ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))]
  rw [rawFormPair_eq_integral hpsi ((rawWeightedCount_measurable hm).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn x) (rawWeightedCount_le hb x))]
  change spatialCutExpectation p hp psi (fun c x => rawWeightedCount f (cutCorePositions c x)^2) ≤ _
  apply spatialCutExpectation_le_raw p hp hpsi
    (fun c => ((rawWeightedCount_measurable hm).comp (cutCorePositions_measurable c)).pow_const 2)
    (A := ((N:ℝ)*A)^2)
    (fun c x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn _)
      ((rawWeightedCount_cutCore_le hn c x).trans (rawWeightedCount_le hb x)))
    ((rawWeightedCount_measurable hm).pow_const 2) (B := ((N:ℝ)*A)^2)
    (fun x => norm_sq_le_of_nonneg (rawWeightedCount_nonneg hn _) (rawWeightedCount_le hb _))
  intro c x _
  exact pow_le_pow_left₀ (rawWeightedCount_nonneg hn _) (rawWeightedCount_cutCore_le hn c x) 2

lemma nextCoreObservation_weighted_statistic_integrable {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) (t : Spins M) :
    Integrable (fun v => coreLawAverage (orderedCutForm p hp (coreSlice psi t v) c)
      (fun phi => rawWeightedMoment phi f)) :=
  nextCoreObservation_statistic_integrable psi p hp c (fun phi => rawWeightedMoment phi f)
    (fun s => rawWeightedMoment_coreSlice_integrable (nextCoreObservation_sobolev hpsi p hp c) hm hn hb s) t

theorem sum_nextCoreObservation_weightedMoment_le {N M : ℕ} {psi : FormVector (N+M)}
    (hpsi : SobolevVector psi) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin N → Fin 2, coreLawAverage (nextCoreObservation p hp psi c)
      (fun phi => rawWeightedMoment phi f)) ≤ coreLawAverage psi (fun phi => rawWeightedMoment phi f) := by
  have ht (c : Fin N → Fin 2) := coreLawAverage_next psi p hp c
    (fun phi => rawWeightedMoment phi f)
    (fun s => rawWeightedMoment_coreSlice_integrable (nextCoreObservation_sobolev hpsi p hp c) hm hn hb s)
  simp_rw [ht]
  rw [Finset.sum_comm]
  change (∑ t : Spins M, ∑ c : Fin N → Fin 2, ∫ v,
    coreLawAverage (orderedCutForm p hp (coreSlice psi t v) c) (fun phi => rawWeightedMoment phi f)) ≤
    ∑ t : Spins M, ∫ v, rawWeightedMoment (coreSlice psi t v) f
  apply Finset.sum_le_sum
  intro t _
  have hi := fun c (_ : c ∈ (Finset.univ : Finset (Fin N → Fin 2))) =>
    nextCoreObservation_weighted_statistic_integrable hpsi p hp c hm hn hb t
  rw [←integral_finsetSum _ hi]
  apply integral_mono_ae (integrable_finsetSum _ hi) (rawWeightedMoment_coreSlice_integrable hpsi hm hn hb t)
  filter_upwards [hpsi.ae_coreSlice t] with v hv
  exact sum_cutCore_weightedMoment_le hv p hp hm hn hb

namespace CoreObservationGraph
 def weightedMoment (G : CoreObservationGraph) (f : Space → ℝ) : ℝ :=
    coreLawAverage G.vector (fun phi => rawWeightedMoment phi f)
 lemma observe_weightedMoment (G : CoreObservationGraph) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (∑ c : Fin G.coreSize → Fin 2, (G.observe p hp c).weightedMoment f) ≤ G.weightedMoment f :=
  sum_nextCoreObservation_weightedMoment_le G.sobolev p hp hm hn hb
end CoreObservationGraph
namespace CoreObservationEnsemble
 def weightedMoment (E : CoreObservationEnsemble) (f : Space → ℝ) : ℝ :=
   ∑ i, (E.graph i).weightedMoment f
 lemma initial_weightedMoment {N : ℕ} (psi : FormVector N) (hpsi : SobolevFermion psi) (f : Space → ℝ) :
   (initial psi hpsi).weightedMoment f = rawWeightedMoment psi f := by
   change (∑ _i : Unit, coreLawAverage (M := 0) psi (fun phi => rawWeightedMoment phi f)) = _
   simp [coreLawAverage_empty]
 lemma observe_weightedMoment (E : CoreObservationEnsemble) (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (E.observe p hp).weightedMoment f ≤ E.weightedMoment f := by
   change (∑ ic : Σ i : E.Branch, Fin (E.graph i).coreSize → Fin 2,
     ((E.graph ic.1).observe p hp ic.2).weightedMoment f) ≤ _
   rw [Fintype.sum_sigma]
   exact Finset.sum_le_sum (fun i _ => (E.graph i).observe_weightedMoment p hp hm hn hb)
 lemma observeCells_weightedMoment (E : CoreObservationEnsemble) (ys : List Space)
    {f : Space → ℝ} (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) {A : ℝ} (hb : ∀ z, f z ≤ A) :
    (E.observeCells ys).weightedMoment f ≤ E.weightedMoment f := by
   classical
   induction ys generalizing E with
   | nil => exact le_rfl
   | cons y ys ih =>
     apply (ih _).trans
     unfold observeCell
     split_ifs
     · exact le_rfl
     · exact observe_weightedMoment E _ _ hm hn hb
end CoreObservationEnsemble
end CoulombAtom

end

end OAI
