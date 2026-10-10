import Mathlib
import OAI.Probability.Ballisticity.Entropy.WindowEntropy
import OAI.Probability.Ballisticity.Entropy.BadWindowEntropy
import OAI.Probability.Ballisticity.Estimates.LocalRadiusOrder
import OAI.Probability.Ballisticity.Crossings.BadCrossingLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma typedCurrentArrayWindow_shift {d : ℕ} (e : Direction d) (i : ℤ) (m : ℕ)
    (Y : ActualEpisodeArray e) :
    typedCurrentArrayWindow e i m (StationaryCompact.shift Y)=typedCurrentArrayWindow e (i+1) m Y := rfl

lemma stationary_currentWindow_law {d : ℕ} (e : Direction d) (m : ℕ)
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
      (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) :
    (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m) =
      (actualCurrentLaw e m ρ : Measure (CurrentWindow e)) := by
  have hs' (j : ℤ) : (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e (j+1) m)=
      (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e j m) := by
    calc
      _ = (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e j m ∘ StationaryCompact.shift) := rfl
      _ = ((ρ : Measure (ActualEpisodeArray e)).map StationaryCompact.shift).map (typedCurrentArrayWindow e j m) :=
        (Measure.map_map (typedCurrentArrayWindow_measurable e j m) hstat.measurable).symm
      _ = _ := by rw [hstat.map_eq]
  induction i using Int.induction_on with
  | zero => rfl
  | succ i hi => exact (hs' i).trans hi
  | pred i hi =>
    have hh := hs' (-(i:ℤ)-1)
    simp only [sub_add_cancel] at hh
    exact hh.symm.trans hi

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

theorem stationary_window_entropy (C : OperationalConstants ν e f D) (hef : e.1≠f.1) (hD : 0≤D)
    (Ns : ℕ → ℕ)
    (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hlarge : ∀ n, 32*C.b ≤ (1/2:ℝ)*Real.log (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ))
    (hstat : MeasurePreserving StationaryCompact.shift (ρ : Measure (ActualEpisodeArray e))
      (ρ : Measure (ActualEpisodeArray e))) (i : ℤ) (m : ℕ) :
    let W := (ρ : Measure (ActualEpisodeArray e)).map (typedCurrentArrayWindow e i m)
    klDiv W (W.fst.compProd (currentWindowReference e ν)) ≤
      ENNReal.ofReal ((m:ℝ)*C.windowEntropyConstant) := by
  dsimp only
  rw [stationary_currentWindow_law e m ρ hstat i]
  exact C.bad_limit_window_entropy hef hD Ns hN hlarge hmass ρ hlim m

end OperationalConstants
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Classical Topology
namespace DirectionalTransience

lemma actualOccupation_ae_of_ae_invariant {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (s : Set (ActualEpisodeArray e)) (hs : MeasurableSet s)
    (ha : ∀ᵐ X ∂episodeInputLaw e ν Q t ht, actualArrayMap e t J X∈s)
    (hshift : ∀ Y∈s, StationaryCompact.shift Y∈s) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), Y∈s := by
  have hiter (i : ℕ) : ∀ᵐ X ∂episodeInputLaw e ν Q t ht,
      StationaryCompact.shift^[i] (actualArrayMap e t J X)∈s := by
    filter_upwards [ha] with X hX
    induction i with
    | zero => exact hX
    | succ i hi =>
      rw [Function.iterate_succ_apply']
      exact hshift _ hi
  have hraw : ∀ᵐ Y ∂actualOccupationRaw e ν Q t J ht N M, Y∈s := by
    unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply (ae_map_iff ((StationaryCompact.shift_continuous.measurable.iterate i).comp
      (actualArrayMap_measurable e t J ht hJ)).aemeasurable hs).mpr
    exact ae_restrict_of_ae (hiter i)
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change ∀ᵐ Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)), Y∈s
  rw [ρ.toMeasure_normalize_eq_of_nonzero hn]
  exact Measure.ae_smul_measure hraw _

def ArrayElliptic {d : ℕ} (e : Direction d) (κ : ℝ≥0) (Y : ActualEpisodeArray e) : Prop :=
  ∀ i m a l z u, κ ≤ (Y.2.2.2 (i,m,a,l,z)).1 u

lemma arrayElliptic_closed {d : ℕ} (e : Direction d) (κ : ℝ≥0) :
    IsClosed {Y : ActualEpisodeArray e | ArrayElliptic e κ Y} := by
  unfold ArrayElliptic
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun m => isClosed_iInter fun a =>
    isClosed_iInter fun l => isClosed_iInter fun z => isClosed_iInter fun u => ?_
  exact isClosed_le continuous_const ((continuous_apply u).comp
    (continuous_subtype_val.comp (by fun_prop)))

lemma arrayElliptic_shift {d : ℕ} (e : Direction d) (κ : ℝ≥0)
    (Y : ActualEpisodeArray e) (h : ArrayElliptic e κ Y) :
    ArrayElliptic e κ (StationaryCompact.shift Y) := by
  intro i m a l z u
  exact h (i+1) m a l z u

lemma auxiliary_rows {d : ℕ} (e : Direction d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u) :
    ∀ᵐ A ∂episodeAuxiliaryLaw e ν, ∀ p q u, κ ≤ (A p q).1 u := by
  have hinner : ∀ᵐ A ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν),
      ∀ q u, κ ≤ (A q).1 u := by
    apply ae_all_iff.mpr
    intro q
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ×HorizontalSpace e => ν) q).quasiMeasurePreserving.ae hν
  apply ae_all_iff.mpr
  intro p
  exact (measurePreserving_eval_infinitePi
    (fun _ : ℤ×ℕ => Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν)) p).quasiMeasurePreserving.ae hinner

lemma actualArrayMap_elliptic_ae {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ X ∂episodeInputLaw e ν Q t ht, ArrayElliptic e κ (actualArrayMap e t J X) := by
  have hm : MeasurableSet {ω : Environment d | ∀ y u, κ ≤ (ω y).1 u} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro y
    apply MeasurableSet.iInter
    intro u
    exact measurableSet_le measurable_const ((measurable_pi_apply u).comp
      (measurable_subtype_coe.comp (measurable_pi_apply y)))
  have hbase := Measure.ae_compProd_of_ae_fst (globalEpisodeAnchors e t ht) hm hQ
  have hfirst := (Measure.quasiMeasurePreserving_fst
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae hbase
  have hsecond := (Measure.quasiMeasurePreserving_snd
    (μ:=Q.compProd (globalEpisodeAnchors e t ht)) (ν:=episodeAuxiliaryLaw e ν)).ae
    (auxiliary_rows e ν κ hν)
  filter_upwards [hfirst,hsecond] with X hX hA
  intro i m a l z u
  change κ ≤ (episodeSplicedRow e t X i m a l z).1 u
  unfold episodeSplicedRow
  split
  · exact hX _ u
  · exact hA _ _ u

lemma actualOccupation_elliptic {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (κ : ℝ≥0) (hν : ∀ᵐ r ∂ν, ∀ u, κ ≤ r.1 u)
    (hQ : ∀ᵐ ω ∂Q, ∀ y u, κ ≤ (ω y).1 u) :
    ∀ᵐ Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)), ArrayElliptic e κ Y :=
  actualOccupation_ae_of_ae_invariant e ν Q t J ht hJ N M hpos _
    (arrayElliptic_closed e κ).measurableSet (actualArrayMap_elliptic_ae e ν Q t J ht κ hν hQ)
    (arrayElliptic_shift e κ)

end DirectionalTransience

end

end OAI
