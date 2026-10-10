import Mathlib
import OAI.Probability.Ballisticity.Estimates.OccupationSampling
import OAI.Probability.Ballisticity.Estimates.LocalRadiusOrder
import OAI.Probability.Ballisticity.Crossings.BadCrossingLaw
import OAI.Probability.Ballisticity.Stationary.BadArraySampling

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

def labelPerm (σ : Equiv.Perm ℕ) : Equiv.Perm StationaryCompact.Label :=
  Equiv.prodCongr (Equiv.refl ℤ) σ

def arrayPerm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (Y : ActualEpisodeArray e) : ActualEpisodeArray e :=
  (Y.1,(fun p => Y.2.1 (labelPerm σ p.1,labelPerm σ p.2)),
    (fun p => Y.2.2.1 (p.1,labelPerm σ p.2.1,p.2.2)),
    (fun p => Y.2.2.2 (p.1,p.2.1,σ p.2.2.1,p.2.2.2)))

lemma arrayPerm_continuous {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Continuous (arrayPerm e σ) := by unfold arrayPerm; fun_prop

lemma arrayPerm_shift {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (Y : ActualEpisodeArray e) :
    arrayPerm e σ (StationaryCompact.shift Y) = StationaryCompact.shift (arrayPerm e σ Y) := rfl

lemma arrayPerm_iterate {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (j : ℕ) (Y : ActualEpisodeArray e) :
    arrayPerm e σ (StationaryCompact.shift^[j] Y) = StationaryCompact.shift^[j] (arrayPerm e σ Y) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',arrayPerm_shift,ih,Function.iterate_succ_apply']

def anchorsPerm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (E : EpisodeAnchors e) : EpisodeAnchors e := E ∘ labelPerm σ
lemma anchorsPerm_measurable {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Measurable (anchorsPerm e σ) := by unfold anchorsPerm; fun_prop

def inputPerm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (X : EpisodeInput e) : EpisodeInput e := ((X.1.1,anchorsPerm e σ X.1.2),X.2)
lemma inputPerm_measurable {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ) :
    Measurable (inputPerm e σ) :=
  ((measurable_fst.comp measurable_fst).prodMk
    ((anchorsPerm_measurable e σ).comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd

lemma arrayPerm_actual {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (t J : Environment d → ℤ → ℕ) (X : EpisodeInput e) :
    arrayPerm e σ (actualArrayMap e t J X) = actualArrayMap e t J (inputPerm e σ X) := rfl

lemma anchorLaw_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) (ω : Environment d) :
    (globalEpisodeAnchors e t ht ω).map (anchorsPerm e σ) = globalEpisodeAnchors e t ht ω := by
  have hh := Measure.infinitePi_map_piCongrLeft
    (fun p : StationaryCompact.Label => episodeProfile e t ω p.1) (labelPerm σ).symm
  convert hh using 1
  · congr 1
    funext E p
    simp [anchorsPerm,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,labelPerm]
  · rfl

lemma inputLaw_perm {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [SFinite Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).map (inputPerm e σ) = episodeInputLaw e ν Q t ht := by
  have hk : (globalEpisodeAnchors e t ht).map (anchorsPerm e σ)=globalEpisodeAnchors e t ht := by
    ext ω
    rw [Kernel.map_apply _ (anchorsPerm_measurable e σ),anchorLaw_perm]
  have hmap : (Q.compProd (globalEpisodeAnchors e t ht)).map (Prod.map id (anchorsPerm e σ)) =
      Q.compProd (globalEpisodeAnchors e t ht) := by
    rw [←Measure.compProd_map (anchorsPerm_measurable e σ),hk]
  unfold episodeInputLaw
  change ((Q.compProd (globalEpisodeAnchors e t ht)).prod (episodeAuxiliaryLaw e ν)).map
    (Prod.map (Prod.map id (anchorsPerm e σ)) id)=_
  rw [←Measure.map_prod_map _ _ (measurable_id.prodMap (anchorsPerm_measurable e σ)) measurable_id,
    hmap,Measure.map_id]

lemma occupation_perm_integral {d : ℕ} (e : Direction d) (σ : Equiv.Perm ℕ)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (hJ : ∀ i, Measurable fun ω => J ω i) (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (F : ActualEpisodeArray e →ᵇ ℝ) :
    (∫ Y, F (arrayPerm e σ Y) ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=
      ∫ Y, F Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)) := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos,
    actualOccupation_integral e ν Q t J ht N M hpos]
  congr 1
  have h₁ := actualOccupationRaw_integral e ν Q t J ht hJ N M hM
    (F.toContinuousMap.comp ⟨arrayPerm e σ,arrayPerm_continuous e σ⟩)
  have h₂ := actualOccupationRaw_integral e ν Q t J ht hJ N M hM F.toContinuousMap
  simp only [ContinuousMap.comp_apply,BoundedContinuousFunction.coe_toContinuousMap,
    ContinuousMap.coe_mk] at h₁ h₂
  rw [h₁,h₂]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [arrayPerm_iterate,arrayPerm_actual]
  have hf : Measurable (fun X : EpisodeInput e => F (StationaryCompact.shift^[j] (actualArrayMap e t J X))) :=
    F.continuous.measurable.comp ((StationaryCompact.shift_continuous.measurable.iterate j).comp
      (actualArrayMap_measurable e t J ht hJ))
  rw [←integral_map (inputPerm_measurable e σ).aemeasurable hf.aestronglyMeasurable,
    inputLaw_perm]

namespace OperationalConstants
variable {d : ℕ} {ν : Measure (Row d)} [IsProbabilityMeasure ν]
  {e f : Direction d} {D : ℝ}

lemma bad_limit_perm (C : OperationalConstants ν e f D) (hef : e.1≠f.1)
    (Ns : ℕ → ℕ) (hN : ∀ n, C.sfloor ≤ (Ns n:ℝ))
    (hmass : ∀ n, (Ns n:ℝ)^(-D) ≤ (environmentLaw ν).real (badCrossingEvent e (Ns n) (1/2)))
    (ρ : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun n => C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)])) atTop (𝓝 ρ)) (σ : Equiv.Perm ℕ) :
    MeasurePreserving (arrayPerm e σ) (ρ : Measure (ActualEpisodeArray e)) (ρ : Measure (ActualEpisodeArray e)) := by
  apply StationaryCompact.invariant_of_weak_limit (arrayPerm e σ) (arrayPerm_continuous e σ) _ ρ hlim
  intro F
  have hz (n : ℕ) : (∫ Y, F (arrayPerm e σ Y) ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) : Measure (ActualEpisodeArray e)))=
      ∫ Y, F Y ∂(C.occupation hef (Ns n)
      ((environmentLaw ν)[|badCrossingEvent e (Ns n) (1/2)]) : Measure (ActualEpisodeArray e)) :=
    occupation_perm_integral e σ ν _ _ _ (C.paddedTimes_measurable hef (Ns n))
      (C.paddedStages_measurable hef (Ns n)) (Ns n) _ (C.activeCount_measurable hef (Ns n))
      (C.bad_raw_mass_pos hef (Ns n) (hN n) (hmass n)) F
  simpa only [hz,sub_self] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end OperationalConstants
end DirectionalTransience

end

end OAI
