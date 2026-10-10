import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.Gluing.FreshTrial
import OAI.Probability.CriticalPercolation.Criticality.BlockIndependence

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma countable_gluing_failure [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (lam : ℝ)
    (ha : ∀ v∈A, 1-lam ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A \ G.hitEvent o T) ≤
      lam * (BernoulliProduct.law q).real (G.hitEvent o A) := by
  have h := G.countable_joint_gluing q o A T (1-lam) ha
  have he := measureReal_sdiff_add_inter (μ := BernoulliProduct.law q)
    (s := G.hitEvent o A) (G.measurableSet_hitEvent o T)
  nlinarith

lemma countable_gluing_failure_le [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (lam : ℝ) (hlam : 0≤lam)
    (ha : ∀ v∈A, 1-lam ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A \ G.hitEvent o T) ≤ lam := by
  have h := G.countable_gluing_failure q o A T lam ha
  have ht : (BernoulliProduct.law q).real (G.hitEvent o A)≤1 := measureReal_le_one
  nlinarith

lemma measurableSet_randomHit [Countable V] [Countable E]
    (o : V) (A : Set E → Set V)
    (hA : ∀ v, MeasurableSet {ω : Set E | v∈A ω}) :
    MeasurableSet {ω : Set E | ω∈G.hitEvent o (A ω)} := by
  have he : {ω : Set E | ω∈G.hitEvent o (A ω)} =
      ⋃ v : V, ({ω : Set E | (G.openGraph ω).Reachable o v}∩{ω | v∈A ω}) := by
    ext ω
    simp only [hitEvent,cluster,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,
      Set.Nonempty]
  rw [he]
  exact MeasurableSet.iUnion fun v => (G.measurable_reachable o v).setOf.inter (hA v)

theorem random_relay_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (o : V) (A : Set E → Set V) (T : Set V)
    (hA : ∀ v, MeasurableSet[blockSigma S] {σ : Set E | v∈A σ})
    (lam : ℝ) (hlam : 0≤lam)
    (ha : ∀ σ v, v∈A σ → 1-lam ≤
      (BernoulliProduct.law (pinnedParameters q S σ)).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real
      {ω : Set E | ω∈G.hitEvent o (A ω) ∧ ω∉G.hitEvent o T} ≤ lam := by
  let F := {ω : Set E | ω∈G.hitEvent o (A ω) ∧ ω∉G.hitEvent o T}
  have hmF : MeasurableSet F :=
    (G.measurableSet_randomHit o A (fun v => (blockSigma_le S) _ (hA v))).inter
      (G.measurableSet_hitEvent o T).compl
  have hpin (σ : Set E) : blockProbability q S F σ =
      BernoulliProduct.law (pinnedParameters q S σ)
        (G.hitEvent o (A σ) \ G.hitEvent o T) := by
    rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn S σ)
      ((G.measurableSet_hitEvent o _).diff (G.measurableSet_hitEvent o T))]
    unfold blockProbability
    congr 1
    ext ω
    have hfixed : A (forceOn S σ ω)=A σ := by
      ext v
      exact block_event_forceOn S {τ : Set E | v∈A τ} (hA v) σ ω
    change (forceOn S σ ω∈G.hitEvent o (A (forceOn S σ ω)) ∧
      forceOn S σ ω∉G.hitEvent o T) ↔
        (forceOn S σ ω∈G.hitEvent o (A σ) ∧ forceOn S σ ω∉G.hitEvent o T)
    rw [hfixed]
  have hb (σ : Set E) : blockProbability q S F σ ≤ ENNReal.ofReal lam := by
    rw [hpin]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hlam]
    exact G.countable_gluing_failure_le _ o (A σ) T lam hlam (ha σ)
  have hint := lintegral_mono (μ := BernoulliProduct.law q) hb
  rw [lintegral_blockProbability q S F hmF,lintegral_const,measure_univ,mul_one] at hint
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
  simpa only [ENNReal.toReal_ofReal hlam,Measure.real,F] using hh

def seedHitEvent (B T : Set V) : Set (Set E) :=
  ⋃ b∈B, G.hitEvent b T

lemma measurableSet_seedHitEvent [Countable V] [Countable E] (B T : Set V) :
    MeasurableSet (G.seedHitEvent B T) :=
  MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => G.measurableSet_hitEvent b T

lemma seedHitEvent_upper (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.hitEvent_mono_edges b T hωτ hω⟩

lemma seed_trial_connects (v : V) (B T : Set V) (F ω : Set E)
    (hF : F⊆ω) (hconnect : ∀ b∈B, (G.openGraph F).Reachable v b)
    (hB : ω∈G.seedHitEvent B T) : ω∈G.hitEvent v T := by
  obtain ⟨b,hb,x,hbx,hx⟩ := Set.mem_iUnion₂.mp hB
  exact ⟨x, ((hconnect b hb).mono (G.openGraph_mono hF)).trans hbx, hx⟩

lemma seed_trial_probability [Countable V] [Countable E]
    (q : E → unitInterval) (S σ F : Set E) (v : V) (B T : Set V)
    (hFS : F⊆S) (hFσ : F⊆σ)
    (hconnect : ∀ b∈B, (G.openGraph F).Reachable v b) :
    (blockProbability q S (G.seedHitEvent B T) σ).toReal ≤
      (BernoulliProduct.law (pinnedParameters q S σ)).real (G.hitEvent v T) := by
  rw [← forceOn_map_law,Measure.real,Measure.map_apply (measurable_forceOn S σ)
    (G.measurableSet_hitEvent v T)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  apply G.seed_trial_connects v B T F (forceOn S σ ω) ?_ hconnect hω
  intro e he
  simp only [mem_forceOn,ite_eq_left (hFS he)]
  exact hFσ he

def goodRelay (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ) (σ : Set E) : Set V :=
  {v | v∈L ∧ F v⊆σ ∧ 1-lam≤(blockProbability q S (G.seedHitEvent (B v) T) σ).toReal}

lemma goodRelay_measurable [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ)
    (hFS : ∀ v, F v⊆S) (v : V) :
    MeasurableSet[blockSigma S] {σ : Set E | v∈G.goodRelay q S L F B T lam σ} := by
  have hW : MeasurableSet[blockSigma S] (allOpen (F v)) :=
    (blockSigma_mono (hFS v)) _ (measurable_allOpen_block (F v))
  have hg := (measurable_blockProbability q S (G.seedHitEvent (B v) T)
    (G.measurableSet_seedHitEvent (B v) T)).ennreal_toReal
  exact MeasurableSet.inter (MeasurableSet.const _) (hW.inter (measurableSet_le measurable_const hg))

theorem goodRelay_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V)
    (hFS : ∀ v, F v⊆S)
    (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
    (o : V) (lam : ℝ) (hlam : 0≤lam) :
    (BernoulliProduct.law q).real {ω : Set E |
      ω∈G.hitEvent o (G.goodRelay q S L F B T lam ω) ∧ ω∉G.hitEvent o T}≤lam := by
  apply G.random_relay_gluing q S o _ T
    (G.goodRelay_measurable q S L F B T lam hFS) lam hlam
  intro σ v hv
  exact hv.2.2.trans (G.seed_trial_probability q S σ (F v) v (B v) T
    (hFS v) hv.2.1 (hconnect v hv.1))

end CriticalPercolation.BondGraph
end
end
end

end OAI
