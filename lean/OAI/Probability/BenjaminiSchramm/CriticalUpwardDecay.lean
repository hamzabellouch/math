import OAI.Probability.BenjaminiSchramm.TiltedHit
import OAI.Probability.CriticalPercolation.Modular.LightTwoPointDecay

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma weightHit_antitone (x : V) : Antitone (fun a : ℝ≥0∞ => G.weightHit a x) := by
  rintro a b hab ω ⟨y,hxy,hy⟩
  exact ⟨y,hxy,hab.trans hy⟩

lemma weightHit_le_modularMass {a : ℝ≥0∞} {x : V} {ω : Set E}
    (h : ω ∈ G.weightHit a x) : a ≤ G.modularMass x (G.cluster ω x) := by
  obtain ⟨y,hxy,hy⟩ := h
  apply hy.trans
  change G.stabilizerWeight x y ≤
    ∑' z, if z ∈ G.cluster ω x then G.stabilizerWeight x z else 0
  have hxy' : y ∈ G.cluster ω x := hxy
  simpa only [ite_eq_left hxy'] using
    (ENNReal.le_tsum (f := fun z => if z ∈ G.cluster ω x then G.stabilizerWeight x z else 0) y)

lemma not_iInter_weightHit_nat_of_mass_ne_top {ω : Set E} {x : V}
    (hm : G.modularMass x (G.cluster ω x) ≠ ⊤) :
    ω ∉ ⋂ n : ℕ, G.weightHit n x := by
  obtain ⟨n,hn⟩ := ENNReal.exists_nat_gt hm
  intro h
  exact hn.not_ge (G.weightHit_le_modularMass (Set.mem_iInter.mp h n))

theorem tendsto_weightHit_nat_zero [Countable V] [Countable E]
    (p : unitInterval) (x : V)
    (hm : ∀ᵐ ω ∂G.law p, G.modularMass x (G.cluster ω x) ≠ ⊤) :
    Tendsto (fun n : ℕ => (G.law p).real (G.weightHit n x)) atTop (𝓝 0) := by
  have hz : G.law p (⋂ n : ℕ, G.weightHit n x) = 0 := by
    simpa only [not_not,Set.ofPred_mem_eq] using
      (ae_iff.mp (hm.mono fun _ h => G.not_iInter_weightHit_nat_of_mass_ne_top h))
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => (G.measurableSet_weightHit (n : ℝ≥0∞) x).nullMeasurableSet)
    (fun (n m : ℕ) hnm => G.weightHit_antitone x (by exact_mod_cast hnm)) ⟨0,measure_ne_top _ _⟩
  rw [hz] at h
  simpa only [Function.comp_def,measureReal_def,ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

lemma Aut.weightHit_preimage (φ : G.Aut) (a : ℝ≥0∞) (x : V) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.weightHit a (φ.vertex x) = G.weightHit a x := by
  ext ω
  constructor
  · rintro ⟨y,hxy,hy⟩
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    exact ⟨z,(SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hxy,
      by simpa only [Aut.stabilizerWeight] using hy⟩
  · rintro ⟨y,hxy,hy⟩
    exact ⟨φ.vertex y,(SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hxy,
      by simpa only [Aut.stabilizerWeight] using hy⟩

lemma Aut.weightHit_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (a : ℝ≥0∞) (x : V) :
    (G.law p).real (G.weightHit a (φ.vertex x)) = (G.law p).real (G.weightHit a x) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_weightHit _ _),φ.weightHit_preimage]

theorem uniform_weightHit_nat_small [Countable V] [Countable E]
    (hq : G.QuasiTransitive) (p : unitInterval)
    (hm : ∀ x, ∀ᵐ ω ∂G.law p, G.modularMass x (G.cluster ω x) ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x, (G.law p).real (G.weightHit n x) < ε := by
  obtain ⟨S,hS,hcover⟩ := hq
  have he (s : V) : ∀ᶠ n : ℕ in atTop, (G.law p).real (G.weightHit n s) < ε :=
    (G.tendsto_weightHit_nat_zero p s (hm s)).eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := (hS.toFinset.eventually_all.mpr fun s _ => he s).exists
  refine ⟨n,fun x => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover x
  rw [φ.weightHit_real]
  exact hn s (hS.mem_toFinset.mpr hs)

theorem nonunimodular_critical_upward_decay [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) (hu : ¬G.CombinatoriallyUnimodular)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ x, (G.law G.criticalProbability).real (G.weightHit n x) < ε := by
  apply G.uniform_weightHit_nat_small hq G.criticalProbability _ ε hε
  intro x
  exact (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu x).mono fun _ h => (h x).ne

end CriticalPercolation.BondGraph

end

end OAI
