import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.TwoPoint
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Modular.ModularSuperlevels
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyNull

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def upperEscapeEvent (v : V) (R : ℕ) : Set (Set E) :=
  {ω | ∃ x, x∈G.clusterUpperSet ω v ∧ x∉G.vertexBall v R}

lemma measurableSet_upperEscapeEvent [Countable V] [Countable E] (v : V) (R : ℕ) :
    MeasurableSet (G.upperEscapeEvent v R) := by
  exact (Measurable.exists fun x =>
    ((G.measurable_reachable v x).and measurable_const).and measurable_const).setOf

lemma upperEscapeEvent_antitone (v : V) : Antitone (G.upperEscapeEvent v) := by
  rintro n m h ω ⟨x,hx,hh⟩
  exact ⟨x,hx,fun hn => hh (G.vertexBall_mono v h hn)⟩

lemma not_iInter_upperEscape_of_mass_finite (hc : G.fullGraph.Connected)
    {ω : Set E} {v : V} (hm : G.modularMass v (G.cluster ω v)≠∞) :
    ω∉⋂ R : ℕ, G.upperEscapeEvent v R := by
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hc v (G.finite_clusterUpperSet_of_mass_ne_top hm)
  intro h
  obtain ⟨x,hx,hout⟩ := Set.mem_iInter.mp h R
  exact hout (hR hx)

lemma tendsto_upperEscape_zero [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (v : V)
    (hm : ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    Tendsto (fun R => (G.law p).real (G.upperEscapeEvent v R)) atTop (𝓝 0) := by
  have hz : G.law p (⋂ R : ℕ, G.upperEscapeEvent v R)=0 := by
    simpa only [not_not,Set.ofPred_mem_eq] using
      (ae_iff.mp (hm.mono (fun _ h => G.not_iInter_upperEscape_of_mass_finite hc h)))
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun R => (G.measurableSet_upperEscapeEvent v R).nullMeasurableSet)
    (G.upperEscapeEvent_antitone v) ⟨0,measure_ne_top _ _⟩
  rw [hz] at h
  have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  change Tendsto (fun R => (G.law p).real (G.upperEscapeEvent v R)) atTop
    (𝓝 ((0 : ℝ≥0∞).toReal)) at hh
  simpa only [ENNReal.toReal_zero] using hh

lemma Aut.upperEscapeEvent_preimage (φ : G.Aut) (v : V) (R : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.upperEscapeEvent (φ.vertex v) R =
      G.upperEscapeEvent v R := by
  ext ω
  change (∃ x, (_ ∧ _) ∧ _) ↔ (∃ x, (_ ∧ _) ∧ _)
  constructor
  · rintro ⟨x,hx,hout⟩
    obtain ⟨y,rfl⟩ := φ.vertex.surjective x
    refine ⟨y,⟨?_,?_⟩,?_⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hx.1
    · simpa only [φ.stabilizerWeight] using hx.2
    · exact fun hy => hout ((φ.vertexBall_mem G v y R).mpr hy)
  · rintro ⟨x,hx,hout⟩
    refine ⟨φ.vertex x,⟨?_,?_⟩,?_⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hx.1
    · simpa only [φ.stabilizerWeight] using hx.2
    · exact fun hy => hout ((φ.vertexBall_mem G v x R).mp hy)

lemma Aut.upperEscapeEvent_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (v : V) (R : ℕ) :
    (G.law p).real (G.upperEscapeEvent (φ.vertex v) R) =
      (G.law p).real (G.upperEscapeEvent v R) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_upperEscapeEvent _ _),φ.upperEscapeEvent_preimage]

lemma uniform_upperEscape_small [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hq : G.QuasiTransitive) (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞)
    (ε : ℝ) (hε : 0<ε) :
    ∃ R : ℕ, ∀ v, (G.law p).real (G.upperEscapeEvent v R)<ε := by
  obtain ⟨S,hS,hcover⟩ := hq
  have he (s : V) : ∀ᶠ R in atTop, (G.law p).real (G.upperEscapeEvent s R)<ε :=
    (G.tendsto_upperEscape_zero hc p s (hm s)).eventually (gt_mem_nhds hε)
  have hh := hS.toFinset.eventually_all.mpr (fun s _ => he s)
  obtain ⟨R,hR⟩ := hh.exists
  refine ⟨R,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.upperEscapeEvent_real]
  exact hR s (hS.mem_toFinset.mpr hs)

lemma stabilizerWeight_ge_one_either (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : 1≤G.stabilizerWeight x y ∨ 1≤G.stabilizerWeight y x := by
  by_cases hxy : 1≤G.stabilizerWeight x y
  · exact Or.inl hxy
  · apply Or.inr
    by_contra hyx
    have hprod := G.stabilizerWeight_change_base hc hl x y x
    rw [G.stabilizerWeight_self] at hprod
    have hh : (1 : ℝ≥0∞)<1 := calc
      1 = G.stabilizerWeight x y * G.stabilizerWeight y x := hprod
      _ ≤ G.stabilizerWeight x y * 1 := by
        gcongr
        exact le_of_not_ge hyx
      _ = G.stabilizerWeight x y := mul_one _
      _ < 1 := lt_of_not_ge hxy
    exact (lt_irrefl _) hh

lemma twoPoint_symm (p : unitInterval) (x y : V) :
    CriticalPercolation.Sharpness.twoPoint G p x y=
      CriticalPercolation.Sharpness.twoPoint G p y x := by
  unfold CriticalPercolation.Sharpness.twoPoint
  rw [CriticalPercolation.Sharpness.hit_singleton_eq,
    CriticalPercolation.Sharpness.hit_singleton_eq]
  congr 1
  ext ω
  exact SimpleGraph.reachable_comm

theorem uniform_twoPoint_decay_of_finite_mass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
      CriticalPercolation.Sharpness.twoPoint G p x y<ε := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  intro ε hε
  obtain ⟨R,hR⟩ := G.uniform_upperEscape_small hc hq p hm ε hε
  refine ⟨R,fun x y hxy => ?_⟩
  have h (x y : V) (hxy : y∉G.vertexBall x R) (hw : 1≤G.stabilizerWeight x y) :
      CriticalPercolation.Sharpness.twoPoint G p x y<ε := by
    apply lt_of_le_of_lt ?_ (hR x)
    unfold CriticalPercolation.Sharpness.twoPoint
    apply measureReal_mono (μ := G.law p) ?_ (measure_ne_top _ _)
    rw [CriticalPercolation.Sharpness.hit_singleton_eq]
    exact fun ω hω => ⟨y,⟨hω,hw⟩,hxy⟩
  rcases G.stabilizerWeight_ge_one_either hc hl x y with hw|hw
  · exact h x y hxy hw
  · rw [G.twoPoint_symm p x y]
    exact h y x (fun hx => hxy (G.vertexBall_comm.mpr hx)) hw

theorem nonunimodular_critical_twoPoint_decay
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) :
    ∀ ε : ℝ, 0<ε → ∃ R : ℕ, ∀ x y, y∉G.vertexBall x R →
      CriticalPercolation.Sharpness.twoPoint G G.criticalProbability x y<ε := by
  apply G.uniform_twoPoint_decay_of_finite_mass hc hl hq G.criticalProbability
  intro v
  exact (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu v).mono (fun ω h => (h v).ne)

end CriticalPercolation.BondGraph
end
end

end OAI
