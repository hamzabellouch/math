import Mathlib
import OAI.Probability.CriticalPercolation.Modular.NormalizedDiscrepancy
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneBernoulli
import OAI.Probability.CriticalPercolation.Modular.HeavyThinning
import OAI.Probability.CriticalPercolation.Modular.HeavyDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) : ℝ :=
  G.weightedDiscrepancy p ω x / (G.modularMass x (G.cluster ω x)).toReal

lemma normalizedSignedDiscrepancy_heavy (p : ℝ) (ω : Set E) (x : V)
    (h : G.modularMass x (G.cluster ω x)=∞) : G.normalizedSignedDiscrepancy p ω x=0 := by
  simp [normalizedSignedDiscrepancy,h]

lemma enorm_normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖ₑ=G.normalizedAbsoluteDiscrepancy p ω x := by
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [G.normalizedSignedDiscrepancy_heavy p ω x hm,normalizedAbsoluteDiscrepancy,hm]
  · have hpos : 0<(G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm
    rw [Real.enorm_eq_ofReal_abs,normalizedSignedDiscrepancy,abs_div,abs_of_pos hpos,
      ENNReal.ofReal_div_of_pos hpos,ENNReal.ofReal_toReal hm]
    rfl

lemma measurable_normalizedSignedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedSignedDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).div (G.measurable_modularClusterMass x x).ennreal_toReal

lemma norm_normalizedSignedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖≤(D*(2*K) : ℕ) := by
  have h := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
  rw [←G.enorm_normalizedSignedDiscrepancy,←ENNReal.ofReal_natCast,Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

lemma eventually_incident_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (x : V) (e : E) :
    ∀ᶠ n in atTop, (e∈G.incidentEdges (G.cluster (a n) x))=(e∈G.incidentEdges (G.cluster ω x)) := by
  by_cases h : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := h
    filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hv] with n hn
    exact propext ⟨fun _ => ⟨v,hv,hve⟩,fun _ => ⟨v,hn,hve⟩⟩
  · apply Eventually.of_forall
    intro n
    apply propext
    constructor
    · rintro ⟨v,hv,hve⟩
      exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
    · exact fun hn => False.elim (h hn)

lemma eventually_mem_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (e : E) :
    ∀ᶠ n in atTop, (e∈a n)=(e∈ω) := by
  by_cases h : e∈ω
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ h)
    exact eventually_atTop.mpr ⟨n,fun m hm => propext ⟨fun _ => h,fun _ => ha hm hn⟩⟩
  · apply Eventually.of_forall
    intro n
    exact propext ⟨fun hn => hu ▸ Set.mem_iUnion.mpr ⟨n,hn⟩, fun hn => False.elim (h hn)⟩

lemma tendsto_weightedDiscrepancy_of_exhaustion (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.weightedDiscrepancy (q n) (a n) x) atTop (𝓝 (G.weightedDiscrepancy p ω x)) := by
  have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hq
  apply tendsto_tsum_of_dominated_convergence (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    have heq : ∀ᶠ n in atTop, G.weightedIncidenceTerm (q n) (a n) x e=G.weightedIncidenceTerm (q n) ω x e := by
      filter_upwards [G.eventually_incident_of_exhaustion a ω ha hu x e,
        eventually_mem_of_exhaustion a ω ha hu e] with n hn hn'
      simp only [weightedIncidenceTerm,centeredCoefficient,hn,hn']
    have heq' : (fun n => G.weightedIncidenceTerm (q n) (a n) x e) =ᶠ[atTop]
        (fun n => G.weightedIncidenceTerm (q n) ω x e) := heq
    apply Tendsto.congr' heq'.symm
    by_cases hi : e∈G.incidentEdges (G.cluster ω x)
    · by_cases ho : e∈ω
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_left ho]
        exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hq')
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_right ho]
        exact tendsto_const_nhds.mul hq'.neg
    · simp only [weightedIncidenceTerm,ite_eq_right hi]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n e
    apply (G.norm_weightedIncidenceTerm_le (q n) (q n).property (a n) x e).trans
    by_cases hi : e∈G.incidentEdges (G.cluster (a n) x)
    · have hf : e∈G.incidentEdges (G.cluster ω x) := by
        obtain ⟨v,hv,hve⟩ := hi
        exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
      simp only [ite_eq_left hi,ite_eq_left hf,le_refl]
    · simp only [ite_eq_right hi,ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_modularMass_toReal_of_exhaustion
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => (G.modularMass x (G.cluster (a n) x)).toReal) atTop
      (𝓝 (G.modularMass x (G.cluster ω x)).toReal) := by
  have hterm (S : Set V) (y : V) : (if y∈S then G.stabilizerWeight x y else 0)≠∞ := by
    split_ifs
    · exact G.stabilizerWeight_ne_top x y
    · exact ENNReal.zero_ne_top
  simp only [modularMass,ENNReal.tsum_toReal_eq (hterm _)]
  apply tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hm)
  · intro y
    by_cases hy : y∈G.cluster ω x
    · apply tendsto_const_nhds.congr'
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      simp only [ite_eq_left hy,ite_eq_left hn]
    · have hn (n : ℕ) : y∉G.cluster (a n) x := fun h => hy (G.cluster_mono (hu ▸ Set.subset_iUnion a n) x h)
      simp only [ite_eq_right hy,ite_eq_right (hn _)]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n y
    by_cases hn : y∈G.cluster (a n) x
    · have hy : y∈G.cluster ω x := G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hn
      simp only [ite_eq_left hn,ite_eq_left hy,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,le_refl]
    · simp only [ite_eq_right hn,ENNReal.toReal_zero,norm_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_normalizedSignedDiscrepancy_finiteMass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.normalizedSignedDiscrepancy (q n) (a n) x) atTop
      (𝓝 (G.normalizedSignedDiscrepancy p ω x)) := by
  exact (G.tendsto_weightedDiscrepancy_of_exhaustion hc hl D K hD hK a ω ha hu p q hq x hm).div
    (G.tendsto_modularMass_toReal_of_exhaustion a ω ha hu x hm)
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).ne'

lemma integrable_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (x : V) :
    Integrable (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x) markLaw := by
  apply Integrable.of_bound
    (((G.measurable_normalizedSignedDiscrepancy p x).comp (measurable_atParameter p)).aestronglyMeasurable)
    (D*(2*K) : ℕ)
  exact Eventually.of_forall (fun u => G.norm_normalizedSignedDiscrepancy_le hc hl D K hD hK p _ x)

theorem tendsto_L1_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, ‖G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x -
      G.normalizedSignedDiscrepancy p (atParameter p u) x‖ₑ ∂markLaw) atTop (𝓝 0) := by
  let f := fun (r : unitInterval) u => G.normalizedSignedDiscrepancy r (atParameter r u) x
  have hfm (r : unitInterval) : Measurable (f r) :=
    (G.measurable_normalizedSignedDiscrepancy r x).comp (measurable_atParameter r)
  let a := fun n u => if G.heavyFlag p u x then
    G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0
  let b := fun n u => if G.heavyFlag p u x then 0 else ‖f (q n) u-f p u‖ₑ
  have hbm (n : ℕ) : Measurable (b n) :=
    measurable_const.ite (G.measurable_heavyFlag p x).setOf ((hfm _).sub (hfm _)).enorm
  have hb : Tendsto (fun n => ∫⁻ u, b n u ∂markLaw) atTop (𝓝 0) := by
    have hbound (n : ℕ) : ∀ᵐ u ∂markLaw, b n u≤((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞) := by
      apply Eventually.of_forall
      intro u
      dsimp only [b]
      split_ifs
      · exact zero_le
      · apply enorm_sub_le.trans
        simpa only [f,G.enorm_normalizedSignedDiscrepancy] using
          add_le_add (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ (q n).property _ x)
            (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ p.property _ x)
    have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n => b n u) atTop (𝓝 (0:ℝ≥0∞)) := by
      apply Eventually.of_forall
      intro u
      by_cases hh : G.heavyFlag p u x
      · simp only [b,ite_eq_left hh]
        exact tendsto_const_nhds
      · simp only [b,ite_eq_right hh]
        have ht := G.tendsto_normalizedSignedDiscrepancy_finiteMass hc hl D K hD hK
          (fun n => atParameter (q n) u) (atParameter p u) ((atParameter_mono u).comp hmono)
          (atParameter_iUnion p q hqp hlim u) p q hlim x hh
        simpa only [f,sub_self,enorm_zero] using (ht.sub_const (f p u)).enorm
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence
      (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => ((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞)) hbm hbound (by
        simpa only [lintegral_const,measure_univ,mul_one] using
          (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,ENNReal.natCast_ne_top _⟩)) ht
  have ha := G.tendsto_expected_heavy_normalizedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  have heq (n : ℕ) (u : E → ℝ) : ‖f (q n) u-f p u‖ₑ=a n u+b n u := by
    by_cases hh : G.heavyFlag p u x
    · simp only [a,b,ite_eq_left hh,add_zero,f,G.normalizedSignedDiscrepancy_heavy p _ x hh,
        sub_zero,G.enorm_normalizedSignedDiscrepancy]
    · simp only [a,b,ite_eq_right hh,zero_add]
  change Tendsto (fun n => ∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) atTop (𝓝 0)
  have hi (n : ℕ) : (∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) =
      (∫⁻ u, a n u ∂markLaw)+(∫⁻ u, b n u ∂markLaw) := by
    simp_rw [heq]
    exact lintegral_add_right _ (hbm n)
  simp_rw [hi]
  simpa only [add_zero] using ha.add hb

 theorem tendsto_expected_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫ u, G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x ∂markLaw)
      atTop (𝓝 (∫ u, G.normalizedSignedDiscrepancy p (atParameter p u) x ∂markLaw)) := by
  apply tendsto_integral_of_L1 (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x)
  · exact (G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK p x).aestronglyMeasurable
  · exact Eventually.of_forall (fun n => G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK (q n) x)
  · exact G.tendsto_L1_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx

end CriticalPercolation.BondGraph
end
end

end OAI
