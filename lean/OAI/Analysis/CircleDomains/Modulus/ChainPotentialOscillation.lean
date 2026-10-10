import OAI.Analysis.CircleDomains.Selection.FiniteChainPotential
import OAI.Analysis.CircleDomains.Uniformization.BandLimits

namespace OAI

/-! Real-valued oscillation and topological bands of the truncated chain
distance. The closure argument retains all cluster values. -/

open Set Filter
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*}

def realChainPotential (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) : ℝ :=
  (chainPotential R E x).toReal

theorem chainPotential_ne_top (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) :
    chainPotential R E x ≠ ∞ :=
  (lt_of_le_of_lt (chainPotential_le_one R E x) (by simp)).ne

theorem realChainPotential_mem_Icc (R : X → X → ℝ≥0∞ → Prop) (E : Set X) (x : X) :
    realChainPotential R E x ∈ Icc 0 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  change (chainPotential R E x).toReal ≤ 1
  simpa only [ENNReal.toReal_one] using
    ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) (chainPotential_le_one R E x)

theorem realChainPotential_difference (R : X → X → ℝ≥0∞ → Prop)
    (hR : ∀ x y a, R x y a → R y x a) {E : Set X} {x y : X} {a : ℝ≥0∞}
    (h : R x y a) : ENNReal.ofReal |realChainPotential R E y - realChainPotential R E x| ≤ 4 * a := by
  by_cases ha : a = ∞
  · simp [ha]
  have hcost : (4 : ℝ≥0∞) * a ≠ ∞ := ENNReal.mul_ne_top (by simp) ha
  obtain ⟨hyx, hxy⟩ := chainPotential_two_sided R hR (E := E) h
  have hyxr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨chainPotential_ne_top R E x, hcost⟩) hyx
  have hxyr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨chainPotential_ne_top R E y, hcost⟩) hxy
  rw [ENNReal.toReal_add (chainPotential_ne_top R E x) hcost] at hyxr
  rw [ENNReal.toReal_add (chainPotential_ne_top R E y) hcost] at hxyr
  apply (ENNReal.ofReal_le_iff_le_toReal hcost).mpr
  apply abs_le.mpr
  change -(4 * a).toReal ≤ (chainPotential R E y).toReal - (chainPotential R E x).toReal ∧
    (chainPotential R E y).toReal - (chainPotential R E x).toReal ≤ (4 * a).toReal
  constructor <;> linarith

variable [TopologicalSpace X] [FirstCountableTopology X]

theorem clusterGraph_oscillation_of_neighborhood {G V : Set X} {f : X → ℝ}
    {s : X} {a b : ℝ} {c : ℝ≥0∞} (hV : V ∈ 𝓝 s)
    (hbound : ∀ x ∈ G ∩ V, ∀ y ∈ G ∩ V, ENNReal.ofReal |f x - f y| ≤ c)
    (ha : (s, a) ∈ clusterGraph G f) (hb : (s, b) ∈ clusterGraph G f) :
    ENNReal.ofReal |a - b| ≤ c := by
  obtain ⟨v, hfv, hv⟩ := (mem_clusterGraph_iff_mapClusterPt.mp ha).exists_seq_tendsto
  obtain ⟨w, hfw, hw⟩ := (mem_clusterGraph_iff_mapClusterPt.mp hb).exists_seq_tendsto
  have hvg := (tendsto_nhdsWithin_iff.mp hv).2
  have hwg := (tendsto_nhdsWithin_iff.mp hw).2
  have hvv := (tendsto_nhdsWithin_iff.mp hv).1.eventually hV
  have hwv := (tendsto_nhdsWithin_iff.mp hw).1.eventually hV
  apply le_of_tendsto (ENNReal.tendsto_ofReal ((hfv.sub hfw).abs))
  filter_upwards [hvg, hwg, hvv, hwv] with n hvg hwg hvv hwv
  exact hbound (v n) ⟨hvg, hvv⟩ (w n) ⟨hwg, hwv⟩

theorem clusterGraph_oscillation_of_jumps (R : X → X → ℝ≥0∞ → Prop)
    (hR : ∀ x y a, R x y a → R y x a) (E G : Set X)
    {s : X} {V : ℕ → Set X} (hV : ∀ j, V j ∈ 𝓝 s) (c : ℕ → ℝ≥0∞)
    (hj : ∀ j, ∀ x ∈ G ∩ V j, ∀ y ∈ G ∩ V j, R x y (c j))
    {a b : ℝ} (ha : (s, a) ∈ clusterGraph G (realChainPotential R E))
    (hb : (s, b) ∈ clusterGraph G (realChainPotential R E)) :
    ENNReal.ofReal |a - b| ≤ 4 * limsup c atTop := by
  have hc (j : ℕ) : ENNReal.ofReal |a - b| ≤ 4 * c j :=
    clusterGraph_oscillation_of_neighborhood (hV j)
      (fun x hx y hy => realChainPotential_difference R hR (hj j y hy x hx)) ha hb
  have hl : ENNReal.ofReal |a - b| ≤ limsup (fun j => (4 : ℝ≥0∞) * c j) atTop := by
    apply le_limsup_of_le (h := ?_)
    intro t ht
    obtain ⟨j, hj⟩ := ht.exists
    exact (hc j).trans hj
  have hm := ENNReal.limsup_mul_le' (f := atTop)
    (u := fun _ : ℕ => (4 : ℝ≥0∞)) (v := c)
    (Or.inl (by simp)) (Or.inl (by simp))
  simp only [limsup_const] at hm
  exact hl.trans hm

end CircleDomainRigidity

end

end OAI
