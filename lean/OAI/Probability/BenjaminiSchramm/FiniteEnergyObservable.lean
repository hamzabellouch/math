import OAI.Probability.BenjaminiSchramm.FiniteEnergyModification
import OAI.Probability.BenjaminiSchramm.HalfspaceRootComparison

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct

variable {E : Type*} [Countable E]

lemma finite_forcing_measure_bound (p : unitInterval) (F : Finset E) (σ : Set E) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card) •
      (law p).map (forceOn (F : Set E) σ) ≤ law p := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply,Measure.map_apply (measurable_forceOn _ _) hB,smul_eq_mul]
  apply finite_energy_modification_bound p F _ B hB
  intro ω hω
  refine ⟨forceOn (F : Set E) σ ω,hω,?_⟩
  intro e he
  rw [mem_forceOn]
  simp only [Finset.mem_coe,he,ite_false]

lemma lintegral_finite_forcing_bound (p : unitInterval) (F : Finset E) (σ : Set E)
    (X : Set E → ℝ≥0∞) (hX : Measurable X) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, X (forceOn (F : Set E) σ ω) ∂law p) ≤ ∫⁻ ω, X ω ∂law p := by
  have hh := lintegral_mono' (finite_forcing_measure_bound p F σ) (le_refl X)
  rwa [lintegral_smul_measure,lintegral_map hX (measurable_forceOn _ _),smul_eq_mul] at hh

variable {V : Type*} [Countable V] (G : BondGraph V E)

omit [Countable E] [Countable V] in
lemma rooted_forced_layer_count_le (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    (ω : Set E) :
    restrictedLayerCount G I W ω y ≤
      restrictedLayerCount G J Z (forceOn (F : Set E) Set.univ ω) x := by
  let η := forceOn (F : Set E) Set.univ ω
  have hωη : ω ⊆ η := by
    intro e he
    rw [mem_forceOn]
    by_cases heF : e ∈ (F : Set E)
    · simp only [heF,ite_true,Set.mem_univ]
    · simpa only [heF,ite_false] using he
  have hFη : (F : Set E) ⊆ η := by
    intro e he
    rw [mem_forceOn,ite_eq_left he]
    exact Set.mem_univ e
  have hxy := hpath η hFη
  apply ENNReal.tsum_le_tsum
  intro z
  by_cases hz : z ∈ W ∧ Conn G (ω ∩ I) y z
  · have hconn := hxy.trans (conn_mono G (Set.inter_subset_inter hωη hIJ) hz.2)
    have ht : z ∈ Z ∧ Conn G (η ∩ J) x z := ⟨hWZ hz.1,hconn⟩
    rw [ite_eq_left hz,ite_eq_left ht]
  · rw [ite_eq_right hz]
    exact bot_le

theorem forced_path_fractional_layer_comparison
    (p : unitInterval) (F : Finset E) (I J : Set E) (W Z : Set V)
    (hIJ : I ⊆ J) (hWZ : W ⊆ Z) (x y : V)
    (hpath : ∀ η : Set E, (F : Set E) ⊆ η → Conn G (η ∩ J) x y)
    {q : ℝ} (hq : 0 ≤ q) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^F.card)*
      (∫⁻ ω, (restrictedLayerCount G I W ω y)^q ∂law p) ≤
        ∫⁻ ω, (restrictedLayerCount G J Z ω x)^q ∂law p := by
  apply (mul_le_mul' le_rfl (lintegral_mono (fun ω =>
    ENNReal.rpow_le_rpow (rooted_forced_layer_count_le G F I J W Z hIJ hWZ x y hpath ω) hq))).trans
  exact lintegral_finite_forcing_bound p F Set.univ _
    ((measurable_restrictedLayerCount G J Z x).pow_const q)

end Percolation.BenjaminiSchramm

end

end OAI
