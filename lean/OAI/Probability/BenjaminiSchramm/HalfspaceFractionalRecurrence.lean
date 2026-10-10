import OAI.Probability.BenjaminiSchramm.SlabFractionalRecurrence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma lower_halfspace_frontier_location (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (x : V) (hx : f x ≤ b)
    {z : V} (hz : z ∈ openFrontier G (ω ∩ J)
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x)) :
    b < f z ∧ f z ≤ b+R := by
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have hub := conn_internalEdges_end_mem G ω {v | f v ≤ b} hx hu
  change f u ≤ b at hub
  have hzb : ¬f z ≤ b := openFrontier_lowerCluster_outside G ω
    {v | f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨lt_of_not_ge hzb,by linarith⟩

variable [Countable V] [Countable E]

theorem lower_halfspace_newLayer_fractional_bound
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G (internalEdges G {v | f v ≤ b}) J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c*(∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  let I := internalEdges G {v | f v ≤ b}
  let B := {u | b-R ≤ f u ∧ f u ≤ b}
  have hfront : (∫⁻ ω, frontierCount G I J ω x^c
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c*∫⁻ ω, restrictedLayerCount G I B ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q := by
    calc
      _ ≤ ∫⁻ ω, ((d : ℝ≥0∞)*restrictedLayerCount G I B ω x)^c
          ∂CriticalPercolation.BernoulliProduct.law q := by
        apply lintegral_mono_ae
        filter_upwards [hfin] with ω hω
        exact ENNReal.rpow_le_rpow
          (lower_halfspace_frontierCount_le_top_band G hloc d hd f R b hjump ω J x hx hω) hc.le
      _ = _ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hc.le]
        exact lintegral_const_mul _ ((measurable_restrictedLayerCount G I B x).pow_const c)
  have hnew := newLayerCount_fractional_bound_on_frontier G hloc q I J x hfin A
    ha ha1 hc hc1 L {z | b < f z ∧ f z ≤ b+R}
    (fun ω z hz => lower_halfspace_frontier_location G f R b hjump ω J x hx hz)
    (fun z hz => hL z hz.1 hz.2)
  exact hnew.trans (mul_le_mul' hfront le_rfl)

theorem lower_halfspace_fractional_recurrence
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (x : V) (hx : f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, restrictedLayerCount G J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, restrictedLayerCount G (internalEdges G {v | f v ≤ b}) A ω x^(a*c)
        ∂CriticalPercolation.BernoulliProduct.law q)+
      (d : ℝ≥0∞)^c*(∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  have hac : a*c ≤ 1 := by
    calc a*c ≤ a*1 := mul_le_mul_of_nonneg_left hc1 ha.le
         _ ≤ 1 := by simpa only [mul_one] using ha1
  exact (restrictedLayerCount_fractional_increment G q _ J A x (mul_pos ha hc) hac).trans
    (add_le_add le_rfl (lower_halfspace_newLayer_fractional_bound G hloc d hd q f R b
      hjump J x hx hfin A ha ha1 hc hc1 L hL))

end Percolation.BenjaminiSchramm

end

end OAI
