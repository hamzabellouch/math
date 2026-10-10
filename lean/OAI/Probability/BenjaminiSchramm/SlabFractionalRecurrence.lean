import OAI.Probability.BenjaminiSchramm.LayerFrontierLocalization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma restrictedLayerCount_le_old_add_new (I J : Set E) (A : Set V)
    (ω : Set E) (x : V) :
    restrictedLayerCount G J A ω x ≤
      restrictedLayerCount G I A ω x + newLayerCount G I J A ω x := by
  unfold restrictedLayerCount newLayerCount
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : y ∈ A ∧ Conn G (ω ∩ J) x y
  · rw [ite_eq_left hy]
    by_cases hi : Conn G (ω ∩ I) x y
    · simp [hy.1,hy.2,hi]
    · simp [hy.1,hy.2,hi]
  · rw [ite_eq_right hy]
    exact bot_le

theorem lower_slab_frontier_location
    (f : V → ℝ) (R m b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (hJ : J ⊆ internalEdges G {v | m ≤ f v})
    (x : V) (hx : m ≤ f x ∧ f x ≤ b)
    {z : V} (hz : z ∈ openFrontier G (ω ∩ J)
      (cluster G (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x)) :
    b < f z ∧ f z ≤ b+R ∧ ∃ u ∈ cluster G
      (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x,
      b-R ≤ f u ∧ f u ≤ b ∧ ∃ e ∈ ω ∩ J, G e = s(u,z) := by
  obtain ⟨hz,u,hu,e,he,heq⟩ := hz
  have huD := conn_internalEdges_end_mem G ω _ hx hu
  have hzD := openFrontier_lowerCluster_outside G ω
    {v | m ≤ f v ∧ f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hzlo : m ≤ f z := hJ he.2 z (by rw [heq]; simp)
  have hzb : b < f z := lt_of_not_ge (fun hh => hzD ⟨hzlo,hh⟩)
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨hzb,by linarith [huD.2],u,hu,by linarith,huD.2,e,he,heq⟩

theorem lower_slab_frontier_incident_top_band
    (f : V → ℝ) (R m b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (ω : Set E) (J : Set E) (hJ : J ⊆ internalEdges G {v | m ≤ f v})
    (x : V) (hx : m ≤ f x ∧ f x ≤ b)
    {u z : V} (hu : u ∈ cluster G
      (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x)
    (hz : z ∉ cluster G (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x)
    {e : E} (he : e ∈ ω ∩ J) (heq : G e = s(u,z)) :
    b-R ≤ f u ∧ f u ≤ b := by
  have huD := conn_internalEdges_end_mem G ω _ hx hu
  have hzD := openFrontier_lowerCluster_outside G ω
    {v | m ≤ f v ∧ f v ≤ b} x hx ⟨hz,u,hu,e,he.1,heq⟩
  have hzlo : m ≤ f z := hJ he.2 z (by rw [heq]; simp)
  have hzb : b < f z := lt_of_not_ge (fun hh => hzD ⟨hzlo,hh⟩)
  have hj := (abs_le.mp (hjump e u z (by rw [heq]; simp) (by rw [heq]; simp))).2
  exact ⟨by linarith,huD.2⟩

variable [Countable V] [Countable E]

theorem restrictedLayerCount_fractional_increment
    (q : E → unitInterval) (I J : Set E) (A : Set V) (x : V)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (∫⁻ ω, restrictedLayerCount G J A ω x^s
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, restrictedLayerCount G I A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q) +
      (∫⁻ ω, newLayerCount G I J A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q) := by
  calc
    _ ≤ ∫⁻ ω, restrictedLayerCount G I A ω x^s + newLayerCount G I J A ω x^s
        ∂CriticalPercolation.BernoulliProduct.law q := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.rpow_le_rpow (restrictedLayerCount_le_old_add_new G I J A ω x) hs.le).trans
        (ENNReal.rpow_add_le_add_rpow _ _ hs.le hs1)
    _ = _ := lintegral_add_left ((measurable_restrictedLayerCount G I A x).pow_const s) _

theorem lower_slab_newLayer_fractional_bound
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R m b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (hJ : J ⊆ internalEdges G {v | m ≤ f v})
    (x : V) (hx : m ≤ f x ∧ f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, newLayerCount G (internalEdges G {v | m ≤ f v ∧ f v ≤ b}) J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c * (∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | m ≤ f v ∧ f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  let I := internalEdges G {v | m ≤ f v ∧ f v ≤ b}
  let B := {u | b-R ≤ f u ∧ f u ≤ b}
  have hfront : (∫⁻ ω, frontierCount G I J ω x^c
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (d : ℝ≥0∞)^c * ∫⁻ ω, restrictedLayerCount G I B ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q := by
    calc
      _ ≤ ∫⁻ ω, ((d : ℝ≥0∞)*restrictedLayerCount G I B ω x)^c
          ∂CriticalPercolation.BernoulliProduct.law q := by
        apply lintegral_mono_ae
        filter_upwards [hfin] with ω hω
        apply ENNReal.rpow_le_rpow _ hc.le
        exact frontierCount_le_boundary_layer G hloc d hd I J ω x B hω
          (fun _ hu _ hz _ he heq =>
            lower_slab_frontier_incident_top_band G f R m b hjump ω J hJ x hx hu hz he heq)
      _ = _ := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hc.le]
        exact lintegral_const_mul _ ((measurable_restrictedLayerCount G I B x).pow_const c)
  have hnew := newLayerCount_fractional_bound_on_frontier G hloc q I J x hfin A
    ha ha1 hc hc1 L {z | b < f z ∧ f z ≤ b+R}
    (fun ω z hz => (lower_slab_frontier_location G f R m b hjump ω J hJ x hx hz).imp_right
      (fun hh => hh.1))
    (fun z hz => hL z hz.1 hz.2)
  exact hnew.trans (mul_le_mul' hfront le_rfl)

theorem lower_slab_fractional_recurrence
    (hloc : LocallyFinite G) (d : ℕ)
    (hd : ∀ u, (finite_neighbors hloc u).toFinset.card ≤ d)
    (q : E → unitInterval) (f : V → ℝ) (R m b : ℝ)
    (hjump : ∀ e u v, u ∈ G e → v ∈ G e → |f v-f u| ≤ R)
    (J : Set E) (hJ : J ⊆ internalEdges G {v | m ≤ f v})
    (x : V) (hx : m ≤ f x ∧ f x ≤ b)
    (hfin : ∀ᵐ ω ∂CriticalPercolation.BernoulliProduct.law q,
      (cluster G (ω ∩ internalEdges G {v | m ≤ f v ∧ f v ≤ b}) x).Finite)
    (A : Set V) {a c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (L : ℝ≥0∞)
    (hL : ∀ z, b < f z → f z ≤ b+R →
      (∫⁻ ω, restrictedLayerCount G J A ω z^a
        ∂CriticalPercolation.BernoulliProduct.law q) ≤ L) :
    (∫⁻ ω, restrictedLayerCount G J A ω x^(a*c)
      ∂CriticalPercolation.BernoulliProduct.law q) ≤
      (∫⁻ ω, restrictedLayerCount G (internalEdges G {v | m ≤ f v ∧ f v ≤ b}) A ω x^(a*c)
        ∂CriticalPercolation.BernoulliProduct.law q) +
      (d : ℝ≥0∞)^c * (∫⁻ ω,
        restrictedLayerCount G (internalEdges G {v | m ≤ f v ∧ f v ≤ b})
          {u | b-R ≤ f u ∧ f u ≤ b} ω x^c
        ∂CriticalPercolation.BernoulliProduct.law q)*L^c := by
  have hac : a*c ≤ 1 := by
    calc a*c ≤ a*1 := mul_le_mul_of_nonneg_left hc1 ha.le
         _ ≤ 1 := by simpa only [mul_one] using ha1
  exact (restrictedLayerCount_fractional_increment G q _ J A x (mul_pos ha hc) hac).trans
    (add_le_add le_rfl (lower_slab_newLayer_fractional_bound G hloc d hd q f R m b
      hjump J hJ x hx hfin A ha ha1 hc hc1 L hL))

end Percolation.BenjaminiSchramm

end

end OAI
