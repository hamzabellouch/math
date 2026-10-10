import OAI.Analysis.LienardCycles.RadiusLimits

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs CanonicalVariation PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates ArchSymmetries

lemma base_bounds {z k r : ℝ} (hr : 0 < r) : -r^2/2 ≤ base ((z,k),r) ∧ base ((z,k),r) < 0 := by
  have hs := base_spec profile profile_contDiff model_local_flow (p := (z,k)) (t := 0) hr
  have hh := height_bound profile profile_contDiff model_local_flow (p := (z,k)) hs.1
  rw [hs.2] at hh
  exact ⟨by dsimp [base]; linarith,hs.1⟩

lemma base_tendsto_zero (z k : ℝ) : Tendsto (fun r => base ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun r : ℝ => -r^2/2) (h := fun _ : ℝ => (0:ℝ))
  · simpa using! (((tendsto_id.mono_left inf_le_left).pow 2).neg.div_const (2:ℝ) :
      Tendsto (fun r : ℝ => -r^2/2) (𝓝[>] (0:ℝ)) (𝓝 (-0^2/2)))
  · exact tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (base_bounds (z := z) (k := k) hr).1
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (base_bounds (z := z) (k := k) hr).2.le

lemma model_tendsto (z k : ℝ) :
    Tendsto (fun r => ((J ((z,k),r),k),r)) (𝓝[>] (0:ℝ)) (𝓝 ((z,k),(0:ℝ))) := by
  have hj : Tendsto (fun r => J ((z,k),r)) (𝓝[>] (0:ℝ)) (𝓝 z) := by
    simpa [J] using (tendsto_const_nhds.add (tendsto_const_nhds.mul (base_tendsto_zero z k)))
  exact (hj.prodMk_nhds tendsto_const_nhds).prodMk_nhds (tendsto_id.mono_left inf_le_left)

lemma U_B_positive_near_zero (z k : ℝ) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < U ((z,k),r) ∧ 0 < B ((z,k),r) := by
  filter_upwards [(model_tendsto z k).eventually (R_G_positive_near_zero z k),
    self_mem_nhdsWithin] with r hh hr
  obtain ⟨hR,hG⟩ := hh hr
  constructor
  · dsimp only [U]
    rw [Dz_formula hr]
    exact div_pos (mul_pos hR (Jz_pos hr)) (D_gap_pos hr)
  · rw [B_formula hr]
    exact div_pos hG (mul_pos (QuadraticVariation.P_pos hr) (D_gap_pos hr))

lemma K_pos {q : (ℝ × ℝ) × ℝ} (hr : 0 < q.2) : 0 < K q := by
  dsimp [K]
  exact div_pos (mul_pos (by norm_num) (by positivity))
    (mul_pos hr (sq_pos_of_pos (A_gap_pos hr)))

lemma U_pos {z k r : ℝ} (hr : 0 < r) : 0 < U ((z,k),r) := by
  have hm : MonotoneOn (fun s => U ((z,k),s)) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (U_deriv hs).continuousAt.continuousWithinAt)
      (fun s hs => (U_deriv (interior_subset (s := Ioi 0) hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : 0 < s := interior_subset hs
    rw [(U_deriv (z := z) (k := k) hs').deriv]
    exact (mul_pos (K_pos hs') (Az_pos hs')).le
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧ 0 < U ((z,k),s) := by
    filter_upwards [U_B_positive_near_zero z k,self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hpos hlt
    exact ⟨hpos,hlt,hs.1⟩
  obtain ⟨s,hs,hlt,hU⟩ := he.exists
  exact hU.trans_le (hm hs hr hlt.le)

lemma B_pos {z k r : ℝ} (hr : 0 < r) : 0 < B ((z,k),r) := by
  have hm : MonotoneOn (fun s => B ((z,k),s)) (Ioi 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
      (fun s hs => (B_deriv hs).continuousAt.continuousWithinAt)
      (fun s hs => (B_deriv (interior_subset (s := Ioi 0) hs)).differentiableAt.differentiableWithinAt)
    intro s hs
    have hs' : 0 < s := interior_subset hs
    rw [(B_deriv (z := z) (k := k) hs').deriv]
    exact (mul_pos (div_pos (mul_pos (mul_pos (A_gap_pos hs')
      (QuadraticVariation.Q_pos hs')) (Jz_pos hs'))
      (mul_pos hs' (sq_pos_of_pos (Az_pos hs')))) (U_pos hs')).le
  have he : ∀ᶠ s in 𝓝[>] (0:ℝ), 0 < s ∧ s < r ∧ 0 < B ((z,k),s) := by
    filter_upwards [U_B_positive_near_zero z k,self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono inf_le_left] with s hs hpos hlt
    exact ⟨hpos,hlt,hs.2⟩
  obtain ⟨s,hs,hlt,hB⟩ := he.exists
  exact hB.trans_le (hm hs hr hlt.le)

lemma J_surjective (d k : ℝ) {r : ℝ} (hr : 0 < r) : ∃ z : ℝ, J ((z,k),r)=d := by
  let t := peakAtWidth profile (((d,k),0),r)
  have hs := peak_spec profile profile_contDiff model_local_flow (p := (d,k)) (h := 0) hr
  have he : baseAtWidth profile (((d,k),t),r)=0 :=
    base_eq profile profile_contDiff model_local_flow hr hs.1 hs.2
  have ht := base_translation d k t hr
  refine ⟨d+k*t,?_⟩
  dsimp [J,base]
  rw [he] at ht
  linear_combination -k*ht

end QuinticLienard.ReferenceCharacteristic

end OAI
