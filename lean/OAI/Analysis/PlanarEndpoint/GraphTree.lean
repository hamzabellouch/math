import OAI.Analysis.PlanarEndpoint.DyadicGraph
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphEnergy
import OAI.Analysis.PlanarEndpoint.GraphLocalization
import OAI.Analysis.PlanarEndpoint.TimeSeparation
import OAI.Analysis.PlanarEndpoint.TimeTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators
namespace PlanarEndpoint

instance volume_ball_isFiniteMeasure (x₀ : Plane) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (Metric.ball x₀ r)) :=
  isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

lemma graph_node_energy_of_shortTime {c₀ C₀ p : ℝ} (hp : 2 < p) (hC₀ : 0 < C₀)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p)
    (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀)
    (B : ℝ) (hB : 0 ≤ B) (hχB : ∀ ξ, ‖χ ξ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ j k : ℕ, k ≤ j → ∀ s : List Bool, s.length=j+k →
      ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T)
        (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1),
      let μ := volume.restrict (Metric.ball x₀ 1)
      let χN := fun ξ : Plane => χ (((2:ℝ)^j)⁻¹ • ξ)
      let hχN := scaled_cutoff_memLp χ hχ.continuous hc (by positivity : 0 < (2:ℝ)^j)
      ‖(((2:ℝ)^j)^(-(1/3:ℝ))) • DyadicGraph.vector χN hχN μ T w hT hw hb s‖^2 ≤
        C*((((2:ℝ)^(-(1/6:ℝ)))^k)^2)*(DyadicGraph.massTree μ T hT).mass s ^(3/2-1/p) := by
  obtain ⟨C,hC,hh⟩ := graph_interpolated_bound_of_shortTime hp hC₀ hshort χ hχ hc hann B hB hχB
  refine ⟨C,hC,?_⟩
  intro j k hk s hs x₀ T w hT hw hb
  dsimp only
  let E := DyadicGraph.fiber T s ∩ Metric.ball x₀ 1
  have hE : MeasurableSet E := (DyadicGraph.fiber_measurable hT s).inter measurableSet_ball
  have hν : (volume.restrict (Metric.ball x₀ 1)).restrict (DyadicGraph.fiber T s) =
      volume.restrict E := Measure.restrict_restrict (DyadicGraph.fiber_measurable hT s)
  let : IsFiniteMeasure (volume.restrict E) := isFiniteMeasure_restrict.mpr
    ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hwidth : DyadicGraph.width s = (1/2:ℝ)^(j+k) := by rw [DyadicGraph.width, hs]
  have htime : ∀ x ∈ E, T x ∈ Icc (DyadicGraph.left s)
      (DyadicGraph.left s+DyadicGraph.width s) := fun x hx => ⟨hx.1.1,hx.1.2.le⟩
  have hbnd := hh j k hk x₀ (DyadicGraph.left s) (DyadicGraph.width s)
    (DyadicGraph.width_pos s).le hwidth.le E hE Set.inter_subset_right T w hT hw hb htime
  have hmass : (DyadicGraph.massTree (volume.restrict (Metric.ball x₀ 1)) T hT).mass s =
      volume.real E := measureReal_restrict_apply (DyadicGraph.fiber_measurable hT s)
  dsimp only [DyadicGraph.vector]
  rw [graphLp_congr_measure _ _ hν T w hT hw hb, hmass]
  exact hbnd

def normalizedDyadicVector (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (j : ℕ) (μ : Measure Plane) [IsFiniteMeasure μ]
    (T : Plane → ℝ) (w : Plane → ℂ) (hT : Measurable T) (hw : Measurable w)
    (hb : ∀ x, ‖w x‖ ≤ 1) (s : List Bool) : L2 :=
  (((2:ℝ)^j)^(-(1/3:ℝ))) • DyadicGraph.vector (fun ξ => χ (((2:ℝ)^j)⁻¹ • ξ))
    (scaled_cutoff_memLp χ hχ.continuous hc (pow_pos (by norm_num) j)) μ T w hT hw hb s

lemma graph_tree_levels_of_shortTime {c₀ C₀ p : ℝ} (hp : 2 < p) (hC₀ : 0 < C₀)
    (hshort : ShortTimeWeakEstimate c₀ C₀ p)
    (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀)
    (B : ℝ) (hB : 0 ≤ B) (hχB : ∀ ξ, ‖χ ξ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ)
      (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1),
      (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) →
      ∀ n : ℕ,
      let μ := volume.restrict (Metric.ball x₀ 1)
      (∑ j ∈ Finset.range n, ∑ s ∈ TimeTree.level j,
        ‖normalizedDyadicVector χ hχ hc j μ T w hT hw hb s‖^2) ≤ C := by
  obtain ⟨C,hC,hh⟩ := graph_node_energy_of_shortTime hp hC₀ hshort χ hχ hc hann B hB hχB
  let α : ℝ := 3/2-1/p
  let q : ℝ := (2:ℝ)^(-(1/6:ℝ))
  have hα : 1 < α := by
    have hdiv : 1/p < (1:ℝ)/2 := (div_lt_div_iff₀ (by linarith) (by norm_num)).2 (by linarith)
    dsimp only [α]
    linarith
  have hq : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  let A := C*(1-q)⁻¹*(Real.pi^α*(1-q)⁻¹*(1+q/((2:ℝ)^α-2)))
  have hA : 0 ≤ A := by
    have hd := TimeTree.MassTree.convexity_constant_pos hα
    exact mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr (by linarith)))
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg Real.pi_nonneg _) (inv_nonneg.mpr (by linarith)))
        (by positivity))
  refine ⟨A+1,by positivity,?_⟩
  intro x₀ T w hT hw hb ht n
  dsimp only
  let μ := volume.restrict (Metric.ball x₀ 1)
  let m := DyadicGraph.massTree μ T hT
  let G (j : ℕ) (s : List Bool) : L2 :=
    normalizedDyadicVector χ hχ hc j μ T w hT hw hb s
  have hsplit (j : ℕ) (s : List Bool) : G j s = G j (false::s)+G j (true::s) := by
    dsimp only [G, normalizedDyadicVector]
    rw [DyadicGraph.vector_split, smul_add]
  have hlight (s : List Bool) (k : ℕ) (hk : k < s.length) :
      ‖G s.length (m.light (m.heavyPath s k))‖^2 ≤
        C*(q^(k+1))^2*m.mass (m.light (m.heavyPath s k))^α := by
    apply hh s.length (k+1) (by omega) _ _ x₀ T w hT hw hb
    rw [m.light_length, m.heavyPath_length]
    omega
  have hterminal (s : List Bool) : ‖G s.length (m.heavyPath s s.length)‖^2 ≤
      C*(q^s.length)^2*m.mass (m.heavyPath s s.length)^α := by
    exact hh s.length s.length le_rfl _ (m.heavyPath_length s s.length) x₀ T w hT hw hb
  have hroot : m.mass [] = Real.pi := by
    rw [DyadicGraph.massTree_root μ T hT]
    · simp [μ, measureReal_def, EuclideanSpace.volume_ball_fin_two,
        ENNReal.toReal_ofReal Real.pi_nonneg]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact ht x hx
  have hbound := m.common_tree_energy_sum_le G hsplit hα hq hq1 hC.le hlight hterminal n
  rw [hroot] at hbound
  exact hbound.trans (by dsimp only [A]; linarith)

lemma norm_smul_sq_bound {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type*} (s : Finset ι) (v : V) (f : ι → V) {a D E : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hE : 0 ≤ E)
    (h : ‖v‖^2 ≤ D*(∑ i ∈ s, ‖f i‖^2)+E) :
    ‖a • v‖^2 ≤ D*(∑ i ∈ s, ‖a • f i‖^2)+E := by
  have ha2 : a^2 ≤ 1 := by nlinarith
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]
  simp_rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg a)
  have he := mul_le_mul_of_nonneg_right ha2 hE
  nlinarith

lemma graph_root_sum_of_shortTime {c₀ C₀ p : ℝ} (hc₀ : 0 < c₀) (hp : 2 < p)
    (hC₀ : 0 < C₀) (hshort : ShortTimeWeakEstimate c₀ C₀ p)
    (χ : Plane → ℂ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hann : ∀ ξ ∈ tsupport χ, c₀ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ C₀)
    (B : ℝ) (hB : 0 ≤ B) (hχB : ∀ ξ, ‖χ ξ‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Plane) (T : Plane → ℝ) (w : Plane → ℂ)
      (hT : Measurable T) (hw : Measurable w) (hb : ∀ x, ‖w x‖ ≤ 1),
      (∀ x ∈ Metric.ball x₀ 1, T x ∈ Ico 0 1) → ∀ n : ℕ,
      (∑ j ∈ Finset.range n, ‖normalizedDyadicVector χ hχ hc j
        (volume.restrict (Metric.ball x₀ 1)) T w hT hw hb []‖^2) ≤ C := by
  obtain ⟨A,hA,hlevels⟩ := graph_tree_levels_of_shortTime hp hC₀ hshort χ hχ hc hann B hB hχB
  obtain ⟨C,D,hC,hD,hsep⟩ := time_separation_uniform hc₀ hχ hc (fun ξ hξ => (hann ξ hξ).1)
  refine ⟨D*A+2*C*Real.pi^2+1, by positivity, ?_⟩
  intro x₀ T w hT hw hb ht n
  let μ := volume.restrict (Metric.ball x₀ 1)
  let G (j : ℕ) (s : List Bool) : L2 := normalizedDyadicVector χ hχ hc j μ T w hT hw hb s
  have hmass : (DyadicGraph.massTree μ T hT).mass [] = Real.pi := by
    rw [DyadicGraph.massTree_root μ T hT]
    · simp [μ, measureReal_def, EuclideanSpace.volume_ball_fin_two,
        ENNReal.toReal_ofReal Real.pi_nonneg]
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact ht x hx
  have hs (j : ℕ) : ‖G j []‖^2 ≤ D*(∑ s ∈ TimeTree.level j, ‖G j s‖^2) +
      C/((2:ℝ)^j)^2*Real.pi^2 := by
    have hh := hsep j μ T w hT hw hb x₀ (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      exact (by simpa only [Metric.mem_ball, dist_eq_norm] using hx : ‖x-x₀‖ < 1).le)
    rw [hmass] at hh
    exact norm_smul_sq_bound _ _ _ (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_le_one_of_one_le_of_nonpos (one_le_pow₀ (by norm_num)) (by norm_num))
      (by positivity) hh
  have heq (j : ℕ) : C/((2:ℝ)^j)^2*Real.pi^2 = C*Real.pi^2*(1/4:ℝ)^j := by
    rw [← pow_mul, mul_comm j 2, pow_mul, div_pow]
    norm_num
    ring
  have hgeom : ∑ j ∈ Finset.range n, (1/4:ℝ)^j ≤ 2 := by
    exact (Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (by norm_num) (by norm_num) j)).trans
      (sum_geometric_two_le n)
  have he : (∑ j ∈ Finset.range n, C/((2:ℝ)^j)^2*Real.pi^2) ≤ 2*C*Real.pi^2 := by
    simp_rw [heq]
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hgeom (mul_nonneg hC (sq_nonneg Real.pi))]
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) => hs j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hl := mul_le_mul_of_nonneg_left (hlevels x₀ T w hT hw hb ht n) hD
  exact hh.trans ((add_le_add hl he).trans (by linarith))

end PlanarEndpoint
end

end OAI
