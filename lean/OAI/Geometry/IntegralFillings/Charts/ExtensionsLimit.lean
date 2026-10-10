import Mathlib
import OAI.Geometry.IntegralFillings.Model

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal

namespace SharpIntegralFillings
variable {E : Type*} [PseudoMetricSpace E]
lemma lipschitzOn_limit {s : Set E} {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    LipschitzOnWith K f s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact le_of_tendsto ((hl x hx).dist (hl y hy))
    (Eventually.of_forall fun j => (hs j).dist_le_mul x hx y hy)

lemma uniform_limit_on_totallyBounded {s : Set E} (hs : TotallyBounded s)
    {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hfs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn fs f atTop s := by
  have hf := lipschitzOn_limit hfs hl
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let δ := ε / (4 * ((K : ℝ)+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : 4 * ((K : ℝ)+1) * δ = ε := by dsimp [δ]; field_simp
  obtain ⟨t, hts, ht, hcov⟩ := finite_approx_of_totallyBounded hs δ hδ
  have hpt : ∀ᶠ j in atTop, ∀ y ∈ t, dist (f y) (fs j y) < ε / 2 := by
    apply (ht.eventually_all.mpr)
    intro y hy
    have hh := (Metric.tendsto_atTop.mp (hl y (hts hy))) (ε/2) (half_pos hε)
    exact (eventually_atTop.mpr hh).mono fun j hj => by simpa only [dist_comm] using hj
  filter_upwards [hpt] with j hj x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hcov hx)
  have hd : dist x y < δ := hxy
  have H := dist_triangle4 (f x) (f y) (fs j y) (fs j x)
  have H₁ := hf.dist_le_mul x hx y (hts hyt)
  have H₂ := (hfs j).dist_le_mul y (hts hyt) x hx
  rw [dist_comm y x] at H₂
  have H₃ := hj y hyt
  have H₄ : (K : ℝ) * dist x y ≤ (K : ℝ) * δ :=
    mul_le_mul_of_nonneg_left hd.le K.coe_nonneg
  nlinarith [K.coe_nonneg]

noncomputable def mcShane (s : Set E) (K : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  ⨅ z : s, f z + K * dist x z

lemma mcShane_bddBelow {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) (x : E) :
    BddBelow (range fun z : s => f z + K * dist x z) := by
  obtain ⟨z,hz⟩ := hs
  refine ⟨f z - K * dist x z, ?_⟩
  rintro w ⟨t,rfl⟩
  dsimp
  rw [_root_.sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist x t)]
  calc
    f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
    _ ≤ f t + K * (dist x z + dist x t) := by gcongr; apply dist_triangle_left

lemma mcShane_eqOn {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) : EqOn f (mcShane s K f) s := by
  let : Nonempty s := hs.to_subtype
  intro x hx
  refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
  simpa only [mcShane, add_zero, Subtype.coe_mk, mul_zero, dist_self] using
    ciInf_le (mcShane_bddBelow hs hf x) ⟨x,hx⟩

lemma mcShane_lipschitz {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzOnWith K f s) : LipschitzWith K (mcShane s K f) := by
  let : Nonempty s := hs.to_subtype
  apply LipschitzWith.of_le_add_mul
  intro x y
  rw [← _root_.sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [_root_.sub_le_iff_le_add]
  calc
    mcShane s K f x ≤ f z + K * dist x z := ciInf_le (mcShane_bddBelow hs hf x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle

lemma mcShane_dist_le {s : Set E} (hs : s.Nonempty) {K : ℝ≥0} {f g : E → ℝ}
    (hf : LipschitzOnWith K f s) (hg : LipschitzOnWith K g s)
    {ε : ℝ} (hε : ∀ x ∈ s, dist (f x) (g x) ≤ ε) (x : E) :
    dist (mcShane s K f x) (mcShane s K g x) ≤ ε := by
  let : Nonempty s := hs.to_subtype
  have aux {f g : E → ℝ} (hf : LipschitzOnWith K f s)
      (h : ∀ z ∈ s, f z ≤ g z + ε) :
      mcShane s K f x - ε ≤ mcShane s K g x := by
    apply le_ciInf
    intro z
    have H := ciInf_le (mcShane_bddBelow hs hf x) z
    change mcShane s K f x ≤ f z + K * dist x z at H
    linarith [h z z.2]
  rw [Real.dist_eq, abs_le]
  have H₁ := aux (g := g) hf (fun z hz => by have H := (abs_le.mp (hε z hz)).2; linarith)
  have H₂ := aux (g := f) hg (fun z hz => by have H := (abs_le.mp (hε z hz)).1; linarith)
  constructor <;> linarith

lemma exists_convergent_lipschitz_extensions {s : Set E} (hs : TotallyBounded s)
    {K : ℝ≥0} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hfs : ∀ j, LipschitzOnWith K (fs j) s)
    (hl : ∀ x ∈ s, Tendsto (fun j => fs j x) atTop (𝓝 (f x))) :
    ∃ (Fs : ℕ → E → ℝ) (F : E → ℝ),
      (∀ j, LipschitzWith K (Fs j)) ∧ LipschitzWith K F ∧
      (∀ j, EqOn (fs j) (Fs j) s) ∧ EqOn f F s ∧
      ∀ x, Tendsto (fun j => Fs j x) atTop (𝓝 (F x)) := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨fun _ _ => 0,fun _ => 0,fun _ => (LipschitzWith.const _).weaken (by positivity),
      (LipschitzWith.const _).weaken (by positivity),fun _ => eqOn_empty _ _,
      eqOn_empty _ _,fun _ => tendsto_const_nhds⟩
  have hf := lipschitzOn_limit hfs hl
  refine ⟨fun j => mcShane s K (fs j),mcShane s K f,
    fun j => mcShane_lipschitz hsne (hfs j),mcShane_lipschitz hsne hf,
    fun j => mcShane_eqOn hsne (hfs j),mcShane_eqOn hsne hf,?_⟩
  intro x
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have HU := Metric.tendstoUniformlyOn_iff.mp (uniform_limit_on_totallyBounded hs hfs hl)
    (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := eventually_atTop.mp HU
  refine ⟨N,fun j hj => ?_⟩
  have HH := mcShane_dist_le hsne hf (hfs j) (fun z hz => (hN j hj z hz).le) x
  rw [dist_comm] at HH
  exact HH.trans_lt (half_lt_self hε)

end SharpIntegralFillings

end

end OAI
