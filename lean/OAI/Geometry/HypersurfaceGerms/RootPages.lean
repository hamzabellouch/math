import Mathlib
import OAI.Geometry.HypersurfaceGerms.InnerGeometry
import OAI.Geometry.HypersurfaceGerms.Preparation
import OAI.Geometry.HypersurfaceGerms.RelativeChains
import OAI.Geometry.HypersurfaceGerms.RootBounds

namespace OAI

/-! Homeomorphic inner-root models and naturality of the root-to-base projection. -/

namespace AmbientMultiplicity.SourceInnerPage
noncomputable section
open Preparation InnerQuartic InnerGeometry Filter Topology

abbrev Base := Fin 2 → ℂ

 
def sourceH (p : Base) : ℂ := p 1*(p 0-(p 1)^2)*(p 0-2*(p 1)^2)

lemma continuous_sourceH : Continuous sourceH := by unfold sourceH; fun_prop

 

def low0 (p : Base) (j : Fin 4) : ℂ := coeff0 p ⟨j, by omega⟩
def low1 (p : Base) (j : Fin 4) : ℂ := coeff1 p ⟨j, by omega⟩

lemma low0_analytic : AnalyticAt ℂ low0 0 := by
  apply AnalyticAt.pi
  intro j
  exact ((proj ⟨j, by omega⟩).analyticAt _).comp coeff0_spec.1

lemma low1_analytic : AnalyticAt ℂ low1 0 := by
  apply AnalyticAt.pi
  intro j
  exact ((proj ⟨j, by omega⟩).analyticAt _).comp coeff1_spec.1

 
def R0 (s : ℝ) (p : Base) (w : ℂ) : ℂ := rescaledQuartic low0 s p w
def R1 (s : ℝ) (p : Base) (w : ℂ) : ℂ := rescaledQuartic low1 s p w

lemma R0_eq_source (s : ℝ) (hs : s ≠ 0) (p : Base) (w : ℂ) :
    R0 s p w = (s : ℂ)^4 * root0 p (w/(s : ℂ)) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [R0, rescaledQuartic, low0, root0, eval_rootPoly, Fin.sum_univ_four]
  norm_num
  field_simp

lemma R1_eq_source (s : ℝ) (hs : s ≠ 0) (p : Base) (w : ℂ) :
    R1 s p w = (s : ℂ)^4 * root1 p (w/(s : ℂ)) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [R1, rescaledQuartic, low1, root1, eval_rootPoly, Fin.sum_univ_four]
  norm_num
  field_simp

lemma common_base_cut : ∃ baseRadius : ℝ, 0 < baseRadius ∧
    ContinuousOn low0 (Metric.closedBall 0 baseRadius) ∧
    ContinuousOn low1 (Metric.closedBall 0 baseRadius) := by
  have hh : ∀ᶠ p : Base in 𝓝 0, ContinuousAt low0 p ∧ ContinuousAt low1 p := by
    filter_upwards [low0_analytic.eventually_analyticAt, low1_analytic.eventually_analyticAt]
      with p h0 h1
    exact ⟨h0.continuousAt, h1.continuousAt⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨r/2, by positivity, ?_, ?_⟩
  · intro p hp
    have hp' : p ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball]
      have := Metric.mem_closedBall.mp hp
      linarith
    exact (hsub hp').1.continuousWithinAt
  · intro p hp
    have hp' : p ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball]
      have := Metric.mem_closedBall.mp hp
      linarith
    exact (hsub hp').2.continuousWithinAt

 
abbrev BasePage (baseRadius : ℝ) (c : ℂ) :=
  {p : Base // ‖p‖ ≤ baseRadius ∧ sourceH p = c}

instance basePage_compact (baseRadius : ℝ) (c : ℂ) : CompactSpace (BasePage baseRadius c) := by
  apply isCompact_iff_compactSpace.mp
  change IsCompact {p : Base | ‖p‖ ≤ baseRadius ∧ sourceH p = c}
  have he : {p : Base | ‖p‖ ≤ baseRadius ∧ sourceH p = c} =
      Metric.closedBall 0 baseRadius ∩ sourceH ⁻¹' {c} := by
    ext p
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [he]
  exact (isCompact_closedBall _ _).inter_right
    (isClosed_singleton.preimage continuous_sourceH)

abbrev Disk (radius : ℝ) := ↑(Metric.closedBall (0 : ℂ) radius)
abbrev RootBase (baseRadius : ℝ) (c : ℂ) (radius : ℝ) := BasePage baseRadius c × Disk radius

def onRootBase (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ) (radius : ℝ) :
    RootBase baseRadius c radius → ℂ := fun g => R g.1.val g.2.val

 

abbrev Model (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius M alpha beta : ℝ) :=
  {v : RootBase baseRadius c radius × (ℂ × ℂ) //
    v.2.1*v.2.2 = onRootBase R baseRadius c radius v.1 ∧
      ‖v.2.1‖ ≤ M*radius^alpha ∧ ‖v.2.2‖ ≤ M*radius^beta}

lemma y_bound_eq {radius alpha beta M : ℝ} (hradius : 0 < radius)
    (hweights : alpha+beta = 4) :
    radius^((alpha-beta)/2)*(M*radius^2) = M*radius^alpha := by
  have he : (alpha-beta)/2 + (2 : ℝ) = alpha := by linarith
  have hp := Real.rpow_add hradius ((alpha-beta)/2) 2
  rw [he, Real.rpow_two] at hp
  calc
    _ = M*(radius^((alpha-beta)/2)*radius^2) := by ring
    _ = _ := by rw [← hp]

lemma z_bound_eq {radius alpha beta M : ℝ} (hradius : 0 < radius)
    (hweights : alpha+beta = 4) :
    (radius^((alpha-beta)/2))⁻¹*(M*radius^2) = M*radius^beta := by
  rw [← Real.rpow_neg hradius.le]
  have he : -((alpha-beta)/2) + (2 : ℝ) = beta := by linarith
  have hp := Real.rpow_add hradius (-((alpha-beta)/2)) 2
  rw [he, Real.rpow_two] at hp
  calc
    _ = M*(radius^(-((alpha-beta)/2))*radius^2) := by ring
    _ = _ := by rw [← hp]

 

def weightedModelHomeomorph (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ)
    (radius M alpha beta : ℝ) (hradius : 0 < radius) (hweights : alpha+beta = 4) :
    WeightedConicBlock (onRootBase R baseRadius c radius) (M*radius^2)
        (radius^((alpha-beta)/2)) ≃ₜ Model R baseRadius c radius M alpha beta :=
  Homeomorph.setCongr (by
    ext v
    simp only [y_bound_eq hradius hweights, z_bound_eq hradius hweights])

lemma continuous_onRootBase_rescaled {A : Base → Fin 4 → ℂ} {baseRadius : ℝ}
    (hA : ContinuousOn A (Metric.closedBall 0 baseRadius)) (c : ℂ) (radius s : ℝ) :
    Continuous (onRootBase (rescaledQuartic A s) baseRadius c radius) := by
  have hcA : Continuous (fun p : BasePage baseRadius c => A p.val) :=
    hA.comp_continuous continuous_subtype_val (fun p => by
      simpa [Metric.mem_closedBall, dist_eq_norm] using p.property.1)
  have hc := continuous_rescaledQuartic (fun p : BasePage baseRadius c => A p.val) hcA
  have hk : Continuous (fun p : RootBase baseRadius c radius => (s, (p.1, p.2.val))) :=
    continuous_const.prodMk (continuous_fst.prodMk continuous_snd.subtype_val)
  have hh := hc.comp hk
  exact hh

lemma eventually_bound_on_base {A : Base → Fin 4 → ℂ} {baseRadius : ℝ}
    (hA : ContinuousOn A (Metric.closedBall 0 baseRadius))
    (radius : ℝ) (hradius : 0 < radius) :
    ∀ᶠ s : ℝ in 𝓝 0, ∀ p : Base, ‖p‖ ≤ baseRadius →
      ∀ w : ℂ, ‖w‖ ≤ radius → ‖rescaledQuartic A s p w‖ ≤ 2*radius^4 := by
  have hcA : Continuous (fun p : ↑(Metric.closedBall (0 : Base) baseRadius) => A p.val) :=
    hA.comp_continuous continuous_subtype_val (fun p => p.property)
  have hh := eventually_quartic_norm_le (fun p : ↑(Metric.closedBall (0 : Base) baseRadius) => A p.val)
    hcA radius hradius
  filter_upwards [hh] with s hs p hp w hw
  exact hs ⟨p, by simpa [Metric.mem_closedBall, dist_eq_norm] using hp⟩ w hw

 

def modelCollapseHomotopyEquiv {A : Base → Fin 4 → ℂ} {baseRadius : ℝ}
    (hA : ContinuousOn A (Metric.closedBall 0 baseRadius))
    (c : ℂ) (radius M alpha beta s : ℝ) (hradius : 0 < radius) (hM : 3 < M)
    (hweights : alpha+beta = 4)
    (hbound : ∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ, ‖w‖ ≤ radius →
      ‖rescaledQuartic A s p w‖ ≤ 2*radius^4) :
    ContinuousMap.HomotopyEquiv (Model (rescaledQuartic A s) baseRadius c radius M alpha beta)
      (CircleCollapse (onRootBase (rescaledQuartic A s) baseRadius c radius)) := by
  let R := onRootBase (rescaledQuartic A s) baseRadius c radius
  have hb : ∀ p : RootBase baseRadius c radius, Real.sqrt ‖R p‖ ≤ M*radius^2 := by
    intro p
    apply sqrt_quartic_bound hradius.le hM (norm_nonneg _)
    exact hbound p.1.val p.1.property.1 p.2.val (by
      have hd := Metric.mem_closedBall.mp p.2.property
      rwa [dist_zero_right] at hd)
  exact (weightedModelHomeomorph (rescaledQuartic A s) baseRadius c radius M alpha beta
      hradius hweights).symm.toHomotopyEquiv.trans
    (weightedBlockCollapseHomotopyEquiv R (M*radius^2) hb
      (continuous_onRootBase_rescaled hA c radius s) (radius^((alpha-beta)/2))
      (Real.rpow_pos_of_pos hradius _))

 

theorem exact_inner_models : ∃ baseRadius : ℝ, 0 < baseRadius ∧
    ∀ radius : ℝ, 0 < radius → ∀ M : ℝ, 3 < M → ∀ alpha beta : ℝ,
      alpha+beta = 4 → ∀ᶠ s : ℝ in 𝓝 0, 0 < s → ∀ c : ℂ,
        Nonempty (ContinuousMap.HomotopyEquiv (Model (R0 s) baseRadius c radius M alpha beta)
          (CircleCollapse (onRootBase (R0 s) baseRadius c radius))) ∧
        Nonempty (ContinuousMap.HomotopyEquiv (Model (R1 s) baseRadius c radius M alpha beta)
          (CircleCollapse (onRootBase (R1 s) baseRadius c radius))) := by
  obtain ⟨baseRadius, hb, h0, h1⟩ := common_base_cut
  refine ⟨baseRadius, hb, ?_⟩
  intro radius hr M hM alpha beta hweights
  filter_upwards [eventually_bound_on_base h0 radius hr, eventually_bound_on_base h1 radius hr]
    with s hs0 hs1 hpos c
  exact ⟨⟨modelCollapseHomotopyEquiv h0 c radius M alpha beta s hr hM hweights hs0⟩,
    ⟨modelCollapseHomotopyEquiv h1 c radius M alpha beta s hr hM hweights hs1⟩⟩

end

 

noncomputable section
open Preparation InnerQuartic InnerGeometry RootConfinement Filter Topology

 
def pi0 (q : ℂ × ℂ) : Base := ![q.1^2 + q1 q.1 q.2, q.1]
def pi1 (q : ℂ × ℂ) : Base := ![q.1, psi q.1 q.2]
def d0 (q : ℂ × ℂ) : ℂ := sourceH (pi0 q)
def d1 (q : ℂ × ℂ) : ℂ := sourceH (pi1 q)

lemma continuous_pi0 : Continuous pi0 := by unfold pi0 q1; fun_prop
lemma continuous_pi1 : Continuous pi1 := by unfold pi1 psi q2 q1; fun_prop

lemma low0_zero : low0 0 = 0 := by
  funext j
  simp only [low0, coeff0_spec.2.1]
  change (graph0 0).coeff j = 0
  rw [graph0_specialization, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]

lemma low1_zero : low1 0 = 0 := by
  funext j
  simp only [low1, coeff1_spec.2.1]
  change (graph1 0).coeff j = 0
  rw [graph1_specialization, Polynomial.coeff_X_pow_mul', ite_eq_right (by omega)]

lemma root0_eq_quartic (p : Base) (w : ℂ) :
    root0 p w = w^4 + ∑ j : Fin 4, low0 p j*w^(j:ℕ) := by
  simp [root0, eval_rootPoly, low0]

lemma root1_eq_quartic (p : Base) (w : ℂ) :
    root1 p w = w^4 + ∑ j : Fin 4, low1 p j*w^(j:ℕ) := by
  simp [root1, eval_rootPoly, low1]

 
lemma eventually_root_graph : ∀ᶠ z : V 3 in 𝓝 0,
    (r0 z = 0 ↔ z 0 = (z 1)^2+q1 (z 1) (z 2)) ∧
    (r1 z = 0 ↔ z 1 = psi (z 0) (z 2)) := by
  have h0 : ∀ᶠ z in 𝓝 (0 : V 3), u0 z ≠ 0 :=
    u0_analytic.continuousAt.eventually_ne (by rw [u0_zero]; norm_num)
  have h1 : ∀ᶠ z in 𝓝 (0 : V 3), u1 z ≠ 0 :=
    u1_analytic.continuousAt.eventually_ne (by rw [u1_zero]; norm_num)
  filter_upwards [graph0_factor, graph1_factor, h0, h1] with z hz0 hz1 hn0 hn1
  constructor
  · have hh : r0 z = 0 ↔ z 0-(z 1)^2-q1 (z 1) (z 2) = 0 := by
      rw [hz0, mul_eq_zero, or_iff_left hn0]
    rw [hh]
    constructor <;> intro h <;> linear_combination h
  · have hh : r1 z = 0 ↔ z 1-psi (z 0) (z 2) = 0 := by
      rw [hz1, mul_eq_zero, or_iff_left hn1]
    exact hh.trans sub_eq_zero

 
def join (p : Base) (w : ℂ) : V 3 := ![p 0,p 1,w]

lemma join_small {p : Base} {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hp : ‖p‖ < r) (hw : ‖w‖ < r) : ‖join p w‖ < r := by
  apply (pi_norm_lt_iff hr).mpr
  intro j
  fin_cases j
  · exact (norm_le_pi_norm p 0).trans_lt hp
  · exact (norm_le_pi_norm p 1).trans_lt hp
  · exact hw

lemma base3_join (p : Base) (w : ℂ) : base3 (join p w) = p := by
  ext j
  fin_cases j <;> rfl

 

theorem common_root_chart : ∃ baseRadius rootRadius : ℝ,
    0 < baseRadius ∧ 0 < rootRadius ∧
    ContinuousOn low0 (Metric.closedBall 0 baseRadius) ∧
    ContinuousOn low1 (Metric.closedBall 0 baseRadius) ∧
    (∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ,
      (root0 p w = 0 → ‖w‖ < rootRadius) ∧
      (root1 p w = 0 → ‖w‖ < rootRadius)) ∧
    (∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ, ‖w‖ < rootRadius →
      (root0 p w = 0 ↔ pi0 (p 1,w) = p) ∧
      (root1 p w = 0 ↔ pi1 (p 0,w) = p)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp eventually_root_graph
  have hε : 0 < r/2 := by positivity
  have hall0 := eventually_all_roots_small low0 low0_analytic.continuousAt low0_zero (r/2) hε
  have hall1 := eventually_all_roots_small low1 low1_analytic.continuousAt low1_zero (r/2) hε
  have hcont : ∀ᶠ p : Base in 𝓝 0, ContinuousAt low0 p ∧ ContinuousAt low1 p := by
    filter_upwards [low0_analytic.eventually_analyticAt, low1_analytic.eventually_analyticAt]
      with p h0 h1
    exact ⟨h0.continuousAt,h1.continuousAt⟩
  obtain ⟨b, hb, hball⟩ := Metric.mem_nhds_iff.mp (hall0.and (hall1.and hcont))
  refine ⟨min b r / 2, r/2, by positivity, hε, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hp' : p ∈ Metric.ball (0 : Base) b := by
      rw [Metric.mem_ball, dist_zero_right]
      have hh := Metric.mem_closedBall.mp hp
      rw [dist_zero_right] at hh
      have hmin := min_le_left b r
      linarith
    exact (hball hp').2.2.1.continuousWithinAt
  · intro p hp
    have hp' : p ∈ Metric.ball (0 : Base) b := by
      rw [Metric.mem_ball, dist_zero_right]
      have hh := Metric.mem_closedBall.mp hp
      rw [dist_zero_right] at hh
      have hmin := min_le_left b r
      linarith
    exact (hball hp').2.2.2.continuousWithinAt
  · intro p hp w
    have hp' : p ∈ Metric.ball (0 : Base) b := by
      rw [Metric.mem_ball, dist_zero_right]
      have hmin := min_le_left b r
      linarith
    exact ⟨fun hz => (hball hp').1 w (by rwa [← root0_eq_quartic]),
      fun hz => (hball hp').2.1 w (by rwa [← root1_eq_quartic])⟩
  · intro p hp w hw
    have jp : join p w ∈ Metric.ball 0 r := by
      rw [Metric.mem_ball, dist_zero_right]
      apply join_small hr
      · have hmin := min_le_right b r
        linarith
      · linarith
    obtain ⟨h0,h1⟩ := hsub jp
    simp only [r0, r1, base3_join] at h0 h1
    constructor
    · constructor
      · intro hz
        ext j
        fin_cases j
        · exact (h0.mp hz).symm
        · rfl
      · intro he
        apply h0.mpr
        exact (congrFun he 0).symm
    · constructor
      · intro hz
        ext j
        fin_cases j
        · rfl
        · exact (h1.mp hz).symm
      · intro he
        apply h1.mpr
        exact (congrFun he 1).symm

 
abbrev RootPage (R : Base → ℂ → ℂ) (baseRadius : ℝ) (c : ℂ) (radius : ℝ) :=
  {g : RootBase baseRadius c radius // onRootBase R baseRadius c radius g = 0}

 
abbrev GraphPage (pi : ℂ × ℂ → Base) (baseRadius : ℝ) (c : ℂ) (rootRadius : ℝ) :=
  {q : ℂ × ℂ // ‖pi q‖ ≤ baseRadius ∧ ‖q.2‖ < rootRadius ∧ sourceH (pi q) = c}

section RootHomeomorph
variable (pi : ℂ × ℂ → Base) (j : Fin 2) (root R : Base → ℂ → ℂ)
variable (baseRadius rootRadius radius s : ℝ) (c : ℂ)
variable (hs : 0 < s) (hsize : s*rootRadius ≤ radius)
variable (hscale : ∀ p w, R p w = (s : ℂ)^4*root p (w/(s : ℂ)))
variable (hconfine : ∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ,
  root p w = 0 → ‖w‖ < rootRadius)
variable (hgraph : ∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ, ‖w‖ < rootRadius →
  (root p w = 0 ↔ pi (p j,w) = p))

include hs hscale in
lemma rootPage_unscaled_zero (g : RootPage R baseRadius c radius) :
    root g.val.1.val (g.val.2.val/(s : ℂ)) = 0 := by
  have hz := g.property
  change R g.val.1.val g.val.2.val = 0 at hz
  rw [hscale] at hz
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hs')

include hs hscale hconfine in
lemma rootPage_unscaled_small (g : RootPage R baseRadius c radius) :
    ‖g.val.2.val/(s : ℂ)‖ < rootRadius :=
  hconfine _ g.val.1.property.1 _ (rootPage_unscaled_zero root R _ _ _ _ hs hscale g)

include hs hscale hconfine hgraph in
lemma rootPage_graph_eq (g : RootPage R baseRadius c radius) :
    pi (g.val.1.val j,g.val.2.val/(s : ℂ)) = g.val.1.val :=
  (hgraph _ g.val.1.property.1 _
    (rootPage_unscaled_small root R _ _ _ _ _ hs hscale hconfine g)).mp
    (rootPage_unscaled_zero root R _ _ _ _ hs hscale g)

 
def rootToGraph (g : RootPage R baseRadius c radius) :
    GraphPage pi baseRadius c rootRadius := by
  let q : ℂ × ℂ := (g.val.1.val j,g.val.2.val/(s : ℂ))
  have he : pi q = g.val.1.val :=
    rootPage_graph_eq pi j root R _ _ _ _ _ hs hscale hconfine hgraph g
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [he]; exact g.val.1.property.1
  · exact rootPage_unscaled_small root R _ _ _ _ _ hs hscale hconfine g
  · rw [he]; exact g.val.1.property.2

variable (hpi : ∀ q : ℂ × ℂ, pi q j = q.1)

 
def graphToRoot (q : GraphPage pi baseRadius c rootRadius) :
    RootPage R baseRadius c radius := by
  have hb : (s : ℂ)*q.val.2 ∈ Metric.closedBall 0 radius := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left q.property.2.1.le hs.le).trans hsize
  have hroot : root (pi q.val) q.val.2 = 0 :=
    (hgraph _ q.property.1 _ q.property.2.1).mpr (by rw [hpi])
  refine ⟨(⟨pi q.val, q.property.1, q.property.2.2⟩,
      ⟨(s : ℂ)*q.val.2, hb⟩), ?_⟩
  change R (pi q.val) ((s : ℂ)*q.val.2) = 0
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [hscale, mul_div_cancel_left₀ _ hs', hroot, mul_zero]

lemma graph_root_left_inverse : Function.LeftInverse
    (graphToRoot pi j root R baseRadius rootRadius radius s c hs hsize hscale hgraph hpi)
    (rootToGraph pi j root R baseRadius rootRadius radius s c hs hscale hconfine hgraph) := by
  intro g
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact rootPage_graph_eq pi j root R _ _ _ _ _ hs hscale hconfine hgraph g
  · apply Subtype.ext
    change (s : ℂ)*(g.val.2.val/(s : ℂ)) = g.val.2.val
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    exact mul_div_cancel₀ _ hs'

lemma root_graph_right_inverse : Function.RightInverse
    (graphToRoot pi j root R baseRadius rootRadius radius s c hs hsize hscale hgraph hpi)
    (rootToGraph pi j root R baseRadius rootRadius radius s c hs hscale hconfine hgraph) := by
  intro q
  apply Subtype.ext
  apply Prod.ext
  · exact hpi q.val
  · change (s : ℂ)*q.val.2/(s : ℂ) = q.val.2
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    exact mul_div_cancel_left₀ _ hs'

 

def rootGraphHomeomorph (hpi_cont : Continuous pi) :
    RootPage R baseRadius c radius ≃ₜ GraphPage pi baseRadius c rootRadius where
  toFun := rootToGraph pi j root R baseRadius rootRadius radius s c hs hscale hconfine hgraph
  invFun := graphToRoot pi j root R baseRadius rootRadius radius s c hs hsize hscale hgraph hpi
  left_inv := graph_root_left_inverse pi j root R _ _ _ _ _ hs hsize hscale hconfine hgraph hpi
  right_inv := root_graph_right_inverse pi j root R _ _ _ _ _ hs hsize hscale hconfine hgraph hpi
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun g : RootPage R baseRadius c radius =>
      (g.val.1.val j,g.val.2.val/(s : ℂ)))
    have cp : Continuous (fun g : RootPage R baseRadius c radius => g.val.1.val) :=
      continuous_subtype_val.fst.subtype_val
    have cw : Continuous (fun g : RootPage R baseRadius c radius => g.val.2.val) :=
      continuous_subtype_val.snd.subtype_val
    exact ((continuous_apply j).comp cp).prodMk (cw.div_const (s : ℂ))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact hpi_cont.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      change Continuous (fun q : GraphPage pi baseRadius c rootRadius => (s : ℂ)*q.val.2)
      fun_prop

end RootHomeomorph

 

theorem exact_root_pages : ∃ baseRadius rootRadius : ℝ,
    0 < baseRadius ∧ 0 < rootRadius ∧
    ∀ radius : ℝ, 0 < radius → ∀ᶠ s : ℝ in 𝓝 0, 0 < s → ∀ c : ℂ,
      Nonempty (RootPage (R0 s) baseRadius c radius ≃ₜ
        GraphPage pi0 baseRadius c rootRadius) ∧
      Nonempty (RootPage (R1 s) baseRadius c radius ≃ₜ
        GraphPage pi1 baseRadius c rootRadius) := by
  obtain ⟨b, e, hb, he, _, _, hconf, hgraph⟩ := common_root_chart
  refine ⟨b, e, hb, he, ?_⟩
  intro radius hradius
  have hc : ContinuousAt (fun s : ℝ => s*e) 0 := by fun_prop
  have hsmall : ∀ᶠ s : ℝ in 𝓝 0, s*e < radius :=
    hc.eventually (gt_mem_nhds (by simpa using hradius))
  filter_upwards [hsmall] with s hsize hs c
  constructor
  · exact ⟨rootGraphHomeomorph pi0 1 root0 (R0 s) b e radius s c hs hsize.le
      (R0_eq_source s hs.ne') (fun p hp w => (hconf p hp w).1)
      (fun p hp w hw => (hgraph p hp w hw).1) (fun _ => rfl) continuous_pi0⟩
  · exact ⟨rootGraphHomeomorph pi1 0 root1 (R1 s) b e radius s c hs hsize.le
      (R1_eq_source s hs.ne') (fun p hp w => (hconf p hp w).2)
      (fun p hp w hw => (hgraph p hp w hw).2) (fun _ => rfl) continuous_pi1⟩

end

 

noncomputable section
open InnerGeometry Preparation Filter Topology CategoryTheory

 
def graphPageProjection (pi : ℂ × ℂ → Base) (hpi : Continuous pi)
    (baseRadius : ℝ) (c : ℂ) (rootRadius : ℝ) :
    C(GraphPage pi baseRadius c rootRadius, BasePage baseRadius c) where
  toFun q := ⟨pi q.val, q.property.1, q.property.2.2⟩
  continuous_toFun := (hpi.comp continuous_subtype_val).subtype_mk _

 
def rootPageProjection (R : Base → ℂ → ℂ)
    (baseRadius : ℝ) (c : ℂ) (radius : ℝ) :
    C(RootPage R baseRadius c radius, BasePage baseRadius c) where
  toFun g := g.val.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

section Naturality
variable (pi : ℂ × ℂ → Base) (j : Fin 2) (root R : Base → ℂ → ℂ)
variable (baseRadius rootRadius radius s : ℝ) (c : ℂ)
variable (hs : 0 < s) (hsize : s*rootRadius ≤ radius)
variable (hscale : ∀ p w, R p w = (s : ℂ)^4*root p (w/(s : ℂ)))
variable (hconfine : ∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ,
  root p w = 0 → ‖w‖ < rootRadius)
variable (hgraph : ∀ p : Base, ‖p‖ ≤ baseRadius → ∀ w : ℂ, ‖w‖ < rootRadius →
  (root p w = 0 ↔ pi (p j,w) = p))
variable (hpi : ∀ q : ℂ × ℂ, pi q j = q.1) (hcont : Continuous pi)

lemma rootGraphHomeomorph_over_base :
    (graphPageProjection pi hcont baseRadius c rootRadius).comp
      (rootGraphHomeomorph pi j root R baseRadius rootRadius radius s c
        hs hsize hscale hconfine hgraph hpi hcont).toHomotopyEquiv.toFun =
      rootPageProjection R baseRadius c radius := by
  apply ContinuousMap.ext
  intro g
  apply Subtype.ext
  exact rootPage_graph_eq pi j root R _ _ _ _ _ hs hscale hconfine hgraph g

 

lemma rootGraphHomeomorph_homology_over_base (n : ℕ) :
    (integralHomologyFunctor n).map (TopCat.ofHom
      (rootGraphHomeomorph pi j root R baseRadius rootRadius radius s c
        hs hsize hscale hconfine hgraph hpi hcont).toHomotopyEquiv.toFun) ≫
    (integralHomologyFunctor n).map (TopCat.ofHom
      (graphPageProjection pi hcont baseRadius c rootRadius)) =
    (integralHomologyFunctor n).map (TopCat.ofHom
      (rootPageProjection R baseRadius c radius)) := by
  rw [← Functor.map_comp]
  have he := rootGraphHomeomorph_over_base pi j root R baseRadius rootRadius radius s c
      hs hsize hscale hconfine hgraph hpi hcont
  exact congrArg ((integralHomologyFunctor n).map ∘ TopCat.ofHom) he

end Naturality

 
def baseSection (baseRadius : ℝ) (c : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) :
    C(BasePage baseRadius c, RootBase baseRadius c radius) where
  toFun p := (p, ⟨0, by simpa using hradius⟩)
  continuous_toFun := continuous_id.prodMk continuous_const

 
def rootBaseHomotopyEquiv (baseRadius : ℝ) (c : ℂ) (radius : ℝ) (hradius : 0 ≤ radius) :
    ContinuousMap.HomotopyEquiv (RootBase baseRadius c radius) (BasePage baseRadius c) where
  toFun := ⟨Prod.fst, continuous_fst⟩
  invFun := baseSection baseRadius c radius hradius
  left_inv := by
    refine ⟨{ toFun := fun z => (z.2.1, ⟨(z.1 : ℝ) • z.2.2.val, ?_⟩)
              continuous_toFun := ?_
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg z.1.property.1]
      have hw := Metric.mem_closedBall.mp z.2.2.property
      rw [dist_zero_right] at hw
      exact (mul_le_of_le_one_left (norm_nonneg _) z.1.property.2).trans hw
    · apply Continuous.prodMk
      · exact continuous_snd.fst
      · apply Continuous.subtype_mk
        exact continuous_fst.subtype_val.smul continuous_snd.snd.subtype_val
    · intro g
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp [baseSection]
    · intro g
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp
  right_inv := by
    apply ContinuousMap.Homotopic.refl

 
def rootBaseHomologyIso (baseRadius : ℝ) (c : ℂ) (radius : ℝ) (hradius : 0 ≤ radius)
    (n : ℕ) : IntegralHomology n (RootBase baseRadius c radius) ≅
      IntegralHomology n (BasePage baseRadius c) :=
  integralHomologyIso (rootBaseHomotopyEquiv baseRadius c radius hradius) n

end
end AmbientMultiplicity.SourceInnerPage

end OAI
