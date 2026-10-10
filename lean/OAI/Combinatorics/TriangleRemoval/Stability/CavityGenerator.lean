import Mathlib
import OAI.Combinatorics.TriangleRemoval.Coupling.UnitTime
import OAI.Combinatorics.TriangleRemoval.Process.TripleFactorBounds
import OAI.Combinatorics.TriangleRemoval.Process.VariationConstants

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter
open scoped BigOperators Topology

section
open scoped BigOperators Topology BoundedContinuousFunction
open scoped BigOperators
open Filter MeasureTheory
open scoped Topology

namespace SharpTerminalLeave
section CavityStability
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ]

noncomputable def cavityGenerator (H : τ → Finset ι) (D : ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun e => (1 / D) •
    ∑ T ∈ messageCandidates H e none, ∑ f ∈ (H T).erase e, ContinuousLinearMap.proj f

omit [Fintype ι] in
@[simp] theorem cavityGenerator_apply (H : τ → Finset ι) (D : ℝ) (z : ι → ℝ) (e : ι) :
    cavityGenerator H D z e = (1 / D) *
      ∑ T ∈ messageCandidates H e none, ∑ f ∈ (H T).erase e, z f := by
  simp [cavityGenerator]

noncomputable def cavityVelocity (H : τ → Finset ι) (D : ℝ) (s : ℝ) (e : ι) : ℝ :=
  1 - Real.exp (2 * s) / D * ∑ T ∈ messageCandidates H e none,
     (∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
       (1 - cavityMessage H D e T s)

noncomputable def cavityResidual (H : τ → Finset ι) (D : ℝ) (s : ℝ) : ι → ℝ :=
  cavityVelocity H D s + cavityGenerator H D (fun e => cavityLog H D e s)

theorem cavityMessage_derivative_bound (H : τ → Finset ι) {D δ s : ℝ}
    (hD : 0 < D) (hδ : δ ≤ 1 / 2) (hcard : ∀ T, (H T).card = 3)
    (hz : ∀ f, |cavityLog H D f s| ≤ δ)
    (hI : ∀ f T, f ∈ H T → cavityMessage H D f T s ≤ 1 / 2)
    (ht : cavityTime D s ∈ Set.Ioo (0 : ℝ) 1) (e : ι) (T : τ) (he : e ∈ H T) :
    deriv (cavityMessage H D e T) s ≤ 12 / D := by
  rw [(cavityMessage_hasDerivAt H D e T ht).deriv]
  obtain ⟨f, g, hfg, hset, hf, hg⟩ := triangle_children (hcard T) he
  have heq := cavity_triangle_message_summand H D e T hfg hset hf hg ht.2
  have hprod : 1 / 4 ≤ (1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s) := by
    have h1 : 1 / 2 ≤ 1 - cavityMessage H D f T s := by linarith [hI f T hf]
    have h2 : 1 / 2 ≤ 1 - cavityMessage H D g T s := by linarith [hI g T hg]
    nlinarith [mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith)]
  have he2 : Real.exp (cavityLog H D f s + cavityLog H D g s) ≤ 3 := by
    apply (Real.exp_le_exp.mpr (show cavityLog H D f s + cavityLog H D g s ≤ 1 from
      by linarith [(abs_le.mp (hz f)).2, (abs_le.mp (hz g)).2])).trans
    exact Real.exp_one_lt_d9.le.trans (by norm_num)
  have hb : Real.exp (2 * s) *
      (∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) ≤ 12 := by
    rw [heq]
    apply (div_le_iff₀ (by linarith : 0 <
      (1 - cavityMessage H D f T s) * (1 - cavityMessage H D g T s))).mpr
    linarith
  calc
    _ = (Real.exp (2 * s) *
      ∏ u ∈ (H T).erase e, cavityLimit H u (some T) (cavityTime D s)) / D := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hb hD.le

theorem cavityMessage_bound (H : τ → Finset ι) {D δ s : ℝ}
    (hD : 0 < D) (hs : 0 ≤ s) (hδ : δ ≤ 1 / 2) (hcard : ∀ T, (H T).card = 3)
    (hz : ∀ u ∈ Set.Icc 0 s, ∀ f, |cavityLog H D f u| ≤ δ)
    (hI : ∀ u ∈ Set.Icc 0 s, ∀ f T, f ∈ H T → cavityMessage H D f T u ≤ 1 / 2)
    (ht : cavityTime D s < 1) (e : ι) (T : τ) (he : e ∈ H T) :
    cavityMessage H D e T s ≤ 12 * s / D := by
  have hi : ∀ u ∈ Set.Ioo 0 s, cavityTime D u ∈ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    exact ⟨cavityTime_pos hD hu.1, (cavityTime_mono hD hu.2.le).trans_lt ht⟩
  have hh := (convex_Icc (0 : ℝ) s).image_sub_le_mul_sub_of_deriv_le
    (continuous_cavityMessage H D e T).continuousOn
    (fun u hu => ((cavityMessage_hasDerivAt H D e T (hi u (by simpa using hu))).differentiableAt).differentiableWithinAt)
    (C := 12 / D) (fun u hu => by
      have hu' : u ∈ Set.Ioo 0 s := by simpa only [interior_Icc] using hu
      exact cavityMessage_derivative_bound H hD hδ hcard
        (hz u ⟨hu'.1.le, hu'.2.le⟩) (hI u ⟨hu'.1.le, hu'.2.le⟩) (hi u hu') e T he)
    0 ⟨le_rfl, hs⟩ s ⟨hs, le_rfl⟩ hs
  simpa only [cavityMessage_zero, sub_zero, div_mul_eq_mul_div] using hh

theorem cavityResidual_bound (H : τ → Finset ι) {D δ ε η s : ℝ}
    (hD : 0 < D) (hδ : δ ≤ 1 / 2) (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 2) (hη : 0 ≤ η)
    (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (hz : ∀ e, |cavityLog H D e s| ≤ δ)
    (hI : ∀ e T, e ∈ H T → cavityMessage H D e T s ≤ ε)
    (ht : cavityTime D s < 1) :
    ‖cavityResidual H D s‖ ≤ η + 64 * δ ^ 2 + 96 * ε := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro e
  let R : τ → ℝ := fun T => Real.exp (2 * s) *
    ((∏ f ∈ (H T).erase e, cavityLimit H f (some T) (cavityTime D s)) /
      (1 - cavityMessage H D e T s))
  let L : τ → ℝ := fun T => ∑ f ∈ (H T).erase e, cavityLog H D f s
  have hres : cavityResidual H D s e =
      1 - (1 / D) * (∑ T ∈ messageCandidates H e none, R T) +
        (1 / D) * (∑ T ∈ messageCandidates H e none, L T) := by
    simp only [cavityResidual, Pi.add_apply, cavityVelocity, cavityGenerator_apply, R, L,
      ← Finset.mul_sum]
    ring
  rw [Real.norm_eq_abs, hres]
  have hb := cavity_row_error (messageCandidates H e none) R L hD
    (show 0 ≤ 32 * δ ^ 2 + 48 * ε by positivity) (hdeg e) (hrow e) (by
      intro T hT
      have he : e ∈ H T := (Finset.mem_filter.mp hT).2.1
      obtain ⟨f, g, hfg, hset, hf, hg⟩ := triangle_children (hcard T) he
      have hR := cavity_triangle_summand H D e T hfg hset hf hg ht
      have hL : L T = cavityLog H D f s + cavityLog H D g s := by
        simp only [L, hset, Finset.sum_pair hfg]
      dsimp only [R]
      rw [hR, hL]
      convert cavity_summand_taylor hδ (hz f) (hz g) hε'
        ⟨cavityMessage_nonneg H D e T s, hI e T he⟩
        ⟨cavityMessage_nonneg H D f T s, hI f T hf⟩
        ⟨cavityMessage_nonneg H D g T s, hI g T hg⟩ using 1
      congr 1
      ring)
  nlinarith

theorem continuousOn_cavityVelocity (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (cavityVelocity H D) (Set.Icc 0 S) := by
  apply continuousOn_pi.mpr
  intro e
  unfold cavityVelocity
  apply continuousOn_const.sub
  apply ContinuousOn.mul
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const D).continuousOn
  · apply continuousOn_finsetSum
    intro T _
    apply ContinuousOn.div
    · apply continuousOn_finsetProd
      intro f _
      exact ((continuous_cavityLimit H f (some T)).comp (continuous_cavityTime D)).continuousOn
    · exact continuousOn_const.sub (continuous_cavityMessage H D e T).continuousOn
    · intro s hs
      exact (cavityLimit_factor_pos H e T ((cavityTime_mono hD hs.2).trans_lt hS)).ne'

theorem continuousOn_cavityLog_vector (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (fun s e => cavityLog H D e s) (Set.Icc 0 S) :=
  continuousOn_pi.mpr (continuousOn_cavityLog H hD hS)

theorem continuousOn_cavityResidual (H : τ → Finset ι) {D S : ℝ}
    (hD : 0 < D) (hS : cavityTime D S < 1) :
    ContinuousOn (cavityResidual H D) (Set.Icc 0 S) :=
  (continuousOn_cavityVelocity H hD hS).add
    ((cavityGenerator H D).continuous.comp_continuousOn (continuousOn_cavityLog_vector H hD hS))

theorem cavityLog_provisional_bound (H : τ → Finset ι) {D δ η K s : ℝ}
    (hD : 0 < D) (hs : 0 ≤ s) (hδ : δ ≤ 1 / 2) (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (hz : ∀ u ∈ Set.Icc 0 s, ∀ e, |cavityLog H D e u| ≤ δ)
    (hI : ∀ u ∈ Set.Icc 0 s, ∀ e T, e ∈ H T → cavityMessage H D e T u ≤ 1 / 2)
    (ht : cavityTime D s < 1) (hsmall : 12 * s / D ≤ 1 / 2)
    (hsem : ∀ u ∈ Set.Icc 0 s, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ‖fun e => cavityLog H D e s‖ ≤ K * (η + 64 * δ ^ 2 + 1152 * s / D) * s := by
  have hi : ∀ u ∈ Set.Icc 0 s, ∀ e T, e ∈ H T →
      cavityMessage H D e T u ≤ 12 * s / D := by
    intro u hu e T he
    apply (cavityMessage_bound H hD hu.1 hδ hcard
      (fun v hv => hz v ⟨hv.1, hv.2.trans hu.2⟩)
      (fun v hv => hI v ⟨hv.1, hv.2.trans hu.2⟩)
      ((cavityTime_mono hD hu.2).trans_lt ht) e T he).trans
    exact div_le_div_of_nonneg_right (by linarith [hu.2]) hD.le
  have hh := forcing_norm_bound (cavityGenerator H D)
    (fun u e => cavityLog H D e u) (cavityResidual H D) hs hK
    (continuousOn_cavityLog_vector H hD ht) (continuousOn_cavityResidual H hD ht)
    (funext (cavityLog_zero H D)) (by
      intro u hu
      apply hasDerivAt_pi.mpr
      intro e
      convert cavityLog_hasDerivAt H D e
        ⟨cavityTime_pos hD hu.1, (cavityTime_mono hD hu.2.le).trans_lt ht⟩ using 1
      dsimp [cavityResidual, cavityVelocity]
      ring) hsem (d := η + 64 * δ ^ 2 + 1152 * s / D) (by
      intro u hu
      have hr := cavityResidual_bound H hD hδ (by positivity : 0 ≤ 12 * s / D)
        hsmall hη hcard hdeg hrow (hz u hu) (hi u hu)
        ((cavityTime_mono hD hu.2).trans_lt ht)
      convert hr using 1
      ring)
  exact hh

noncomputable def cavityIncidentMessages (H : τ → Finset ι) (D s : ℝ) : ι × τ → ℝ :=
  fun p => if p.1 ∈ H p.2 then cavityMessage H D p.1 p.2 s else 0

theorem continuous_cavityIncidentMessages (H : τ → Finset ι) (D : ℝ) :
    Continuous (cavityIncidentMessages H D) := by
  apply continuous_pi
  intro p
  by_cases hp : p.1 ∈ H p.2
  · simpa only [cavityIncidentMessages, ite_eq_left hp] using continuous_cavityMessage H D p.1 p.2
  · simpa only [cavityIncidentMessages, ite_eq_right hp] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

@[simp] theorem cavityIncidentMessages_zero (H : τ → Finset ι) (D : ℝ) :
    cavityIncidentMessages H D 0 = 0 := by
  ext p
  simp [cavityIncidentMessages]

theorem cavityIncidentMessages_norm_iff (H : τ → Finset ι) (D s b : ℝ) (hb : 0 ≤ b) :
    ‖cavityIncidentMessages H D s‖ ≤ b ↔
      ∀ e T, e ∈ H T → cavityMessage H D e T s ≤ b := by
  rw [pi_norm_le_iff_of_nonneg hb]
  constructor
  · intro hh e T he
    simpa only [cavityIncidentMessages, ite_eq_left he, Real.norm_eq_abs,
      abs_of_nonneg (cavityMessage_nonneg H D e T s)] using hh (e, T)
  · intro hh p
    by_cases hp : p.1 ∈ H p.2
    · simpa only [cavityIncidentMessages, ite_eq_left hp, Real.norm_eq_abs,
        abs_of_nonneg (cavityMessage_nonneg H D p.1 p.2 s)] using hh p.1 p.2 hp
    · simpa only [cavityIncidentMessages, ite_eq_right hp, norm_zero] using hb

theorem cavity_strict_continuation (H : τ → Finset ι) {D S δ η K : ℝ}
    (hD : 0 < D) (hS : 0 ≤ S) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (ht : cavityTime D S < 1)
    (hsmall : 12 * S / D ≤ 1 / 4)
    (himprove : K * (η + 64 * δ ^ 2 + 1152 * S / D) * S ≤ δ / 2)
    (hsem : ∀ u ∈ Set.Icc 0 S, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ∀ s ∈ Set.Icc 0 S,
      (∀ e, |cavityLog H D e s| ≤ δ / 2) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
  let Q : ℝ → ℝ := fun s => max (‖fun e => cavityLog H D e s‖ / δ)
    (2 * ‖cavityIncidentMessages H D s‖)
  have hQ : ContinuousOn Q (Set.Icc 0 S) :=
    ((continuousOn_cavityLog_vector H hD ht).norm.div_const δ).sup
      (continuousOn_const.mul (continuous_cavityIncidentMessages H D).continuousOn.norm)
  have hzero : Q 0 ≤ 1 := by
    simp only [Q, cavityLog_zero, show (fun _ : ι => (0 : ℝ)) = 0 from rfl,
      norm_zero, zero_div, cavityIncidentMessages_zero, mul_zero, max_self, zero_le_one]
  have hdecode : ∀ s, Q s ≤ 1 →
      (∀ e, |cavityLog H D e s| ≤ δ) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 1 / 2) := by
    intro s hh
    have hm := max_le_iff.mp hh
    constructor
    · have hb : ‖fun e => cavityLog H D e s‖ ≤ δ := by
        exact (div_le_one hδ).mp hm.1
      simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hδ.le).mp hb
    · apply (cavityIncidentMessages_norm_iff H D s _ (by norm_num)).mp
      linarith [hm.2]
  have hboot : ∀ s ∈ Set.Icc 0 S, Q s ≤ 1 / 2 := by
    apply strict_bootstrap (δ := 1) (by norm_num) hQ hzero
    intro s hs hp
    have hz := fun u hu => (hdecode u (hp u hu)).1
    have hI := fun u hu => (hdecode u (hp u hu)).2
    have ht' : cavityTime D s < 1 := (cavityTime_mono hD hs.2).trans_lt ht
    have hsmall' : 12 * s / D ≤ 1 / 4 :=
      (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le).trans hsmall
    apply max_le_iff.mpr
    constructor
    · apply (div_le_iff₀ hδ).mpr
      have hh := cavityLog_provisional_bound H hD hs.1 hδ' hη hK hcard hdeg hrow hz hI
        ht' (by linarith) (fun u hu => hsem u ⟨hu.1, hu.2.trans hs.2⟩)
      have hforce : η + 64 * δ ^ 2 + 1152 * s / D ≤ η + 64 * δ ^ 2 + 1152 * S / D := by
        have := div_le_div_of_nonneg_right (by linarith [hs.2] : 1152 * s ≤ 1152 * S) hD.le
        linarith
      have hcmp : K * (η + 64 * δ ^ 2 + 1152 * s / D) * s ≤
          K * (η + 64 * δ ^ 2 + 1152 * S / D) * S := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hforce hK) hs.2 hs.1
        positivity
      linarith [hh.trans hcmp, himprove]
    · have hm : ‖cavityIncidentMessages H D s‖ ≤ 12 * s / D := by
        apply (cavityIncidentMessages_norm_iff H D s _
          (div_nonneg (mul_nonneg (by norm_num) hs.1) hD.le)).mpr
        exact cavityMessage_bound H hD hs.1 hδ' hcard hz hI ht'
      linarith
  intro s hs
  have hpre : ∀ u ∈ Set.Icc 0 s, Q u ≤ 1 := fun u hu =>
    (hboot u ⟨hu.1, hu.2.trans hs.2⟩).trans (by norm_num)
  constructor
  · have hh := (max_le_iff.mp (hboot s hs)).1
    have hn : ‖fun e => cavityLog H D e s‖ ≤ δ / 2 := by
      have := (div_le_iff₀ hδ).mp hh
      linarith
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg (by positivity)).mp hn
  · exact cavityMessage_bound H hD hs.1 hδ' hcard
      (fun u hu => (hdecode u (hpre u hu)).1)
      (fun u hu => (hdecode u (hpre u hu)).2)
      ((cavityTime_mono hD hs.2).trans_lt ht)

omit [Fintype ι] [Fintype τ] [DecidableEq ι] [DecidableEq τ] in
theorem cavityTime_strictMono {D : ℝ} (hD : 0 < D) : StrictMono (cavityTime D) := by
  intro s t hst
  apply div_lt_div_of_pos_right _ (by positivity)
  exact sub_lt_sub_right (Real.exp_lt_exp.mpr (by linarith)) _

theorem cavity_closed_continuation (H : τ → Finset ι) {D S δ η K : ℝ}
    (hD : 0 < D) (hS : 0 < S) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hcard : ∀ T, (H T).card = 3)
    (hdeg : ∀ e, |((messageCandidates H e none).card : ℝ) / D - 1| ≤ η)
    (hrow : ∀ e, ((messageCandidates H e none).card : ℝ) / D ≤ 2)
    (ht : cavityTime D S ≤ 1)
    (hsmall : 12 * S / D ≤ 1 / 4)
    (himprove : K * (η + 64 * δ ^ 2 + 1152 * S / D) * S ≤ δ / 2)
    (hsem : ∀ u ∈ Set.Icc 0 S, ‖NormedSpace.exp ((-u) • cavityGenerator H D)‖ ≤ K) :
    ∀ s ∈ Set.Icc 0 S,
      (∀ e, Real.exp (-s - δ / 2) ≤ cavityLimit H e none (cavityTime D s) ∧
        cavityLimit H e none (cavityTime D s) ≤ Real.exp (-s + δ / 2)) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
  have hpre : ∀ s ∈ Set.Ico 0 S,
      (∀ e, Real.exp (-s - δ / 2) ≤ cavityLimit H e none (cavityTime D s) ∧
        cavityLimit H e none (cavityTime D s) ≤ Real.exp (-s + δ / 2)) ∧
      (∀ e T, e ∈ H T → cavityMessage H D e T s ≤ 12 * s / D) := by
    intro s hs
    have ht' : cavityTime D s < 1 := (cavityTime_strictMono hD hs.2).trans_le ht
    have hsmall' : 12 * s / D ≤ 1 / 4 :=
      (div_le_div_of_nonneg_right (by linarith [hs.2]) hD.le).trans hsmall
    have hforce : η + 64 * δ ^ 2 + 1152 * s / D ≤ η + 64 * δ ^ 2 + 1152 * S / D := by
      linarith [div_le_div_of_nonneg_right (by linarith [hs.2] : 1152 * s ≤ 1152 * S) hD.le]
    have hcmp : K * (η + 64 * δ ^ 2 + 1152 * s / D) * s ≤
        K * (η + 64 * δ ^ 2 + 1152 * S / D) * S := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hforce hK) hs.2.le hs.1
      positivity
    have hh := cavity_strict_continuation H hD hs.1 hδ hδ' hη hK hcard hdeg hrow ht'
      hsmall' (hcmp.trans himprove) (fun u hu => hsem u ⟨hu.1, hu.2.trans hs.2.le⟩) s ⟨hs.1, le_rfl⟩
    refine ⟨?_, hh.2⟩
    intro e
    rw [cavityLog_exp H D e ht']
    constructor <;> apply Real.exp_le_exp.mpr <;> linarith [(abs_le.mp (hh.1 e)).1, (abs_le.mp (hh.1 e)).2]
  have hclose {P : ℝ → Prop} (hp : IsClosed {s | P s})
      (hh : ∀ s ∈ Set.Ico 0 S, P s) : ∀ s ∈ Set.Icc 0 S, P s := by
    have hx : closure (Set.Ico 0 S) ⊆ {s | P s} := closure_minimal hh hp
    simpa only [closure_Ico hS.ne, Set.subset_def, Set.mem_ofPred_eq] using hx
  intro s hs
  constructor
  · intro e
    have hc := (continuous_cavityLimit H e none).comp (continuous_cavityTime D)
    constructor
    · exact hclose (isClosed_le (Real.continuous_exp.comp
        (continuous_id.neg.sub continuous_const)) hc) (fun u hu => (hpre u hu).1 e |>.1) s hs
    · exact hclose (isClosed_le hc (Real.continuous_exp.comp
        (continuous_id.neg.add continuous_const))) (fun u hu => (hpre u hu).1 e |>.2) s hs
  · intro e T he
    exact hclose (isClosed_le (continuous_cavityMessage H D e T)
      ((continuous_const.mul continuous_id).div_const D)) (fun u hu => (hpre u hu).2 e T he) s hs

end CavityStability
end SharpTerminalLeave

end

end

end OAI
