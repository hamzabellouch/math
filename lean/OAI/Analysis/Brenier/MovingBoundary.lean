import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Problem358.MovingBoundary

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- A moving integration endpoint in a product-space strip differentiates to the
integral on its boundary slice. Only almost-everywhere slice continuity is needed. -/
theorem hasDerivAt_integral_movingEndpoint
    {f : ℝ → X → ℝ} {c : ℝ} {bound : X → ℝ}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hbound : ∀ᶠ t in 𝓝 c, ∀ᵐ x ∂μ, ‖f t x‖ ≤ bound x)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun t => f t x) c)
    (hint : ∀ᶠ t in 𝓝 c,
      Integrable (Function.uncurry f) ((volume.restrict (uIoc c t)).prod μ)) :
    HasDerivAt (fun t => ∫ x, (∫ s in c..t, f s x) ∂μ)
      (∫ x, f c x ∂μ) c := by
  have hm : ∀ t, AEStronglyMeasurable (f t) μ := by
    intro t
    exact (hf.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hslice : ContinuousAt (fun t => ∫ x, f t x ∂μ) c :=
    continuousAt_of_dominated (Eventually.of_forall hm) hbound hbound_int hcont
  have hsm : StronglyMeasurable (fun t => ∫ x, f t x ∂μ) :=
    hf.integral_prod_right'
  have hd := intervalIntegral.integral_hasDerivAt_right
    (by simp : IntervalIntegrable (fun t => ∫ x, f t x ∂μ) volume c c)
    hsm.stronglyMeasurableAtFilter hslice
  apply hd.congr_of_eventuallyEq
  filter_upwards [hint] with t ht
  exact (intervalIntegral_integral_swap ht).symm

/-- Global domination in the transverse variable supplies all local strip
integrability requirements of the moving-endpoint formula. -/
theorem hasDerivAt_integral_movingEndpoint_of_bound
    {f : ℝ → X → ℝ} {c : ℝ} {bound : X → ℝ}
    (hf : StronglyMeasurable (Function.uncurry f))
    (hbound : ∀ᵐ x ∂μ, ∀ t, ‖f t x‖ ≤ bound x)
    (hbound_int : Integrable bound μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun t => f t x) c) :
    HasDerivAt (fun t => ∫ x, (∫ s in c..t, f s x) ∂μ)
      (∫ x, f c x ∂μ) c := by
  apply hasDerivAt_integral_movingEndpoint hf
    (Eventually.of_forall (fun t => hbound.mono fun x hx => hx t)) hbound_int hcont
  apply Eventually.of_forall
  intro t
  let : IsFiniteMeasure (volume.restrict (uIoc c t)) :=
    ⟨by simp [Real.volume_uIoc]⟩
  apply (hbound_int.comp_snd (volume.restrict (uIoc c t))).mono' hf.aestronglyMeasurable
  have hpair : ∀ᵐ p ∂(volume.restrict (uIoc c t)).prod μ,
      ∀ s, ‖f s p.2‖ ≤ bound p.2 := Measure.quasiMeasurePreserving_snd.ae hbound
  filter_upwards [hpair] with p hp
  exact hp p.1

/-- The velocity may vary across the transverse slice. This is the local
moving-face formula after straightening a hyperplane and rescaling its normal. -/
theorem hasDerivAt_integral_movingBoundary
    {f : ℝ → X → ℝ} {v : X → ℝ} {c : ℝ} {bound : X → ℝ}
    (hf : StronglyMeasurable (Function.uncurry f)) (hv : Measurable v)
    (hbound : ∀ᵐ x ∂μ, ∀ t, ‖f t x‖ ≤ bound x)
    (hweighted : Integrable (fun x => |v x| * bound x) μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun t => f t x) c) :
    HasDerivAt (fun t => ∫ x, (∫ s in c..(c + t * v x), f s x) ∂μ)
      (∫ x, v x * f c x ∂μ) 0 := by
  let F : ℝ → X → ℝ := fun t x => v x * f (v x * t + c) x
  have hF : StronglyMeasurable (Function.uncurry F) := by
    apply Measurable.stronglyMeasurable
    exact (hv.comp measurable_snd).mul (hf.measurable.comp
      ((((hv.comp measurable_snd).mul measurable_fst).add measurable_const).prodMk
        measurable_snd))
  have hFb : ∀ᵐ x ∂μ, ∀ t, ‖F t x‖ ≤ |v x| * bound x := by
    filter_upwards [hbound] with x hx t
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx _) (abs_nonneg _)
  have hFc : ∀ᵐ x ∂μ, ContinuousAt (fun t => F t x) 0 := by
    filter_upwards [hcont] with x hx
    have hi : ContinuousAt (fun t : ℝ => v x * t + c) 0 := by fun_prop
    have hx' : ContinuousAt (fun t => f t x) (v x * 0 + c) := by simpa using hx
    exact continuousAt_const.mul (ContinuousAt.comp (f := fun t : ℝ => v x * t + c) hx' hi)
  have hd := hasDerivAt_integral_movingEndpoint_of_bound hF hFb hweighted hFc
  have heq (t : ℝ) :
      (∫ x, (∫ s in (0 : ℝ)..t, F s x) ∂μ) =
        ∫ x, (∫ s in c..(c + t * v x), f s x) ∂μ := by
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    dsimp [F]
    rw [intervalIntegral.integral_const_mul]
    simpa only [mul_zero, zero_add, add_comm c, mul_comm t] using
      (intervalIntegral.mul_integral_comp_mul_add (a := 0) (b := t)
        (f := fun s => f s x) (v x) c)
  simpa only [heq, F, mul_zero, zero_add] using hd

/-- Normal coefficients may also move: solving an affine moving-face equation
introduces the scalar factor `t / (n + t * k)`. Its derivative is harmless when
`n ≠ 0`, as required for a genuine initial face normal. -/
theorem hasDerivAt_integral_movingAffineFace
    {f : ℝ → X → ℝ} {v : X → ℝ} {c n k : ℝ} {bound : X → ℝ}
    (hn : n ≠ 0) (hf : StronglyMeasurable (Function.uncurry f)) (hv : Measurable v)
    (hbound : ∀ᵐ x ∂μ, ∀ t, ‖f t x‖ ≤ bound x)
    (hweighted : Integrable (fun x => |v x| * bound x) μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun t => f t x) c) :
    HasDerivAt (fun t => ∫ x,
      (∫ s in c..(c + (t / (n + t * k)) * v x), f s x) ∂μ)
      ((∫ x, v x * f c x ∂μ) / n) 0 := by
  have hden : HasDerivAt (fun t : ℝ => n + t * k) k 0 := by
    convert! (hasDerivAt_const (0 : ℝ) n).add ((hasDerivAt_id 0).mul_const k) using 1
    ring
  have hparameter : HasDerivAt (fun t : ℝ => t / (n + t * k)) (1 / n) 0 := by
    convert! (hasDerivAt_id 0).div hden (by simpa using hn) using 1
    simp only [id_eq, zero_mul, add_zero, one_mul, sub_zero]
    field_simp [hn]
  have hd := hasDerivAt_integral_movingBoundary hf hv hbound hweighted hcont
  have hd' : HasDerivAt (fun t => ∫ x, (∫ s in c..(c + t * v x), f s x) ∂μ)
      (∫ x, v x * f c x ∂μ) ((0 : ℝ) / (n + 0 * k)) := by simpa using hd
  simpa only [Function.comp_def, mul_one_div] using hd'.comp 0 hparameter

end Problem358.MovingBoundary

end

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal

namespace Problem358.MovingBoundary

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

/-- Fubini for a measurable subgraph, with the normal coordinate integrated first. -/
theorem integral_subgraph_eq_iterated
    {f : ℝ → X → ℝ} {q : X → ℝ}
    (hf : Integrable (Function.uncurry f) (volume.prod μ)) (hq : Measurable q) :
    (∫ p in {p : ℝ × X | p.1 ≤ q p.2}, f p.1 p.2 ∂volume.prod μ) =
      ∫ x, (∫ s in Iic (q x), f s x) ∂μ := by
  have hS : MeasurableSet {p : ℝ × X | p.1 ≤ q p.2} :=
    measurableSet_le measurable_fst (hq.comp measurable_snd)
  rw [← integral_indicator hS]
  change (∫ p, {p : ℝ × X | p.1 ≤ q p.2}.indicator
    (Function.uncurry f) p ∂volume.prod μ) = _
  rw [integral_prod_symm _ (hf.indicator hS)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [← integral_indicator measurableSet_Iic]
  rfl

/-- The inner subgraph integral is integrable in the transverse coordinate. -/
theorem integrable_integral_subgraph
    {f : ℝ → X → ℝ} {q : X → ℝ}
    (hf : Integrable (Function.uncurry f) (volume.prod μ)) (hq : Measurable q) :
    Integrable (fun x => ∫ s in Iic (q x), f s x) μ := by
  have hS : MeasurableSet {p : ℝ × X | p.1 ≤ q p.2} :=
    measurableSet_le measurable_fst (hq.comp measurable_snd)
  have hi := (hf.indicator hS).integral_prod_right
  convert hi using 1
  funext x
  rw [← integral_indicator measurableSet_Iic]
  rfl

/-- The difference of two subgraph integrals is exactly their oriented strip integral. -/
theorem integral_subgraph_sub
    {f : ℝ → X → ℝ} {q₀ q₁ : X → ℝ}
    (hf : Integrable (Function.uncurry f) (volume.prod μ))
    (hq₀ : Measurable q₀) (hq₁ : Measurable q₁) :
    (∫ p in {p : ℝ × X | p.1 ≤ q₁ p.2}, f p.1 p.2 ∂volume.prod μ) -
        (∫ p in {p : ℝ × X | p.1 ≤ q₀ p.2}, f p.1 p.2 ∂volume.prod μ) =
      ∫ x, (∫ s in q₀ x..q₁ x, f s x) ∂μ := by
  rw [integral_subgraph_eq_iterated hf hq₁, integral_subgraph_eq_iterated hf hq₀,
    ← integral_sub (integrable_integral_subgraph hf hq₁)
      (integrable_integral_subgraph hf hq₀)]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with x hx
  exact intervalIntegral.integral_Iic_sub_Iic hx.integrableOn hx.integrableOn

/-- An oriented moving strip has the expected absolute integral bound.
This estimate needs no boundary continuity and supplies local Lipschitz control. -/
theorem norm_integral_subgraph_sub_le
    {f : ℝ → X → ℝ} {q₀ q₁ bound : X → ℝ}
    (hf : Integrable (Function.uncurry f) (volume.prod μ))
    (hq₀ : Measurable q₀) (hq₁ : Measurable q₁)
    (hbound : ∀ᵐ x ∂μ, ∀ s, ‖f s x‖ ≤ bound x)
    (hint : Integrable (fun x => bound x * |q₁ x - q₀ x|) μ) :
    ‖(∫ p in {p : ℝ × X | p.1 ≤ q₁ p.2}, f p.1 p.2 ∂volume.prod μ) -
        (∫ p in {p : ℝ × X | p.1 ≤ q₀ p.2}, f p.1 p.2 ∂volume.prod μ)‖ ≤
      ∫ x, bound x * |q₁ x - q₀ x| ∂μ := by
  rw [integral_subgraph_sub hf hq₀ hq₁]
  apply norm_integral_le_of_norm_le hint
  filter_upwards [hbound] with x hx
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hx s)

/-- Lipschitz motion of the threshold gives Lipschitz motion of the subgraph
integral. The transverse speed is allowed to vary and is integrated against the
density bound, so this applies to affine moving-face charts on compact sources. -/
theorem lipschitzOnWith_integral_subgraph
    {A : Type*} [PseudoMetricSpace A] {S : Set A} {C : ℝ≥0}
    {f : ℝ → X → ℝ} {q : A → X → ℝ} {bound speed : X → ℝ}
    (hf : Integrable (Function.uncurry f) (volume.prod μ))
    (hq : ∀ a ∈ S, Measurable (q a))
    (hbound : ∀ᵐ x ∂μ, ∀ s, ‖f s x‖ ≤ bound x)
    (hweighted : Integrable (fun x => bound x * speed x) μ)
    (hcost : (∫ x, bound x * speed x ∂μ) ≤ C)
    (hmotion : ∀ a ∈ S, ∀ b ∈ S, ∀ᵐ x ∂μ,
      |q a x - q b x| ≤ speed x * dist a b) :
    LipschitzOnWith C (fun a => ∫ p in {p : ℝ × X | p.1 ≤ q a p.2},
      f p.1 p.2 ∂volume.prod μ) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  rw [dist_eq_norm, integral_subgraph_sub hf (hq b hb) (hq a ha)]
  calc
    ‖∫ x, (∫ s in q b x..q a x, f s x) ∂μ‖ ≤
        ∫ x, (bound x * speed x) * dist a b ∂μ := by
      apply norm_integral_le_of_norm_le (hweighted.mul_const (dist a b))
      filter_upwards [hbound, hmotion a ha b hb] with x hx hqx
      have hb0 : 0 ≤ bound x := (norm_nonneg (f 0 x)).trans (hx 0)
      calc
        ‖∫ s in q b x..q a x, f s x‖ ≤ bound x * |q a x - q b x| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => hx s)
        _ ≤ bound x * (speed x * dist a b) := mul_le_mul_of_nonneg_left hqx hb0
        _ = (bound x * speed x) * dist a b := (mul_assoc _ _ _).symm
    _ = (∫ x, bound x * speed x ∂μ) * dist a b := integral_mul_const _ _
    _ ≤ C * dist a b := mul_le_mul_of_nonneg_right hcost dist_nonneg

/-- A genuine moving-halfspace integral differentiates to its boundary integral.
The global integrability assumption is automatic for bounded compactly supported
cell densities, while continuity is only required almost everywhere on the initial face. -/
theorem hasDerivAt_subgraph_movingAffineFace
    {f : ℝ → X → ℝ} {v : X → ℝ} {c n k : ℝ} {bound : X → ℝ}
    (hn : n ≠ 0) (hf : StronglyMeasurable (Function.uncurry f))
    (hfi : Integrable (Function.uncurry f) (volume.prod μ)) (hv : Measurable v)
    (hbound : ∀ᵐ x ∂μ, ∀ t, ‖f t x‖ ≤ bound x)
    (hweighted : Integrable (fun x => |v x| * bound x) μ)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (fun t => f t x) c) :
    HasDerivAt (fun t => ∫ p in {p : ℝ × X | p.1 ≤ c +
        (t / (n + t * k)) * v p.2}, f p.1 p.2 ∂volume.prod μ)
      ((∫ x, v x * f c x ∂μ) / n) 0 := by
  have hd := hasDerivAt_integral_movingAffineFace (k := k) hn hf hv hbound hweighted hcont
  have heq (t : ℝ) :
      (∫ p in {p : ℝ × X | p.1 ≤ c + (t / (n + t * k)) * v p.2},
          f p.1 p.2 ∂volume.prod μ) =
        (∫ x, (∫ s in c..(c + (t / (n + t * k)) * v x), f s x) ∂μ) +
          (∫ p in {p : ℝ × X | p.1 ≤ c}, f p.1 p.2 ∂volume.prod μ) := by
    apply (sub_eq_iff_eq_add).mp
    exact integral_subgraph_sub hfi measurable_const
      (measurable_const.add (measurable_const.mul hv))
  simpa only [← heq] using hd.add_const
    (∫ p in {p : ℝ × X | p.1 ≤ c}, f p.1 p.2 ∂volume.prod μ)

end Problem358.MovingBoundary

end

end OAI
