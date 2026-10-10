import OAI.Probability.DilutedSpin.CompoundPhysicalMean
import OAI.Probability.DilutedSpin.CountBridgeTools
import OAI.Probability.DilutedSpin.InsertionCoefficient

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma integral_conv_increment (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable id μ) (hν : Integrable id ν) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    (∫ x,f x ∂(μ∗ν))-(∫ x,f x ∂μ)=∫ x,∫ y,f (x+y)-f x ∂ν ∂μ := by
  have hfi := integrable_lipschitz_of_id μ hμ hf
  have hfc := integrable_lipschitz_of_id (μ∗ν) (integrable_id_conv μ ν hμ hν) hf
  have hfp : Integrable (fun z : E×E => f (z.1+z.2)) (μ.prod ν) :=
    (integrable_map_measure hf.continuous.measurable.aestronglyMeasurable (by fun_prop)).mp hfc
  rw [integral_conv hfc,← integral_sub hfp.integral_prod_left hfi]
  apply integral_congr_ae
  filter_upwards [] with x
  have hx : Integrable (fun y => f (x+y)) ν := by
    apply integrable_lipschitz_of_id ν hν
    simpa only [mul_one,Function.comp_def] using hf.comp (isometry_add_left x).lipschitzWith
  rw [integral_sub hx (integrable_const _)]
  simp

/-- Exact old-system addition formula at the level of physical energy laws. -/
lemma compoundPoisson_increment (r s : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ} (hf : LipschitzWith C f) :
    (∫ x,f x ∂compoundPoisson (r+s) μ)-(∫ x,f x ∂compoundPoisson r μ)=
      ∫ x,∫ y,f (x+y)-f x ∂compoundPoisson s μ ∂compoundPoisson r μ := by
  rw [compoundPoisson_add]
  exact integral_conv_increment _ _ (compoundPoisson_integrable_id r μ hμ)
    (compoundPoisson_integrable_id s μ hμ) hf

lemma compoundPoisson_increment_rate_bound (r s t : ℝ≥0) (μ : Measure E)
    [IsProbabilityMeasure μ] (hμ : Integrable id μ) {C : ℝ≥0} {f : E → ℝ}
    (hf : LipschitzWith C f) :
    |(∫ x,∫ y,f (x+y)-f x ∂compoundPoisson s μ ∂compoundPoisson r μ)-
      (∫ x,∫ y,f (x+y)-f x ∂compoundPoisson t μ ∂compoundPoisson r μ)|≤
      C * |(s:ℝ)-t| * (∫ y,‖y‖ ∂μ) := by
  rw [← compoundPoisson_increment r s μ hμ hf,← compoundPoisson_increment r t μ hμ hf,
    sub_sub_sub_cancel_right]
  have hh := compoundPoisson_rate_bound (r+s) (r+t) μ hμ hf
  simpa only [NNReal.coe_add,add_sub_add_left_eq_sub] using hh

/-- The reservoir deficit can be replaced by its exact limiting insertion
rate, uniformly over the old energy and every finite auxiliary hierarchy. -/
lemma reservoir_increment_limit (α : ℝ≥0) (q : ℕ) (μ : Measure E)
    [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (f : ℕ → E → ℝ) (hf : ∀ N,LipschitzWith 1 (f N)) :
    Tendsto (fun N : ℕ =>
      (∫ x,f N x ∂compoundPoisson (α*N) μ)-
      (∫ x,f N x ∂compoundPoisson (reservoirRate α q N) μ)-
      (∫ x,∫ y,f N (x+y)-f N x ∂compoundPoisson (α*q) μ
        ∂compoundPoisson (reservoirRate α q N) μ)) atTop (𝓝 0) := by
  have hs (N : ℕ) : reservoirRate α q N+(α*N-reservoirRate α q N)=α*N :=
    add_tsub_cancel_of_le (reservoirRate_le α q N)
  have hh (N : ℕ) := compoundPoisson_increment_rate_bound (reservoirRate α q N)
    (α*N-reservoirRate α q N) (α*q) μ hμ (hf N)
  have hl := (((reservoir_deficit_tendsto α q).sub_const ((α*q:ℝ≥0):ℝ)).abs).mul_const (∫ y,‖y‖ ∂μ)
  simp only [NNReal.coe_mul,NNReal.coe_natCast,sub_self,abs_zero,zero_mul] at hl
  apply squeeze_zero_norm' (Eventually.of_forall (fun N => ?_)) hl
  have hh := hh N
  rw [← compoundPoisson_increment _ _ μ hμ (hf N),hs N] at hh
  simpa only [Real.norm_eq_abs,NNReal.coe_one,one_mul,NNReal.coe_sub (reservoirRate_le α q N),NNReal.coe_mul,NNReal.coe_natCast] using hh

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.FiniteLaw
open _root_.MeasureTheory _root_.OAI.MeasureTheory SizeCoupling
variable {X Y J W : Type} [MeasurableSpace X] [MeasurableSpace Y] [Fintype J] [Fintype W]

lemma expect_double_integral (P : FiniteLaw W) (Q : FiniteLaw J)
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (F : X → Y → J → W → ℝ)
    (hf : ∀ j w,Measurable (fun z : X × Y => F z.1 z.2 j w))
    {B : ℝ} (hb : ∀ x y j w,|F x y j w|≤B) :
    P.expect (fun w => ∫ x,Q.expect (fun j => ∫ y,F x y j w ∂ν) ∂μ) =
      ∫ x,∫ y,Q.expect (fun j => P.expect (fun w => F x y j w)) ∂ν ∂μ := by
  have hmj (j : J) (w : W) : Measurable (fun x => ∫ y,F x y j w ∂ν) :=
    (hf j w).stronglyMeasurable.integral_prod_right'.measurable
  rw [← integral_expect_bounded P μ (fun x w => Q.expect (fun j => ∫ y,F x y j w ∂ν))
    (fun w => measurable_expect _ (fun j => hmj j w))
    (fun x w => abs_expect_le _ (fun j => abs_integral_le_const _ (fun y => hb x y j w)))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [expect_comm]
  symm
  rw [integral_expect_bounded Q ν (fun y j => P.expect (fun w => F x y j w))
    (fun j => measurable_expect _ (fun w => (hf j w).comp (measurable_const.prodMk measurable_id)))
    (fun y j => abs_expect_le _ (fun w => hb x y j w))]
  apply expect_congr
  intro j
  exact integral_expect_bounded P ν (fun y w => F x y j w)
    (fun w => (hf j w).comp (measurable_const.prodMk measurable_id)) (fun y w => hb x y j w)

end DilutedSpinGlass.FiniteLaw

end

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι α β : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

lemma expect_pi_bind (P : ι → FiniteLaw α) (Q : ι → α → FiniteLaw β)
    (f : (ι → α×β) → ℝ) :
    (pi (fun i => (P i).bind (Q i))).expect f =
      (pi P).expect (fun a => (pi (fun i => Q i (a i))).expect (fun b => f (fun i => (a i,b i)))) := by
  classical
  let e : (ι → α×β) ≃ (ι → α)×(ι → β) :=
    ⟨fun x => (fun i => (x i).1,fun i => (x i).2),fun x i => (x.1 i,x.2 i),
      fun x => rfl,fun x => rfl⟩
  unfold expect
  rw [show (∑ x, (pi (fun i => (P i).bind (Q i))).weight x*f x)=
      ∑ x : (ι → α)×(ι → β),(∏ i,(P i).weight (x.1 i))*(∏ i,(Q i (x.1 i)).weight (x.2 i))*f (fun i => (x.1 i,x.2 i)) from
    Fintype.sum_equiv e _ _ (fun x => by
      simp only [e,Equiv.coe_fn_mk,pi,bind,Finset.prod_mul_distrib])]
  simp only [Fintype.sum_prod_type,pi,Finset.mul_sum,mul_assoc]

end DilutedSpinGlass.FiniteLaw

end

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

noncomputable def mixedFactor {p : ℕ} (z : InteractionSample p) (sel : Fin p → Bool)
    (s : Fin p → Spin) (x : Fin p → ℝ) : ℝ :=
  z.2.2.1 * ∏ l : Fin p,if sel l then z.2.2.2 l (s l) else averagedFactor (z.2.2.2 l) (x l)

lemma mixedFactor_bound {p : ℕ} (z : InteractionSample p)
    (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) : |mixedFactor z sel s x|≤1 := by
  have he (l : Fin p) :
      ((if sel l then FiniteLaw.point (s l) else qLaw (x l)) : FiniteLaw Spin).expect (z.2.2.2 l)=
      if sel l then z.2.2.2 l (s l) else averagedFactor (z.2.2.2 l) (x l) := by
    cases sel l <;> simp only [Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_point]
    rfl
  have hh := averaged_product_bound z.2.2.1 z.2.2.2 hz
    (fun l => if sel l then FiniteLaw.point (s l) else qLaw (x l))
  simpa only [he,mixedFactor] using hh

lemma measurable_mixedFactor {p : ℕ} (sel : Fin p → Bool)
    (s : Fin p → Spin) (x : Fin p → ℝ) : Measurable (fun z : InteractionSample p => mixedFactor z sel s x) := by
  unfold mixedFactor averagedFactor
  apply Measurable.mul (by fun_prop)
  apply Finset.measurable_prod
  intro l _
  cases sel l <;> simp only [Bool.false_eq_true,↓reduceIte]
  · apply Finset.measurable_sum
    intro a _
    fun_prop
  · fun_prop

noncomputable def insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (z : InteractionSample p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) : ℝ :=
  (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
    (fun w => ∏ a : Fin n,-mixedFactor z sel (fun l => old (w l).1 a) (fun l => x (w l).2 a))

lemma measurable_insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    Measurable (fun z : InteractionSample p => insertionPoint z old Q x sel) := by
  unfold insertionPoint FiniteLaw.expect
  apply Finset.measurable_sum
  intro w _
  apply Measurable.const_mul
  exact Finset.measurable_prod _ (fun a _ => (measurable_mixedFactor sel _ _).neg)

lemma insertionPoint_bound {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (z : InteractionSample p) (hz : ∀ s : Fin p → Spin,|z.2.2.1*∏ l,z.2.2.2 l (s l)|≤1)
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    |insertionPoint z old Q x sel|≤1 := by
  apply FiniteLaw.abs_expect_le
  intro w
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
  intro a _
  rw [abs_neg]
  exact mixedFactor_bound z hz sel _ _

lemma integrable_insertionPoint {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (hM : Admissible M) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    Integrable (fun z => insertionPoint z old Q x sel) M.disorder.toMeasure := by
  apply Integrable.of_bound (measurable_insertionPoint old Q x sel).aestronglyMeasurable 1
  filter_upwards [hM.factorization] with z hz
  simpa only [Real.norm_eq_abs] using insertionPoint_bound z (fun s => (hz.2 s).2.le) old Q x sel

lemma insertionCoefficient_eq_integral_point {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    insertionCoefficient M old Q x sel=∫ z,insertionPoint z old Q x sel ∂M.disorder.toMeasure := rfl

lemma integral_expected_insertionPoint {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    (∫ z,P.expect (fun w => insertionPoint z (old w) Q x sel) ∂M.disorder.toMeasure)=
      P.expect (fun w => insertionCoefficient M (old w) Q x sel) :=
  FiniteLaw.integral_expect P M.disorder.toMeasure _
    (fun w => integrable_insertionPoint M hM (old w) Q x sel)

end DilutedSpinGlass

end

end OAI
