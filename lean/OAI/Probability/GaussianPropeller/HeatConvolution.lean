import OAI.Probability.GaussianPropeller.Stein

namespace OAI

universe uV uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology

namespace GaussianPropeller.HeatConvolution
open GaussianPropeller.Stein
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

noncomputable def heat {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : E → V) (t : ℝ) (x : E) : V := ∫ z, F (x+Real.sqrt t • z) ∂γ

section General
variable {V : Type uV} [NormedAddCommGroup V]

lemma integrable_shift [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) (t : ℝ) (x : E) :
    Integrable (fun z => F (x+Real.sqrt t • z)) γ :=
  Integrable.mono' (integrable_const B) (by fun_prop) (ae_of_all _ (fun z => hB _))

lemma continuous_heat [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {F : E → V} (hF : Continuous F) {B : ℝ}
    (hB : ∀ x, ‖F x‖ ≤ B) : Continuous (fun p : ℝ × E => heat F p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ : E => B)
  · intro p; fun_prop
  · intro p; exact ae_of_all _ (fun z => hB _)
  · exact integrable_const _
  · filter_upwards [] with z; fun_prop

variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

lemma fderiv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    (t : ℝ) (x : E) : HasFDerivAt (heat F t) (heat D t x) x := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (bound := fun _ => C) (F' := fun x z => D (x+Real.sqrt t • z)) (by simp)
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  · exact integrable_shift hc hB t x
  · fun_prop
  · exact ae_of_all _ (fun z x _ => hC _)
  · exact integrable_const _
  · filter_upwards [] with z x _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using
      (hD (x+Real.sqrt t • z)).comp x ((hasFDerivAt_id x).add_const _)

lemma time_deriv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((1/(2*Real.sqrt t)) • (∫ z, D (x+Real.sqrt t • z) z ∂γ)) t := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun x => (hD x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (D 0)).trans (hC 0)
  have hp : 0 < Real.sqrt (t/2) := Real.sqrt_pos.mpr (by linarith)
  have hi : Integrable (fun z : E => ‖z‖) γ := (IsGaussian.integrable_id (μ := γ)).norm
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := γ) (x₀ := t) (F := fun s z => F (x+Real.sqrt s • z))
    (F' := fun s z => (1/(2*Real.sqrt s)) • D (x+Real.sqrt s • z) z)
    (s := Ioo (t/2) (2*t)) (bound := fun z => (1/(2*Real.sqrt (t/2)))*C*‖z‖)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall (fun s => by fun_prop))
    (integrable_shift hc hB t x) (by fun_prop) ?_ (hi.const_mul _) ?_
  · simpa only [integral_smul, heat] using hd.2
  · filter_upwards [] with z s hs
    have hs0 : 0 < s := by linarith only [hs.1, ht]
    have hsqrt : Real.sqrt (t/2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by positivity))]
    calc
      (1/(2*Real.sqrt s))*‖D (x+Real.sqrt s • z) z‖ ≤
          (1/(2*Real.sqrt (t/2)))*(C*‖z‖) :=
        mul_le_mul (one_div_le_one_div_of_le (by positivity) (by linarith))
          ((D _).le_opNorm z |>.trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · filter_upwards [] with z s hs
    have hs0 : s ≠ 0 := ne_of_gt (by linarith only [hs.1, ht])
    simpa only [Function.comp_def, map_smul] using
      (hD (x+Real.sqrt s • z)).comp_hasDerivAt s
        ((Real.hasDerivAt_sqrt hs0).smul_const z |>.const_add x)

end General

lemma stein_trace {g : E → E} {K : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {C D : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hD : ∀ x, ‖K x‖ ≤ D)
    (r : ℝ) (x : E) :
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = r*(∫ z, ∑ i, ⟪K (x+r•z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) := by
  let e := EuclideanSpace.basisFun ι ℝ
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC 0)
  have hD0 : 0 ≤ D := (norm_nonneg (K 0)).trans (hD 0)
  have he (i : ι) : ‖e i‖ = 1 := e.orthonormal.norm_eq_one i
  have hi (i : ι) :
      r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) =
        ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
    have hh := integration_by_parts (H := fun z => ⟪e i,g (x+r•z)⟫)
      (D := fun z => r • ((innerSL ℝ (e i)).comp (K (x+r•z))))
      (B := C) (C := |r| *D) ?_ (by fun_prop) ?_ ?_ (e i)
    · simpa only [smul_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply, smul_eq_mul, integral_const_mul] using hh
    · intro z
      have hh := ((innerSL ℝ (e i)).hasFDerivAt).comp z
        ((hg (x+r•z)).comp z ((hasFDerivAt_id z).const_smul r |>.const_add x))
      convert hh using 1 <;> (first | rfl | (ext v; simp))
    · intro z
      exact (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    · intro z
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖(innerSL ℝ (e i)).comp (K (x+r•z))‖ ≤ ‖innerSL ℝ (e i)‖*‖K (x+r•z)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D := by rw [innerSL_apply_norm, he, one_mul]; exact hD _
  have hleft (i : ι) : Integrable (fun z : E => ⟪e i,g (x+r•z)⟫*⟪e i,z⟫) γ := by
    apply Integrable.mono' ((IsGaussian.integrable_id (μ := γ)).norm.const_mul C) (by fun_prop)
    filter_upwards [] with z
    rw [norm_mul]
    have ha : ‖⟪e i,g (x+r•z)⟫‖ ≤ C :=
      (norm_inner_le_norm _ _).trans (by rw [he, one_mul]; exact hC _)
    have hb : ‖⟪e i,z⟫‖ ≤ ‖z‖ := by simpa only [he, one_mul] using norm_inner_le_norm (e i) z
    exact mul_le_mul ha hb (norm_nonneg _) hC0
  have hright (i : ι) : Integrable (fun z : E => ⟪e i,K (x+r•z) (e i)⟫) γ := by
    apply integrable_bounded (by fun_prop) (B := D)
    intro z
    calc
      ‖⟪e i,K (x+r•z) (e i)⟫‖ ≤ ‖e i‖*‖K (x+r•z) (e i)‖ := norm_inner_le_norm _ _
      _ ≤ D := by rw [he, one_mul]; simpa only [he, mul_one] using
        ((K _).le_opNorm (e i)).trans (mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _))
  calc
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = ∫ z, ∑ i, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simpa only [real_inner_comm (e _) (g _)] using (e.sum_inner_mul_inner (g (x+r•z)) z).symm
    _ = ∑ i, ∫ z, ⟪e i,g (x+r•z)⟫*⟪e i,z⟫ ∂γ := integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, r*(∫ z, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by simp_rw [hi]
    _ = r*(∫ z, ∑ i, ⟪e i,K (x+r•z) (e i)⟫ ∂γ) := by
      rw [integral_finsetSum _ (fun i _ => hright i), Finset.mul_sum]
    _ = _ := by congr 1; apply integral_congr_ae; filter_upwards [] with z; congr 1; ext i; exact real_inner_comm _ _

lemma heat_gradient {F : E → ℝ} {g : E → E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x) (hcg : Continuous g)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (t : ℝ) (x : E) :
    HasFDerivAt (heat F t) (innerSL ℝ (heat g t x)) x := by
  have hd := fderiv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) t x
  have heq : heat (fun y => innerSL ℝ (g y)) t x = innerSL ℝ (heat g t x) :=
    (innerSL ℝ).integral_comp_comm (integrable_shift hcg hC t x)
  rwa [heq] at hd

lemma heat_equation {F : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hF : ∀ x, HasFDerivAt F (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {B C D : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖g x‖ ≤ C)
    (hD : ∀ x, ‖K x‖ ≤ D) {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s => heat F s x)
      ((∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫)/2) t := by
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  have hd := time_deriv_heat hF (by fun_prop) hB (fun x => by
    rw [innerSL_apply_norm]; exact hC x) ht x
  simp only [innerSL_apply_apply, smul_eq_mul] at hd
  rw [stein_trace hg hcK hC hD] at hd
  have hi : Integrable (fun z => K (x+Real.sqrt t • z)) γ :=
    Integrable.mono' (integrable_const D) (by fun_prop) (ae_of_all _ (fun z => hD _))
  have heq : (∫ z, ∑ i : ι, ⟪K (x+Real.sqrt t • z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) =
      ∑ i : ι, ⟪(heat K t x) (EuclideanSpace.basisFun ι ℝ i),
        EuclideanSpace.basisFun ι ℝ i⟫ := by
    let e := EuclideanSpace.basisFun ι ℝ
    have hii (i : ι) : Integrable (fun z => ⟪K (x+Real.sqrt t • z) (e i),e i⟫) γ :=
      ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi).inner_const (e i)
    rw [integral_finsetSum _ (fun i _ => hii i)]
    apply Finset.sum_congr rfl
    intro i _
    change (∫ z, ⟪K (x+Real.sqrt t • z) (e i),e i⟫ ∂γ) = ⟪heat K t x (e i),e i⟫
    calc
      _ = ∫ z, ⟪e i,K (x+Real.sqrt t • z) (e i)⟫ ∂γ :=
        integral_congr_ae (ae_of_all _ (fun z => real_inner_comm _ _))
      _ = ⟪e i,∫ z, K (x+Real.sqrt t • z) (e i) ∂γ⟫ :=
        integral_inner ((ContinuousLinearMap.apply ℝ E (e i)).integrable_comp hi) _
      _ = _ := by
        rw [← ContinuousLinearMap.integral_apply hi]
        exact real_inner_comm _ _
  rw [heq] at hd
  convert hd using 1
  field_simp [ne_of_gt (Real.sqrt_pos.mpr ht)]

end GaussianPropeller.HeatConvolution

end OAI
