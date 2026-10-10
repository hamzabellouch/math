import Mathlib
import OAI.Probability.GaussianInformation.Kernel.Coercivity

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
namespace KernelPotential
open Filter
open scoped Topology NNReal
namespace Coercivity
open KernelPotential.Geometry Sphere
open EntropySupport
lemma log_ratio_lower {a b P : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hP : 0 < P) (hz : b = 0 → a = 0) :
    a*(Real.log P+1)-P*b ≤ a*Real.log (a/b) := by
  by_cases hb0 : b = 0
  · simp [hb0,hz hb0]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have h := xlog_lower_tangent (div_nonneg ha hb) hP
  have H := mul_le_mul_of_nonneg_left h hb
  dsimp [xlog] at H
  field_simp at H
  nlinarith

lemma log_ratio_mul {a b : ℝ} (hb : b ≠ 0) :
    a*Real.log (a/b) = xlog a-a*Real.log b := by
  by_cases ha : a = 0
  · simp [ha,xlog_zero]
  rw [Real.log_div ha hb]
  simp [xlog,mul_sub]

lemma perspective_sum_le {ι : Type*} [Fintype ι] (w x y : ι → ℝ)
    (hw : ∀ i,0 ≤ w i) (hx : ∀ i,0 ≤ x i) (hy : ∀ i,0 < y i)
    (hQ : 0 < ∑ i,w i*y i) :
    xlog (∑ i,w i*x i)-(∑ i,w i*x i)*Real.log (∑ i,w i*y i) ≤
      ∑ i,w i*(xlog (x i)-x i*Real.log (y i)) := by
  have hF0 : 0 ≤ ∑ i,w i*x i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx i))
  by_cases hF : ∑ i,w i*x i = 0
  · have hz : ∀ i,w i*x i=0 := fun i => (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i) (hx i))).mp hF i (Finset.mem_univ i)
    have hz' : ∀ i,w i*(xlog (x i)-x i*Real.log (y i))=0 := by
      intro i
      rcases mul_eq_zero.mp (hz i) with hi|hi <;> simp [hi,xlog_zero]
    simp [hF,hz',xlog_zero]
  have hFp : 0 < ∑ i,w i*x i := lt_of_le_of_ne hF0 (Ne.symm hF)
  let P := (∑ i,w i*x i)/(∑ i,w i*y i)
  have hP : 0 < P := div_pos hFp hQ
  have hi (i : ι) : w i*(x i*(Real.log P+1)-P*y i) ≤
      w i*(xlog (x i)-x i*Real.log (y i)) := by
    have h := log_ratio_lower (hx i) (hy i).le hP (fun hz => ((hy i).ne' hz).elim)
    rw [log_ratio_mul (hy i).ne'] at h
    exact mul_le_mul_of_nonneg_left h (hw i)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have he : (∑ i,w i*(x i*(Real.log P+1)-P*y i)) =
      (∑ i,w i*x i)*(Real.log P+1)-P*(∑ i,w i*y i) := by
    simp_rw [mul_sub,← mul_assoc]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at h
  have hlog : Real.log P = Real.log (∑ i,w i*x i)-Real.log (∑ i,w i*y i) :=
    Real.log_div hFp.ne' hQ.ne'
  have hmul : P*(∑ i,w i*y i)=(∑ i,w i*x i) := div_mul_cancel₀ _ hQ.ne'
  rw [hlog,hmul] at h
  dsimp [xlog] at h ⊢
  nlinarith

lemma mixture_probability {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (w : ι → ℝ) (hw0 : ∀ i,0 ≤ w i) (hw1 : ∑ i,w i=1)
    (ν : ι → Measure α) (hν : ∀ i,IsProbabilityMeasure (ν i)) :
    IsProbabilityMeasure (∑ i,ENNReal.ofReal (w i) • ν i) := by
  have (i : ι) : IsProbabilityMeasure (ν i) := hν i
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw0 i),hw1,ENNReal.ofReal_one]

lemma mixture_density {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (w : ι → ℝ) (hw0 : ∀ i,0 ≤ w i)
    (f : ι → α → ℝ) (hf : ∀ i,Measurable (f i)) (hf0 : ∀ i x,0 ≤ f i x) :
    (∑ i,ENNReal.ofReal (w i) • μ.withDensity (fun x => ENNReal.ofReal (f i x))) =
      μ.withDensity (fun x => ENNReal.ofReal (∑ i,w i*f i x)) := by
  ext s hs
  rw [Measure.finsetSum_apply,withDensity_apply _ hs]
  simp only [Measure.smul_apply,smul_eq_mul,withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw0 i) (hf0 i _)),
    ENNReal.ofReal_mul (hw0 _)]
  rw [lintegral_finsetSum (f := fun i x => ENNReal.ofReal (w i)*ENNReal.ofReal (f i x)) Finset.univ
    (fun i _ => measurable_const.mul (hf i).ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro i _
  exact (lintegral_const_mul _ (hf i).ennreal_ofReal).symm

lemma density_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ) {H : ℝ} (hfH : ∀ x,f x ≤ H) :
    μ.withDensity (fun x => ENNReal.ofReal (f x)) ≤ ENNReal.ofReal H • μ := by
  intro s
  rw [withDensity_apply' _ s,Measure.smul_apply,smul_eq_mul]
  calc
    _ ≤ ∫⁻ x in s, ENNReal.ofReal H ∂μ := lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfH x))
    _ = _ := by simp

lemma J_mixture {d q : ℕ} (hd : 16 ≤ d) (w : Fin q → ℝ) (hw : ∀ i,0 ≤ w i)
    (ν : Fin q → Measure (Ambient d)) (hνp : ∀ i,IsProbabilityMeasure (ν i))
    (hνb : ∀ i,BoundedDensity (ν i)) (s : Ambient d) :
    (J (∑ i,ENNReal.ofReal (w i) • ν i) s).toReal = ∑ i,w i*(J (ν i) s).toReal := by
  have (i : Fin q) : IsProbabilityMeasure (ν i) := hνp i
  have ht (i : Fin q) : J (ν i) s ≠ ∞ := by
    obtain ⟨H,hH,hνH⟩ := hνb i
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (bounded_J hd (ν i) hH hνH s)
  unfold J
  rw [lintegral_finsetSum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul]
  change (∑ i,ENNReal.ofReal (w i)*J (ν i) s).toReal = _
  rw [ENNReal.toReal_sum (f := fun i => ENNReal.ofReal (w i)*J (ν i) s)
    (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ht i))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw _),J]

lemma finite_convexity {d : ℕ} (hd : 16 ≤ d) (q : ℕ) (w : Fin q → ℝ)
    (hw0 : ∀ i,0 ≤ w i) (hw1 : ∑ i,w i=1)
    (ν : Fin q → Measure (Ambient d)) (hνp : ∀ i,IsProbabilityMeasure (ν i))
    (hνb : ∀ i,BoundedDensity (ν i)) :
    Phi (∑ i,ENNReal.ofReal (w i) • ν i) ≤ ∑ i,w i*Phi (ν i) := by
  have (i : Fin q) : IsProbabilityMeasure (ν i) := hνp i
  have hνb' := hνb
  choose H hH hνH using hνb'
  choose f hf hf0 hfH heq using fun i => bounded_density_representation (sphereProbability d) (ν i) (hH i) (hνH i)
  let F : Ambient d → ℝ := fun x => ∑ i,w i*f i x
  let M : ℝ := 1+∑ i,w i*H i
  let τ := ∑ i,ENNReal.ofReal (w i) • ν i
  have hτeq : τ = (sphereProbability d).withDensity (fun x => ENNReal.ofReal (F x)) := by
    dsimp [τ,F]
    simp_rw [heq]
    exact mixture_density (sphereProbability d) w hw0 f hf hf0
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ => measurable_const.mul (hf i))
  have hF0 : ∀ x,0 ≤ F x := fun x => Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) (hf0 i x))
  have hFM : ∀ x,F x ≤ M := by
    intro x
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hfH i x) (hw0 i))
    dsimp [F,M]
    linarith
  have hM : 0 < M := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hw0 i) (hH i).le)
    dsimp [M]
    linarith
  have hτH : τ ≤ ENNReal.ofReal M • sphereProbability d := by
    rw [hτeq]; exact density_bounded _ F hFM
  have hτb : BoundedDensity τ := ⟨M,hM,hτH⟩
  have : IsProbabilityMeasure τ := mixture_probability w hw0 hw1 ν hνp
  have hix : ∀ i, Integrable (fun s => xlog (f i s)-f i s*Real.log (J (ν i) s).toReal) (sphereProbability d) := by
    intro i
    apply (integrable_xlog_bounded _ _ (hf i) (hf0 i) (hfH i)).sub
    exact (integrable_log_J hd (ν i) (hνb i) _ (ae_unit_norm (by omega))).bdd_mul
      (hf i).aestronglyMeasurable (ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 i x)]; exact hfH i x))
  have hiF : Integrable (fun s => xlog (F s)-F s*Real.log (J τ s).toReal) (sphereProbability d) := by
    apply (integrable_xlog_bounded _ _ hF hF0 hFM).sub
    exact (integrable_log_J hd τ hτb _ (ae_unit_norm (by omega))).bdd_mul
      hF.aestronglyMeasurable (ae_of_all _ (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hF0 x)]; exact hFM x))
  have hpoint : ∀ᵐ s ∂sphereProbability d,
      xlog (F s)-F s*Real.log (J τ s).toReal ≤
        ∑ i,w i*(xlog (f i s)-f i s*Real.log (J (ν i) s).toReal) := by
    filter_upwards [ae_unit_norm (by omega : 0 < d)] with s hs
    have hji : ∀ i,0 < (J (ν i) s).toReal := fun i =>
      lt_of_lt_of_le (by positivity) (J_real_bounds hd (ν i) (hH i) (hνH i) s hs).1
    have hjτ : 0 < (J τ s).toReal := lt_of_lt_of_le (by positivity) (J_real_bounds hd τ hM hτH s hs).1
    have hJ := J_mixture hd w hw0 ν hνp hνb s
    change (J τ s).toReal = _ at hJ
    rw [hJ] at hjτ ⊢
    exact perspective_sum_le w (fun i => f i s) (fun i => (J (ν i) s).toReal) hw0 (fun i => hf0 i s) hji hjτ
  have h := integral_mono_ae hiF (integrable_finsetSum _ (fun i _ => (hix i).const_mul (w i))) hpoint
  rw [integral_finsetSum _ (fun i _ => (hix i).const_mul (w i))] at h
  simp only [integral_const_mul] at h
  have hrhs : (∑ i,w i*Phi (ν i)) =
      ∑ i,w i*(∫ s,xlog (f i s)-f i s*Real.log (J (ν i) s).toReal ∂sphereProbability d) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Phi_density_formula hd (f i) (hf i) (hf0 i) (hfH i) (ν i) (hνb i) (heq i)]
  change Phi τ ≤ _
  rw [Phi_density_formula hd F hF hF0 hFM τ hτb hτeq,hrhs]
  exact h

end Coercivity

theorem kernel_coercivity : CoercivityStatement := by
  refine ⟨10,by norm_num,16,?_⟩
  intro d hd
  refine ⟨?_,Coercivity.Phi_uniform_le hd,?_⟩
  · intro ν hν hνb
    have := hν
    exact Coercivity.coercivity hd ν hνb
  · exact Coercivity.finite_convexity hd

namespace Coercivity

end Coercivity

end KernelPotential

end OAI
