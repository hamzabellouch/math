import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelCancellation
import OAI.Analysis.LipschitzHilbert.Fourier.LineConvolutionLocal

namespace OAI

/-! The L2 kernel commutator estimate for multiplication by a bounded
Lipschitz function. The cost is its Lipschitz bound times the first moment. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def lineMultiplicationCommutator (K b h : ℝ → ℂ) (x : ℝ) : ℂ :=
  b x*lineConvolution K h x-lineConvolution K (fun y => b y*h y) x

theorem lineMoment_dominated_energy (K : SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ)
    (F : ℝ → ℂ) (hFm : Measurable F) (L : ℝ)
    (hdom : ∀ x, ‖F x‖≤L*(∫ t, |t| *‖K t‖*‖h (x-t)‖)) :
    MemLp F 2 volume ∧ (∫ x, ‖F x‖^2)≤
      L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖h x‖^2) := by
  let a := fun t => ((|t| *‖K t‖:ℝ):ℂ)
  let v := fun x => ((‖h x‖:ℝ):ℂ)
  have ha (t : ℝ) : ‖a t‖=|t| *‖K t‖ := by
    simp only [a,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
  have hv (x : ℝ) : ‖v x‖=‖h x‖ := by
    simp only [v,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  have hai : Integrable a := (schwartz_first_absolute_moment_integrable K).ofReal
  have ham : Measurable a := by dsimp [a]; fun_prop
  have hvm : Measurable v := by dsimp [v]; fun_prop
  have hvlp : MemLp v 2 volume := (h.memLp 2 volume).norm.ofReal
  have hc := lineConvolution_energy_bound a hai ham v hvm hvlp
  have he (x : ℝ) : ‖lineConvolution a v x‖=∫ t, |t| *‖K t‖*‖h (x-t)‖ := by
    have hh : lineConvolution a v x=((∫ t, |t| *‖K t‖*‖h (x-t)‖:ℝ):ℂ) := by
      unfold lineConvolution
      simp only [a,v,←Complex.ofReal_mul]
      exact integral_ofReal
    rw [hh,Complex.norm_real,Real.norm_of_nonneg]
    exact integral_nonneg (fun _ => by positivity)
  have hp (x : ℝ) : ‖F x‖^2≤L^2*‖lineConvolution a v x‖^2 := by
    rw [←mul_pow,he]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdom x) 2
  have hi : Integrable (fun x => ‖F x‖^2) :=
    ((hc.1.integrable_norm_pow (by decide : 2≠0)).const_mul (L^2)).mono'
      (hFm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hp x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).mpr hi,?_⟩
  calc
    _ ≤ ∫ x, L^2*‖lineConvolution a v x‖^2 :=
      integral_mono hi ((hc.1.integrable_norm_pow (by decide : 2≠0)).const_mul _) hp
    _ = L^2*(∫ x, ‖lineConvolution a v x‖^2) := integral_const_mul _ _
    _ ≤ L^2*((∫ t, ‖a t‖)^2*(∫ x, ‖v x‖^2)) :=
      mul_le_mul_of_nonneg_left hc.2 (sq_nonneg L)
    _ = _ := by simp only [ha,hv]; ring

theorem lineMultiplicationCommutator_formula (K h : SchwartzMap ℝ ℂ)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B) (x : ℝ) :
    lineMultiplicationCommutator K b h x=
      ∫ t, K t*(b x-b (x-t))*h (x-t) := by
  have hh := lineConvolution_integrand_of_bounded K h K.integrable h.continuous.measurable
    (SchwartzMap.seminorm ℝ 0 0 h) (fun x => h.norm_le_seminorm ℝ x) x
  have hbh := lineConvolution_integrand_of_bounded K (fun y => b y*h y) K.integrable
    (hbm.mul h.continuous.measurable) (B*SchwartzMap.seminorm ℝ 0 0 h)
    (fun y => by rw [norm_mul]; exact mul_le_mul (hb y) (h.norm_le_seminorm ℝ y) (norm_nonneg _) hB) x
  unfold lineMultiplicationCommutator lineConvolution
  rw [←integral_const_mul,←integral_sub (hh.const_mul (b x)) hbh]
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem lineMultiplicationCommutator_energy (K h : SchwartzMap ℝ ℂ)
    (b : ℝ → ℂ) (hbm : Measurable b) (B : ℝ) (hB : 0≤B) (hb : ∀ x, ‖b x‖≤B)
    (L : ℝ) (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    MemLp (lineMultiplicationCommutator K b h) 2 volume ∧
    (∫ x, ‖lineMultiplicationCommutator K b h x‖^2)≤
      L^2*(∫ t, |t| *‖K t‖)^2*(∫ x, ‖h x‖^2) := by
  have hm : Measurable (lineMultiplicationCommutator K b h) :=
    (hbm.mul (lineConvolution_measurable K K.continuous.measurable h h.continuous.measurable)).sub
      (lineConvolution_measurable K K.continuous.measurable (fun y => b y*h y)
        (hbm.mul h.continuous.measurable))
  apply lineMoment_dominated_energy K h _ hm L
  intro x
  rw [lineMultiplicationCommutator_formula K h b hbm B hB hb]
  have hi : Integrable (fun t => |t| *‖K t‖*‖h (x-t)‖) := by
    apply ((schwartz_first_absolute_moment_integrable K).mul_const (SchwartzMap.seminorm ℝ 0 0 h)).mono'
      (by apply Measurable.aestronglyMeasurable; fun_prop)
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (h.norm_le_seminorm ℝ _) (by positivity)
  have hh := norm_integral_le_of_norm_le (hi.const_mul L)
    (Filter.Eventually.of_forall (fun t => show ‖K t*(b x-b (x-t))*h (x-t)‖≤L*(|t| *‖K t‖*‖h (x-t)‖) from by
      rw [norm_mul,norm_mul]
      have hl := hLip x (x-t)
      rw [sub_sub_cancel] at hl
      calc
        _ ≤ ‖K t‖*(L*|t|)*‖h (x-t)‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring))
  simpa only [integral_const_mul] using hh

end LipschitzHilbert.PacketRepresentation

end

end OAI
