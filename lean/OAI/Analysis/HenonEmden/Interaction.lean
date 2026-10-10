import OAI.Analysis.HenonEmden.Energy

namespace OAI

section Interaction

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open LayerTonelli

/-- The Newton kernel, including its harmless diagonal convention. -/
def newtonKernel (n : ℕ) (z : Space n × Space n) : ℝ :=
  (newtonDenom n)⁻¹*‖z.1-z.2‖^(2-(n:ℝ))

@[fun_prop] lemma measurable_newtonKernel (n : ℕ) : Measurable (newtonKernel n) := by
  unfold newtonKernel; fun_prop
lemma newtonKernel_symm (n : ℕ) (x y : Space n) :
    newtonKernel n (x,y)=newtonKernel n (y,x) := by
  simp only [newtonKernel,norm_sub_rev x y]
lemma newtonKernel_nonneg {n : ℕ} (hn : 3 ≤ n) (z : Space n × Space n) :
    0 ≤ newtonKernel n z :=
  mul_nonneg (inv_nonneg.mpr (newtonDenom_pos hn).le) (Real.rpow_nonneg (norm_nonneg _) _)

lemma IsSolution.newton_potential_u {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {x : Space n} (hx : x ≠ 0) :
    potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) x =
      ENNReal.ofReal (u x) := by
  have hd := newtonDenom_pos (h.dimension_ge_three hn)
  have hgm := measurable_source h.continuous_v p A
  unfold potential newtonKernel
  simp_rw [ENNReal.ofReal_mul (inv_nonneg.mpr hd.le),mul_left_comm (ENNReal.ofReal (source v p A _))]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hi := ofReal_integral_eq_lintegral_ofReal (h.kernel_g_integrable hn x)
    (ae_of_all _ fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (source_nonneg (fun y => (h.positive_v y).le) p A y))
  have he : (∫⁻ y, ENNReal.ofReal (source v p A y)*ENNReal.ofReal (‖x-y‖^(2-(n:ℝ)))) =
      ENNReal.ofReal (newtonDenom n*u x) := by
    rw [h.potential_u hn hq hx]
    simp only [WeakPDE.rawPotential,finrank_euclideanSpace_fin]
    rw [hi]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),mul_comm]
  rw [he,← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]
  congr 1
  field_simp

lemma IsSolution.newton_potential_u_ae {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    ∀ᵐ x, potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) (source v p A) x =
      ENNReal.ofReal (u x) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  filter_upwards [ae_iff.mpr (by simp : volume {x : Space n | ¬ x ≠ 0}=0)] with x hx
  exact h.newton_potential_u hn hq hx

def interaction {n : ℕ} (f g : Space n → ℝ) : Measure (Space n × Space n) :=
  (volume.prod volume).withDensity (fun z => ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*
    ENNReal.ofReal (newtonKernel n z))

instance interaction_sigmaFinite {n : ℕ} (f g : Space n → ℝ) : SigmaFinite (interaction f g) := by
  unfold interaction
  apply SigmaFinite.withDensity_of_ne_top
  filter_upwards [] with z
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

lemma lintegral_interaction {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n × Space n → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ z, F z ∂interaction f g) =
      ∫⁻ z, ENNReal.ofReal (f z.1)*ENNReal.ofReal (g z.2)*ENNReal.ofReal (newtonKernel n z)*F z ∂volume.prod volume :=
  lintegral_withDensity_eq_lintegral_mul _ (by fun_prop [measurable_newtonKernel]) hF

lemma lintegral_interaction_left {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.1 ∂interaction f g) = ∫⁻ x, ENNReal.ofReal (f x)*F x*
      potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) g x := by
  rw [lintegral_interaction hf hg (by fun_prop),lintegral_prod _ (by fun_prop [measurable_newtonKernel])]
  apply lintegral_congr
  intro x
  have he (y : Space n) :
      ENNReal.ofReal (f x)*ENNReal.ofReal (g y)*ENNReal.ofReal (newtonKernel n (x,y))*F x =
      (ENNReal.ofReal (f x)*F x)*(ENNReal.ofReal (g y)*ENNReal.ofReal (newtonKernel n (x,y))) := by ring
  simp_rw [he]
  rw [lintegral_const_mul _ (by fun_prop [measurable_newtonKernel])]
  rfl

lemma lintegral_interaction_right {n : ℕ} {f g : Space n → ℝ}
    (hf : Measurable f) (hg : Measurable g) {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.2 ∂interaction f g) = ∫⁻ y, ENNReal.ofReal (g y)*F y*
      potential volume (fun z => ENNReal.ofReal (newtonKernel n z)) f y := by
  rw [lintegral_interaction hf hg (by fun_prop),← lintegral_prod_swap]
  change (∫⁻ z : Space n × Space n, ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*
    ENNReal.ofReal (newtonKernel n (z.2,z.1))*F z.1 ∂volume.prod volume) = _
  simp_rw [newtonKernel_symm n _ _]
  have he (z : Space n × Space n) :
      ENNReal.ofReal (f z.2)*ENNReal.ofReal (g z.1)*ENNReal.ofReal (newtonKernel n (z.1,z.2))*F z.1 =
      ENNReal.ofReal (g z.1)*ENNReal.ofReal (f z.2)*ENNReal.ofReal (newtonKernel n z)*F z.1 := by ring
  simp_rw [he]
  rw [← lintegral_interaction hg hf (by fun_prop)]
  exact lintegral_interaction_left hg hf hF

lemma IsSolution.interaction_left {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.1 ∂interaction (source u q B) (source v p A)) =
      ∫⁻ x, ENNReal.ofReal (source u q B x*u x)*F x := by
  rw [lintegral_interaction_left (measurable_source h.continuous_u q B) (measurable_source h.continuous_v p A) hF]
  apply lintegral_congr_ae
  filter_upwards [h.newton_potential_u_ae hn hq] with x hx
  rw [hx,ENNReal.ofReal_mul (source_nonneg (fun x => (h.positive_u x).le) q B x)]
  ring

lemma IsSolution.interaction_right {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z.2 ∂interaction (source u q B) (source v p A)) =
      ∫⁻ y, ENNReal.ofReal (source v p A y*v y)*F y := by
  rw [lintegral_interaction_right (measurable_source h.continuous_u q B) (measurable_source h.continuous_v p A) hF]
  apply lintegral_congr_ae
  filter_upwards [h.swap.newton_potential_u_ae hn hp] with y hy
  rw [hy,ENNReal.ofReal_mul (source_nonneg (fun x => (h.positive_v x).le) p A y)]
  ring

end HenonLaneEmden
end
end Interaction

end OAI
