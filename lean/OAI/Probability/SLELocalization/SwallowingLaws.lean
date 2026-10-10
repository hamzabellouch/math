import Mathlib
import OAI.Probability.SLELocalization.GreenTilts
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Swallowing estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.Swallowing
open GreenPhysical

lemma generator_eq (κ β C x y : ℝ) (hy : 0 < y) :
    generator κ β C x y =
      (x^2+y^2)^(β/2-1) *
        (β*(κ-4)/2 + β*(8-2*κ+κ*β)/2*(x^2/(x^2+y^2))) -
      (2*C*β)*y^β/(x^2+y^2) := by
  have hq := (q_pos x hy).ne'
  have hp : (x^2+y^2)^(β/2-2) = (x^2+y^2)^(β/2-1)/(x^2+y^2) := by
    rw [← Real.rpow_sub_one hq]
    congr 1
    ring
  have hyp : y^(β-1)*y = y^β := by
    conv_lhs => rhs; rw [← Real.rpow_one y]
    rw [← Real.rpow_add hy]
    congr 1
    ring
  unfold generator radialXX
  rw [hp]
  calc
    _ = (x^2+y^2)^(β/2-1)*
        (β*(κ-4)/2+β*(8-2*κ+κ*β)/2*(x^2/(x^2+y^2))) -
        2*C*β*(y^(β-1)*y)/(x^2+y^2) := by field_simp; ring
    _ = _ := by rw [hyp]

lemma radial_height_ineq {β : ℝ} (hβ : β ≤ 2) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    (x^2+y^2)^(β/2-1)*y^2 ≤ y^β := by
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hy)
    (show y^2 ≤ x^2+y^2 by nlinarith [sq_nonneg x]) (show β/2-1 ≤ 0 by linarith)
  calc
    _ ≤ (y^2)^(β/2-1)*y^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg y)
    _ = y^β := by
      rw [← Real.rpow_natCast_mul hy.le]
      conv_lhs => rhs; rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hy]
      norm_num
      congr 1
      ring

lemma generator_negative {κ β : ℝ} (hκ : 4 < κ) (hβ : 0 < β)
    (hβκ : β < 1-4/κ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    let C := (2*κ-8-κ*β)/4
    let d := β*(κ-4-κ*β)/2
    0 < C ∧ 0 < d ∧ generator κ β C x y ≤ -d*(x^2+y^2)^(β/2-1) := by
  have hk : 0 < κ := by linarith
  have hbk : κ*β < κ-4 := by
    have hh := (mul_lt_mul_of_pos_left hβκ hk)
    field_simp at hh
    linarith
  have hb2 : β ≤ 2 := by
    have h4 := div_pos (by norm_num : (0:ℝ)<4) hk
    linarith
  dsimp only
  have hC : 0 < (2*κ-8-κ*β)/4 := by linarith
  have hd : 0 < β*(κ-4-κ*β)/2 := by positivity
  refine ⟨hC,hd,?_⟩
  have he := radial_height_ineq hb2 x hy
  have hq := q_pos x hy
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ β*(2*κ-8-κ*β)/2 from div_nonneg (mul_nonneg hβ.le (by linarith)) (by norm_num))
  rw [generator_eq _ _ _ _ _ hy]
  apply (mul_le_mul_iff_left₀ hq).1
  have heq :
      ((x^2+y^2)^(β/2-1)*(β*(κ-4)/2+β*(8-2*κ+κ*β)/2*(x^2/(x^2+y^2))) -
        (2*((2*κ-8-κ*β)/4)*β)*y^β/(x^2+y^2))*(x^2+y^2) =
      -(β*(κ-4-κ*β)/2)*(x^2+y^2)^(β/2-1)*(x^2+y^2)+
        (β*(2*κ-8-κ*β)/2)*((x^2+y^2)^(β/2-1)*y^2-y^β) := by
    field_simp
    ring
  rw [heq]
  nlinarith

lemma monomial_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) {y a : ℝ} (hy : ε ≤ y)
    (n : ℕ) (ha : a+(n:ℝ)/2 ≤ 0) :
    |x|^n*(x^2+y^2)^a ≤ (ε^2)^(a+(n:ℝ)/2) := by
  have hq := q_pos x (hε.trans_le hy)
  have hx : |x| ≤ Real.sqrt (x^2+y^2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg y])
  have hl : ε^2 ≤ x^2+y^2 := by nlinarith [sq_nonneg x]
  calc
    _ ≤ (Real.sqrt (x^2+y^2))^n*(x^2+y^2)^a := by gcongr
    _ = (x^2+y^2)^(a+(n:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hq.le,← Real.rpow_add hq]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hε) hl ha

lemma radialX_bound {ε β : ℝ} (hε : 0 < ε) (hβ : β ≤ 1) (x : ℝ) {y : ℝ} (hy : ε ≤ y) :
    |radialX β x y| ≤ |β| *(ε^2)^(β/2-1/2) := by
  have hh := monomial_bound (a := β/2-1) hε x hy 1 (by norm_num; linarith)
  norm_num at hh
  rw [radialX,abs_mul,abs_mul,abs_of_nonneg (Real.rpow_nonneg (q_pos x (hε.trans_le hy)).le _)]
  have he : β/2-1+1/2 = β/2-1/2 := by ring
  rw [he] at hh
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (abs_nonneg β)

lemma radialXX_bound {ε β : ℝ} (hε : 0 < ε) (hβ : β ≤ 1) (x : ℝ) {y : ℝ} (hy : ε ≤ y) :
    |radialXX β x y| ≤ (|β|+|β*(β-2)|)*(ε^2)^(β/2-1) := by
  have h0 := monomial_bound (a := β/2-1) hε x hy 0 (by norm_num; linarith)
  have h2 := monomial_bound (a := β/2-2) hε x hy 2 (by norm_num; linarith)
  norm_num at h0 h2
  rw [show β/2-2+1 = β/2-1 by ring] at h2
  calc
    _ ≤ |β| *(x^2+y^2)^(β/2-1)+|β*(β-2)| *(|x|^2*(x^2+y^2)^(β/2-2)) := by
      unfold radialXX
      exact (abs_add_le _ _).trans_eq (by simp [abs_mul,abs_pow,abs_of_nonneg (Real.rpow_nonneg (q_pos x (hε.trans_le hy)).le _)];ring)
    _ ≤ |β| *(ε^2)^(β/2-1)+|β*(β-2)| *(ε^2)^(β/2-1) := by
      gcongr
      simpa only [sq_abs] using h2
    _ = _ := by ring

lemma radialXXX_bound {ε β : ℝ} (hε : 0 < ε) (hβ : β ≤ 1) (x : ℝ) {y : ℝ} (hy : ε ≤ y) :
    |radialXXX β x y| ≤ (|3*β*(β-2)|+|β*(β-2)*(β-4)|)*(ε^2)^(β/2-3/2) := by
  have h1 := monomial_bound (a := β/2-2) hε x hy 1 (by norm_num; linarith)
  have h3 := monomial_bound (a := β/2-3) hε x hy 3 (by norm_num; linarith)
  norm_num at h1 h3
  rw [show β/2-2+1/2 = β/2-3/2 by ring] at h1
  rw [show β/2-3+3/2 = β/2-3/2 by ring] at h3
  calc
    _ ≤ |3*β*(β-2)| *(|x| *(x^2+y^2)^(β/2-2))+
        |β*(β-2)*(β-4)| *(|x|^3*(x^2+y^2)^(β/2-3)) := by
      unfold radialXXX
      exact (abs_add_le _ _).trans_eq (by simp [abs_mul,abs_pow,abs_of_nonneg (Real.rpow_nonneg (q_pos x (hε.trans_le hy)).le _)];ring)
    _ ≤ |3*β*(β-2)| *(ε^2)^(β/2-3/2)+|β*(β-2)*(β-4)| *(ε^2)^(β/2-3/2) := by gcongr
    _ = _ := by ring

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.Swallowing
open GreenPhysical LoewnerCutoff LoewnerExit

lemma deriv_lyapunov_driver (β C c y s b : ℝ) (hy : 0 < y) :
    deriv (fun b => lyapunov β C (c-s*b) y) b = -s*radialX β (c-s*b) y := by
  have hd := ((hasDerivAt_radial_x β (c-s*b) y hy).comp b
    (((hasDerivAt_id b).const_mul s).const_sub c)).add_const (C*y^β)
  convert hd.deriv using 1 <;> simp [lyapunov]; ring

lemma second_lyapunov_driver (β C c y s b : ℝ) (hy : 0 < y) :
    iteratedDeriv 2 (fun b => lyapunov β C (c-s*b) y) b = s^2*radialXX β (c-s*b) y := by
  have he : deriv (fun b => lyapunov β C (c-s*b) y) = fun b => -s*radialX β (c-s*b) y :=
    funext (fun b => deriv_lyapunov_driver β C c y s b hy)
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  rw [he]
  have hd := ((hasDerivAt_radialX_x β (c-s*b) y hy).comp b
    (((hasDerivAt_id b).const_mul s).const_sub c)).const_mul (-s)
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1
  ring

lemma third_lyapunov_driver (β C c y s b : ℝ) (hy : 0 < y) :
    iteratedDeriv 3 (fun b => lyapunov β C (c-s*b) y) b = -s^3*radialXXX β (c-s*b) y := by
  have he : iteratedDeriv 2 (fun b => lyapunov β C (c-s*b) y) = fun b => s^2*radialXX β (c-s*b) y :=
    funext (fun b => second_lyapunov_driver β C c y s b hy)
  rw [show (3:ℕ)=2+1 by rfl,iteratedDeriv_succ,he]
  have hd := ((hasDerivAt_radialXX_x β (c-s*b) y hy).comp b
    (((hasDerivAt_id b).const_mul s).const_sub c)).const_mul (s^2)
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1
  ring

lemma continuous_radial_comp {α : Type*} [TopologicalSpace α] {X Y : α → ℝ}
    (hX : Continuous X) (hY : Continuous Y) (hy : ∀ a, 0 < Y a) (β : ℝ) :
    Continuous (fun a => radial β (X a) (Y a)) := by
  exact ((hX.pow 2).add (hY.pow 2)).rpow_const (fun a => Or.inl (q_pos _ (hy a)).ne')

lemma continuous_radialX_comp {α : Type*} [TopologicalSpace α] {X Y : α → ℝ}
    (hX : Continuous X) (hY : Continuous Y) (hy : ∀ a, 0 < Y a) (β : ℝ) :
    Continuous (fun a => radialX β (X a) (Y a)) := by
  exact (continuous_const.mul hX).mul (((hX.pow 2).add (hY.pow 2)).rpow_const
    (fun a => Or.inl (q_pos _ (hy a)).ne'))

lemma continuous_radialXX_comp {α : Type*} [TopologicalSpace α] {X Y : α → ℝ}
    (hX : Continuous X) (hY : Continuous Y) (hy : ∀ a, 0 < Y a) (β : ℝ) :
    Continuous (fun a => radialXX β (X a) (Y a)) := by
  have hp (e : ℝ) := ((hX.pow 2).add (hY.pow 2)).rpow_const (p := e)
    (fun a => Or.inl (q_pos _ (hy a)).ne')
  exact (continuous_const.mul (hp _)).add ((continuous_const.mul (hX.pow 2)).mul (hp _))

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.Swallowing
open GreenPhysical LoewnerCutoff LoewnerExit
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

def field (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) : ℝ :=
  lyapunov β C ((position hε hT U z t).re-s*b) (LoewnerField.height hε hT U z t)

def drift (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) : ℝ :=
  let x := (position hε hT U z t).re-s*b
  let y := LoewnerField.height hε hT U z t
  let v := velocity ε (extendDriver T U t) (position hε hT U z t)
  β*(x*v.re+y*v.im)*(x^2+y^2)^(β/2-1)+C*(β*y^(β-1)*v.im)

lemma first_eq (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    iteratedDeriv 1 (field hε hT β C s U z t) b =
      -s*radialX β ((position hε hT U z t).re-s*b) (LoewnerField.height hε hT U z t) := by
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  exact deriv_lyapunov_driver _ _ _ _ _ _ (LoewnerField.height_pos hε hT U z t)

lemma second_eq (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    iteratedDeriv 2 (field hε hT β C s U z t) b =
      s^2*radialXX β ((position hε hT U z t).re-s*b) (LoewnerField.height hε hT U z t) :=
  second_lyapunov_driver _ _ _ _ _ _ (LoewnerField.height_pos hε hT U z t)

lemma third_eq (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    iteratedDeriv 3 (field hε hT β C s U z t) b =
      -s^3*radialXXX β ((position hε hT U z t).re-s*b) (LoewnerField.height hε hT U z t) :=
  third_lyapunov_driver _ _ _ _ _ _ (LoewnerField.height_pos hε hT U z t)

lemma smooth (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    ContDiff ℝ 3 (field hε hT β C s U z t) := by
  exact ((contDiff_radial_driver β _ _ s (LoewnerField.height_pos hε hT U z t)).of_le (by simp)).add contDiff_const

lemma coeff_uniform_bound (β C s : ℝ) (hβ : β ≤ 1) (z : ℂ) (k : ℕ)
    (hk : k=1 ∨ k=2 ∨ k=3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : C(I, ℝ)) (t b : ℝ),
      |iteratedDeriv k (field hε hT β C s U z t) b| ≤ K := by
  rcases hk with rfl|rfl|rfl
  · refine ⟨|s| * (|β| * (ε^2)^(β/2-1/2)),by positivity,?_⟩
    intro U t b
    rw [first_eq,abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left (radialX_bound hε hβ _ (le_max_left _ _)) (abs_nonneg _)
  · refine ⟨|s|^2*((|β|+|β*(β-2)|)*(ε^2)^(β/2-1)),by positivity,?_⟩
    intro U t b
    rw [second_eq,abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (radialXX_bound hε hβ _ (le_max_left _ _)) (by positivity)
  · refine ⟨|s|^3*((|3*β*(β-2)|+|β*(β-2)*(β-4)|)*(ε^2)^(β/2-3/2)),by positivity,?_⟩
    intro U t b
    rw [third_eq,abs_mul,abs_neg,abs_pow]
    exact mul_le_mul_of_nonneg_left (radialXXX_bound hε hβ _ (le_max_left _ _)) (by positivity)

lemma continuous_field (β C s : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => field hε hT β C s q.1.1 z q.1.2 q.2) := by
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => LoewnerField.height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  exact (continuous_radial_comp hx hy (fun q => LoewnerField.height_pos hε hT q.1.1 z q.1.2) β).add
    (continuous_const.mul (hy.rpow_const (fun q => Or.inl (LoewnerField.height_pos hε hT q.1.1 z q.1.2).ne')))

lemma continuous_coeff (β C s : ℝ) (z : ℂ) (k : ℕ) (hk : k=1 ∨ k=2) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => iteratedDeriv k (field hε hT β C s q.1.1 z q.1.2) q.2) := by
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => LoewnerField.height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  rcases hk with rfl|rfl
  · simp only [first_eq]
    exact continuous_const.mul (continuous_radialX_comp hx hy (fun q => LoewnerField.height_pos hε hT q.1.1 z q.1.2) β)
  · simp only [second_eq]
    exact continuous_const.mul (continuous_radialXX_comp hx hy (fun q => LoewnerField.height_pos hε hT q.1.1 z q.1.2) β)

lemma continuous_drift (β C s : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => drift hε hT β C s q.1.1 z q.1.2 q.2) := by
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hD := (continuous_joint_extendDriver T).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hV := (continuous_velocity hε).comp (hD.prodMk hH)
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => LoewnerField.height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  have hp (e : ℝ) := ((hx.pow 2).add (hy.pow 2)).rpow_const (p := e)
    (fun q => Or.inl (q_pos _ (LoewnerField.height_pos hε hT q.1.1 z q.1.2)).ne')
  exact ((continuous_const.mul ((hx.mul (Complex.continuous_re.comp hV)).add
    (hy.mul (Complex.continuous_im.comp hV)))).mul (hp _)).add
    (continuous_const.mul ((continuous_const.mul (hy.rpow_const (fun q =>
      Or.inl (LoewnerField.height_pos hε hT q.1.1 z q.1.2).ne'))).mul (Complex.continuous_im.comp hV)))

lemma time_deriv (β C s : ℝ) (U : C(I, ℝ)) (z : ℂ) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (hy : ε < (position hε hT U z t).im) (b : ℝ) :
    HasDerivAt (fun v => field hε hT β C s U z v b) (drift hε hT β C s U z t b) t := by
  have hH := position_deriv hε hT U z ht
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hH
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hH
  dsimp only [Function.comp_def,Complex.imCLM_apply,Complex.reCLM_apply] at hIm hRe
  have hY : HasDerivAt (LoewnerField.height hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)).im t := by
    apply hIm.congr_of_eventuallyEq
    filter_upwards [hIm.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hy)] with s hs
    exact max_eq_right hs.le
  have hR := hasDerivAt_radial_path β (hRe.sub_const (s*b)) hY (LoewnerField.height_pos hε hT U z t)
  have hP := hY.rpow_const (p := β) (Or.inl (LoewnerField.height_pos hε hT U z t).ne')
  apply (hR.add (hP.const_mul C)).congr_deriv
  dsimp only [drift]
  ring

lemma regular (hTp : 0 < T) (β C s : ℝ) (hβ : β ≤ 1) (U : C(I, ℝ)) (z : ℂ)
    (ρ δ : ℝ) (b : ℝ → ℝ) (hb : Continuous b) :
    BrownianField.FieldRegular (field hε hT β C s U z) (drift hε hT β C s U z) b
      (stop hε hT U z ρ δ) := by
  constructor
  · exact smooth hε hT β C s U z
  · obtain ⟨K,hK,hb⟩ := coeff_uniform_bound hε hT β C s hβ z 3 (Or.inr (Or.inr rfl))
    exact ⟨K,hK,hb U⟩
  · intro x
    exact ((continuous_field hε hT β C s z).comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)).continuousOn
  · intro t ht x
    have htT : t ∈ Ioo 0 T := ⟨ht.1,ht.2.trans_le (stop_bounds hε hT U z ρ δ).2⟩
    have hh := (deficit_pos_iff hε hT U z ρ δ t).1
      (positive_before hε hT hTp U z ρ δ ht.1.le ht.2)
    exact time_deriv hε hT β C s U z htT hh.2.1 x
  · exact ((continuous_drift hε hT β C s z).comp
      ((continuous_const.prodMk continuous_fst).prodMk (hb.comp continuous_snd))).continuousOn
  · exact ((continuous_coeff hε hT β C s z 2 (Or.inr rfl)).comp
      ((continuous_const.prodMk continuous_id).prodMk hb)).continuousOn

lemma field_prefix_eq {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (U V : C(I, ℝ))
    (z : ℂ) (β C s : ℝ) (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    field hε hS β C s U z t = field hε hT β C s V z t := by
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V z hUV ht
  ext b
  simp only [field,LoewnerField.height,hH]

end SLEExactGauge.Swallowing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing GreenPhysical
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

def factor (β a : ℝ) (U : C(I, ℝ)) (x t : ℝ) : ℝ :=
  Real.exp ((a*β/2)*logDerivative hε hT U (x:ℂ) t)

def field (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) : ℝ :=
  factor hε hT β a U x t * radial (-β) ((position hε hT U (x:ℂ) t).re-s*b) ε

def drift (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) : ℝ :=
  let X := (position hε hT U (x:ℂ) t).re-s*b
  factor hε hT β a U x t *
    ((a*β/2)*variation hε hT U (x:ℂ) t * radial (-β) X ε +
    radialX (-β) X ε * (velocity ε (extendDriver T U t) (position hε hT U (x:ℂ) t)).re)

lemma factor_pos (β a : ℝ) (U : C(I, ℝ)) (x t : ℝ) :
    0 < factor hε hT β a U x t := Real.exp_pos _

lemma field_pos (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) :
    0 < field hε hT β a s U x t b :=
  mul_pos (factor_pos hε hT β a U x t) (radial_pos _ _ hε)

lemma factor_bound (β a : ℝ) (U : C(I, ℝ)) (x t : ℝ) :
    factor hε hT β a U x t ≤ Real.exp (|a*β/2| *((2/ε^2)*T)) := by
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans
    (mul_le_mul_of_nonneg_left (abs_logDerivative_le hε hT U (x:ℂ) t) (abs_nonneg _)))

lemma first_eq (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) :
    iteratedDeriv 1 (field hε hT β a s U x t) b =
      factor hε hT β a U x t * (-s*radialX (-β) ((position hε hT U (x:ℂ) t).re-s*b) ε) := by
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  have hd := ((hasDerivAt_radial_x (-β) _ ε hε).comp b
    (((hasDerivAt_id b).const_mul s).const_sub ((position hε hT U (x:ℂ) t).re))).const_mul (factor hε hT β a U x t)
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1 <;> first | rfl | ring

lemma second_eq (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) :
    iteratedDeriv 2 (field hε hT β a s U x t) b =
      factor hε hT β a U x t * (s^2*radialXX (-β) ((position hε hT U (x:ℂ) t).re-s*b) ε) := by
  have he := funext (first_eq hε hT β a s U x t)
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,he]
  have hd := (((hasDerivAt_radialX_x (-β) _ ε hε).comp b
    (((hasDerivAt_id b).const_mul s).const_sub ((position hε hT U (x:ℂ) t).re))).const_mul (-s)).const_mul (factor hε hT β a U x t)
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1
  first | rfl | ring

lemma third_eq (β a s : ℝ) (U : C(I, ℝ)) (x t b : ℝ) :
    iteratedDeriv 3 (field hε hT β a s U x t) b =
      factor hε hT β a U x t * (-s^3*radialXXX (-β) ((position hε hT U (x:ℂ) t).re-s*b) ε) := by
  have he := funext (second_eq hε hT β a s U x t)
  rw [show (3:ℕ)=2+1 by rfl,iteratedDeriv_succ,he]
  have hd := (((hasDerivAt_radialXX_x (-β) _ ε hε).comp b
    (((hasDerivAt_id b).const_mul s).const_sub ((position hε hT U (x:ℂ) t).re))).const_mul (s^2)).const_mul (factor hε hT β a U x t)
  simp only [Function.comp_def,id_eq] at hd
  convert hd.deriv using 1
  first | rfl | ring

lemma smooth (β a s : ℝ) (U : C(I, ℝ)) (x t : ℝ) :
    ContDiff ℝ 3 (field hε hT β a s U x t) :=
  contDiff_const.mul ((contDiff_radial_driver (-β) _ ε s hε).of_le (by simp))

lemma coeff_uniform_bound (β a s : ℝ) (hβ : 0 ≤ β) (x : ℝ) (k : ℕ)
    (hk : k=1 ∨ k=2 ∨ k=3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : C(I, ℝ)) (t b : ℝ),
      |iteratedDeriv k (field hε hT β a s U x t) b| ≤ K := by
  let E := Real.exp (|a*β/2| *((2/ε^2)*T))
  have hβ' : -β ≤ 1 := by linarith
  have hf (U : C(I, ℝ)) (t : ℝ) : |factor hε hT β a U x t| ≤ E := by
    rw [abs_of_pos (factor_pos hε hT β a U x t)]
    exact factor_bound hε hT β a U x t
  rcases hk with rfl|rfl|rfl
  · refine ⟨E*(|s| *(|-β| *(ε^2)^((-β)/2-1/2))),by positivity,?_⟩
    intro U t b
    rw [first_eq,abs_mul,abs_mul,abs_neg]
    exact mul_le_mul (hf U t) (mul_le_mul_of_nonneg_left
      (radialX_bound hε hβ' _ le_rfl) (abs_nonneg _)) (by positivity) (by positivity)
  · refine ⟨E*(|s|^2*((|-β|+|(-β)*(-β-2)|)*(ε^2)^((-β)/2-1))),by positivity,?_⟩
    intro U t b
    rw [second_eq,abs_mul,abs_mul,abs_pow]
    exact mul_le_mul (hf U t) (mul_le_mul_of_nonneg_left
      (radialXX_bound hε hβ' _ le_rfl) (by positivity)) (by positivity) (by positivity)
  · refine ⟨E*(|s|^3*((|3*(-β)*(-β-2)|+|(-β)*(-β-2)*(-β-4)|)*(ε^2)^((-β)/2-3/2))),by positivity,?_⟩
    intro U t b
    rw [third_eq,abs_mul,abs_mul,abs_neg,abs_pow]
    exact mul_le_mul (hf U t) (mul_le_mul_of_nonneg_left
      (radialXXX_bound hε hβ' _ le_rfl) (by positivity)) (by positivity) (by positivity)

lemma continuous_factor (β a x : ℝ) :
    Continuous (fun q : C(I, ℝ) × ℝ => factor hε hT β a q.1 x q.2) :=
  Real.continuous_exp.comp (continuous_const.mul (continuous_logDerivative hε hT (x:ℂ)))

lemma continuous_field (β a s x : ℝ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => field hε hT β a s q.1.1 x q.1.2 q.2) := by
  have hH := (continuous_position hε hT (x:ℂ)).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  exact ((continuous_factor hε hT β a x).comp continuous_fst).mul
    (continuous_radial_comp hx continuous_const (fun _ => hε) (-β))

lemma continuous_coeff (β a s x : ℝ) (k : ℕ) (hk : k=1 ∨ k=2) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => iteratedDeriv k (field hε hT β a s q.1.1 x q.1.2) q.2) := by
  have hH := (continuous_position hε hT (x:ℂ)).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  rcases hk with rfl|rfl
  · simp only [first_eq]
    exact ((continuous_factor hε hT β a x).comp continuous_fst).mul
      (continuous_const.mul (continuous_radialX_comp hx continuous_const (fun _ => hε) (-β)))
  · simp only [second_eq]
    exact ((continuous_factor hε hT β a x).comp continuous_fst).mul
      (continuous_const.mul (continuous_radialXX_comp hx continuous_const (fun _ => hε) (-β)))

lemma continuous_drift (β a s x : ℝ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => drift hε hT β a s q.1.1 x q.1.2 q.2) := by
  have hH := (continuous_position hε hT (x:ℂ)).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hD := (continuous_joint_extendDriver T).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hV := (continuous_velocity hε).comp (hD.prodMk hH)
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => s*q.2))
  have hR := continuous_radial_comp hx continuous_const (fun _ => hε) (-β)
  have hRX := continuous_radialX_comp hx continuous_const (fun _ => hε) (-β)
  exact ((continuous_factor hε hT β a x).comp continuous_fst).mul
    (((continuous_const.mul ((continuous_variation hε hT (x:ℂ)).comp continuous_fst)).mul hR).add
    (hRX.mul (Complex.continuous_re.comp hV)))

lemma time_deriv (β a s : ℝ) (U : C(I, ℝ)) (x : ℝ) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (b : ℝ) :
    HasDerivAt (fun v => field hε hT β a s U x v b) (drift hε hT β a s U x t b) t := by
  have hH := position_deriv hε hT U (x:ℂ) ht
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hH
  dsimp only [Function.comp_def,Complex.reCLM_apply] at hRe
  have hR := (hasDerivAt_radial_x (-β) _ ε hε).comp t (hRe.sub_const (s*b))
  have hD := ((hasDerivAt_logDerivative hε hT U (x:ℂ) ht).const_mul (a*β/2)).exp
  apply (hD.mul hR).congr_deriv
  dsimp only [field,drift,factor,Function.comp_def]
  ring

lemma field_prefix_eq {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (U V : C(I, ℝ))
    (x β a s : ℝ) (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    field hε hS β a s U x t = field hε hT β a s V x t := by
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V (x:ℂ) hUV ht
  have hD := logDerivative_prefix_eq hε hS hT hS le_rfl hST U V (x:ℂ) hUV ht
  ext b
  simp only [field,factor,hH,hD]

def gap (U : C(I, ℝ)) (x t : ℝ) : ℝ :=
  (position hε hT U (x:ℂ) t).re-extendDriver T U t

def weight (U : C(I, ℝ)) (x β a t : ℝ) : ℝ :=
  factor hε hT β a U x t * radial (-β) (gap hε hT U x t) ε

def deficit (U : C(I, ℝ)) (x β a L t : ℝ) : ℝ :=
  min (gap hε hT U x t-ε) (L-weight hε hT U x β a t)

lemma continuous_gap (x : ℝ) :
    Continuous (fun q : C(I, ℝ) × ℝ => gap hε hT q.1 x q.2) :=
  (Complex.continuous_re.comp (continuous_position hε hT (x:ℂ))).sub
    (continuous_joint_extendDriver T)

lemma continuous_weight (x β a : ℝ) :
    Continuous (fun q : C(I, ℝ) × ℝ => weight hε hT q.1 x β a q.2) :=
  (continuous_factor hε hT β a x).mul
    (continuous_radial_comp (continuous_gap hε hT x) continuous_const (fun _ => hε) (-β))

lemma continuous_deficit (x β a L : ℝ) :
    Continuous (fun q : C(I, ℝ) × ℝ => deficit hε hT q.1 x β a L q.2) :=
  ((continuous_gap hε hT x).sub continuous_const).min
    (continuous_const.sub (continuous_weight hε hT x β a))

lemma deficit_pos_iff (U : C(I, ℝ)) (x β a L t : ℝ) :
    0 < deficit hε hT U x β a L t ↔
      ε < gap hε hT U x t ∧ weight hε hT U x β a t < L := by
  simp only [deficit,lt_min_iff,sub_pos]

lemma deficit_nonneg_iff (U : C(I, ℝ)) (x β a L t : ℝ) :
    0 ≤ deficit hε hT U x β a L t ↔
      ε ≤ gap hε hT U x t ∧ weight hε hT U x β a t ≤ L := by
  simp only [deficit,le_min_iff,sub_nonneg]

def exitPath (U : C(I, ℝ)) (x β a L : ℝ) : C(I, ℝ) := by
  refine ⟨fun q => deficit hε hT U x β a L (T*q), ?_⟩
  have hp : Continuous (fun q : I => (U,T*q)) :=
    continuous_const.prodMk (continuous_const.mul continuous_subtype_val)
  have hc := (continuous_deficit hε hT x β a L).comp hp
  dsimp only [Function.comp_def] at hc
  exact hc

def stop (U : C(I, ℝ)) (x β a L : ℝ) : ℝ :=
  T * ContinuousExit.time (exitPath hε hT U x β a L)

lemma stop_bounds (U : C(I, ℝ)) (x β a L : ℝ) :
    stop hε hT U x β a L ∈ Icc 0 T := by
  have hh := ContinuousExit.time_bounds (exitPath hε hT U x β a L)
  exact ⟨mul_nonneg hT hh.1, by simpa only [stop, mul_one] using mul_le_mul_of_nonneg_left hh.2 hT⟩

lemma exitPath_extend (U : C(I, ℝ)) (x β a L : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ContinuousExit.extend (exitPath hε hT U x β a L) t = deficit hε hT U x β a L (T*t) := by
  simpa only [exitPath, ContinuousMap.coe_mk] using ContinuousExit.extend_coe
    (exitPath hε hT U x β a L) (⟨t,ht⟩ : I)

lemma exitPath_extend_div (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContinuousExit.extend (exitPath hε hT U x β a L) (t/T) = deficit hε hT U x β a L t := by
  rw [exitPath_extend hε hT U x β a L
    ⟨div_nonneg ht.1 hT, (div_le_one hTp).2 ht.2⟩, mul_div_cancel₀ _ hTp.ne']

lemma positive_before (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htτ : t < stop hε hT U x β a L) :
    0 < deficit hε hT U x β a L t := by
  rw [← exitPath_extend_div hε hT hTp U x β a L ⟨ht,htτ.le.trans (stop_bounds hε hT U x β a L).2⟩]
  apply ContinuousExit.positive_before (div_nonneg ht hT)
  exact (div_lt_iff₀ hTp).2 (by simpa only [stop, mul_comm] using htτ)

lemma stop_pos (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    (h0 : 0 < deficit hε hT U x β a L 0) : 0 < stop hε hT U x β a L := by
  apply mul_pos hTp (ContinuousExit.time_pos _)
  simpa only [exitPath_extend hε hT U x β a L ⟨le_rfl,zero_le_one⟩, mul_zero] using h0

lemma nonneg_until (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    (h0 : 0 < deficit hε hT U x β a L 0) {t : ℝ}
    (ht : t ∈ Icc 0 (stop hε hT U x β a L)) : 0 ≤ deficit hε hT U x β a L t := by
  rw [← exitPath_extend_div hε hT hTp U x β a L ⟨ht.1,ht.2.trans (stop_bounds hε hT U x β a L).2⟩]
  apply ContinuousExit.nonneg_until
  · simpa only [exitPath_extend hε hT U x β a L ⟨le_rfl,zero_le_one⟩, mul_zero] using h0
  · exact ⟨div_nonneg ht.1 hT, (div_le_iff₀ hTp).2 (by simpa only [stop, mul_comm] using ht.2)⟩

lemma nonpos_at_of_lt (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    (hτ : stop hε hT U x β a L < T) :
    deficit hε hT U x β a L (stop hε hT U x β a L) ≤ 0 := by
  have hs : ContinuousExit.time (exitPath hε hT U x β a L) < 1 := by
    apply (mul_lt_mul_iff_right₀ hTp).mp
    simpa only [mul_one, stop] using hτ
  exact (exitPath_extend hε hT U x β a L (ContinuousExit.time_bounds _)) ▸
    ContinuousExit.nonpos_at_of_lt_one hs

lemma lt_stop_iff (hTp : 0 < T) (U : C(I, ℝ)) (x β a L : ℝ)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    t < stop hε hT U x β a L ↔ ∀ s ∈ Icc 0 t, 0 < deficit hε hT U x β a L s := by
  constructor
  · intro hh s hs
    exact positive_before hε hT hTp U x β a L hs.1 (hs.2.trans_lt hh)
  · intro hh
    change t < T * ContinuousExit.time (exitPath hε hT U x β a L)
    rw [mul_comm]
    apply (div_lt_iff₀ hTp).1
    apply (ContinuousExit.lt_time_iff (p := exitPath hε hT U x β a L)
      ⟨div_nonneg ht.1 hT, (div_lt_one hTp).2 ht.2⟩).2
    intro s hs
    rw [exitPath_extend hε hT U x β a L
      ⟨hs.1, hs.2.trans ((div_le_one hTp).2 ht.2.le)⟩]
    apply hh
    exact ⟨mul_nonneg hT hs.1, (mul_le_mul_of_nonneg_left hs.2 hT).trans_eq
      (mul_div_cancel₀ _ hTp.ne')⟩

lemma isOpen_positive_on (x β a L t : ℝ) :
    IsOpen {U : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < deficit hε hT U x β a L s} := by
  let S : Set (C(I, ℝ) × Icc 0 t) := {q | deficit hε hT q.1 x β a L q.2 ≤ 0}
  have hmap : Continuous (fun q : C(I, ℝ) × Icc 0 t => (q.1,(q.2:ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hd := (continuous_deficit hε hT x β a L).comp hmap
  dsimp only [Function.comp_def] at hd
  have hc : IsClosed S := isClosed_le hd continuous_const
  have hh := isClosedMap_fst_of_compactSpace S hc
  have he : {U : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < deficit hε hT U x β a L s} = (Prod.fst '' S)ᶜ := by
    ext U
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, S, not_exists, not_and]
    constructor
    · intro hp q hq hqp
      subst U
      exact (not_lt_of_ge hq) (hp q.2 q.2.property)
    · intro hp s hs
      by_contra hn
      exact hp (U,⟨s,hs⟩) (not_lt.1 hn) rfl
  rw [he]
  exact hh.isOpen_compl

lemma deficit_prefix_eq {S : ℝ} (hS : 0 ≤ S) (hST : S ≤ T) (U V : C(I, ℝ))
    (x β a L : ℝ) (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S)) :
    EqOn (deficit hε hS U x β a L) (deficit hε hT V x β a L) (Icc 0 S) := by
  intro t ht
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V (x:ℂ) hUV ht
  have hD := logDerivative_prefix_eq hε hS hT hS le_rfl hST U V (x:ℂ) hUV ht
  simp only [deficit,weight,factor,gap,hH,hD,hUV ht]

lemma regular (_hTp : 0 < T) (β a s : ℝ) (hβ : 0 ≤ β) (U : C(I, ℝ)) (x L : ℝ)
    (b : ℝ → ℝ) (hb : Continuous b) :
    BrownianField.FieldRegular (field hε hT β a s U x) (drift hε hT β a s U x) b
      (stop hε hT U x β a L) := by
  constructor
  · exact smooth hε hT β a s U x
  · obtain ⟨K,hK,hb⟩ := coeff_uniform_bound hε hT β a s hβ x 3 (Or.inr (Or.inr rfl))
    exact ⟨K,hK,hb U⟩
  · intro v
    exact ((continuous_field hε hT β a s x).comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)).continuousOn
  · intro t ht v
    exact time_deriv hε hT β a s U x ⟨ht.1,ht.2.trans_le (stop_bounds hε hT U x β a L).2⟩ v
  · exact ((continuous_drift hε hT β a s x).comp
      ((continuous_const.prodMk continuous_fst).prodMk (hb.comp continuous_snd))).continuousOn
  · exact ((continuous_coeff hε hT β a s x 2 (Or.inr rfl)).comp
      ((continuous_const.prodMk continuous_id).prodMk hb)).continuousOn

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
variable {ε : ℝ} (hε : 0 < ε)

def coeffAt (k : ℕ) (s : ℝ≥0) (β a sdev : ℝ) (x : ℝ) (L : ℝ)
    (q : C(I, ℝ) × ℝ) : ℝ := by
  classical
  exact if ∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg q.1 x β a L t then
    iteratedDeriv k (field hε s.coe_nonneg β a sdev q.1 x s) q.2 else 0

lemma coeffAt_measurable (k : ℕ) (hk : k = 1 ∨ k = 2) (s : ℝ≥0)
    (β a sdev : ℝ) (x : ℝ) (L : ℝ) :
    @Measurable (C(I, ℝ) × ℝ) ℝ (@Prod.instMeasurableSpace _ _ (borel _) inferInstance) _ (coeffAt hε k s β a sdev x L) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hc : Continuous (fun q : C(I, ℝ) × ℝ =>
      iteratedDeriv k (field hε s.coe_nonneg β a sdev q.1 x s) q.2) := by
    have hp : Continuous (fun q : C(I, ℝ) × ℝ => ((q.1,(s:ℝ)),q.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    have hh := (continuous_coeff hε s.coe_nonneg β a sdev x k hk).comp hp
    dsimp only [Function.comp_def] at hh
    exact hh
  apply hc.measurable.ite _ measurable_const
  exact ((isOpen_positive_on hε s.coe_nonneg x β a L s).preimage continuous_fst).measurableSet

def rawCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (β a sdev : ℝ) (x : ℝ) (L : ℝ) (sample : Ω) : ℝ :=
  if s < T then coeffAt hε k s β a sdev x L (BrownianDriver.path B sdev s sample, B s sample) else 0

lemma rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k = 1 ∨ k = 2) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (β a sdev : ℝ) (x : ℝ) (L : ℝ) :
    Measurable[pastSigma B s] (rawCoeff hε k B T s β a sdev x L) := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s β a sdev x L).comp
      ((BrownianDriver.path_measurable_past B sdev s).prodMk (past_measurable_eval B (s := s) le_rfl))
  · exact measurable_const

lemma rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (T s : ℝ≥0)
    (β a sdev : ℝ) (x : ℝ) (L : ℝ) :
    AEMeasurable (rawCoeff hε k B T s β a sdev x L) P := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s β a sdev x L).comp_aemeasurable
      ((BrownianDriver.path_aemeasurable hB sdev s).prodMk (hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable)
  · exact aemeasurable_const

lemma rawCoeff_eq {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hT : 0 < (T:ℝ)) (β a sdev : ℝ) (x : ℝ) (L : ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    rawCoeff hε k B T s β a sdev x L sample =
      if (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) x β a L then
        iteratedDeriv k (field hε T.coe_nonneg β a sdev (BrownianDriver.path B sdev T sample) x s) (B s sample) else 0 := by
  classical
  by_cases hsT : s < T
  · have he := BrownianDriver.prefix_eq B sdev s T sample hc hsT.le
    have hf := field_prefix_eq hε T.coe_nonneg s.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) x β a sdev he
      ⟨s.coe_nonneg, le_rfl⟩
    have hd := deficit_prefix_eq hε T.coe_nonneg s.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) x β a L he
    have hi : (∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg (BrownianDriver.path B sdev s sample) x β a L t) ↔
        (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) x β a L := by
      rw [lt_stop_iff hε T.coe_nonneg hT _ x β a L ⟨s.coe_nonneg,hsT⟩]
      exact forall₂_congr (fun t ht => by rw [hd ht])
    simp only [rawCoeff, ite_eq_left hsT, coeffAt, hi, hf]
  · have hstop : ¬ (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) x β a L :=
      not_lt_of_ge ((stop_bounds hε T.coe_nonneg _ x β a L).2.trans (not_lt.1 hsT))
    simp only [rawCoeff, ite_eq_right hsT, ite_eq_right hstop]

lemma rawCoeff_stoppedCoeff_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (T : ℝ≥0)
    (hT : 0 < (T:ℝ)) (β a sdev : ℝ) (x : ℝ) (L : ℝ) (n i : ℕ) :
    rawCoeff hε k B T (dyadicTime T n i) β a sdev x L =ᵐ[P]
      stoppedCoeff k B T
        (fun sample => stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) x β a L)
        (fun sample => field hε T.coe_nonneg β a sdev (BrownianDriver.path B sdev T sample) x) n i := by
  filter_upwards [hB.cont] with sample hc
  rw [rawCoeff_eq hε k B T _ hT β a sdev x L sample hc]
  simp only [stoppedCoeff, coe_dyadicTime]

theorem localized_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (β a sdev : ℝ) (hβ : 0 ≤ β)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (x : ℝ) (L : ℝ) :
    let U := BrownianDriver.path B sdev T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) x β a L
    let F := fun sample => field hε T.coe_nonneg β a sdev (U sample) x
    let V := fun sample => drift hε T.coe_nonneg β a sdev (U sample) x
    let Y := fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)
    Integrable Y P ∧ (∫ sample, Y sample ∂P) = 0 := by
  dsimp only
  let U := BrownianDriver.path B sdev T
  let τ := fun sample => stop hε T.coe_nonneg (U sample) x β a L
  let F := fun sample => field hε T.coe_nonneg β a sdev (U sample) x
  let V := fun sample => drift hε T.coe_nonneg β a sdev (U sample) x
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact regular hε T.coe_nonneg hT β a sdev hβ (U sample) x L _
      (hc.comp continuous_real_toNNReal)
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => stop_bounds hε T.coe_nonneg (U sample) x β a L)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg β a sdev hβ x 1 (Or.inl rfl)
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg β a sdev hβ x 2 (Or.inr (Or.inl rfl))
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg β a sdev W x t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => rawCoeff hε 1 B T (dyadicTime T n i) β a sdev x L
  let Q := fun n i => rawCoeff hε 2 B T (dyadicTime T n i) β a sdev x L
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 1 T hT β a sdev x L n i
  have hCe (n i : ℕ) : Q n i =ᵐ[P] stoppedCoeff 2 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 2 T hT β a sdev x L n i
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    rawCoeff_measurable_past hε 1 (Or.inl rfl) B T _ _ _ _ x L
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) :=
    rawCoeff_measurable_past hε 2 (Or.inr rfl) B T _ _ _ _ x L
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 1 (Or.inl rfl) T _ _ _ _ x L).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 2 (Or.inr rfl) T _ _ _ _ x L).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |Q n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_field_ito_centered_ae hB T τ F V htau hreg A Q hAe hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) hAm hA2 K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  exact hi

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BoundaryGreen
open Swallowing GreenPhysical

def generator (κ β a x ε : ℝ) : ℝ :=
  -(a*β/x^2)*radial (-β) x ε + radialX (-β) x ε*(2/x)+κ/2*radialXX (-β) x ε

lemma generator_factor (κ β a x ε : ℝ) (hx : 0 < x) (hε : 0 < ε) :
    generator κ β a x ε = β*(x^2+ε^2)^((-β)/2-2)/x^2 *
      ((κ*(β+1)/2-2-a)*x^4-(2+κ/2+2*a)*x^2*ε^2-a*ε^4) := by
  have hq := (q_pos x hε).ne'
  have hp₁ : (x^2+ε^2)^((-β)/2-1) = (x^2+ε^2)^((-β)/2-2)*(x^2+ε^2) := by
    conv_rhs => rhs; rw [← Real.rpow_one (x^2+ε^2)]
    rw [← Real.rpow_add (q_pos x hε)]
    congr 1
    ring
  have hp₀ : (x^2+ε^2)^((-β)/2) = (x^2+ε^2)^((-β)/2-2)*(x^2+ε^2)^2 := by
    conv_rhs => rhs; rw [← Real.rpow_natCast]
    rw [← Real.rpow_add (q_pos x hε)]
    congr 1
    norm_num
  unfold generator radial radialX radialXX
  rw [hp₀,hp₁]
  field_simp
  ring

lemma generator_nonpos {κ β a x ε : ℝ} (hκ : 0 ≤ κ) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (hba : κ*(β+1) ≤ 4+2*a) (hx : 0 < x) (hε : 0 < ε) :
    generator κ β a x ε ≤ 0 := by
  rw [generator_factor κ β a x ε hx hε]
  apply mul_nonpos_of_nonneg_of_nonpos
  · positivity
  · have h₁ : (κ*(β+1)/2-2-a)*x^4 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    have h₂ : 0 ≤ (2+κ/2+2*a)*x^2*ε^2 := by positivity
    have h₃ : 0 ≤ a*ε^4 := by positivity
    linarith

lemma exponent_choice {κ : ℝ} (hκ : 0 < κ) (h8 : κ < 8) :
    let β := (8/κ-1)/2
    let a := 1+κ/8
    0 < β ∧ 0 < a ∧ a < 2 ∧ κ*(β+1) < 4+2*a := by
  have hd : 1 < 8/κ := (lt_div_iff₀ hκ).2 (by simpa)
  dsimp only
  refine ⟨by linarith,by positivity,by linarith,?_⟩
  have he : κ*((8/κ-1)/2+1) = 4+κ/2 := by field_simp; ring
  rw [he]
  linarith

end SLEExactGauge.BoundaryGreen

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BoundaryGreen
open BoundaryFunctional Swallowing GreenPhysical

lemma field_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (β a s : ℝ) (U : C(I, ℝ)) (x : ℝ) :
    field hε hT β a s U x 0 0 = radial (-β) x ε := by
  simp only [field,factor,logDerivative_initial,mul_zero,Real.exp_zero,position_initial,
    Complex.ofReal_re,sub_zero,one_mul]

lemma generator_field {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (κ β a : ℝ) (hκ : 0 ≤ κ) (U : C(I, ℝ)) (x t b : ℝ)
    (hx : ε ≤ gap hε hT U x t) (hU : extendDriver T U t = Real.sqrt κ*b) :
    drift hε hT β a (Real.sqrt κ) U x t b+
      (1/2:ℝ)*iteratedDeriv 2 (field hε hT β a (Real.sqrt κ) U x t) b =
    factor hε hT β a U x t * generator κ β a (gap hε hT U x t) ε := by
  have hz : position hε hT U (x:ℂ) t = ((position hε hT U (x:ℂ) t).re:ℂ) := by
    apply Complex.ext <;> simp [position_im_zero]
  have hc : clampRe ε (position hε hT U (x:ℂ) t-(extendDriver T U t:ℂ)) =
      (gap hε hT U x t:ℂ) := by
    change BoundaryCutoff.clamp 1 ε _ = _
    rw [BoundaryCutoff.clamp_eq (by norm_num : |(1:ℝ)|=1) (by simpa [gap] using hx)]
    rw [hz]
    simp only [gap,Complex.ofReal_sub]
  have hv : velocity ε (extendDriver T U t) (position hε hT U (x:ℂ) t) =
      (2/(gap hε hT U x t):ℝ) := by
    change 2/clampRe ε _ = _
    rw [hc]
    push_cast
    rfl
  have hd : variation hε hT U (x:ℂ) t = -2/(gap hε hT U x t)^2 := by
    unfold variation
    rw [hc]
    norm_cast
  rw [second_eq,Real.sq_sqrt hκ]
  dsimp only [drift]
  rw [hv,hd,Complex.ofReal_re]
  have he : (position hε hT U (x:ℂ) t).re-Real.sqrt κ*b = gap hε hT U x t := by
    simp only [gap,hU]
  rw [he]
  unfold generator
  ring

end SLEExactGauge.BoundaryGreen

end

end

end OAI
