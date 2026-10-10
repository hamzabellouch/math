import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppingMeasurability

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
open MeasureTheory
noncomputable section
open Set Filter Real
open scoped Topology
namespace SLEExactGauge.ReverseDerivative
lemma line_deriv_test (a b : ℝ) {q : State} (hu : 0 ≤ q.1) (hy : 0 < q.2.1.im)
    (v : State) :
    HasDerivAt (fun t : ℝ => test a (q+t • v) b)
      (test a q b * (lambda a*v.2.2+Hx a q.1 (q.2.1.re-b) q.2.1.im*v.2.1.re+
        Hy a q.1 (q.2.1.re-b) q.2.1.im*v.2.1.im-
        zeta a/(4*D q.1 (q.2.1.re-b) q.2.1.im)*v.1)) 0 := by
  let x := q.2.1.re-b
  let y := q.2.1.im
  let u := q.1
  have dx : HasDerivAt (fun t : ℝ => x+t*v.2.1.re) v.2.1.re 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.2.1.re).const_add x
  have dy : HasDerivAt (fun t : ℝ => y+t*v.2.1.im) v.2.1.im 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.2.1.im).const_add y
  have du : HasDerivAt (fun t : ℝ => u+t*v.1) v.1 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.1).const_add u
  have dl : HasDerivAt (fun t : ℝ => q.2.2+t*v.2.2) v.2.2 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.2.2).const_add q.2.2
  have dr := (dx.pow 2).add (dy.pow 2)
  have dd := dr.add (du.div_const 2)
  have hR := (R_pos x hy).ne'
  have hD := (D_pos hu hy x).ne'
  have hlogR := dr.log (by simpa [R,y] using hR)
  have hlogD := dd.log (by simpa [D,R,y,u] using hD)
  have hlogY := dy.log (by simpa [y] using hy.ne')
  have hd := ((((dl.const_mul (lambda a)).add (hlogR.const_mul (r a/2))).add
    (hlogY.const_mul (zeta a-r a))).sub (hlogD.const_mul (zeta a/2))).exp
  convert! hd using 1
  · ext t
    simp [test,F,H,R,D,x,y,u,Complex.add_re,Complex.add_im]
    congr 4 <;> ring_nf
  · simp only [zero_mul,add_zero] at *
    dsimp [test,F,H,Hx,Hy,R,D,x,y,u] at *
    simp only [zero_mul,add_zero,pow_one]
    congr 1
    field_simp [hR,hD,hy.ne']
    ring

lemma fderiv_test_vector (a b : ℝ) {q : State} (hu : 0 ≤ q.1) (hy : 0 < q.2.1.im) :
    fderiv ℝ (fun q => test a q b) q (vector a q b) =
      test a q b * ((-a*(q.2.1.re-b)/R (q.2.1.re-b) q.2.1.im)*
        Hx a q.1 (q.2.1.re-b) q.2.1.im+
        (a*q.2.1.im/R (q.2.1.re-b) q.2.1.im)*Hy a q.1 (q.2.1.re-b) q.2.1.im+
        a*((q.2.1.re-b)^2-q.2.1.im^2)/(R (q.2.1.re-b) q.2.1.im)^2*lambda a+
        zeta a/(4*D q.1 (q.2.1.re-b) q.2.1.im)) := by
  have hv := (((hasDerivAt_id (0:ℝ)).smul_const (vector a q b)).const_add q)
  simp only [id_eq,one_smul] at hv
  have hq : q + (0:ℝ) • vector a q b = q := by simp
  have houter := (differentiableAt_test a b hu hy).hasFDerivAt
  rw [← hq] at houter
  have hd := houter.comp_hasDerivAt (0:ℝ)
    (show HasDerivAt (fun t : ℝ => q+t • vector a q b) (vector a q b) 0 from hv)
  simp only [zero_smul,add_zero] at hd
  rw [hd.unique (line_deriv_test a b hu hy (vector a q b))]
  congr 1
  simp [vector,Complex.div_re,Complex.div_im,Complex.inv_re,Complex.inv_im,
    Complex.mul_re,pow_two,Complex.normSq_apply,R]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma second_driver_test (a : ℝ) {q : State} (hu : 0 ≤ q.1) (hy : 0 < q.2.1.im) (b : ℝ) :
    deriv (deriv (test a q)) b = test a q b *
      ((Hx a q.1 (q.2.1.re-b) q.2.1.im)^2+Hxx a q.1 (q.2.1.re-b) q.2.1.im) := by
  have hfirst : deriv (test a q) = fun b => -test a q b * Hx a q.1 (q.2.1.re-b) q.2.1.im := by
    funext b
    have hd := ((hasDerivAt_Hx (a := a) (x := q.2.1.re-b) (l := q.2.2) hu hy).exp).comp b
      ((hasDerivAt_id b).const_sub q.2.1.re)
    convert! hd.deriv using 1
    simp only [test,F]
    ring
  rw [hfirst]
  have hf := ((hasDerivAt_Hx (a := a) (x := q.2.1.re-b) (l := q.2.2) hu hy).exp).comp b
    ((hasDerivAt_id b).const_sub q.2.1.re)
  have hh := (hasDerivAt_Hxx (a := a) (x := q.2.1.re-b) hu hy).comp b
    ((hasDerivAt_id b).const_sub q.2.1.re)
  convert! (hf.neg.mul hh).deriv using 1
  simp only [test,F,Function.comp_apply,Pi.neg_apply]
  ring

lemma test_generator_nonpos {a : ℝ} (ha : 1/4 < a) {q : State}
    (hu : 0 ≤ q.1) (hy : 0 < q.2.1.im) (b : ℝ) :
    fderiv ℝ (fun q => test a q b) q (vector a q b)+deriv (deriv (test a q)) b/2 ≤ 0 := by
  rw [fderiv_test_vector a b hu hy,second_driver_test a hu hy]
  have hi := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (H a q.1 (q.2.1.re-b) q.2.1.im q.2.2)).le
    (generator_nonpos (x := q.2.1.re-b) ha hu hy)
  change test a q b * _ ≤ 0 at hi
  nlinarith only [hi]

end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open scoped ContDiff

def domain : Set (State × ℝ) := {q | 0 < q.1.1 ∧ 0 < q.1.2.1.im}

lemma isOpen_domain : IsOpen domain := by
  apply IsOpen.inter
  · exact isOpen_lt continuous_const (continuous_fst.comp continuous_fst)
  · exact isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_fst.comp (continuous_snd.comp continuous_fst)))

lemma contDiffOn_test (a : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (test a)) domain := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hre : ContDiffAt ℝ ∞ (fun q : State × ℝ => q.1.2.1.re-q.2) q :=
    (Complex.reCLM.contDiff.contDiffAt.comp q
      (contDiffAt_fst.comp q (contDiffAt_snd.comp q contDiffAt_fst))).sub contDiffAt_snd
  have him : ContDiffAt ℝ ∞ (fun q : State × ℝ => q.1.2.1.im) q :=
    Complex.imCLM.contDiff.contDiffAt.comp q
      (contDiffAt_fst.comp q (contDiffAt_snd.comp q contDiffAt_fst))
  have hr := (hre.pow 2).add (him.pow 2)
  have hd := hr.add ((contDiffAt_fst.comp q contDiffAt_fst).div_const 2)
  have hl : ContDiffAt ℝ ∞ (fun q : State × ℝ => q.1.2.2) q :=
    contDiffAt_snd.comp q (contDiffAt_snd.comp q contDiffAt_fst)
  have hR := (R_pos (q.1.2.1.re-q.2) hq.2).ne'
  have hD := (D_pos hq.1.le hq.2 (q.1.2.1.re-q.2)).ne'
  have he := ((((contDiffAt_const (c := lambda a)).mul hl).add
    ((contDiffAt_const (c := r a/2)).mul (hr.log hR))).add
    ((contDiffAt_const (c := zeta a-r a)).mul (him.log hq.2.ne'))).sub
    ((contDiffAt_const (c := zeta a/2)).mul (hd.log hD))
  exact he.exp

lemma contDiffOn_vector (a : ℝ) :
    ContDiffOn ℝ ∞ (Function.uncurry (vector a)) domain := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hz : ContDiffAt ℝ ∞ (fun q : State × ℝ => q.1.2.1-(q.2:ℂ)) q :=
    (contDiffAt_fst.comp q (contDiffAt_snd.comp q contDiffAt_fst)).sub
      (Complex.ofRealCLM.contDiff.contDiffAt.comp q contDiffAt_snd)
  have hn : q.1.2.1-(q.2:ℂ) ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact hq.2.ne' hi
  have hi := hz.inv hn
  have hg : ContDiffAt ℝ ∞ (fun q : State × ℝ => -(a:ℂ)/(q.1.2.1-q.2)) q := by
    convert! (contDiffAt_const (c := -(a:ℂ))).mul hi using 1
  have hl : ContDiffAt ℝ ∞ (fun q : State × ℝ => a*((q.1.2.1-q.2)⁻¹^2).re) q :=
    contDiffAt_const.mul (Complex.reCLM.contDiff.contDiffAt.comp q (hi.pow 2))
  exact contDiffAt_const.prodMk (hg.prodMk hl)
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open Cutoff

def globalVector (a q : ℝ) (x : State) (b : ℝ) : State :=
  (-1, (-(a:ℂ)*inverse q (x.2.1-b), a*(inverse q (x.2.1-b)^2).re))

def bound (a q : ℝ) : ℝ := 1+|a| *q⁻¹+|a| *q⁻¹^2

def lipBound (a q : ℝ) : ℝ := |a| *(3/q^2)+|a| *(6/q^3)

lemma continuous_globalVector {q : ℝ} (hq : 0 < q) (a : ℝ) :
    Continuous (Function.uncurry (globalVector a q)) := by
  have hi : Continuous (fun x : State × ℝ => inverse q (x.1.2.1-x.2)) :=
    (lipschitz_inverse hq).continuous.comp
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).sub
        (Complex.continuous_ofReal.comp continuous_snd))
  exact continuous_const.prodMk ((continuous_const.mul hi).prodMk
    (continuous_const.mul (Complex.continuous_re.comp (hi.pow 2))))

lemma norm_globalVector_le {q : ℝ} (hq : 0 < q) (a : ℝ) (x : State) (b : ℝ) :
    ‖globalVector a q x b‖ ≤ bound a q := by
  have hi := norm_inverse_le hq (x.2.1-b)
  have h1 : ‖-(a:ℂ)*inverse q (x.2.1-b)‖ ≤ |a| *q⁻¹ := by
    rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
  have h2 : |a*(inverse q (x.2.1-b)^2).re| ≤ |a| *q⁻¹^2 := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (Complex.abs_re_le_norm _).trans (by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hi 2)
  change max ‖(-1:ℝ)‖ (max ‖-(a:ℂ)*inverse q (x.2.1-b)‖
    ‖a*(inverse q (x.2.1-b)^2).re‖) ≤ _
  simp only [Real.norm_eq_abs,abs_neg,abs_one]
  apply max_le
  · dsimp [bound]; nlinarith [show 0 ≤ |a| *q⁻¹ by positivity,show 0 ≤ |a| *q⁻¹^2 by positivity]
  · apply max_le
    · exact h1.trans (by dsimp [bound]; nlinarith [show 0 ≤ |a| *q⁻¹^2 by positivity])
    · exact h2.trans (by dsimp [bound]; nlinarith [show 0 ≤ |a| *q⁻¹ by positivity])

lemma inverse_sq_sub_le {q : ℝ} (hq : 0 < q) (z w : ℂ) :
    ‖inverse q z^2-inverse q w^2‖ ≤ (6/q^3)*‖z-w‖ := by
  have hh : inverse q z^2-inverse q w^2 = (inverse q z-inverse q w)*(inverse q z+inverse q w) := by ring
  rw [hh,norm_mul]
  have hi : ‖inverse q z+inverse q w‖ ≤ 2*q⁻¹ :=
    (norm_add_le _ _).trans (by linarith [norm_inverse_le hq z,norm_inverse_le hq w])
  have h := mul_le_mul (inverse_sub_bound hq z w) hi (norm_nonneg _) (by positivity)
  exact h.trans_eq (by ring)

lemma globalVector_sub_le {q : ℝ} (hq : 0 < q) (a b : ℝ) (x y : State) :
    ‖globalVector a q x b-globalVector a q y b‖ ≤ lipBound a q*‖x-y‖ := by
  have hxy : ‖x.2.1-y.2.1‖ ≤ ‖x-y‖ :=
    (norm_fst_le (x.2-y.2)).trans (norm_snd_le (x-y))
  have hz : x.2.1-(b:ℂ)-(y.2.1-b) = x.2.1-y.2.1 := by abel
  have h1 : ‖-(a:ℂ)*inverse q (x.2.1-b)- (-(a:ℂ)*inverse q (y.2.1-b))‖ ≤
      |a| *(3/q^2)*‖x-y‖ := by
    rw [← mul_sub,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    have h := inverse_sub_bound hq (x.2.1-b) (y.2.1-b)
    rw [hz] at h
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans (by
      calc |a| * ((3/q^2)*‖x.2.1-y.2.1‖) = |a| *(3/q^2)*‖x.2.1-y.2.1‖ := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left hxy (by positivity))
  have h2 : |a*(inverse q (x.2.1-b)^2).re-a*(inverse q (y.2.1-b)^2).re| ≤
      |a| *(6/q^3)*‖x-y‖ := by
    rw [← mul_sub,abs_mul,← Complex.sub_re]
    have h := inverse_sq_sub_le hq (x.2.1-b) (y.2.1-b)
    rw [hz] at h
    exact (mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans h) (abs_nonneg _)).trans
      (by calc
        |a| * ((6/q^3)*‖x.2.1-y.2.1‖) = |a| *(6/q^3)*‖x.2.1-y.2.1‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hxy (by positivity))
  change max ‖(-1:ℝ)-(-1)‖ (max _ ‖a*(inverse q (x.2.1-b)^2).re-a*(inverse q (y.2.1-b)^2).re‖) ≤ _
  simp only [sub_self,norm_zero,Real.norm_eq_abs]
  apply max_le
  · dsimp [lipBound]; positivity
  · apply max_le
    · exact h1.trans (by dsimp [lipBound]; nlinarith [norm_nonneg (x-y),show 0 ≤ |a| *(6/q^3) by positivity])
    · exact h2.trans (by dsimp [lipBound]; nlinarith [norm_nonneg (x-y),show 0 ≤ |a| *(3/q^2) by positivity])

lemma inverse_eq_of_height {q : ℝ} (hq : 0 < q) (z : ℂ) (b : ℝ) (hz : q ≤ z.im) :
    inverse q (z-b) = (z-b)⁻¹ := by
  have hqn : q ≤ ‖z-b‖ := hz.trans (by simpa using Complex.im_le_norm (z-b))
  have hsq : q^2 ≤ ‖z-b‖^2 := pow_le_pow_left₀ hq.le hqn 2
  rw [inverse, denominator, max_eq_left hsq,Complex.inv_def]
  simp only [Complex.normSq_eq_norm_sq,div_eq_mul_inv,Complex.ofReal_inv,starRingEnd_apply]

lemma globalVector_eq {q : ℝ} (hq : 0 < q) (a : ℝ) (x : State) (b : ℝ)
    (hy : q ≤ x.2.1.im) : globalVector a q x b = vector a x b := by
  simp only [globalVector,vector,inverse_eq_of_height hq _ _ hy,div_eq_mul_inv]

end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
def timeClip (T t : ℝ) : ℝ := max 0 (min T t)
lemma continuous_timeClip (T : ℝ) : Continuous (timeClip T) := continuous_const.max (continuous_const.min continuous_id)
lemma timeClip_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : timeClip T t ∈ Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
lemma timeClip_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : timeClip T t = t :=
  by rw [timeClip,min_eq_right ht.2,max_eq_right ht.1]
 
lemma reverse_height_formula {T : ℝ} {y r : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (r t*y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, y t = y 0 * Real.exp (∫ u in (0:ℝ)..t, r (timeClip T u)) := by
  let A (t : ℝ) := ∫ u in (0:ℝ)..t, r (timeClip T u)
  have hc : Continuous (fun u => r (timeClip T u)) :=
    hr.comp_continuous (continuous_timeClip T) (timeClip_mem hT)
  have hA (t : ℝ) : HasDerivAt A (r (timeClip T t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hA' : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hd0 (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => y u * Real.exp (-A u)) 0 (Icc 0 T) t := by
    have he := (hd t ht).mul ((hA t).neg.exp.hasDerivWithinAt)
    rw [timeClip_eq ht] at he
    convert! he using 1
    first | rfl | ring
  have hconst := constant_of_has_deriv_right_zero
    (hy.mul ((Real.continuous_exp.comp hA'.neg).continuousOn)) (fun t (ht : t ∈ Ico 0 T) =>
      (hd0 t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
  intro t ht
  have he := hconst t ht
  dsimp only [Pi.mul_apply,Function.comp_def,Pi.neg_apply] at he
  have hA0 : A 0 = 0 := by simp [A]
  rw [hA0,neg_zero,Real.exp_zero,mul_one] at he
  calc
    y t = (y t * Real.exp (-A t))*Real.exp (A t) := by
      rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = y 0 * Real.exp (A t) := by rw [he]

lemma reverse_height_le {T : ℝ} {y r : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (r t*y t) (Icc 0 T) t)
    (hy0 : 0 ≤ y 0) (hr0 : ∀ t ∈ Icc 0 T, 0 ≤ r t) (t : ℝ) (ht : t ∈ Icc 0 T) :
    y 0 ≤ y t := by
  rw [reverse_height_formula hT hy hr hd t ht]
  apply le_mul_of_one_le_right hy0
  apply Real.one_le_exp_iff.mpr
  apply intervalIntegral.integral_nonneg ht.1
  intro u _
  exact hr0 (timeClip T u) (timeClip_mem hT u)

lemma globalVector_height (a q : ℝ) (x : State) (b : ℝ) :
    (globalVector a q x b).2.1.im = (a/Cutoff.denominator q (x.2.1-b))*x.2.1.im := by
  simp [globalVector,Cutoff.inverse,Complex.mul_im,Complex.div_ofReal_im]
  ring

def initial (U y : ℝ) : State := (U, (⟨0,y⟩,0))
def reverseFlow (a q U y : ℝ) (b : ℝ≥0 → ℝ) : ℝ → State :=
  ODEPath.flow (globalVector a q) (initial U y) b

lemma reverseFlow_solution {q : ℝ} (hq : 0 < q) (a U y : ℝ) (b : ℝ≥0 → ℝ)
    (hb : Continuous b) {T : ℝ} (hT : 0 ≤ T) :
    reverseFlow a q U y b 0 = initial U y ∧
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (reverseFlow a q U y b)
      (globalVector a q (reverseFlow a q U y b t) (b t.toNNReal)) (Icc 0 T) t := by
  exact ODEPath.flow_solution _ (continuous_globalVector hq a) _ b hb
    (by dsimp [bound]; positivity) (by dsimp [lipBound]; positivity) hT
    (norm_globalVector_le hq a) (globalVector_sub_le hq a)

lemma reverseFlow_height {q a y : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (U : ℝ) (b : ℝ≥0 → ℝ) (hb : Continuous b) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc 0 T) : y ≤ (reverseFlow a q U y b t).2.1.im := by
  let g := reverseFlow a q U y b
  have hg := reverseFlow_solution hq a U y b hb hT
  have hc : ContinuousOn g (Icc 0 T) := fun s hs => (hg.2 s hs).continuousWithinAt
  let proj : State →L[ℝ] ℝ := Complex.imCLM.comp
    ((ContinuousLinearMap.fst ℝ ℂ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℂ × ℝ)))
  let r := fun s => a/Cutoff.denominator q ((g s).2.1-b s.toNNReal)
  have hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun t => proj (g t)) (r s * proj (g s)) (Icc 0 T) s := by
    intro s hs
    have hh := proj.hasFDerivAt.comp_hasDerivWithinAt s (hg.2 s hs)
    convert! hh using 1
    exact (globalVector_height a q (g s) (b s.toNNReal)).symm
  have hr : ContinuousOn r (Icc 0 T) := by
    apply continuousOn_const.div
    · unfold Cutoff.denominator
      exact continuous_max.comp_continuousOn
        ((((hc.snd.fst.sub ((Complex.continuous_ofReal.comp
        (hb.comp continuous_real_toNNReal)).continuousOn)).norm).pow 2).prodMk continuousOn_const)
    · intro s hs; exact (Cutoff.denominator_pos hq _).ne'
  have he := reverse_height_le hT (proj.continuous.comp_continuousOn hc) hr hd
    (by
      change 0 ≤ (reverseFlow a q U y b 0).2.1.im
      rw [hg.1]
      exact hy)
    (fun s hs => div_nonneg ha (Cutoff.denominator_pos hq _).le) t ht
  change (reverseFlow a q U y b 0).2.1.im ≤ (reverseFlow a q U y b t).2.1.im at he
  rw [hg.1] at he
  exact he

lemma reverseFlow_time {q : ℝ} (hq : 0 < q) (a U y : ℝ) (b : ℝ≥0 → ℝ)
    (hb : Continuous b) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    (reverseFlow a q U y b t).1 = U-t := by
  let g := reverseFlow a q U y b
  have hg := reverseFlow_solution hq a U y b hb hT
  have hc : ContinuousOn g (Icc 0 T) := fun s hs => (hg.2 s hs).continuousWithinAt
  have hd : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => (g s).1+s) 0 (Icc 0 T) s := by
    intro s hs
    have hdg := (ContinuousLinearMap.fst ℝ ℝ (ℂ × ℝ)).hasFDerivAt.comp_hasDerivWithinAt s (hg.2 s hs)
    convert! hdg.add (hasDerivWithinAt_id s (Icc 0 T)) using 1
    simp [globalVector]
  have he := constant_of_has_deriv_right_zero (hc.fst.add continuousOn_id)
    (fun s (hs : s ∈ Ico 0 T) => (hd s ⟨hs.1,hs.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1))) t ht
  change (reverseFlow a q U y b t).1+t = (reverseFlow a q U y b 0).1+0 at he
  rw [hg.1] at he
  change (reverseFlow a q U y b t).1+t = U+0 at he
  linarith

lemma reverseFlow_actual {q a y : ℝ} (hq : 0 < q) (ha : 0 ≤ a) (hy : q ≤ y)
    (U : ℝ) (b : ℝ≥0 → ℝ) (hb : Continuous b) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt (reverseFlow a q U y b)
      (vector a (reverseFlow a q U y b t) (b t.toNNReal)) (Icc 0 T) t := by
  intro t ht
  have hg := (reverseFlow_solution hq a U y b hb hT).2 t ht
  rw [globalVector_eq hq a _ _
    (hy.trans (reverseFlow_height hq ha (hq.le.trans hy) U b hb hT t ht))] at hg
  exact hg
end SLEExactGauge.ReverseDerivative

namespace SLEExactGauge.ReverseDerivative
open _root_.OAI.SLEExactGauge.Localization BrownianCalculus ODEPath RationalStop
open MeasureTheory ProbabilityTheory

end SLEExactGauge.ReverseDerivative
end
end
end
end
end
end
end
end
end
end
end

end OAI
