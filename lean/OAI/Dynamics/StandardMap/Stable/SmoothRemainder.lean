import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Lyapunov.MeasurableFrame

namespace OAI

section
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal

lemma potential_lift_sub_bound (k : ℝ) (z w : ℂ) :
    |torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1|≤
      4*Real.pi^2*|k| *‖z-w‖ := by
  have hc := Real.abs_cos_sub_cos_le (2*Real.pi*z.re) (2*Real.pi*w.re)
  have hz : |z.re-w.re|≤‖z-w‖ := Complex.abs_re_le_norm (z-w)
  have he : torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1 =
      2*Real.pi*k*(Real.cos (2*Real.pi*z.re)-Real.cos (2*Real.pi*w.re)) := by
    simp only [complexProjection,torusPotential,cosine_coe]
    ring
  rw [he,abs_mul]
  calc
    _ ≤ |2*Real.pi*k| * |2*Real.pi*z.re-2*Real.pi*w.re| :=
      mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = (4*Real.pi^2*|k|)*|z.re-w.re| := by
      rw [show 2*Real.pi*z.re-2*Real.pi*w.re=2*Real.pi*(z.re-w.re) by ring]
      simp only [abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)

noncomputable def derivativeVariationBound (k : ℝ) : ℝ := 8*Real.pi^2*|k|
lemma derivativeVariationBound_nonneg (k : ℝ) : 0≤derivativeVariationBound k := by
  unfold derivativeVariationBound
  positivity

lemma standardDerivative_lift_sub_bound (k : ℝ) (z w : ℂ) :
    ‖standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)‖≤
      derivativeVariationBound k*‖z-w‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (derivativeVariationBound_nonneg k) (norm_nonneg _))
  intro v
  have hre : ((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).re =
      (torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1)*v.re := by
    simp only [sub_apply,Complex.sub_re,standardDerivative_re]
    ring
  have him : ((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).im =
      (torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1)*v.re := by
    simp only [sub_apply,Complex.sub_im,standardDerivative_im]
    ring
  calc
    _ ≤ |((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).re|+
        |((standardDerivative k (complexProjection z)-standardDerivative k (complexProjection w)) v).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 2*|torusPotential k (complexProjection z).1-torusPotential k (complexProjection w).1| * |v.re| := by
      rw [hre,him,abs_mul]
      ring
    _ ≤ 2*(4*Real.pi^2*|k| *‖z-w‖)*‖v‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (potential_lift_sub_bound k z w) (by norm_num))
        (Complex.abs_re_le_norm v) (abs_nonneg _) (by positivity)
    _ = _ := by unfold derivativeVariationBound; ring

noncomputable def liftRemainder (k : ℝ) (z v : ℂ) : ℂ :=
  standardLift k (z+v)-standardLift k z-standardDerivative k (complexProjection z) v
@[simp] lemma liftRemainder_zero (k : ℝ) (z : ℂ) : liftRemainder k z 0=0 := by
  simp only [liftRemainder,add_zero,sub_self,map_zero]

lemma hasFDerivAt_liftRemainder (k : ℝ) (z v : ℂ) :
    HasFDerivAt (liftRemainder k z)
      (standardDerivative k (complexProjection (z+v))-standardDerivative k (complexProjection z)) v := by
  have hh := ((hasFDerivAt_standardLift k (z+v)).comp v ((hasFDerivAt_id v).const_add z)).sub_const (standardLift k z)
  have hh' := hh.sub (standardDerivative k (complexProjection z)).hasFDerivAt
  convert! hh' using 1

lemma liftRemainder_sub_bound (k : ℝ) (z : ℂ) {r : ℝ} {v w : ℂ}
    (hv : ‖v‖≤r) (hw : ‖w‖≤r) :
    ‖liftRemainder k z v-liftRemainder k z w‖≤derivativeVariationBound k*r*‖v-w‖ := by
  apply (convex_closedBall (0 : ℂ) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x _ => (hasFDerivAt_liftRemainder k z x).hasFDerivWithinAt) (fun x hx => ?_)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)
  have hh := standardDerivative_lift_sub_bound k (z+x) z
  rw [add_sub_cancel_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
    (derivativeVariationBound_nonneg k))

noncomputable def chartRemainder (k : ℝ) (z : ℂ) (F C : ℂ →L[ℝ] ℂ) (v : ℂ) : ℂ :=
  C (liftRemainder k z (F v))
@[simp] lemma chartRemainder_zero (k : ℝ) (z : ℂ) (F C : ℂ →L[ℝ] ℂ) : chartRemainder k z F C 0=0 := by
  simp only [chartRemainder,map_zero,liftRemainder_zero]

lemma chartRemainder_sub_bound (k : ℝ) (z : ℂ) (F C : ℂ →L[ℝ] ℂ) {r : ℝ}
    (hr : 0≤r) {v w : ℂ} (hv : ‖v‖≤r) (hw : ‖w‖≤r) :
    ‖chartRemainder k z F C v-chartRemainder k z F C w‖≤
      (‖C‖*derivativeVariationBound k*‖F‖^2*r)*‖v-w‖ := by
  have hfv := (F.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg F))
  have hfw := (F.le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg F))
  have hr0 := derivativeVariationBound_nonneg k
  calc
    _ = ‖C (liftRemainder k z (F v)-liftRemainder k z (F w))‖ := by rw [map_sub]; rfl
    _ ≤ ‖C‖*‖liftRemainder k z (F v)-liftRemainder k z (F w)‖ := C.le_opNorm _
    _ ≤ ‖C‖*(derivativeVariationBound k*(‖F‖*r)*‖F v-F w‖) :=
      mul_le_mul_of_nonneg_left (liftRemainder_sub_bound k z hfv hfw) (norm_nonneg C)
    _ ≤ ‖C‖*(derivativeVariationBound k*(‖F‖*r)*(‖F‖*‖v-w‖)) := by
      rw [← map_sub]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (F.le_opNorm (v-w)) (by positivity)) (norm_nonneg C)
    _ = _ := by ring

end StandardMapEntropy

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal

abbrev Plane := ℝ × ℝ
abbrev Sequence := BoundedContinuousFunction ℕ Plane

structure Recurrence (ℓ δ : ℝ≥0) where
  a : ℕ → ℝ
  b : ℕ → ℝ
  remainder : ℕ → Plane → Plane
  stable_bound : ∀ n, |a n|≤ℓ
  inverse_bound : ∀ n, |(b n)⁻¹|≤ℓ
  b_ne : ∀ n, b n≠0
  lipschitz : ∀ n, LipschitzWith δ (remainder n)
  zero : ∀ n, remainder n 0=0

variable {ℓ δ : ℝ≥0}

def Recurrence.step (r : Recurrence ℓ δ) (n : ℕ) (v : Plane) : Plane :=
  (r.a n*v.1+(r.remainder n v).1, r.b n*v.2+(r.remainder n v).2)

noncomputable def Recurrence.perronValue (r : Recurrence ℓ δ) (s : ℝ) (x : Sequence) (n : ℕ) : Plane :=
  ((match n with | 0 => s | m+1 => r.a m*(x m).1+(r.remainder m (x m)).1),
    (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2))

lemma point_sub_bound (x y : Sequence) (n : ℕ) : ‖x n-y n‖≤‖x-y‖ :=
  (x-y).norm_coe_le_norm n
lemma fst_sub_bound (x y : Sequence) (n : ℕ) : |(x n).1-(y n).1|≤‖x-y‖ :=
  (norm_fst_le (x n-y n)).trans (point_sub_bound x y n)
lemma snd_sub_bound (x y : Sequence) (n : ℕ) : |(x n).2-(y n).2|≤‖x-y‖ :=
  (norm_snd_le (x n-y n)).trans (point_sub_bound x y n)

lemma remainder_sub_bound (r : Recurrence ℓ δ) (x y : Sequence) (n : ℕ) :
    ‖r.remainder n (x n)-r.remainder n (y n)‖≤(δ : ℝ)*‖x-y‖ := by
  have hh := (r.lipschitz n).dist_le_mul (x n) (y n)
  rw [dist_eq_norm,dist_eq_norm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (point_sub_bound x y n) δ.coe_nonneg)

lemma perronValue_sub_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1)
    (s t : ℝ) (x y : Sequence) (n : ℕ) :
    ‖r.perronValue s x n-r.perronValue t y n‖≤
      max |s-t| (((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖) := by
  have hδ : 0≤(δ : ℝ) := δ.coe_nonneg
  have hℓ0 : 0≤(ℓ : ℝ) := ℓ.coe_nonneg
  have hℓ1 : (ℓ : ℝ)≤1 := hℓ
  have hfst (m : ℕ) := (norm_fst_le (r.remainder m (x m)-r.remainder m (y m))).trans
    (remainder_sub_bound r x y m)
  have hsnd (m : ℕ) := (norm_snd_le (r.remainder m (x m)-r.remainder m (y m))).trans
    (remainder_sub_bound r x y m)
  rw [Prod.norm_def]
  apply max_le
  · cases n with
    | zero => exact le_max_left _ _
    | succ m =>
      change |r.a m*(x m).1+(r.remainder m (x m)).1-
        (r.a m*(y m).1+(r.remainder m (y m)).1)|≤_
      calc
        _ = |r.a m*((x m).1-(y m).1)+((r.remainder m (x m)).1-(r.remainder m (y m)).1)| := by congr 1; ring
        _ ≤ |r.a m| *|(x m).1-(y m).1| +|(r.remainder m (x m)).1-(r.remainder m (y m)).1| := by
          simpa only [abs_mul] using abs_add_le (r.a m*((x m).1-(y m).1))
            ((r.remainder m (x m)).1-(r.remainder m (y m)).1)
        _ ≤ (ℓ : ℝ)*‖x-y‖+(δ : ℝ)*‖x-y‖ := add_le_add
          (mul_le_mul (r.stable_bound m) (fst_sub_bound x y m) (abs_nonneg _) hℓ0) (hfst m)
        _ = ((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖ := by push_cast; ring
        _ ≤ _ := le_max_right _ _
  · change |(r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)-
      (r.b n)⁻¹*((y (n+1)).2-(r.remainder n (y n)).2)|≤_
    calc
      _ = |(r.b n)⁻¹| *|((x (n+1)).2-(y (n+1)).2)-
          ((r.remainder n (x n)).2-(r.remainder n (y n)).2)| := by rw [← abs_mul]; congr 1; ring
      _ ≤ |(r.b n)⁻¹| *(|(x (n+1)).2-(y (n+1)).2| +
          |(r.remainder n (x n)).2-(r.remainder n (y n)).2|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ (ℓ : ℝ)*(‖x-y‖+(δ : ℝ)*‖x-y‖) := mul_le_mul (r.inverse_bound n)
        (add_le_add (snd_sub_bound x y (n+1)) (hsnd n)) (by positivity) hℓ0
      _ ≤ ((ℓ+δ : ℝ≥0) : ℝ)*‖x-y‖ := by
        have hh := mul_le_mul_of_nonneg_right hℓ1 (mul_nonneg hδ (norm_nonneg (x-y)))
        push_cast
        nlinarith
      _ ≤ _ := le_max_right _ _

@[simp] lemma perronValue_zero (r : Recurrence ℓ δ) (n : ℕ) : r.perronValue 0 0 n=0 := by
  cases n <;> simp [Recurrence.perronValue,r.zero]

lemma perronValue_norm_bound (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) (n : ℕ) :
    ‖r.perronValue s x n‖≤ max |s| (((ℓ+δ : ℝ≥0) : ℝ)*‖x‖) := by
  simpa only [perronValue_zero,sub_zero] using perronValue_sub_bound r hℓ s 0 x 0 n

noncomputable def Recurrence.perron (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (r.perronValue s x)
    (max |s| (((ℓ+δ : ℝ≥0) : ℝ)*‖x‖)) (perronValue_norm_bound r hℓ s x)

@[simp] lemma perron_apply (r : Recurrence ℓ δ) (hℓ : ℓ≤1) (s : ℝ) (x : Sequence) (n : ℕ) :
    r.perron hℓ s x n=r.perronValue s x n := rfl

lemma perron_contracting (r : Recurrence ℓ δ) (h : ℓ+δ<1) {s : ℝ} :
    ContractingWith (ℓ+δ) (r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s) := by
  refine ⟨h,LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [dist_eq_norm,dist_eq_norm]
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro n
  have hh := perronValue_sub_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s s x y n
  simpa only [BoundedContinuousFunction.sub_apply, perron_apply, sub_self, abs_zero,
    max_eq_right (mul_nonneg (ℓ+δ).coe_nonneg (norm_nonneg _))] using hh

noncomputable def Recurrence.solution (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : Sequence :=
  ContractingWith.fixedPoint _ (perron_contracting r h (s := s))

lemma solution_fixed (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) :
    r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s (r.solution h s)=r.solution h s :=
  (perron_contracting r h (s := s)).fixedPoint_isFixedPt

lemma bound_of_max_contraction {d c K : ℝ} (hc : 0≤ c) (hK : K<1)
    (h : d≤ max c (K*d)) : d≤ c := by
  by_contra hh
  have hd : 0< d := hc.trans_lt (lt_of_not_ge hh)
  have hlt : max c (K*d)< d := max_lt (lt_of_not_ge hh) (by nlinarith)
  exact (not_lt_of_ge h) hlt

lemma fixed_norm_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (hx : r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s x=x) : ‖x‖≤|s| := by
  apply bound_of_max_contraction (abs_nonneg _) (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  conv_lhs => rw [← hx]
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
  intro n
  exact perronValue_norm_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le) s x n

lemma solution_norm_bound (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : ‖r.solution h s‖≤|s| :=
  fixed_norm_bound r h s _ (solution_fixed r h s)

lemma solution_initial (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : (r.solution h s 0).1=s := by
  have hh := congrArg (fun x : Sequence => (x 0).1) (solution_fixed r h s)
  exact hh.symm

lemma solution_orbit (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (n : ℕ) :
    r.solution h s (n+1)=r.step n (r.solution h s n) := by
  have hh := congrArg (fun x : Sequence => x (n+1)) (solution_fixed r h s)
  have hh' := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  apply Prod.ext
  · exact (congrArg Prod.fst hh).symm
  · have he := congrArg Prod.snd hh'
    change (r.b n)⁻¹*((r.solution h s (n+1)).2-(r.remainder n (r.solution h s n)).2)=
      (r.solution h s n).2 at he
    change _=r.b n*(r.solution h s n).2+(r.remainder n (r.solution h s n)).2
    have he' := congrArg (fun t : ℝ => r.b n*t) he
    rw [← mul_assoc, mul_inv_cancel₀ (r.b_ne n), one_mul] at he'
    linarith

lemma solution_lipschitz (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) :
    ‖r.solution h s-r.solution h t‖≤|s-t| := by
  apply bound_of_max_contraction (abs_nonneg _) (show ((ℓ+δ : ℝ≥0) : ℝ)<1 from h)
  apply (BoundedContinuousFunction.norm_le (le_trans (abs_nonneg _) (le_max_left _ _))).mpr
  intro n
  have hh := perronValue_sub_bound r (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ δ from bot_le)) h.le)
    s t (r.solution h s) (r.solution h t) n
  have h1 := congrArg (fun x : Sequence => x n) (solution_fixed r h s)
  have h2 := congrArg (fun x : Sequence => x n) (solution_fixed r h t)
  change r.perronValue s (r.solution h s) n=r.solution h s n at h1
  change r.perronValue t (r.solution h t) n=r.solution h t n at h2
  rwa [h1,h2] at hh

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy.NonlinearStable
open Filter
open scoped Topology NNReal
variable {ℓ δ : ℝ≥0}

noncomputable def Sequence.tail (x : Sequence) (m : ℕ) : Sequence :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun n => x (m+n)) ‖x‖
    (fun n => x.norm_coe_le_norm (m+n))
@[simp] lemma tail_apply (x : Sequence) (m n : ℕ) : x.tail m n=x (m+n) := rfl

noncomputable def Recurrence.tail (r : Recurrence ℓ δ) (m : ℕ) : Recurrence ℓ δ where
  a n := r.a (m+n)
  b n := r.b (m+n)
  remainder n := r.remainder (m+n)
  stable_bound n := r.stable_bound (m+n)
  inverse_bound n := r.inverse_bound (m+n)
  b_ne n := r.b_ne (m+n)
  lipschitz n := r.lipschitz (m+n)
  zero n := r.zero (m+n)

lemma orbit_fixed (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    r.perron (le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0)≤δ from bot_le)) h.le) s x=x := by
  apply BoundedContinuousFunction.ext
  intro n
  apply Prod.ext
  · cases n with
    | zero => exact h0.symm
    | succ n => exact (congrArg Prod.fst (horbit n)).symm
  · have hh := congrArg Prod.snd (horbit n)
    change (x (n+1)).2=r.b n*(x n).2+(r.remainder n (x n)).2 at hh
    change (r.b n)⁻¹*((x (n+1)).2-(r.remainder n (x n)).2)=(x n).2
    rw [hh,add_sub_cancel_right,←mul_assoc,inv_mul_cancel₀ (r.b_ne n),one_mul]

lemma solution_unique (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (x : Sequence)
    (h0 : (x 0).1=s) (horbit : ∀ n, x (n+1)=r.step n (x n)) :
    x=r.solution h s :=
  (perron_contracting r h (s := s)).fixedPoint_unique (orbit_fixed r h s x h0 horbit)

lemma solution_tail (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) (m : ℕ) :
    (r.solution h s).tail m=(r.tail m).solution h (r.solution h s m).1 := by
  apply solution_unique
  · simp only [tail_apply,Nat.add_zero]
  · intro n
    simpa only [tail_apply,Recurrence.tail,Recurrence.step,Nat.add_assoc] using
      solution_orbit r h s (m+n)

lemma solution_cone (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤|(r.solution h s n).1-(r.solution h t n).1| := by
  have hh := solution_lipschitz (r.tail n) h (r.solution h s n).1 (r.solution h t n).1
  rw [←solution_tail,←solution_tail] at hh
  have hb := (point_sub_bound ((r.solution h s).tail n) ((r.solution h t).tail n) 0).trans hh
  simpa only [tail_apply,Nat.add_zero] using hb

lemma step_fst_sub_bound (r : Recurrence ℓ δ) (n : ℕ) (v w : Plane) :
    |(r.step n v).1-(r.step n w).1|≤((ℓ+δ : ℝ≥0) : ℝ)*‖v-w‖ := by
  have hr := (r.lipschitz n).dist_le_mul v w
  rw [dist_eq_norm,dist_eq_norm] at hr
  have hrf := (norm_fst_le (r.remainder n v-r.remainder n w)).trans hr
  have hvw : |v.1-w.1|≤‖v-w‖ := norm_fst_le (v-w)
  change |r.a n*v.1+(r.remainder n v).1-(r.a n*w.1+(r.remainder n w).1)|≤_
  calc
    _ = |r.a n*(v.1-w.1)+((r.remainder n v).1-(r.remainder n w).1)| := by congr 1; ring
    _ ≤ |r.a n| * |v.1-w.1|+|(r.remainder n v).1-(r.remainder n w).1| := by
      simpa only [abs_mul] using abs_add_le (r.a n*(v.1-w.1)) ((r.remainder n v).1-(r.remainder n w).1)
    _ ≤ (ℓ : ℝ)*‖v-w‖+(δ : ℝ)*‖v-w‖ := add_le_add
      (mul_le_mul (r.stable_bound n) hvw (abs_nonneg _) ℓ.coe_nonneg) hrf
    _ = _ := by push_cast; ring

lemma solution_step_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s (n+1)-r.solution h t (n+1)‖≤
      ((ℓ+δ : ℝ≥0) : ℝ)*‖r.solution h s n-r.solution h t n‖ := by
  apply (solution_cone r h s t (n+1)).trans
  rw [solution_orbit,solution_orbit]
  exact step_fst_sub_bound r n _ _

lemma solution_exponential_contraction (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s t : ℝ) (n : ℕ) :
    ‖r.solution h s n-r.solution h t n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t| := by
  induction n with
  | zero => simpa only [pow_zero,one_mul,solution_initial] using solution_cone r h s t 0
  | succ n ih =>
    apply (solution_step_contraction r h s t n).trans
    calc
      _ ≤ ((ℓ+δ : ℝ≥0) : ℝ)*(((ℓ+δ : ℝ≥0) : ℝ)^n*|s-t|) :=
        mul_le_mul_of_nonneg_left ih (ℓ+δ).coe_nonneg
      _ = _ := by rw [pow_succ]; ring

noncomputable def Recurrence.graph (r : Recurrence ℓ δ) (h : ℓ+δ<1) (s : ℝ) : ℝ :=
  (r.solution h s 0).2

lemma graph_lipschitz (r : Recurrence ℓ δ) (h : ℓ+δ<1) : LipschitzWith 1 (r.graph h) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [dist_eq_norm,dist_eq_norm,NNReal.coe_one,one_mul]
  exact (norm_snd_le (r.solution h s 0-r.solution h t 0)).trans
    ((point_sub_bound _ _ 0).trans (solution_lipschitz r h s t))

lemma solution_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) : r.solution h 0=0 := by
  exact norm_eq_zero.mp (le_antisymm (by simpa only [abs_zero] using solution_norm_bound r h 0) (norm_nonneg _))

@[simp] lemma graph_zero (r : Recurrence ℓ δ) (h : ℓ+δ<1) : r.graph h 0=0 := by
  simp [Recurrence.graph,solution_zero]

theorem stable_graph (r : Recurrence ℓ δ) (h : ℓ+δ<1) :
    ∃ g : ℝ → ℝ, g 0=0 ∧ LipschitzWith 1 g ∧
      ∀ s : ℝ, ∃ x : Sequence, x 0=(s,g s) ∧
        (∀ n, x (n+1)=r.step n (x n)) ∧
        (∀ n, ‖x n‖≤((ℓ+δ : ℝ≥0) : ℝ)^n*|s|) ∧
        (∀ y : Sequence, (y 0).1=s → (∀ n, y (n+1)=r.step n (y n)) → y=x) := by
  refine ⟨r.graph h,graph_zero r h,graph_lipschitz r h,fun s =>
    ⟨r.solution h s,?_,solution_orbit r h s,?_,fun y h0 hy => solution_unique r h s y h0 hy⟩⟩
  · exact Prod.ext (solution_initial r h s) rfl
  · intro n
    simpa [solution_zero] using
      solution_exponential_contraction r h s 0 n

end StandardMapEntropy.NonlinearStable

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology NNReal

abbrev RealPlane := ℝ × ℝ
noncomputable def complexToPair : ℂ →L[ℝ] RealPlane := Complex.equivRealProdCLM.toContinuousLinearMap
noncomputable def pairToComplex : RealPlane →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap
@[simp] lemma complexToPair_apply (v : ℂ) : complexToPair v=(v.re,v.im) := rfl
@[simp] lemma pairToComplex_apply (v : RealPlane) : pairToComplex v=⟨v.1,v.2⟩ := rfl
@[simp] lemma complexToPair_pairToComplex (v : RealPlane) : complexToPair (pairToComplex v)=v := by rfl
@[simp] lemma pairToComplex_complexToPair (v : ℂ) : pairToComplex (complexToPair v)=v := by rfl
lemma complexToPair_norm_le (v : ℂ) : ‖complexToPair v‖≤‖v‖ := by
  exact max_le (Complex.abs_re_le_norm v) (Complex.abs_im_le_norm v)
lemma pairToComplex_norm_le (v : RealPlane) : ‖pairToComplex v‖≤2*‖v‖ := by
  have hh := Complex.norm_le_abs_re_add_abs_im (pairToComplex v)
  have h1 : |v.1|≤‖v‖ := norm_fst_le v
  have h2 : |v.2|≤‖v‖ := norm_snd_le v
  exact hh.trans (by change |v.1|+|v.2|≤_; linarith)
lemma norm_complexToPair_le : ‖complexToPair‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simpa only [one_mul] using complexToPair_norm_le v
lemma norm_pairToComplex_le : ‖pairToComplex‖≤2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) pairToComplex_norm_le

noncomputable def flatFrame (q : ℝ) (F : ℂ →L[ℝ] ℂ) : RealPlane →L[ℝ] ℂ :=
  (q • F).comp pairToComplex
noncomputable def flatInverse (q : ℝ) (C : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] RealPlane :=
  complexToPair.comp (q⁻¹ • C)

lemma flatInverse_frame {q : ℝ} (hq : q≠0) {F C : ℂ →L[ℝ] ℂ}
    (hCF : C.comp F=ContinuousLinearMap.id ℝ ℂ) (v : RealPlane) :
    flatInverse q C (flatFrame q F v)=v := by
  have hh : C (F (pairToComplex v))=pairToComplex v := congrArg (fun D : ℂ →L[ℝ] ℂ => D (pairToComplex v)) hCF
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    hh,smul_smul,mul_inv_cancel₀ hq,one_smul,complexToPair_pairToComplex]
lemma flatFrame_inverse {q : ℝ} (hq : q≠0) {F C : ℂ →L[ℝ] ℂ}
    (hFC : F.comp C=ContinuousLinearMap.id ℝ ℂ) (v : ℂ) :
    flatFrame q F (flatInverse q C v)=v := by
  have hh : F (C v)=v := congrArg (fun D : ℂ →L[ℝ] ℂ => D v) hFC
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul,
    pairToComplex_complexToPair,hh,smul_smul,inv_mul_cancel₀ hq,one_smul]

lemma flatFrame_norm_le {q : ℝ} (hq : 0≤q) {F : ℂ →L[ℝ] ℂ} (hF : ‖F‖≤1) :
    ‖flatFrame q F‖≤2*q := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [flatFrame,ContinuousLinearMap.comp_apply,smul_apply,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg hq]
  have hh := (F.le_opNorm (pairToComplex v)).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))
  have hh' : ‖F (pairToComplex v)‖≤2*‖v‖ := by simpa only [one_mul] using hh.trans (by simpa using pairToComplex_norm_le v)
  exact (mul_le_mul_of_nonneg_left hh' hq).trans_eq (by ring)

lemma flatInverse_norm_le {q : ℝ} (hq : 0≤q) (C : ℂ →L[ℝ] ℂ) :
    ‖flatInverse q C‖≤q⁻¹*‖C‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hh := complexToPair_norm_le (q⁻¹ • C v)
  simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg hq] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (C.le_opNorm v) (inv_nonneg.mpr hq)).trans_eq (by ring))

lemma flat_diagonal {q p : ℝ} (D F C : ℂ →L[ℝ] ℂ) {a b : ℝ}
    (h : C.comp (D.comp F)=diagonalPlane a b) (v : RealPlane) :
    flatInverse p C (D (flatFrame q F v))=(q/p*a*v.1,q/p*b*v.2) := by
  have hh : C (D (F (pairToComplex v)))=diagonalPlane a b (pairToComplex v) :=
    congrArg (fun T : ℂ →L[ℝ] ℂ => T (pairToComplex v)) h
  simp only [flatInverse,flatFrame,ContinuousLinearMap.comp_apply,smul_apply,map_smul]
  rw [hh]
  simp only [diagonalPlane_apply,complexToPair_apply,pairToComplex_apply]
  apply Prod.ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,div_eq_mul_inv] <;> ring

noncomputable def flatRemainder (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) (v : RealPlane) : RealPlane := C (liftRemainder k z (F v))
@[simp] lemma flatRemainder_zero (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) : flatRemainder k z F C 0=0 := by
  simp only [flatRemainder,map_zero,liftRemainder_zero]

lemma flatRemainder_sub_bound (k : ℝ) (z : ℂ) (F : RealPlane →L[ℝ] ℂ)
    (C : ℂ →L[ℝ] RealPlane) {v w : RealPlane} (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖flatRemainder k z F C v-flatRemainder k z F C w‖≤
      (‖C‖*derivativeVariationBound k*‖F‖^2)*‖v-w‖ := by
  have hfv : ‖F v‖≤‖F‖ := (F.le_opNorm v).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg F))
  have hfw : ‖F w‖≤‖F‖ := (F.le_opNorm w).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (norm_nonneg F))
  calc
    _ = ‖C (liftRemainder k z (F v)-liftRemainder k z (F w))‖ := by rw [map_sub]; rfl
    _ ≤ ‖C‖*‖liftRemainder k z (F v)-liftRemainder k z (F w)‖ := C.le_opNorm _
    _ ≤ ‖C‖*(derivativeVariationBound k*‖F‖*‖F v-F w‖) :=
      mul_le_mul_of_nonneg_left (liftRemainder_sub_bound k z hfv hfw) (norm_nonneg C)
    _ ≤ ‖C‖*(derivativeVariationBound k*‖F‖*(‖F‖*‖v-w‖)) := by
      rw [←map_sub]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (F.le_opNorm (v-w))
        (mul_nonneg (derivativeVariationBound_nonneg k) (norm_nonneg F))) (norm_nonneg C)
    _ = _ := by ring

end StandardMapEntropy

end
end

end OAI
