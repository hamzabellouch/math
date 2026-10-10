import Mathlib
import OAI.Probability.ThreeState.RadialMoments

namespace OAI

/-! Radial logarithmic derivatives and the entropy inequality. -/

namespace ThreeState.Radial

noncomputable def ray (v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := fun i => t*v i
noncomputable def logAvg (v : Fin 3 → ℝ) := avg (fun i => Real.log (1+v i))
noncomputable def logVariance (v : Fin 3 → ℝ) := avg (fun i => (centeredLog v i)^2)
noncomputable def weightedLogVariance (v : Fin 3 → ℝ) :=
  avg (fun i => (1+v i)*(centeredLog v i)^2)
 
noncomputable def energy (v : Fin 3 → ℝ) :=
  3*logAvg v+2*logMoment v+(2/5 : ℝ)*weightedLogVariance v
 
noncomputable def gapY (v : Fin 3 → ℝ) :=
  1-invMoment v 1-6*logAvg v-2*logMoment v-(2/5 : ℝ)*weightedLogVariance v-
    (2/5 : ℝ)*logVariance v+(4/5 : ℝ)*invMoment v 1*logMoment v-(momentX v)^2
 
noncomputable def gapZ (v : Fin 3 → ℝ) :=
  6*logAvg v-5+(26/5 : ℝ)*invMoment v 1-invMoment v 2+
    (4/5 : ℝ)*logVariance v+(4/5 : ℝ)*(invMoment v 2-2*invMoment v 1)*logMoment v+
    (4/5 : ℝ)*logInvMoment v 1+(4/5 : ℝ)*(invMoment v 1)^2-3*(momentX v)^2

lemma avg_hasDerivAt (f : Fin 3 → ℝ → ℝ) (f' : Fin 3 → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt (f i) (f' i) t) :
    HasDerivAt (fun t => avg (fun i => f i t)) (avg f') t := by
  simp only [avg_expand]
  exact (((hf 0).add (hf 1)).add (hf 2)).div_const 3

lemma avg_ray (v : Fin 3 → ℝ) (t : ℝ) : avg (ray v t) = t*avg v := by
  simp only [avg_expand, ray]; ring
lemma X_ray (v : Fin 3 → ℝ) (t : ℝ) : momentX (ray v t) = t^2*momentX v := by
  simp only [momentX, avg_expand, ray]; ring
lemma centeredLog_avg_zero (v : Fin 3 → ℝ) : avg (centeredLog v) = 0 := by
  simp only [centeredLog, avg_expand]; ring

lemma ray_log_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (hp : ∀ i, 1+t*v i ≠ 0)
    (i : Fin 3) : HasDerivAt (fun t => Real.log (1+t*v i)) (v i/(1+t*v i)) t := by
  simpa using (((hasDerivAt_id t).mul_const (v i)).const_add 1).log (hp i)
lemma ray_inv_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (hp : ∀ i, 1+t*v i ≠ 0)
    (i : Fin 3) : HasDerivAt (fun t => (1+t*v i)⁻¹) (-v i/(1+t*v i)^2) t := by
  convert (((hasDerivAt_id t).mul_const (v i)).const_add 1).inv (hp i) using 1 <;>
    first | rfl | norm_num

lemma logAvg_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => logAvg (ray v t)) ((1-invMoment (ray v t) 1)/t) t := by
  have hh := avg_hasDerivAt (fun i t => Real.log (1+t*v i)) (fun i => v i/(1+t*v i)) t
    (ray_log_hasDerivAt v t hp)
  convert hh using 1
  · rfl
  · simp only [invMoment, avg_expand, ray, pow_one]
    field_simp [hp 0, hp 1, hp 2]
    ring

lemma centeredLog_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) (i : Fin 3) :
    HasDerivAt (fun t => centeredLog (ray v t) i)
      ((invMoment (ray v t) 1-(1+t*v i)⁻¹)/t) t := by
  have hh := (ray_log_hasDerivAt v t hp i).sub (logAvg_hasDerivAt v t ht hp)
  convert hh using 1 <;> first | rfl | (field_simp [hp i]; ring)

lemma invMoment_one_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => invMoment (ray v t) 1)
      ((invMoment (ray v t) 2-invMoment (ray v t) 1)/t) t := by
  have hh := avg_hasDerivAt (fun i t => (1+t*v i)⁻¹)
    (fun i => -v i/(1+t*v i)^2) t (ray_inv_hasDerivAt v t hp)
  convert hh using 1
  · simp only [invMoment, ray, pow_one]
  · simp only [invMoment, avg_expand, ray, pow_one]
    field_simp [hp 0, hp 1, hp 2]
    ring

lemma invMoment_two_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => invMoment (ray v t) 2)
      ((2*(invMoment (ray v t) 3-invMoment (ray v t) 2))/t) t := by
  have hh := avg_hasDerivAt (fun i t => ((1+t*v i)⁻¹)^2)
    (fun i => 2*(1+t*v i)⁻¹*(-v i/(1+t*v i)^2)) t
    (fun i => by
      convert (ray_inv_hasDerivAt v t hp i).pow 2 using 1; first | rfl | norm_num)
  convert hh using 1
  · rfl
  · simp only [invMoment, avg_expand, ray]
    field_simp [hp 0, hp 1, hp 2]
    ring

lemma logMoment_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => logMoment (ray v t))
      ((logMoment (ray v t)+invMoment (ray v t) 1-1)/t) t := by
  have hh := avg_hasDerivAt
    (fun i t => t*v i*centeredLog (ray v t) i)
    (fun i => v i*centeredLog (ray v t) i+t*v i*((invMoment (ray v t) 1-(1+t*v i)⁻¹)/t)) t
    (fun i => by
      convert ((hasDerivAt_id t).mul_const (v i)).mul (centeredLog_hasDerivAt v t ht hp i) using 1 <;>
        first | rfl | simp)
  have hv2 := zero_sum_elim v hv
  convert hh using 1
  · rfl
  · simp only [logMoment, invMoment, avg_expand, ray, pow_one]
    field_simp [hp 0, hp 1, hp 2]
    rw [hv2]
    ring

lemma logVariance_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => logVariance (ray v t))
      ((-2*logInvMoment (ray v t) 1)/t) t := by
  have hh := avg_hasDerivAt
    (fun i t => (centeredLog (ray v t) i)^2)
    (fun i => 2*centeredLog (ray v t) i*((invMoment (ray v t) 1-(1+t*v i)⁻¹)/t)) t
    (fun i => by
      convert (centeredLog_hasDerivAt v t ht hp i).pow 2 using 1; first | rfl | norm_num)
  have hu2 := zero_sum_elim (centeredLog (ray v t)) (centeredLog_avg_zero (ray v t))
  convert hh using 1
  · rfl
  · simp only [logInvMoment, invMoment, avg_expand, pow_one]
    simp only [hu2, ray]
    ring

lemma weightedLogVariance_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => weightedLogVariance (ray v t))
      ((weightedLogVariance (ray v t)-logVariance (ray v t)+
        2*invMoment (ray v t) 1*logMoment (ray v t))/t) t := by
  have hh := avg_hasDerivAt
    (fun i t => (1+t*v i)*(centeredLog (ray v t) i)^2)
    (fun i => v i*(centeredLog (ray v t) i)^2+(1+t*v i)*
      (2*centeredLog (ray v t) i*((invMoment (ray v t) 1-(1+t*v i)⁻¹)/t))) t
    (fun i => by
      convert (((hasDerivAt_id t).mul_const (v i)).const_add 1).mul
        ((centeredLog_hasDerivAt v t ht hp i).pow 2) using 1 <;> first | rfl | norm_num)
  have hu2 := zero_sum_elim (centeredLog (ray v t)) (centeredLog_avg_zero (ray v t))
  convert hh using 1
  · rfl
  · simp only [weightedLogVariance, logVariance, logMoment, invMoment, avg_expand, pow_one]
    simp only [hu2, ray]
    field_simp [hp 0, hp 1, hp 2]
    ring

lemma logInvMoment_one_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => logInvMoment (ray v t) 1)
      (((invMoment (ray v t) 1)^2-invMoment (ray v t) 2-
        logInvMoment (ray v t) 1+logInvMoment (ray v t) 2)/t) t := by
  have hh := avg_hasDerivAt
    (fun i t => centeredLog (ray v t) i*(1+t*v i)⁻¹)
    (fun i => ((invMoment (ray v t) 1-(1+t*v i)⁻¹)/t)*(1+t*v i)⁻¹+
      centeredLog (ray v t) i*(-v i/(1+t*v i)^2)) t
    (fun i => (centeredLog_hasDerivAt v t ht hp i).mul (ray_inv_hasDerivAt v t hp i))
  convert hh using 1
  · simp only [logInvMoment, ray, pow_one]
  · simp only [logInvMoment, invMoment, avg_expand, pow_one, ray]
    field_simp [hp 0, hp 1, hp 2]
    ring

lemma X_hasDerivAt (v : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun t => momentX (ray v t)) (2*t*momentX v) t := by
  simp_rw [X_ray]
  convert ((hasDerivAt_id t).pow 2).mul_const (momentX v) using 1 <;> first | rfl | norm_num

lemma energy_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => energy (ray v t))
      ((gapY (ray v t)+2*energy (ray v t)+(momentX (ray v t))^2)/t) t := by
  have hh := (((logAvg_hasDerivAt v t ht hp).const_mul 3).add
    ((logMoment_hasDerivAt v hv t ht hp).const_mul 2)).add
    ((weightedLogVariance_hasDerivAt v t ht hp).const_mul (2/5 : ℝ))
  convert hh using 1 <;> first | rfl | (simp only [gapY, energy]; ring)

lemma gapY_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => gapY (ray v t))
      ((gapZ (ray v t)+gapY (ray v t))/t) t := by
  have hg := logAvg_hasDerivAt v t ht hp
  have hm := logMoment_hasDerivAt v hv t ht hp
  have hu := invMoment_one_hasDerivAt v t ht hp
  have hvv := weightedLogVariance_hasDerivAt v t ht hp
  have hw := logVariance_hasDerivAt v t ht hp
  have hx := X_hasDerivAt v t
  have hh := (((((((hasDerivAt_const t (1 : ℝ)).sub hu).sub (hg.const_mul 6)).sub
    (hm.const_mul 2)).sub (hvv.const_mul (2/5 : ℝ))).sub (hw.const_mul (2/5 : ℝ))).add
    ((hu.const_mul (4/5 : ℝ)).mul hm)).sub (hx.pow 2)
  convert hh using 1 <;> first | rfl | (simp only [gapY, gapZ, X_ray]; field_simp; ring)

lemma gapZ_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0) (t : ℝ) (ht : t ≠ 0)
    (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => gapZ (ray v t))
      ((gExpr (ray v t)-12*(momentX (ray v t))^2)/t) t := by
  have hg := logAvg_hasDerivAt v t ht hp
  have hm := logMoment_hasDerivAt v hv t ht hp
  have hu := invMoment_one_hasDerivAt v t ht hp
  have hu2 := invMoment_two_hasDerivAt v t ht hp
  have hw := logVariance_hasDerivAt v t ht hp
  have hs := logInvMoment_one_hasDerivAt v t ht hp
  have hx := X_hasDerivAt v t
  have hh := ((((((((hg.const_mul 6).sub_const 5).add (hu.const_mul (26/5 : ℝ))).sub hu2).add
    (hw.const_mul (4/5 : ℝ))).add
    (((hu2.sub (hu.const_mul 2)).const_mul (4/5 : ℝ)).mul hm)).add
    (hs.const_mul (4/5 : ℝ))).add ((hu.pow 2).const_mul (4/5 : ℝ))).sub
    ((hx.pow 2).const_mul 3)
  convert hh using 1 <;> first | rfl | (simp only [gExpr, X_ray, Pi.sub_apply]; field_simp; ring)

end ThreeState.Radial
namespace ThreeState.Radial

@[simp] lemma ray_zero (v : Fin 3 → ℝ) : ray v 0 = 0 := by ext i; simp [ray]
@[simp] lemma ray_one (v : Fin 3 → ℝ) : ray v 1 = v := by ext i; simp [ray]
@[simp] lemma logAvg_zero : logAvg 0 = 0 := by norm_num [logAvg, avg_expand]
@[simp] lemma centeredLog_zero (i : Fin 3) : centeredLog 0 i = 0 := by
  norm_num [centeredLog, avg_expand]
@[simp] lemma logMoment_zero : logMoment 0 = 0 := by norm_num [logMoment, avg_expand]
@[simp] lemma logVariance_zero : logVariance 0 = 0 := by norm_num [logVariance, avg_expand]
@[simp] lemma weightedLogVariance_zero : weightedLogVariance 0 = 0 := by
  norm_num [weightedLogVariance, avg_expand]
@[simp] lemma invMoment_zero (n : ℕ) : invMoment 0 n = 1 := by
  norm_num [invMoment, avg_expand]
@[simp] lemma logInvMoment_zero (n : ℕ) : logInvMoment 0 n = 0 := by
  norm_num [logInvMoment, avg_expand]
@[simp] lemma momentX_zero : momentX 0 = 0 := by norm_num [momentX, avg_expand]
@[simp] lemma energy_zero : energy 0 = 0 := by norm_num [energy]
@[simp] lemma gapY_zero : gapY 0 = 0 := by norm_num [gapY]
@[simp] lemma gapZ_zero : gapZ 0 = 0 := by norm_num [gapZ]

lemma logAvg_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => logAvg (ray v t)) 0 0 := by
  have hh := avg_hasDerivAt (fun i t => Real.log (1+t*v i)) v 0 (fun i => by
    simpa using ray_log_hasDerivAt v 0 (by simp) i)
  simpa [logAvg, ray, hv] using hh

lemma centeredLog_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) (i : Fin 3) :
    HasDerivAt (fun t => centeredLog (ray v t) i) (v i) 0 := by
  have hh := (ray_log_hasDerivAt v 0 (by simp) i).sub (logAvg_hasDerivAt_zero v hv)
  convert hh using 1 <;> first | rfl | simp

lemma invMoment_one_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => invMoment (ray v t) 1) 0 0 := by
  have hh := avg_hasDerivAt (fun i t => (1+t*v i)⁻¹) (fun i => -v i) 0
    (fun i => by simpa using ray_inv_hasDerivAt v 0 (by simp) i)
  have hz : avg (fun i => -v i) = 0 := by simp only [avg_expand] at *; linarith
  simpa [invMoment, ray, hz] using hh

lemma logMoment_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => logMoment (ray v t)) 0 0 := by
  have hh := avg_hasDerivAt (fun i t => t*v i*centeredLog (ray v t) i) (fun _ => 0) 0
    (fun i => by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const (v i)).mul
        (centeredLog_hasDerivAt_zero v hv i) using 1 <;> first | rfl | simp)
  simpa [logMoment, ray, avg_expand, centeredLog] using hh

lemma logVariance_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => logVariance (ray v t)) 0 0 := by
  have hh := avg_hasDerivAt (fun i t => (centeredLog (ray v t) i)^2) (fun _ => 0) 0
    (fun i => by
      convert (centeredLog_hasDerivAt_zero v hv i).pow 2 using 1; first | rfl | simp)
  simpa [logVariance, avg_expand] using hh

lemma weightedLogVariance_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => weightedLogVariance (ray v t)) 0 0 := by
  have hh := avg_hasDerivAt (fun i t => (1+t*v i)*(centeredLog (ray v t) i)^2) (fun _ => 0) 0
    (fun i => by
      convert (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add 1).mul
        ((centeredLog_hasDerivAt_zero v hv i).pow 2) using 1 <;> first | rfl | simp)
  simpa [weightedLogVariance, ray, avg_expand, centeredLog] using hh

lemma gapY_hasDerivAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    HasDerivAt (fun t => gapY (ray v t)) 0 0 := by
  have hu := invMoment_one_hasDerivAt_zero v hv
  have hm := logMoment_hasDerivAt_zero v hv
  have hh := (((((((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hu).sub
    ((logAvg_hasDerivAt_zero v hv).const_mul 6)).sub (hm.const_mul 2)).sub
    ((weightedLogVariance_hasDerivAt_zero v hv).const_mul (2/5 : ℝ))).sub
    ((logVariance_hasDerivAt_zero v hv).const_mul (2/5 : ℝ))).add
    ((hu.const_mul (4/5 : ℝ)).mul hm)).sub ((X_hasDerivAt v 0).pow 2)
  convert hh using 1 <;> first | rfl | simp

lemma logAvg_continuousAt (v : Fin 3 → ℝ) (t : ℝ) (hp : ∀ i, 1+t*v i ≠ 0) :
    ContinuousAt (fun t => logAvg (ray v t)) t := by
  have hh (i : Fin 3) := (ray_log_hasDerivAt v t hp i).continuousAt
  simp only [logAvg, avg_expand, ray]
  exact (((hh 0).add (hh 1)).add (hh 2)).div_const 3

lemma centeredLog_continuousAt (v : Fin 3 → ℝ) (t : ℝ)
    (hp : ∀ i, 1+t*v i ≠ 0) (i : Fin 3) :
    ContinuousAt (fun t => centeredLog (ray v t) i) t :=
  ((ray_log_hasDerivAt v t hp i).continuousAt).sub (logAvg_continuousAt v t hp)

lemma gapZ_continuousAt (v : Fin 3 → ℝ) (t : ℝ) (hp : ∀ i, 1+t*v i ≠ 0) :
    ContinuousAt (fun t => gapZ (ray v t)) t := by
  have hg := logAvg_continuousAt v t hp
  have hu (i : Fin 3) := centeredLog_continuousAt v t hp i
  have hinv (i : Fin 3) := (ray_inv_hasDerivAt v t hp i).continuousAt
  unfold gapZ invMoment logMoment logVariance logInvMoment momentX
  simp only [avg_expand, ray]
  fun_prop

lemma normalized_gapY_continuousAt_zero (v : Fin 3 → ℝ) (hv : avg v = 0) :
    ContinuousAt (fun t => gapY (ray v t)/t) 0 := by
  have hh := (gapY_hasDerivAt_zero v hv).continuousAt_div
  simp only [ray_zero, gapY_zero, sub_zero] at hh
  have heq : Function.update (fun t => gapY (ray v t)/t) 0 0 =
      (fun t => gapY (ray v t)/t) := by
    ext t
    by_cases ht : t = 0
    · simp [ht]
    · simp [Function.update, ht]
  rwa [heq] at hh

lemma gapZ_nonneg (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ gapZ (ray v t) := by
  have hmono : MonotoneOn (fun t => gapZ (ray v t)) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      (gExpr (ray v t)-12*(momentX (ray v t))^2)/t) (convex_Icc _ _)
    · intro s hs
      exact (gapZ_continuousAt v s (fun i =>
        ne_of_gt (message_segment_pos v hp s hs.1 hs.2 i))).continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (gapZ_hasDerivAt v hv s hs.1.ne' (fun i =>
        ne_of_gt (message_segment_pos v hp s hs.1.le hs.2.le i))).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      apply div_nonneg _ hs.1.le
      apply sub_nonneg.mpr
      apply gExpr_lower (ray v s)
      · rw [avg_ray, hv, mul_zero]
      · exact fun i => message_segment_pos v hp s hs.1.le hs.2.le i
  simpa using hmono (by simp) ⟨ht0, ht1⟩ ht0

lemma normalized_gapY_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0)
    (t : ℝ) (ht : t ≠ 0) (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => gapY (ray v t)/t) (gapZ (ray v t)/t^2) t := by
  have hh := (gapY_hasDerivAt v hv t ht hp).div (hasDerivAt_id t) ht
  convert hh using 1 <;> first | rfl | (simp only [id_eq]; field_simp; ring)

lemma gapY_nonneg (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ gapY (ray v t) := by
  have hmono : MonotoneOn (fun t => gapY (ray v t)/t) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      gapZ (ray v t)/t^2) (convex_Icc _ _)
    · intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · rw [← h]
        exact (normalized_gapY_continuousAt_zero v hv).continuousWithinAt
      · exact (normalized_gapY_hasDerivAt v hv s h.ne' (fun i =>
          ne_of_gt (message_segment_pos v hp s hs.1 hs.2 i))).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (normalized_gapY_hasDerivAt v hv s hs.1.ne' (fun i =>
        ne_of_gt (message_segment_pos v hp s hs.1.le hs.2.le i))).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact div_nonneg (gapZ_nonneg v hv hp s hs.1.le hs.2.le) (sq_nonneg s)
  have h := hmono (by simp) ⟨ht0, ht1⟩ ht0
  simp only [div_zero] at h
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · simp [← h0]
  · simpa using (le_div_iff₀ h0).mp h

lemma normalized_energy_hasDerivAt (v : Fin 3 → ℝ) (hv : avg v = 0)
    (t : ℝ) (ht : t ≠ 0) (hp : ∀ i, 1+t*v i ≠ 0) :
    HasDerivAt (fun t => (energy (ray v t)-(1/2 : ℝ)*(momentX (ray v t))^2)/t^2)
      (gapY (ray v t)/t^3) t := by
  have hh := ((energy_hasDerivAt v hv t ht hp).sub
    (((X_hasDerivAt v t).pow 2).const_mul (1/2 : ℝ))).div ((hasDerivAt_id t).pow 2)
    (pow_ne_zero 2 ht)
  convert hh using 1 <;> first | rfl | (simp only [X_ray, id_eq, Pi.pow_apply, Pi.sub_apply]; field_simp; ring)

 
theorem radial_inequality (v : Fin 3 → ℝ) (hv : avg v = 0) (hp : ∀ i, 0 < 1+v i)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    (1-l^2)/2*(momentX v)^2 ≤ energy v-l⁻¹^2*energy (ray v l) := by
  have hmono : MonotoneOn
      (fun t => (energy (ray v t)-(1/2 : ℝ)*(momentX (ray v t))^2)/t^2)
      (Set.Icc l 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t =>
      gapY (ray v t)/t^3) (convex_Icc _ _)
    · intro s hs
      exact (normalized_energy_hasDerivAt v hv s (lt_of_lt_of_le hl0 hs.1).ne' (fun i =>
        ne_of_gt (message_segment_pos v hp s (le_trans hl0.le hs.1) hs.2 i))).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (normalized_energy_hasDerivAt v hv s (lt_trans hl0 hs.1).ne' (fun i =>
        ne_of_gt (message_segment_pos v hp s (lt_trans hl0 hs.1).le hs.2.le i))).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact div_nonneg (gapY_nonneg v hv hp s (lt_trans hl0 hs.1).le hs.2.le)
        (pow_nonneg (lt_trans hl0 hs.1).le 3)
  have hh := hmono ⟨le_rfl, hl1.le⟩ ⟨hl1.le, le_rfl⟩ hl1.le
  simp only [ray_one, X_ray, one_pow, div_one] at hh
  have hl : l ≠ 0 := hl0.ne'
  have hsq : 0 < l^2 := sq_pos_of_pos hl0
  rw [div_le_iff₀ hsq] at hh
  apply (mul_le_mul_iff_left₀ hsq).mp
  field_simp [hl]
  nlinarith [hh]

end ThreeState.Radial
namespace ThreeState.Radial

 
noncomputable def sourceF (m : Fin 3 → ℝ) : ℝ :=
  3*avg (fun i => Real.log (m i)) +
  4*((1/2 : ℝ)*avg (fun i => (m i-1)*Real.log (m i))) +
  (4/5 : ℝ)*((1/2 : ℝ)*avg (fun i => m i*
    (Real.log (m i)-avg (fun j => Real.log (m j)))^2))

lemma avg_message_deviation (m : Fin 3 → ℝ) (hm : avg m = 1) :
    avg (fun i => m i-1) = 0 := by
  simp only [avg_expand] at *
  linarith

lemma logMoment_uncentered (v : Fin 3 → ℝ) (hv : avg v = 0) :
    logMoment v = avg (fun i => v i*Real.log (1+v i)) := by
  have hv2 := zero_sum_elim v hv
  simp only [logMoment, centeredLog, avg_expand, hv2]
  ring

lemma energy_sourceF (m : Fin 3 → ℝ) (hm : avg m = 1) :
    energy (fun i => m i-1) = sourceF m := by
  rw [energy, logMoment_uncentered _ (avg_message_deviation m hm)]
  simp only [logAvg, weightedLogVariance, centeredLog, sourceF]
  have he (i : Fin 3) : 1+(m i-1) = m i := by ring
  simp only [he]
  ring

 
theorem radial_source (m : Fin 3 → ℝ) (hm : avg m = 1) (hp : ∀ i, 0 < m i)
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1) :
    sourceF m-l⁻¹^2*sourceF (fun i => 1+l*(m i-1)) ≥
      (1-l^2)/2*((1/2 : ℝ)*avg (fun i => (m i-1)^2))^2 := by
  have hv := avg_message_deviation m hm
  have h := radial_inequality (fun i => m i-1) hv (by simpa using hp) l hl0 hl1
  have he : avg (fun i => 1+l*(m i-1)) = 1 := by
    simp only [avg_expand] at *
    nlinarith [hm]
  have hr : ray (fun i => m i-1) l = (fun i => (1+l*(m i-1))-1) := by
    ext i; simp [ray]
  rw [energy_sourceF m hm, hr, energy_sourceF _ he] at h
  convert h using 1
  simp only [momentX]
  ring

end ThreeState.Radial

end OAI
