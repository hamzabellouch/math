import Mathlib
import OAI.Probability.ThreeStateClauses.RadialBounds

namespace OAI

/-! Positive Moments. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Positive
open Radial

def fourthResolvent (v : Vec) (t : ℝ) : ℝ := avg (fun i ↦ v i^4/(1+t*v i))

def fourthEdgeResolvent (v : Vec) (lam t : ℝ) : ℝ :=
  avg (fun i ↦ v i^4/((1+t*v i)*(1+t*lam*v i)))

def momentA (m : Vec) : ℝ := ∫ t in (0:ℝ)..1, t^2*fourthResolvent (centered m) t

def momentQ (m : Vec) (lam : ℝ) : ℝ :=
  (1/2)*∫ t in (0:ℝ)..1, t^2*fourthEdgeResolvent (centered m) lam t

lemma fourthMoment {v : Vec} (hv : avg v = 0) :
    avg (fun i ↦ v i^4) = 6*momentX v^2 := by
  simp only [momentX, avg]; rw [third_eq hv]; ring

lemma fourthResolvent_eq {v : Vec} (hv : avg v = 0) {t : ℝ}
    (hp : ∀ i, 1+t*v i ≠ 0) (hD : denom v t ≠ 0) :
    fourthResolvent v t =
      (6*momentX v^2-10*t*momentX v*momentY v+4*t^2*momentY v^2)/denom v t := by
  have he (i : Fin 3) : v i^4/(1+t*v i) =
      (v i^3*(v i-t*v i^2+2*t^2*momentY v))/denom v t := by
    calc
      _ = v i^3*(v i/(1+t*v i)) := by ring
      _ = _ := by rw [rational_identity hv t i (hp i) hD]; ring
  simp only [fourthResolvent, he, avg_div]
  congr 1
  simp only [momentX, momentY, avg]
  rw [third_eq hv]; ring

lemma fraction_lower {z k : ℝ} (hz₀ : 0 ≤ z) (hz₁ : z < 1)
    (_hk₀ : -1 ≤ k) (hk₁ : k ≤ 1) (hD : 0 < 1-3*z^2+2*z^3*k) :
    4+(64/9)*(z-1/2)^2 ≤ (6-10*z*k+4*z^2*k^2)/(1-3*z^2+2*z^3*k) := by
  have hB : 0 < 1+z-2*z^2 := by nlinarith [mul_pos (by linarith : 0 < 1-z) (by linarith : 0 < 1+2*z)]
  have hBtop : 1+z-2*z^2 ≤ 9/8 := by nlinarith [sq_nonneg (z-1/4)]
  have hnum : 6-10*z+4*z^2 ≤ 6-10*z*k+4*z^2*k^2 := by
    have hfac : 0 ≤ 10-4*z*(k+1) := by nlinarith [mul_nonneg hz₀ (by linarith : 0 ≤ 1-k)]
    have := mul_nonneg (mul_nonneg hz₀ (by linarith : 0 ≤ 1-k)) hfac
    nlinarith
  have hnum0 : 0 ≤ 6-10*z+4*z^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-z) (by linarith : 0 ≤ 6-4*z)]
  have hden : 1-3*z^2+2*z^3*k ≤ 1-3*z^2+2*z^3 := by
    nlinarith [mul_nonneg (pow_nonneg hz₀ 3) (by linarith : 0 ≤ 1-k)]
  have hdenpos : 0 < 1-3*z^2+2*z^3 := lt_of_lt_of_le hD hden
  have heq : (6-10*z+4*z^2)/(1-3*z^2+2*z^3) = (6-4*z)/(1+z-2*z^2) := by
    apply (div_eq_div_iff (ne_of_gt hdenpos) (ne_of_gt hB)).2
    ring
  have hbase : 4+(64/9)*(z-1/2)^2 ≤ (6-4*z)/(1+z-2*z^2) := by
    apply (le_div_iff₀ hB).2
    have := mul_nonneg (sq_nonneg (z-1/2)) (sub_nonneg.mpr hBtop)
    nlinarith
  calc
    _ ≤ (6-4*z)/(1+z-2*z^2) := hbase
    _ = (6-10*z+4*z^2)/(1-3*z^2+2*z^3) := heq.symm
    _ ≤ (6-10*z+4*z^2)/(1-3*z^2+2*z^3*k) :=
      div_le_div_of_nonneg_left hnum0 hD hden
    _ ≤ _ := (div_le_div_iff_of_pos_right hD).2 hnum

lemma fourthResolvent_nonneg {m : Vec} (hm : PositiveMessage m)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ fourthResolvent (centered m) t := by
  have hi (i : Fin 3) : 0 ≤ centered m i^4/(1+t*centered m i) :=
    div_nonneg (by positivity) (edge_pos hm ht i).le
  unfold fourthResolvent avg
  exact div_nonneg (add_nonneg (add_nonneg (hi 0) (hi 1)) (hi 2)) (by norm_num)

lemma fourthResolvent_lower {m : Vec} (hm : PositiveMessage m) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) :
    (4+(64/9)*(t*Real.sqrt (momentX (centered m))-1/2)^2)*momentX (centered m)^2 ≤
      fourthResolvent (centered m) t := by
  let v := centered m
  let x := momentX v
  let y := momentY v
  have hx₀ : 0 ≤ x := momentX_nonneg v
  have hx₁ : x < 1 := momentX_lt_one hm
  by_cases hx : x = 0
  · have hn := fourthResolvent_nonneg hm ht
    change (4+(64/9)*(t*Real.sqrt x-1/2)^2)*x^2 ≤ fourthResolvent v t
    simpa [hx] using hn
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hx)
  let r := Real.sqrt x
  have hrpos : 0 < r := Real.sqrt_pos.mpr hxpos
  have hr2 : r^2 = x := Real.sq_sqrt hx₀
  have hr₁ : r < 1 := by nlinarith
  let k := y/r^3
  have hyr : y = k*r^3 := (div_mul_cancel₀ _ (pow_ne_zero 3 (ne_of_gt hrpos))).symm
  have hk2 : k^2 ≤ 1 := by
    have hxy : y^2 ≤ x^3 := moment_discriminant (avg_centered hm)
    have heq : k^2 = y^2/r^6 := by dsimp [k]; ring
    rw [heq, div_le_iff₀ (pow_pos hrpos 6)]
    rw [← hr2] at hxy
    nlinarith [hxy]
  have hk₀ : -1 ≤ k := by nlinarith [sq_nonneg (k+1)]
  have hk₁ : k ≤ 1 := by nlinarith [sq_nonneg (k-1)]
  have hz₀ : 0 ≤ t*r := mul_nonneg ht.1 hrpos.le
  have hz₁ : t*r < 1 := by nlinarith [ht.2]
  have hD := denom_pos hm ht
  have hDeq : denom v t = 1-3*(t*r)^2+2*(t*r)^3*k := by
    dsimp only [denom]
    change 1-3*t^2*x+2*t^3*y = _
    rw [← hr2, hyr]; ring
  have hD' : 0 < 1-3*(t*r)^2+2*(t*r)^3*k := by rw [← hDeq]; exact hD
  have heq : fourthResolvent v t = x^2*((6-10*(t*r)*k+4*(t*r)^2*k^2)/(1-3*(t*r)^2+2*(t*r)^3*k)) := by
    rw [fourthResolvent_eq (avg_centered hm) (fun i ↦ ne_of_gt (edge_pos hm ht i)) (ne_of_gt hD), hDeq]
    change (6*x^2-10*t*x*y+4*t^2*y^2)/_ = _
    rw [← hr2, hyr]; ring
  change (4+(64/9)*(t*r-1/2)^2)*x^2 ≤ fourthResolvent v t
  rw [heq, mul_comm (x^2)]
  exact mul_le_mul_of_nonneg_right (fraction_lower hz₀ hz₁ hk₀ hk₁ hD') (sq_nonneg x)

lemma fourthResolvent_continuousOn {m : Vec} (hm : PositiveMessage m) :
    ContinuousOn (fourthResolvent (centered m)) (Icc (0:ℝ) 1) := by
  have hi (i : Fin 3) : ContinuousOn (fun t : ℝ ↦ centered m i^4/(1+t*centered m i)) (Icc 0 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht ↦ ne_of_gt (edge_pos hm ht i))
  exact (((hi 0).add (hi 1)).add (hi 2)).div_const 3

lemma lower_integral (r x : ℝ) :
    (∫ t in (0:ℝ)..1, t^2*((4+(64/9)*(t*r-1/2)^2)*x^2)) =
      (37/27+(64/45)*(r-5/8)^2)*x^2 := by
  conv_lhs => arg 1; ext t; ring_nf
  simp (disch := apply Continuous.intervalIntegrable; fun_prop) only
    [intervalIntegral.integral_add, intervalIntegral.integral_mul_const, integral_pow]
  norm_num
  ring

theorem momentA_lower {m : Vec} (hm : PositiveMessage m) :
    (37/27)*momentX (centered m)^2 ≤ momentA m := by
  have hcr : ContinuousOn (fun t : ℝ ↦ t^2*fourthResolvent (centered m) t) (Icc 0 1) :=
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ t^2) (Icc 0 1)).mul (fourthResolvent_continuousOn hm)
  have hcl : Continuous (fun t : ℝ ↦ t^2*((4+(64/9)*(t*Real.sqrt (momentX (centered m))-1/2)^2)*momentX (centered m)^2)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hcl.intervalIntegrable 0 1) (hcr.intervalIntegrable_of_Icc (by norm_num))
    (fun t ht ↦ mul_le_mul_of_nonneg_left (fourthResolvent_lower hm ht) (sq_nonneg t))
  rw [lower_integral] at hi
  have hn : 0 ≤ (Real.sqrt (momentX (centered m))-5/8)^2*momentX (centered m)^2 := by positivity
  dsimp only [momentA]
  linarith

lemma avg_mono {a b : Vec} (h : ∀ i, a i ≤ b i) : avg a ≤ avg b := by
  unfold avg
  exact div_le_div_of_nonneg_right (add_le_add (add_le_add (h 0) (h 1)) (h 2)) (by norm_num)

lemma fourthResolvent_four {m : Vec} (hm : PositiveMessage m) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) : 4*momentX (centered m)^2 ≤ fourthResolvent (centered m) t := by
  have h := fourthResolvent_lower hm ht
  nlinarith [mul_nonneg (sq_nonneg (t*Real.sqrt (momentX (centered m))-1/2))
    (sq_nonneg (momentX (centered m)))]

lemma fourthEdgeResolvent_lower {m : Vec} (hm : PositiveMessage m) {lam t : ℝ}
    (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1) (ht : t ∈ Icc (0:ℝ) 1) :
    (2/(2+lam))*fourthResolvent (centered m) t ≤ fourthEdgeResolvent (centered m) lam t := by
  let v := centered m
  let a : Vec := fun i ↦ v i^4/(1+t*v i)
  let b : Vec := fun i ↦ 1+t*lam*v i
  let c : ℝ := 1+lam/2
  have hc : 0 < c := by dsimp [c]; linarith
  have htl : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl₀, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl₁ ht.1]⟩
  have hb (i : Fin 3) : 0 < b i := by dsimp [b]; exact edge_pos hm htl i
  have ha (i : Fin 3) : 0 ≤ a i := div_nonneg (by positivity) (edge_pos hm ht i).le
  have hab (i : Fin 3) : a i*b i = (1-lam)*a i+lam*v i^4 := by
    dsimp only [a, b]
    have hd : 1+t*v i ≠ 0 := ne_of_gt (edge_pos hm ht i)
    calc
      _ = (v i^4/(1+t*v i))*((1-lam)+lam*(1+t*v i)) := by ring
      _ = (1-lam)*(v i^4/(1+t*v i))+lam*((v i^4/(1+t*v i))*(1+t*v i)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hd]
  have habavg : avg (fun i ↦ a i*b i) = (1-lam)*fourthResolvent v t+6*lam*momentX v^2 := by
    simp_rw [hab]
    rw [avg_add, avg_mul, avg_mul, fourthMoment (avg_centered hm)]
    change (1-lam)*fourthResolvent v t+lam*(6*momentX v^2) = _
    ring
  have havga : avg a = fourthResolvent v t := rfl
  have havgab : avg (fun i ↦ a i/b i) = fourthEdgeResolvent v lam t := by
    simp only [a, b, fourthEdgeResolvent, div_div]
  have htangent (i : Fin 3) : a i*(2*c-b i) ≤ c^2*(a i/b i) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (hb i)).2
    nlinarith [mul_nonneg (ha i) (sq_nonneg (b i-c))]
  have hs : 2*c*fourthResolvent v t-((1-lam)*fourthResolvent v t+6*lam*momentX v^2) ≤
      c^2*fourthEdgeResolvent v lam t := by
    calc
      _ = avg (fun i ↦ a i*(2*c-b i)) := by
        rw [← habavg, ← havga]
        simp only [avg]; ring
      _ ≤ avg (fun i ↦ c^2*(a i/b i)) := avg_mono htangent
      _ = _ := by rw [avg_mul, havgab]
  have hfour := fourthResolvent_four hm ht
  have hh : 0 ≤ lam*((3/2)*fourthResolvent v t-6*momentX v^2) :=
    mul_nonneg hl₀ (by linarith)
  have hd : 0 ≤ c*(c*fourthEdgeResolvent v lam t-fourthResolvent v t) := by
    dsimp only [c] at hs ⊢
    nlinarith
  have hh' := (mul_nonneg_iff_of_pos_left hc).mp hd
  have hfinal : fourthResolvent v t/c ≤ fourthEdgeResolvent v lam t := by
    apply (div_le_iff₀ hc).2
    nlinarith
  have heq : (2/(2+lam))*fourthResolvent v t = fourthResolvent v t/c := by
    dsimp [c]
    field_simp
  rw [heq]
  exact hfinal

lemma fourthEdgeResolvent_continuousOn {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1) :
    ContinuousOn (fourthEdgeResolvent (centered m) lam) (Icc (0:ℝ) 1) := by
  have hi (i : Fin 3) : ContinuousOn
      (fun t : ℝ ↦ centered m i^4/((1+t*centered m i)*(1+t*lam*centered m i))) (Icc 0 1) := by
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    have htl : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl₀, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl₁ ht.1]⟩
    exact ne_of_gt (mul_pos (edge_pos hm ht i) (edge_pos hm htl i))
  exact (((hi 0).add (hi 1)).add (hi 2)).div_const 3

theorem momentQ_lower {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1) : momentA m/(2+lam) ≤ momentQ m lam := by
  have hcr : ContinuousOn (fun t : ℝ ↦ t^2*fourthEdgeResolvent (centered m) lam t) (Icc 0 1) :=
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ t^2) (Icc 0 1)).mul (fourthEdgeResolvent_continuousOn hm hl₀ hl₁)
  have hcl : ContinuousOn (fun t : ℝ ↦ t^2*((2/(2+lam))*fourthResolvent (centered m) t)) (Icc 0 1) :=
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ t^2) (Icc 0 1)).mul
      (continuousOn_const.mul (fourthResolvent_continuousOn hm))
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hcl.intervalIntegrable_of_Icc (by norm_num)) (hcr.intervalIntegrable_of_Icc (by norm_num))
    (fun t ht ↦ mul_le_mul_of_nonneg_left (fourthEdgeResolvent_lower hm hl₀ hl₁ ht) (sq_nonneg t))
  have he : (∫ t in (0:ℝ)..1, t^2*((2/(2+lam))*fourthResolvent (centered m) t)) =
      (2/(2+lam))*momentA m := by
    rw [momentA, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  rw [he] at hi
  have heq : (2/(2+lam))*momentA m = 2*(momentA m/(2+lam)) := by ring
  rw [heq] at hi
  dsimp only [momentQ]
  linarith

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Positive
open Radial

def residual (m : Vec) (lam : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, t*avg (fun i ↦ centered m i^3 /
    ((1+t*centered m i)*(1+t*lam*centered m i)))

lemma avg_integrable {f : ℝ → Vec} (h : ∀ i, IntervalIntegrable (fun t ↦ f t i) volume 0 1) :
    IntervalIntegrable (fun t ↦ avg (f t)) volume 0 1 :=
  (((h 0).add (h 1)).add (h 2)).div_const 3

lemma avg_continuousOn {f : ℝ → Vec} {S : Set ℝ} (h : ∀ i, ContinuousOn (fun t ↦ f t i) S) :
    ContinuousOn (fun t ↦ avg (f t)) S :=
  (((h 0).add (h 1)).add (h 2)).div_const 3

lemma edge_message {m : Vec} (hm : PositiveMessage m) {lam : ℝ} (hl : lam ∈ Icc (0:ℝ) 1) :
    PositiveMessage (edge lam m) := by
  refine ⟨fun i ↦ edge_pos hm hl i, ?_⟩
  change avg (fun i ↦ 1+lam*centered m i) = 1
  rw [avg_add, avg_const, avg_mul]
  rw [avg_centered hm]; ring

lemma centered_edge (m : Vec) (lam : ℝ) : centered (edge lam m) = fun i ↦ lam*centered m i := by
  funext i; simp [centered, edge]

lemma symEntropy_integral {m : Vec} (hm : PositiveMessage m) :
    symEntropy m = (1/2)*∫ t in (0:ℝ)..1, avg (fun i ↦ centered m i^2/(1+t*centered m i)) := by
  have hi (i : Fin 3) : IntervalIntegrable (fun t : ℝ ↦ centered m i^2/(1+t*centered m i)) volume 0 1 :=
    (continuousOn_const.div (by fun_prop : ContinuousOn (fun t : ℝ ↦ 1+t*centered m i) (Icc 0 1))
      (fun t ht ↦ ne_of_gt (edge_pos hm ht i))).intervalIntegrable_of_Icc (by norm_num)
  rw [integral_avg hi]
  have he (i : Fin 3) : (∫ t in (0:ℝ)..1, centered m i^2/(1+t*centered m i)) =
      centered m i*Real.log (m i) := by
    rw [← integral_log_edge hm i, ← intervalIntegral.integral_const_mul]
    congr 1; funext t; ring
  simp_rw [he]
  simp only [symEntropy, centered, avg]
  ring

lemma symEntropy_nonneg {m : Vec} (hm : PositiveMessage m) : 0 ≤ symEntropy m := by
  have hi (i : Fin 3) : 0 ≤ (m i-1)*Real.log (m i) := by
    rcases le_total 1 (m i) with h | h
    · exact mul_nonneg (sub_nonneg.mpr h) (Real.log_nonneg h)
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (Real.log_nonpos (hm.1 i).le h)
  dsimp only [symEntropy, avg]
  exact div_nonneg (div_nonneg (add_nonneg (add_nonneg (hi 0) (hi 1)) (hi 2)) (by norm_num)) (by norm_num)

lemma residual_continuousOn {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl : lam ∈ Icc (0:ℝ) 1) : ContinuousOn
      (fun t : ℝ ↦ t*avg (fun i ↦ centered m i^3/((1+t*centered m i)*(1+t*lam*centered m i)))) (Icc 0 1) := by
  apply continuousOn_id.mul
  apply avg_continuousOn
  intro i
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  have htl : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl.1, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl.2 ht.1]⟩
  exact ne_of_gt (mul_pos (edge_pos hm ht i) (edge_pos hm htl i))

lemma symEntropy_residual {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl : lam ∈ Icc (0:ℝ) 1) :
    symEntropy m = momentX (centered m)-lam*momentQ m lam-residual m lam/2 := by
  let v := centered m
  have hi : IntervalIntegrable (fun t : ℝ ↦ avg (fun i ↦ v i^2/(1+t*v i))) volume 0 1 := by
    apply (avg_continuousOn (fun i ↦ continuousOn_const.div (by fun_prop) (fun t ht ↦ ne_of_gt (edge_pos hm ht i)))).intervalIntegrable_of_Icc
    norm_num
  have hq : IntervalIntegrable (fun t : ℝ ↦ t^2*fourthEdgeResolvent v lam t) volume 0 1 :=
    ((by fun_prop : ContinuousOn (fun t : ℝ ↦ t^2) (Icc 0 1)).mul
      (fourthEdgeResolvent_continuousOn hm hl.1 hl.2)).intervalIntegrable_of_Icc (by norm_num)
  have hr : IntervalIntegrable (fun t : ℝ ↦ t*avg (fun i ↦ centered m i^3/((1+t*centered m i)*(1+t*lam*centered m i)))) volume 0 1 :=
    (residual_continuousOn hm hl).intervalIntegrable_of_Icc (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : avg (fun i ↦ v i^2/(1+t*v i)) =
      2*momentX v-lam*(t^2*fourthEdgeResolvent v lam t)-
      t*avg (fun i ↦ v i^3/((1+t*v i)*(1+t*lam*v i))) := by
    have he (i : Fin 3) : v i^2/(1+t*v i) = v i^2-lam*t^2*(v i^4/((1+t*v i)*(1+t*lam*v i)))-
        t*(v i^3/((1+t*v i)*(1+t*lam*v i))) := by
      have htlam : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl.1, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl.2 ht.1]⟩
      have h₁ : 1+t*v i ≠ 0 := ne_of_gt (edge_pos hm ht i)
      have h₂ : 1+t*lam*v i ≠ 0 := ne_of_gt (edge_pos hm htlam i)
      have h₁' : 1+v i*t ≠ 0 := by simpa only [mul_comm] using h₁
      have h₂' : 1+v i*t*lam ≠ 0 := by convert h₂ using 1; ring
      field_simp [h₁', h₂']
      ring
    simp_rw [he]
    rw [avg_sub, avg_sub, avg_mul, avg_mul]
    dsimp only [momentX, fourthEdgeResolvent]
    ring
  rw [symEntropy_integral hm]
  have hconvert := intervalIntegral.integral_congr (μ := volume) (a := (0:ℝ)) (b := 1) (fun t ht ↦ hp t (by simpa using ht))
  rw [hconvert, intervalIntegral.integral_sub ((intervalIntegrable_const).sub (hq.const_mul lam)) hr,
    intervalIntegral.integral_sub intervalIntegrable_const (hq.const_mul lam),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  dsimp only [momentQ, residual]
  ring

lemma powerResolvent_continuousOn {m : Vec} (hm : PositiveMessage m) (n : ℕ)
    {lam : ℝ} (hl : lam ∈ Icc (0:ℝ) 1) :
    ContinuousOn (fun t : ℝ ↦ avg (fun i ↦ centered m i^n/(1+t*lam*centered m i))) (Icc 0 1) := by
  apply avg_continuousOn
  intro i
  apply continuousOn_const.div (by fun_prop)
  intro t ht
  have htl : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl.1, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl.2 ht.1]⟩
  exact ne_of_gt (edge_pos hm htl i)

lemma edge_symEntropy_integral {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl : lam ∈ Icc (0:ℝ) 1) :
    symEntropy (edge lam m) = (lam^2/2)*∫ t in (0:ℝ)..1,
      avg (fun i ↦ centered m i^2/(1+t*lam*centered m i)) := by
  rw [symEntropy_integral (edge_message hm hl), centered_edge]
  have he (t : ℝ) : avg (fun i ↦ (lam*centered m i)^2/(1+t*(lam*centered m i))) =
      lam^2*avg (fun i ↦ centered m i^2/(1+t*lam*centered m i)) := by
    dsimp only [avg]; ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  ring

lemma symEntropy_edge_residual {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl : lam ∈ Icc (0:ℝ) 1) :
    symEntropy (edge lam m) = lam^2*(symEntropy m+(1-lam)*residual m lam/2) := by
  let v := centered m
  have hi : IntervalIntegrable (fun t : ℝ ↦ avg (fun i ↦ v i^2/(1+t*v i))) volume 0 1 := by
    simpa using (powerResolvent_continuousOn hm 2 (by norm_num : (1:ℝ) ∈ Icc 0 1)).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  have hr : IntervalIntegrable (fun t : ℝ ↦ t*avg (fun i ↦ v i^3/((1+t*v i)*(1+t*lam*v i)))) volume 0 1 :=
    (residual_continuousOn hm hl).intervalIntegrable_of_Icc (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : avg (fun i ↦ v i^2/(1+t*lam*v i)) =
      avg (fun i ↦ v i^2/(1+t*v i))+(1-lam)*(t*avg (fun i ↦ v i^3/((1+t*v i)*(1+t*lam*v i)))) := by
    have he (i : Fin 3) : v i^2/(1+t*lam*v i) = v i^2/(1+t*v i)+
        (1-lam)*t*(v i^3/((1+t*v i)*(1+t*lam*v i))) := by
      have htlam : t*lam ∈ Icc (0:ℝ) 1 := ⟨mul_nonneg ht.1 hl.1, by nlinarith [ht.2, mul_le_mul_of_nonneg_left hl.2 ht.1]⟩
      have h₁ : 1+v i*t ≠ 0 := by simpa only [mul_comm] using ne_of_gt (edge_pos hm ht i)
      have h₂ : 1+v i*t*lam ≠ 0 := by convert ne_of_gt (edge_pos hm htlam i) using 1; ring
      field_simp [h₁, h₂]
      ring
    simp_rw [he]
    rw [avg_add, avg_mul]
    ring
  rw [edge_symEntropy_integral hm hl, symEntropy_integral hm]
  have he := intervalIntegral.integral_congr (μ := volume) (a := (0:ℝ)) (b := 1) (fun t ht ↦ hp t (by simpa using ht))
  rw [he, intervalIntegral.integral_add hi (hr.const_mul (1-lam)), intervalIntegral.integral_const_mul]
  dsimp only [residual]
  ring

lemma momentA_identity {m : Vec} (hm : PositiveMessage m) :
    momentA m = momentY (centered m)-2*momentX (centered m)+2*symEntropy m := by
  let v := centered m
  have hi : IntervalIntegrable (fun t : ℝ ↦ avg (fun i ↦ v i^2/(1+t*v i))) volume 0 1 := by
    simpa using (powerResolvent_continuousOn hm 2 (by norm_num : (1:ℝ) ∈ Icc 0 1)).intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  have ha : IntervalIntegrable (fun t : ℝ ↦ t^2*fourthResolvent v t) volume 0 1 :=
    ((by fun_prop : ContinuousOn (fun t : ℝ ↦ t^2) (Icc 0 1)).mul
      (fourthResolvent_continuousOn hm)).intervalIntegrable_of_Icc (by norm_num)
  have hp (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : avg (fun i ↦ v i^2/(1+t*v i)) =
      2*momentX v-t*(2*momentY v)+t^2*fourthResolvent v t := by
    have he (i : Fin 3) : v i^2/(1+t*v i) = v i^2-t*v i^3+t^2*(v i^4/(1+t*v i)) := by
      have h₁ : 1+v i*t ≠ 0 := by simpa only [mul_comm] using ne_of_gt (edge_pos hm ht i)
      field_simp [h₁]
      ring
    simp_rw [he]
    rw [avg_add, avg_sub, avg_mul, avg_mul]
    dsimp only [momentX, momentY, fourthResolvent]
    ring
  have he := intervalIntegral.integral_congr (μ := volume) (a := (0:ℝ)) (b := 1) (fun t ht ↦ hp t (by simpa using ht))
  rw [symEntropy_integral hm, he]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) ha,
    intervalIntegral.integral_sub intervalIntegrable_const (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_mul_const, integral_id]
  dsimp only [momentA]
  ring

lemma momentY_residual {m : Vec} (hm : PositiveMessage m) {lam : ℝ}
    (hl : lam ∈ Icc (0:ℝ) 1) :
    momentY (centered m) = momentA m+2*lam*momentQ m lam+residual m lam := by
  rw [momentA_identity hm, symEntropy_residual hm hl]
  ring

end ThreeState.TreeClauses.Positive

end

end OAI
