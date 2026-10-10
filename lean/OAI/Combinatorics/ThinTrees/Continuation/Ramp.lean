import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.CenteredDomain

namespace OAI

/-! Continuation ramp. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma incidence_ne_zero (G : MultiGraph n m) (e : Fin m) : G.incidence e ≠ 0 := by
  intro hz
  have he := congrFun hz (G.left e)
  simp [MultiGraph.incidence,MultiGraph.point,G.loopless e] at he

lemma centered_resistance_pos (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    0 < resistance G X e := by
  simpa only [resistance,inverseOnZeroSum,StrongThinTree.qform,star_trivial] using
    (regularize_pd hn hX).inv.dotProduct_mulVec_pos (incidence_ne_zero G e)

def cappedParameter (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  min 2 (s*resistance G X e)⁻¹

def ramp (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) : ℝ :=
  max 0 (cappedParameter G s X e-1)

lemma cappedParameter_pos (G : MultiGraph n m) (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    0 < cappedParameter G s X e :=
  lt_min (by norm_num) (inv_pos.mpr (mul_pos hs (centered_resistance_pos G hn hX e)))

lemma cappedParameter_le_two (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) :
    cappedParameter G s X e ≤ 2 := min_le_left _ _

lemma ramp_nonneg (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) :
    0 ≤ ramp G s X e := le_max_left _ _

lemma ramp_le_one (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) :
    ramp G s X e ≤ 1 := max_le (by norm_num) (by linarith [cappedParameter_le_two G s X e])

lemma ramp_active (G : MultiGraph n m) {s : ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {e : Fin m}
    (ha : 0 < ramp G s X e) :
    1 < cappedParameter G s X e ∧ ramp G s X e=cappedParameter G s X e-1 := by
  have hp : 0 < cappedParameter G s X e-1 := by
    simpa only [ramp,lt_max_iff,lt_self_iff_false,false_or] using ha
  exact ⟨by linarith,max_eq_right hp.le⟩

lemma capped_rankOne (G : MultiGraph n m) (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    (s*cappedParameter G s X e) • vecMulVec (G.incidence e) (G.incidence e) ≤ X := by
  rw [Matrix.le_iff,centered_resistance_order hn hX (incidence_sum G e)
    (mul_pos hs (cappedParameter_pos G hn hs hX e))]
  change s*cappedParameter G s X e*resistance G X e ≤ 1
  have hr : 0 < s*resistance G X e := mul_pos hs (centered_resistance_pos G hn hX e)
  have hm := mul_le_mul_of_nonneg_right
    (min_le_right (2:ℝ) (s*resistance G X e)⁻¹) hr.le
  rw [inv_mul_cancel₀ hr.ne'] at hm
  dsimp only [cappedParameter]
  nlinarith only [hm]

def lowerCapacity (κ t u y : ℝ) : ℝ :=
  if 0 < u then κ+min 1 (u+t*(5*y-4)) else κ

lemma lowerCapacity_lower {κ t u y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) :
    κ-4*t ≤ lowerCapacity κ t u y := by
  unfold lowerCapacity
  split_ifs with hu
  · have hm : -4*t ≤ min 1 (u+t*(5*y-4)) := by
      apply le_min
      · linarith
      · nlinarith [mul_nonneg ht hy]
    linarith
  · linarith

lemma lowerCapacity_nonneg {κ t u y : ℝ} (ht : 0 ≤ t) (hy : 0 ≤ y) (hκ : 4*t ≤ κ) :
    0 ≤ lowerCapacity κ t u y := (sub_nonneg.mpr hκ).trans (lowerCapacity_lower ht hy)

lemma lowerCapacity_le {κ t u y : ℝ} : lowerCapacity κ t u y ≤ κ+1 := by
  unfold lowerCapacity
  split_ifs
  · exact add_le_add_right (min_le_left _ _) κ
  · linarith

lemma continuation_scalar {t p y : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hp : p ≤ 2) (hy : 0 ≤ y) :
    p+t*(5*y-4) ≤ ((1-t)*p+6*t*y)/(1+t) := by
  apply (le_div_iff₀ (by linarith : 0 < 1+t)).mpr
  have hy' : 0 ≤ (1-5*t)*y := mul_nonneg (by linarith) hy
  have hrem : 0 ≤ t*((1-5*t)*y+4+4*t-2*p) :=
    mul_nonneg ht (by linarith)
  nlinarith only [hrem]

lemma ramp_scalar_lower {p z t y : ℝ} (hp : 1 < p) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hp2 : p ≤ 2) (hy : 0 ≤ y)
    (hz : ((1-t)*p+6*t*y)/(1+t) ≤ z) :
    min 1 (max 0 (p-1)+t*(5*y-4)) ≤ max 0 (min 2 z-1) := by
  rw [max_eq_right (by linarith : 0 ≤ p-1)]
  have hz' := (continuation_scalar ht ht1 hp2 hy).trans hz
  have hcap := min_le_min_left (2:ℝ) hz'
  have he : min (1:ℝ) (p-1+t*(5*y-4))=min 2 (p+t*(5*y-4))-1 := by
    rw [←min_sub_sub_right]
    congr 1 <;> ring
  rw [he]
  exact (sub_le_sub_right hcap 1).trans (le_max_right _ _)

lemma continuation_reciprocal (G : MultiGraph n m) (hn : 0 < n)
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X)
    {s t y : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hy : 0 ≤ y) (e : Fin m)
    (hresp : (6*s*y) • vecMulVec (G.incidence e) (G.incidence e) ≤ Y)
    (hnew : CenteredPositive ((1-t) • X+t • Y)) :
    ((1-t)*cappedParameter G s X e+6*t*y)/(1+t) ≤
      ((1+t)*s*resistance G ((1-t) • X+t • Y) e)⁻¹ := by
  let b := vecMulVec (G.incidence e) (G.incidence e)
  let p := cappedParameter G s X e
  let c := ((1-t)*p+6*t*y)*s
  have ht' : 0 < 1-t := by linarith
  have hp : 0 < p := cappedParameter_pos G hn hs hX e
  have hc : 0 < c := mul_pos (add_pos_of_pos_of_nonneg (mul_pos ht' hp) (by positivity)) hs
  have horder : c • b ≤ (1-t) • X+t • Y := by
    have h1 := (Matrix.le_iff.mp (capped_rankOne G hn hs hX e)).smul ht'.le
    have h2 := (Matrix.le_iff.mp hresp).smul ht
    apply Matrix.le_iff.mpr
    convert h1.add h2 using 1
    dsimp [c,p,b]
    simp only [smul_sub,smul_smul]
    module
  have hrank := (centered_resistance_order hn hnew (incidence_sum G e) hc).mp (Matrix.le_iff.mp horder)
  have hR := centered_resistance_pos G hn hnew e
  have hnR : 0 < (1+t)*s*resistance G ((1-t) • X+t • Y) e := by positivity
  rw [←one_div]
  apply (le_div_iff₀ hnR).mpr
  have hden : (1-t)*p+6*t*y ≥ 0 := by positivity
  have hquot := (div_mul_cancel₀ ((1-t)*p+6*t*y) (by linarith : (1+t) ≠ 0))
  have he : (((1-t)*p+6*t*y)/(1+t))*((1+t)*s*resistance G ((1-t) • X+t • Y) e)=
      c*resistance G ((1-t) • X+t • Y) e := by
    dsimp [c]
    calc
      _ = ((((1-t)*p+6*t*y)/(1+t))*(1+t))*(s*resistance G ((1-t) • X+t • Y) e) := by ring
      _ = _ := by rw [hquot]; ring
  rw [he]
  exact hrank

theorem continuation_ramp_lower (G : MultiGraph n m) (hn : 0 < n) (hconn : G.Connected univ)
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) (hY : Y ∈ metricDomain G)
    {s t κ : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (y : Fin m → ℝ) (hy : ∀e, 0 ≤ y e)
    (hresp : ∀e, 0 < ramp G s X e →
      (6*s*y e) • vecMulVec (G.incidence e) (G.incidence e) ≤ Y) :
    ((1-t) • X+t • Y) ∈ metricDomain G ∧ ∀e,
      lowerCapacity κ t (ramp G s X e) (y e) ≤
        ramp G ((1+t)*s) ((1-t) • X+t • Y) e+κ := by
  have hnext := domain_convex G hX hY (by linarith : 0 ≤ 1-t) ht (by ring : 1-t+t=1)
  refine ⟨hnext,?_⟩
  intro e
  by_cases hactive : 0 < ramp G s X e
  · rw [lowerCapacity,ite_eq_left hactive]
    have hrecip := continuation_reciprocal G hn (domain_positive G hn hconn hX)
      hs ht ht1 (hy e) e (hresp e hactive) (domain_positive G hn hconn hnext)
    have hscalar := ramp_scalar_lower (ramp_active G hactive).1 ht ht1
      (cappedParameter_le_two G s X e) (hy e) hrecip
    change min 1 (ramp G s X e+t*(5*y e-4)) ≤
      ramp G ((1+t)*s) ((1-t) • X+t • Y) e at hscalar
    linarith
  · rw [lowerCapacity,ite_eq_right hactive]
    linarith [ramp_nonneg G ((1+t)*s) ((1-t) • X+t • Y) e]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
