import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Search

namespace OAI

/-! Continuation iteration. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma continuation_ramp_lower_of_le (G : MultiGraph n m) (hn : 0 < n)
    (hconn : G.Connected univ)
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) (hY : Y ∈ metricDomain G)
    {s t κ : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (u y : Fin m → ℝ) (hur : ∀e, u e ≤ ramp G s X e) (hy : ∀e, 0 ≤ y e)
    (hresp : ∀e, 0 < u e →
      (6*s*y e) • vecMulVec (G.incidence e) (G.incidence e) ≤ Y) :
    (1-t) • X+t • Y ∈ metricDomain G ∧ ∀e,
      lowerCapacity κ t (u e) (y e) ≤
        ramp G ((1+t)*s) ((1-t) • X+t • Y) e+κ := by
  have hnext := domain_convex G hX hY (by linarith : 0 ≤ 1-t) ht (by ring : 1-t+t=1)
  refine ⟨hnext,?_⟩
  intro e
  by_cases ha : 0 < u e
  · rw [lowerCapacity,ite_eq_left ha]
    have har : 0 < ramp G s X e := ha.trans_le (hur e)
    have hr := continuation_reciprocal G hn (domain_positive G hn hconn hX)
      hs ht ht1 (hy e) e (hresp e ha) (domain_positive G hn hconn hnext)
    have hscalar := ramp_scalar_lower (ramp_active G har).1 ht ht1
      (cappedParameter_le_two G s X e) (hy e) hr
    change min 1 (ramp G s X e+t*(5*y e-4)) ≤
      ramp G ((1+t)*s) ((1-t) • X+t • Y) e at hscalar
    have hh := (min_le_min_left (1:ℝ) (show u e+t*(5*y e-4) ≤ ramp G s X e+t*(5*y e-4) by linarith only [hur e])).trans hscalar
    linarith only [hh]
  · rw [lowerCapacity,ite_eq_right ha]
    linarith only [ramp_nonneg G ((1+t)*s) ((1-t) • X+t • Y) e]

lemma stepFeasible_mono_target (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q q' : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepFeasible H s κ t q u) (hqq : q' ≤ q) :
    x ∈ stepFeasible H s κ t q' u := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  refine ⟨hx.1,fun p => (hx.2 p).trans ?_⟩
  unfold slack
  apply sub_le_sub_left
  exact mul_le_mul_of_nonneg_right hqq (by
    have hh : (1:ℝ) ≤ partCount p := by exact_mod_cast partCount_pos p
    linarith only [hh])

noncomputable def StepFree.nextCapacity (x : StepFree n m) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) : ℝ :=
  max 0 (x.capacities κ u e-κ)

lemma StepFree.nextCapacity_nonneg (x : StepFree n m) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) :
    0 ≤ x.nextCapacity κ u e := le_max_left _ _

lemma StepFree.nextCapacity_bounds (H : MultiGraph n m)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepCore H s κ t u) (e : Fin m) :
    x.nextCapacity κ u e ≤ 1 ∧ x.capacities κ u e ≤ x.nextCapacity κ u e+κ := by
  have he : x.capacities κ u e ≤ κ+1 := by
    unfold StepFree.capacities
    split_ifs
    · exact (hx.2.2.2.2.1 e).2
    · linarith
  refine ⟨max_le (by norm_num) (by linarith only [he]),?_⟩
  have hh := le_max_right (0:ℝ) (x.capacities κ u e-κ)
  change x.capacities κ u e ≤ max 0 (x.capacities κ u e-κ)+κ
  linarith only [hh]

theorem stepFeasible_update (H : MultiGraph n m) (hn : 0 < n) (hconn : H.Connected univ)
    {s κ t q : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain H)
    (u : Fin m → ℝ) (hur : ∀e, u e ≤ ramp H s X e)
    {x : StepFree n m} (hx : x ∈ stepFeasible H s κ t q u) :
    (1-t) • X+t • x.matrix ∈ metricDomain H ∧
      (∀e, x.nextCapacity κ u e ≤ ramp H ((1+t)*s) ((1-t) • X+t • x.matrix) e) ∧
      (∀e, 0 ≤ x.nextCapacity κ u e ∧ x.nextCapacity κ u e ≤ 1) ∧
      ∀p, 0 ≤ slack H.left H.right (fun e => x.nextCapacity κ u e+κ) q p := by
  have had := stepCore_admissible H hn hx.1
  obtain ⟨hnew,hramp⟩ := continuation_ramp_lower_of_le H hn hconn hX had.1 hs ht ht1
    u x.y hur (fun e => (had.2.1 e).1) had.2.2
  refine ⟨hnew,?_,?_,?_⟩
  · intro e
    apply max_le (ramp_nonneg _ _ _ _)
    have hh := (stepCore_capacity_le H hx.1 e).trans (hramp e)
    linarith only [hh]
  · intro e
    exact ⟨x.nextCapacity_nonneg κ u e,(x.nextCapacity_bounds H hx.1 e).1⟩
  · intro p
    apply (hx.2 p).trans
    unfold slack capacity
    apply sub_le_sub_right
    apply sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (x.nextCapacity_bounds H hx.1 e).2
      (crossingIndicator_nonneg _ _ _)

end AlgorithmicThinTrees.MetricTests

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma search_error_le_step (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ) :
    4*(errorQ n m:ℝ) ≤ (stepQ m:ℝ) := by
  have hP := connected_size_five H hn hc
  have hP0 := graphSize_pos (n:=n) (m:=m)
  have hpow : (128:ℝ) ≤ (graphSize n m)^9 := calc
    _ ≤ (5:ℝ)^9 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hP 9
  have hh := scaled_inverse_power hP0 1 9 hpow
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd,_root_.zpow_neg_one] at hh
  have hbase := baseline_lower (n:=n) (m:=m)
  rw [cast_stepQ,cast_errorQ,continuationStep]
  linarith only [hh,hbase]

def target (m r : ℕ) (Q g : ℚ) : ℚ := Q-g*r*stepQ m-2*stepQ m

lemma cast_target (m r : ℕ) (Q g : ℚ) :
    (target m r Q g:ℝ)=(Q:ℝ)-(g:ℝ)*r*continuationStep m-2*continuationStep m := by
  simp only [target,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat,cast_stepQ]

theorem uniform_search_response :
    ∃r0 : ℕ, 8 ≤ r0 ∧ ∀r : ℕ, r0 ≤ r →
      ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.Connected univ → r ≤ m →
      ∀(u : Fin m → ℚ), (∀e, 0 ≤ (u e:ℝ)) → (∀e, (u e:ℝ) ≤ 1) →
      ∀(s Q g : ℚ), 0 < (s:ℝ) → (s:ℝ) ≤ (r:ℝ)^(1/4:ℝ) →
      3*(r:ℝ)/4 ≤ (Q:ℝ) → (Q:ℝ) ≤ r →
      (r:ℝ)^(-1/8:ℝ) ≤ (g:ℝ) → (g:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) →
      3 ≤ (g:ℝ)*r →
      (∀p, 0 ≤ slack H.left H.right (fun e => (u e:ℝ)+continuationBaseline m) (Q:ℝ) p) →
      (rational (search H s (target m r Q g) u)).real ∈
        stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
          ((Q:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (u e:ℝ)) := by
  obtain ⟨r0,hr0,hr⟩ := feasible_continuation_response
  refine ⟨r0,hr0,?_⟩
  intro r hrr n m H hn hc hrm u hu0 hu1 s Q g hs hsr hQ hQr hg hgg hgr hinv
  have hr8 : (8:ℝ) ≤ r := by exact_mod_cast hr0.trans hrr
  have hr1 : (1:ℝ) ≤ r := by linarith only [hr8]
  have hg0 : 0 ≤ (g:ℝ) := (Real.rpow_nonneg (Nat.cast_nonneg r) _).trans hg
  have hg2 : (g:ℝ) ≤ 2 := by
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by norm_num : (-1/8:ℝ) ≤ 0)
    linarith only [hp,hgg]
  obtain ⟨hκ,hκ1,hκm,ht,ht1,hκt,htm⟩ := continuation_parameters m
  have hsP : (s:ℝ) ≤ graphSize n m := calc
    _ ≤ (r:ℝ)^(1/4:ℝ) := hsr
    _ ≤ (r:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le hr1 (by norm_num)
    _ = r := Real.rpow_one _
    _ ≤ m := by exact_mod_cast hrm
    _ ≤ _ := by unfold graphSize; linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have hβ : (graphSize n m)⁻¹/32 ≤ continuationStep m := by
    unfold continuationStep
    linarith only [baseline_lower (n:=n) (m:=m)]
  have hgrt : 0 ≤ (g:ℝ)*r*continuationStep m := by positivity
  have hq : (graphSize n m)^(-12:ℤ) ≤ (target m r Q g:ℝ) := by
    have hP1 : 1 ≤ graphSize n m := by linarith only [connected_size_five H hn hc]
    have hpinv : (graphSize n m)^(-12:ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ hP1 (by norm_num)
    have hgt := mul_le_mul hg2 ht1 ht (by norm_num : (0:ℝ) ≤ 2)
    have hh := mul_le_mul_of_nonneg_right hgt (Nat.cast_nonneg r)
    rw [cast_target]
    nlinarith only [hpinv,hh,hr8,hQ,ht1]
  have hqm : (target m r Q g:ℝ)+continuationStep m ≤ m := by
    have hm : (r:ℝ) ≤ m := by exact_mod_cast hrm
    rw [cast_target]
    linarith only [hQr,hm,hgrt,ht]
  obtain ⟨w,hw,hp⟩ := hr r hrr n m H hn hc (fun e => (u e:ℝ)) hu0 hu1
    s Q g hs hsr hQ hQr hg hgg hinv
  obtain ⟨z,hz,_,_⟩ := response_to_stepFeasible H (by omega) ht hκt hw hp
  have hz' : z ∈ stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
      ((target m r Q g:ℝ)+continuationStep m+continuationStep m) (fun e => (u e:ℝ)) := by
    rw [cast_target]
    convert hz using 1
    ring_nf
  have hout := search_sound H hn hc s (target m r Q g) (continuationStep m) u
    hs.le hsP hq hqm hβ hu0 hz'
  apply stepFeasible_mono_target H (by omega) hout
  rw [cast_target]
  have hh := mul_le_mul_of_nonneg_right hgr ht
  have he := search_error_le_step H hn hc
  rw [cast_stepQ] at he
  nlinarith only [hh,he]

def qresponse (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  qproject n*((1/2:ℚ) • (A+Aᵀ))*qproject n

lemma cast_qresponse (A : Matrix (Fin n) (Fin n) ℚ) :
    (qresponse A).map (fun a => (a:ℝ))=responseMatrix (A.map (fun a => (a:ℝ))) := by
  ext i j
  simp only [qresponse,Matrix.map_apply,Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_add,cast_qproject,
    responseMatrix,centered]

structure State (n m : ℕ) where
  scale : ℚ
  quality : ℚ
  matrix : Matrix (Fin n) (Fin n) ℚ
  capacity : Fin m → ℚ

def update (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) : State n m :=
  let v := search H a.scale (target m r a.quality g) a.capacity
  { scale := (1+stepQ m)*a.scale
    quality := a.quality-2*g*r*stepQ m
    matrix := (1-stepQ m) • a.matrix+stepQ m • qresponse (rawMatrix v)
    capacity := fun e => if 0 < a.capacity e then max 0 (z v e-baselineQ m) else 0 }

noncomputable def State.realMatrix (a : State n m) : Matrix (Fin n) (Fin n) ℝ :=
  a.matrix.map (fun q => (q:ℝ))

def Invariant (H : MultiGraph n m) (a : State n m) : Prop :=
  0 < (a.scale:ℝ) ∧ a.realMatrix ∈ metricDomain H ∧
    (∀e, 0 ≤ (a.capacity e:ℝ) ∧ (a.capacity e:ℝ) ≤ 1 ∧
      (a.capacity e:ℝ) ≤ ramp H (a.scale:ℝ) a.realMatrix e) ∧
    ∀p, 0 ≤ slack H.left H.right (fun e => (a.capacity e:ℝ)+continuationBaseline m)
      (a.quality:ℝ) p

lemma update_realMatrix (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) :
    (update H r g a).realMatrix=(1-continuationStep m) • a.realMatrix+
      continuationStep m • (rational (search H a.scale (target m r a.quality g) a.capacity)).real.matrix := by
  have hh := cast_qresponse (rawMatrix (search H a.scale (target m r a.quality g) a.capacity))
  ext i j
  change ((((1-stepQ m)*a.matrix i j+stepQ m*_) : ℚ) : ℝ)=_
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,cast_stepQ]
  have hhi := congrFun (congrFun hh i) j
  exact congrArg (fun z : ℝ => (1-continuationStep m)*a.realMatrix i j+continuationStep m*z) hhi

lemma update_capacity (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) (e : Fin m) :
    ((update H r g a).capacity e:ℝ)=
      (rational (search H a.scale (target m r a.quality g) a.capacity)).real.nextCapacity
        (continuationBaseline m) (fun f => (a.capacity f:ℝ)) e := by
  simp only [update,StepFree.nextCapacity,StepFree.capacities]
  by_cases he : 0 < a.capacity e
  · have heR : 0 < (a.capacity e:ℝ) := by exact_mod_cast he
    simp only [ite_eq_left he,ite_eq_left heR,Rat.cast_max,Rat.cast_zero,Rat.cast_sub,cast_baselineQ]
    rfl
  · have heR : ¬0 < (a.capacity e:ℝ) := by exact_mod_cast he
    simp only [ite_eq_right he,ite_eq_right heR,Rat.cast_zero,sub_self,max_self]

lemma update_invariant (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (r : ℕ) (g : ℚ) (a : State n m) (ha : Invariant H a)
    (hv : (rational (search H a.scale (target m r a.quality g) a.capacity)).real ∈
      stepFeasible H (a.scale:ℝ) (continuationBaseline m) (continuationStep m)
        ((a.quality:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (a.capacity e:ℝ))) :
    Invariant H (update H r g a) := by
  have ht := (continuation_parameters m).2.2.2.1
  have ht1 := (continuation_parameters m).2.2.2.2.1
  have hh := stepFeasible_update H hn hc ha.1 ht (by linarith : continuationStep m ≤ 1/5)
    ha.2.1 (fun e => (a.capacity e:ℝ)) (fun e => (ha.2.2.1 e).2.2) hv
  have hs : ((update H r g a).scale:ℝ)=(1+continuationStep m)*(a.scale:ℝ) := by
    simp only [update,Rat.cast_mul,Rat.cast_add,Rat.cast_one,cast_stepQ]
  have hq : ((update H r g a).quality:ℝ)=(a.quality:ℝ)-2*(g:ℝ)*r*continuationStep m := by
    simp only [update,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,cast_stepQ]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hs]
    exact mul_pos (by linarith only [ht]) ha.1
  · rw [update_realMatrix]
    exact hh.1
  · intro e
    rw [update_capacity,hs,update_realMatrix]
    exact ⟨(hh.2.2.1 e).1,(hh.2.2.1 e).2,hh.2.1 e⟩
  · simpa only [update_capacity,hq] using hh.2.2.2

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
