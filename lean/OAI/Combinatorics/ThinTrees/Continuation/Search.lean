import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.PencilCorrectness

namespace OAI

/-! Continuation search. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Orientations
open scoped BigOperators
variable {n m : ℕ}

def sizeQ (n m : ℕ) : ℚ := n+m+2
def baselineQ (m : ℕ) : ℚ := 1/(m+1)
def stepQ (m : ℕ) : ℚ := baselineQ m/32
def radiusQ (n m : ℕ) : ℚ := (sizeQ n m)^(-50:ℤ)
def boundQ (n m : ℕ) : ℚ := 6*sizeQ n m*(dimension n m+1)
def errorQ (n m : ℕ) : ℚ := (sizeQ n m)^(-10:ℤ)

@[simp] lemma cast_sizeQ (n m : ℕ) : (sizeQ n m:ℝ)=graphSize n m := by
  simp [sizeQ,graphSize]
@[simp] lemma cast_baselineQ (m : ℕ) : (baselineQ m:ℝ)=continuationBaseline m := by
  simp [baselineQ,continuationBaseline]
@[simp] lemma cast_stepQ (m : ℕ) : (stepQ m:ℝ)=continuationStep m := by
  simp [stepQ,continuationStep]
@[simp] lemma cast_radiusQ (n m : ℕ) : (radiusQ n m:ℝ)=(graphSize n m)^(-50:ℤ) := by
  simp [radiusQ]
@[simp] lemma cast_boundQ (n m : ℕ) : (boundQ n m:ℝ)=6*graphSize n m*(dimension n m+1) := by
  simp [boundQ]
@[simp] lemma cast_errorQ (n m : ℕ) : (errorQ n m:ℝ)=(graphSize n m)^(-10:ℤ) := by
  simp [errorQ]

lemma sizeQ_two (n m : ℕ) : 2  ≤  sizeQ n m := by
  unfold sizeQ
  linarith only [Nat.cast_nonneg (α:=ℚ) n,Nat.cast_nonneg (α:=ℚ) m]
lemma radiusQ_pos (n m : ℕ) : 0 < radiusQ n m :=
  zpow_pos (by linarith only [sizeQ_two n m]) _
lemma radiusQ_le_one (n m : ℕ) : radiusQ n m ≤ 1 := by
  exact zpow_le_one_of_nonpos₀ (by linarith only [sizeQ_two n m]) (by norm_num)

lemma boundQ_nonneg (n m : ℕ) : 0 ≤ boundQ n m := by
  unfold boundQ sizeQ
  positivity

def search (H : MultiGraph n m) (s qbar : ℚ) (u : Fin m → ℚ) : Fin (dimension n m) → ℚ :=
  (continuationPencil H s (baselineQ m) (stepQ m) qbar (errorQ n m) u).search
    (radiusQ n m) (boundQ n m) 0

lemma coordinate_ball (c : StepFree n m) (F : FlowPoint n m) {ρ : ℝ}
    {v : EuclideanSpace ℝ (Fin (dimension n m))}
    (hv : v ∈ Metric.closedBall (WithLp.toLp 2 (encode c F)) ρ) :
    (step v).Close c ρ ∧ (flow v).Close F ρ := by
  apply close_step_flow
  intro i
  have hh := PiLp.norm_apply_le (v-WithLp.toLp 2 (encode c F)) i
  have hd : ‖v-WithLp.toLp 2 (encode c F)‖ ≤ ρ := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hv
  simpa only [PiLp.sub_apply,PiLp.toLp_apply,Real.norm_eq_abs] using hh.trans hd

lemma center_norm (c : StepFree n m) (F : FlowPoint n m)
    (hc : c.Bounded (6*graphSize n m)) (hF : F.Bounded (6*graphSize n m)) :
    ‖CurrentKS.RationalSDP.realVector (0 : Fin (dimension n m) → ℚ)-
      WithLp.toLp 2 (encode c F)‖ ≤ (boundQ n m:ℝ) := by
  have hb := encode_bound c F (show 0  ≤  6*graphSize n m from by positivity [graphSize_pos (n:=n) (m:=m)]) hc hF
  have hz : CurrentKS.RationalSDP.realVector (0 : Fin (dimension n m) → ℚ)=0 := by
    ext i
    simp [CurrentKS.RationalSDP.realVector]
  rw [hz,zero_sub,norm_neg,cast_boundQ]
  calc
    _  ≤  ∑i, |encode c F i| := CurrentKS.RationalSDP.norm_le_sum_abs _
    _  ≤  ∑_i : Fin (dimension n m), 6*graphSize n m := sum_le_sum (fun i _ =>  hb i)
    _ = (dimension n m:ℝ)*(6*graphSize n m) := by simp
    _  ≤  _ := by nlinarith only [graphSize_pos (n:=n) (m:=m)]

theorem search_sound (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    (s qbar : ℚ) (β : ℝ) (u : Fin m → ℚ)
    (hs : 0 ≤ (s:ℝ)) (hsP : (s:ℝ) ≤ graphSize n m)
    (hq : (graphSize n m)^(-12:ℤ) ≤ (qbar:ℝ)) (hqm : (qbar:ℝ)+β ≤ m)
    (hβ : (graphSize n m)⁻¹/32 ≤ β) (hu : ∀e, 0 ≤ (u e:ℝ))
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H (s:ℝ) (continuationBaseline m) (continuationStep m)
      ((qbar:ℝ)+β+β) (fun e =>  (u e:ℝ))) :
    (rational (search H s qbar u)).real ∈ stepFeasible H (s:ℝ)
      (continuationBaseline m) (continuationStep m) ((qbar:ℝ)-4*(errorQ n m:ℝ))
      (fun e =>  (u e:ℝ)) := by
  obtain ⟨c,F,hc,hF,hball⟩ := finite_continuation_inner_cube H hn hconn hs hsP hq hqm hβ
    (fun e =>  (u e:ℝ)) hu hz
  let B := continuationPencil H s (baselineQ m) (stepQ m) qbar (errorQ n m) u
  have hcb : Metric.closedBall (WithLp.toLp 2 (encode c F)) (radiusQ n m:ℝ) ⊆ B.feasible := by
    intro v hv
    have hclose := coordinate_ball c F hv
    rw [cast_radiusQ] at hclose
    have hf := hball (step v) (flow v) hclose.1 hclose.2
    change (B.realEval v).PosSemidef
    apply (continuationPencil_psd H s (baselineQ m) (stepQ m) qbar (errorQ n m) u v).mpr
    simpa only [cast_baselineQ,cast_stepQ,cast_errorQ] using hf
  have hsearch := B.search_accepts (radiusQ n m) (boundQ n m) 0
    (WithLp.toLp 2 (encode c F)) (radiusQ_pos n m) (radiusQ_le_one n m)
    (boundQ_nonneg n m) hcb (center_norm c F hc hF)
  have hp := (B.witness_none_iff _).mp hsearch
  change (B.realEval (fun i =>  (search H s qbar u i:ℝ))).PosSemidef at hp
  have hf := (continuationPencil_psd H s (baselineQ m) (stepQ m) qbar (errorQ n m) u _).mp hp
  rw [cast_baselineQ,cast_stepQ] at hf
  rw [rational_real]
  exact finiteStep_sound H (by omega) (by rw [cast_errorQ]; positivity [graphSize_pos (n:=n) (m:=m)]) hf

lemma search_fuel_bound (n m : ℕ) :
    CurrentKS.RationalSDP.searchFuel (dimension n m) (radiusQ n m) (boundQ n m) ≤
      2304*(n+m+2)^114+1 := by
  let P : ℚ := sizeQ n m
  let D : ℚ := dimension n m+1
  have hP : 1 ≤ P := by linarith only [sizeQ_two n m]
  have hP0 : 0 < P := by linarith only [hP]
  have hD : 0 < D := by dsimp [D]; positivity
  have hd : D ≤ 2*P^3 := by
    have hh : (dimension n m:ℚ) ≤ P^3 := by
      dsimp [P, sizeQ]
      exact_mod_cast dimension_bound n m
    have hp : 1 ≤ P^3 := one_le_pow₀ hP
    dsimp only [D]
    linarith only [hh,hp]
  have he : 4*(boundQ n m)^2/(CurrentKS.RationalSDP.searchStep (dimension n m) (radiusQ n m))^2 =
      144*P^102*D^4 := by
    change 4*(6*P*D)^2/(P^(-50:ℤ)/D)^2=144*P^102*D^4
    rw [_root_.zpow_neg]
    field_simp
    ring
  have hpow := pow_le_pow_left₀ hD.le hd 4
  have hh : 4*(boundQ n m)^2/(CurrentKS.RationalSDP.searchStep (dimension n m) (radiusQ n m))^2 ≤
      (2304*(n+m+2)^114:ℕ) := by
    rw [he]
    have ht := mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℚ) ≤ 144*P^102)
    have hr : 144*P^102*(2*P^3)^4=2304*P^114 := by ring
    rw [hr] at ht
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add,P,sizeQ] using ht
  unfold CurrentKS.RationalSDP.searchFuel
  exact Nat.succ_le_succ ((Nat.ceil_le).mpr hh)

lemma search_on_mesh (H : MultiGraph n m) (s qbar : ℚ) (u : Fin m → ℚ) :
    ∀i, ∃k : ℤ, search H s qbar u i =
      CurrentKS.RationalSDP.searchMesh (dimension n m) (radiusQ n m) (boundQ n m)*k := by
  apply CurrentKS.RationalSDP.Pencil.iterate_on_mesh
  intro i
  exact ⟨0,by simp⟩

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
