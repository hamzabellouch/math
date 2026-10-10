import OAI.NumberTheory.Jacobsthal.Analysis.ContinuousReference

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

abbrev Profile := Side → ℝ → ℝ → ℝ

def JointContinuous (H : Profile) : Prop := ∀ i,Continuous (fun p : ℝ×ℝ => H i p.1 p.2)

noncomputable def gate (H : Profile) (i : Side) (r b : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..upperCutoff i r b,H i.flip (r-x) x/(max 1 x)

theorem gate_integrand_continuous {H : Profile} (hH : JointContinuous H) (i : Side) (r : ℝ) :
    Continuous (fun x : ℝ => H i.flip (r-x) x/(max 1 x)) := by
  have hc : Continuous (fun x : ℝ => H i.flip (r-x) x) :=
    (hH i.flip).comp ((continuous_const.sub continuous_id).prodMk continuous_id)
  exact hc.div (continuous_const.max continuous_id) (fun x => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 x)))

theorem gate_continuous {H : Profile} (hH : JointContinuous H) : JointContinuous (gate H) := by
  intro i
  let F : (ℝ×ℝ) → ℝ → ℝ := fun p x => H i.flip (p.1-x) x/(max 1 x)
  have hc : Continuous (fun q : (ℝ×ℝ)×ℝ => H i.flip (q.1.1-q.2) q.2) :=
    (hH i.flip).comp ((continuous_fst.fst.sub continuous_snd).prodMk continuous_snd)
  have hd : Continuous (fun q : (ℝ×ℝ)×ℝ => max 1 q.2) := continuous_const.max continuous_snd
  have hF : Continuous F.uncurry := hc.div hd (fun q => ne_of_gt
    ((by norm_num : (0:ℝ)<1).trans_le (le_max_left 1 q.2)))
  exact continuous_variable_upper_integral F hF (fun p => upperCutoff i p.1 p.2) (upperCutoff_continuous i)

theorem gate_add {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (i : Side) (r b : ℝ) :
    gate (fun j s t => H j s t+G j s t) i r b=gate H i r b+gate G i r b := by
  simp only [gate,add_div]
  exact intervalIntegral.integral_add
    ((gate_integrand_continuous hH i r).intervalIntegrable 1 _) ((gate_integrand_continuous hG i r).intervalIntegrable 1 _)

theorem gate_mul (c : ℝ) (H : Profile) (i : Side) (r b : ℝ) :
    gate (fun j s t => c*H j s t) i r b=c*gate H i r b := by
  simp only [gate,mul_div_assoc,intervalIntegral.integral_const_mul]

theorem gate_sum (N : ℕ) (H : ℕ → Profile) (hH : ∀ n,JointContinuous (H n))
    (i : Side) (r b : ℝ) :
    gate (fun j s t => ∑ n ∈ Finset.range N,H n j s t) i r b=
      ∑ n ∈ Finset.range N,gate (H n) i r b := by
  simp only [gate,Finset.sum_div]
  exact intervalIntegral.integral_finsetSum (fun n _ => (gate_integrand_continuous (hH n) i r).intervalIntegrable 1 _)

theorem gate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (i : Side) (r b : ℝ) :
    0 ≤ gate H i r b := by
  apply intervalIntegral.integral_nonneg_of_forall (upperCutoff_bounds i r b).1
  intro x
  exact div_nonneg (hH i.flip (r-x) x) (zero_le_one.trans (le_max_left 1 x))

theorem gate_odd_small (H : Profile) {r b : ℝ} (hr : r ≤ 4) : gate H .odd r b=0 := by
  rw [gate,upperCutoff_odd_small hr,intervalIntegral.integral_same]

end ErdosContinuousOmission

end

section

open _root_.MeasureTheory _root_.Set
namespace ErdosContinuousOmission
open ErdosContinuousBoundary NumberTheoryLean.FinitePathGeometry

noncomputable def gateIterate : ℕ → Profile → Profile
  | 0,H => H
  | n+1,H => gate (gateIterate n H)

theorem gateIterate_continuous {H : Profile} (hH : JointContinuous H) (n : ℕ) :
    JointContinuous (gateIterate n H) := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_continuous ih

theorem gateIterate_nonnegative {H : Profile} (hH : ∀ i r b,0 ≤ H i r b) (n : ℕ) :
    ∀ i r b,0 ≤ gateIterate n H i r b := by
  induction n with
  | zero => exact hH
  | succ n ih => exact gate_nonnegative ih

theorem gateIterate_depth_zero (H : Profile) (n : ℕ) (i : Side) {r b : ℝ}
    (hr : r ≤ (n:ℝ)+1) : gateIterate (n+2) H i r b=0 := by
  induction n generalizing i r b with
  | zero =>
    cases i with
    | odd => exact gate_odd_small (gateIterate 1 H) (by norm_num at hr; linarith)
    | even =>
      change (∫ x in (1:ℝ)..upperCutoff .even r b,gate H .odd (r-x) x/(max 1 x))=0
      calc
        _ = ∫ _x in (1:ℝ)..upperCutoff .even r b,(0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le (upperCutoff_bounds .even r b).1] at hx
          dsimp only
          rw [gate_odd_small H (by norm_num at hr; linarith [hx.1]),zero_div]
        _ = 0 := by simp
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,gateIterate,gate]
    calc
      _ = ∫ _x in (1:ℝ)..upperCutoff i r b,(0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (upperCutoff_bounds i r b).1] at hx
        dsimp only
        have hchild : r-x ≤ (n:ℝ)+1 := by push_cast at hr; linarith [hx.1]
        rw [ih i.flip hchild,zero_div]
      _ = 0 := by simp

theorem gateIterate_zero_of_index (H : Profile) {N : ℕ} (hN : 2 ≤ N) (i : Side)
    {r b : ℝ} (hr : r ≤ (N:ℝ)-1) : gateIterate N H i r b=0 := by
  have he : N=(N-2)+2 := by omega
  rw [he]
  apply gateIterate_depth_zero
  have hc : ((N-2:ℕ):ℝ)=(N:ℝ)-2 := by rw [Nat.cast_sub hN]; norm_num
  linarith

theorem gateIterate_add {H G : Profile} (hH : JointContinuous H) (hG : JointContinuous G)
    (n : ℕ) (i : Side) (r b : ℝ) :
    gateIterate n (fun j s t => H j s t+G j s t) i r b=
      gateIterate n H i r b+gateIterate n G i r b := by
  induction n generalizing i r b with
  | zero => rfl
  | succ n ih =>
    have he : gateIterate n (fun j s t => H j s t+G j s t)=
        (fun j s t => gateIterate n H j s t+gateIterate n G j s t) := by funext j s t; exact ih j s t
    rw [gateIterate,he]
    exact gate_add (gateIterate_continuous hH n) (gateIterate_continuous hG n) i r b

theorem gateIterate_gate (n : ℕ) (H : Profile) : gateIterate n (gate H)=gateIterate (n+1) H := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gateIterate,ih]

theorem finite_forcing_expansion {H F : Profile} (hH : JointContinuous H) (hF : JointContinuous F)
    (heq : ∀ i r b,H i r b=F i r b+gate H i r b) (N : ℕ) (i : Side) (r b : ℝ) :
    H i r b=(∑ n ∈ Finset.range N,gateIterate n F i r b)+gateIterate N H i r b := by
  have hf : H=(fun j s t => F j s t+gate H j s t) := by funext j s t; exact heq j s t
  have hs (n : ℕ) : gateIterate n H i r b=gateIterate n F i r b+gateIterate (n+1) H i r b := by
    calc
      _ = gateIterate n (fun j s t => F j s t+gate H j s t) i r b := congrArg (fun G => gateIterate n G i r b) hf
      _ = gateIterate n F i r b+gateIterate n (gate H) i r b := gateIterate_add hF (gate_continuous hH) n i r b
      _ = _ := by rw [gateIterate_gate]
  induction N with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,zero_add,gateIterate]
  | succ n ih =>
    rw [Finset.sum_range_succ,add_assoc,← hs n]
    exact ih

end ErdosContinuousOmission

end

end Erdos970

end OAI
