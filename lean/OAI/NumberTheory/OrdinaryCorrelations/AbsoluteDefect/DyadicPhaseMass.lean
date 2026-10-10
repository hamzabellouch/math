import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BoxAddWidth

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryLocalAdditive
open OrdinaryCorrelations OrdinarySharpWindow OrdinaryChainScales Finset Filter MeasureTheory
lemma dyadic_phase_mass {f : ℕ→ℂ} (hf : OneBounded f) (α : ℝ) (X : ℕ) :
    (∑n∈Ioc X (2*X),‖f n*phase (α*n)‖) ≤ (X:ℝ) := by
  have hc : (Finset.Ioc X (2*X)).card=X := by simp only [Nat.card_Ioc]; omega
  calc
    _ ≤ ∑n∈Ioc X (2*X),(1:ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,norm_phase,mul_one]
      exact hf n
    _ = _ := by simp [hc]
lemma dyadic_mass {f : ℕ→ℂ} (hf : OneBounded f) (X : ℕ) :
    (∑n∈Ioc X (2*X),‖f n‖) ≤ (X:ℝ) := by
  have hc : (Finset.Ioc X (2*X)).card=X := by simp only [Nat.card_Ioc]; omega
  calc
    _ ≤ ∑n∈Ioc X (2*X),(1:ℝ) := sum_le_sum (fun n hn=>hf n)
    _ = _ := by simp [hc]

theorem local_windowSmall {f : ℕ→ℂ} (hf : OneBounded f) {β : ℝ}
    (hβ : WindowSmall (fun n=>f n*phase (β*n))) {ε : ℝ} (hε : 0 < ε) :
    ∃η : ℝ,0 < η ∧ ∃D0 : ℕ,0 < D0 ∧ ∀ᶠ X : ℕ in atTop,
      ∀D : ℝ,(D0:ℝ) ≤ D → ∀α : ℝ,|α-β| ≤ η →
        (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (fun n=>f n*phase (α*n))
          (fun n=>(n:ℝ)) D x‖) < ε*D*X := by
  obtain ⟨L,hLp,hLE⟩ := hβ (ε/4) (by positivity)
  have hL : (0:ℝ) < L := by exact_mod_cast hLp
  let η : ℝ := ε/(8*Real.pi*L)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨D0,hD0⟩ := exists_nat_gt (max 1 (4*(L:ℝ)/ε))
  have hD0p : 0 < D0 := by
    have hh : (0:ℝ) < D0 := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ((le_max_left _ _).trans hD0.le)
    exact_mod_cast hh
  refine ⟨η,hη,D0,hD0p,?_⟩
  filter_upwards [hLE (L:ℝ) le_rfl,eventually_ge_atTop (1:ℕ)] with X hLX hX
  intro D hDD α hα
  have hXr : (0:ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hD : 0 < D := (by exact_mod_cast hD0p : (0:ℝ) < D0).trans_le hDD
  have hrem : (L:ℝ) < ε*D/4 := by
    have hh := (le_max_right 1 (4*(L:ℝ)/ε)).trans_lt (hD0.trans_le hDD)
    have hp := (div_lt_iff₀ hε).mp hh
    nlinarith only [hp]
  have hηeq : 2*Real.pi*η*(L:ℝ)^2=ε*L/4 := by dsimp [η]; field_simp; ring
  have hshort : (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (fun n=>f n*phase (α*n))
      (fun n=>(n:ℝ)) L x‖) < ε*L*X/2 := by
    have hh := sharp_phase_l1 (Ioc X (2*X)) f (fun n=>(n:ℝ)) hL.le α β
    have hmass := dyadic_mass hf X
    have herr : 2*Real.pi*|α-β| *(L:ℝ)^2*(∑n∈Ioc X (2*X),‖f n‖) ≤ ε*L*X/4 := by
      calc
        _ ≤ 2*Real.pi*η*(L:ℝ)^2*(X:ℝ) := by
          apply mul_le_mul _ hmass (sum_nonneg (fun n hn=>norm_nonneg _)) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (by positivity)) (sq_nonneg _)
        _ = _ := by rw [hηeq]; ring
    nlinarith only [hh,hLX,herr]
  have hlong := sharpWindow_long_from_short (Ioc X (2*X))
    (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) hL hD.le
  have hm := mul_le_mul_of_nonneg_left (dyadic_phase_mass hf α X) hL.le
  have hb := mul_lt_mul_of_pos_left hshort (div_pos hD hL)
  have he : D/(L:ℝ)*(ε*L*X/2)=ε*D*X/2 := by field_simp
  rw [he] at hb
  have hr := mul_lt_mul_of_pos_right hrem hXr
  have hp : 0 < ε*D*X := mul_pos (mul_pos hε hD) hXr
  linarith only [hlong,hm,hb,hr,hp]

theorem rational_local_windowSmall {f : ℕ→ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f)
    (a : ℤ) {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∃η : ℝ,0 < η ∧ ∃D0 : ℕ,0 < D0 ∧ ∀ᶠ X : ℕ in atTop,
      ∀D : ℝ,(D0:ℝ) ≤ D → ∀α : ℝ,|α-(a:ℝ)/q| ≤ η →
        (∫x : ℝ,‖sharpWindow (Ioc X (2*X)) (fun n=>f n*phase (α*n))
          (fun n=>(n:ℝ)) D x‖) < ε*D*X :=
  local_windowSmall hf (rational_windowSmall hf hm hNP a hq) hε

end OrdinaryLocalAdditive

end

end OAI
