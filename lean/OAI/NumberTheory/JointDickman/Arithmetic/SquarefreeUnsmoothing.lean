import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszPrimitiveExpansion
import OAI.NumberTheory.JointDickman.Amplification.LogScaleBigO
import OAI.NumberTheory.JointDickman.Analysis.RieszSecantBounds
import OAI.NumberTheory.JointDickman.Amplification.UnsmoothingPowerBound

namespace OAI

/-! # Removing the Riesz smoothing by positive finite differences -/
namespace JointDickman
open Filter Asymptotics Set
open scoped Topology

theorem squarefreeSummatory_derivative_approx {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    ∃ b : ℕ → ℝ, b 0 = squarefreeLeadingConstant z/2 ∧ 0 < b 0 ∧
      ∀ H : ℕ, (fun x : ℝ => squarefreeSummatory z x-
        rieszLogDerivative b z (2*H+2) x) =O[atTop]
          (fun x => x*(Real.log x)^(z-2-H)) := by
  obtain ⟨b,hb,hb0,hF⟩ := squarefreeRieszPrimitive_expansion hz hz1
  refine ⟨b,hb,hb0,fun H => ?_⟩
  let K := 2*H+2
  obtain ⟨C,hC,herr⟩ := isBigO_uniform_log_square (hF K)
  obtain ⟨M,hM,hsecond⟩ := rieszLogSecondDerivative_uniform_bound b z K
  apply IsBigO.of_bound (M+2*C)
  filter_upwards [herr,eventually_gt_atTop (4:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ))] with x he hx4 hlog
  have hx : 0 < x := by linarith
  have hl : 0 < Real.log x := by linarith
  let B : ℝ := (H:ℝ)+2
  let h : ℝ := x/(Real.log x)^B
  have hB : 1 ≤ B := by dsimp [B]; have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hpow : 2 ≤ (Real.log x)^B := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ Real.log x) hB
    rw [Real.rpow_one] at hp
    exact hlog.trans hp
  have hh : 0 < h := by dsimp [h]; positivity
  have hhx : h ≤ x/2 := div_le_div_of_nonneg_left hx.le (by norm_num) hpow
  have hxminus : 0 < x-h := by linarith
  have hbetween (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) : t ∈ Icc (x/2) (2*x) := by
    constructor <;> linarith [ht.1,ht.2]
  have hfirst (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      HasDerivAt (rieszLogPolynomial b z K) (rieszLogDerivative b z K t) t :=
    hasDerivAt_rieszLogPolynomial b z K (by linarith [ht.1])
  have hsecond' (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      HasDerivAt (rieszLogDerivative b z K) (rieszLogSecondDerivative b z K t) t :=
    hasDerivAt_rieszLogDerivative b z K (by linarith [ht.1])
  have hbound (t : ℝ) (ht : t ∈ Icc (x-h) (x+h)) :
      |rieszLogSecondDerivative b z K t| ≤ M*(Real.log x)^(z-1) :=
    hsecond x t hx hlog (hbetween t ht)
  have hsMinus := secant_error_of_second_derivative
    (a := x-h) (b := x) (x := x) (M := M*(Real.log x)^(z-1))
    (by linarith) ⟨by linarith,le_rfl⟩ (by positivity)
    (fun t ht => hfirst t ⟨ht.1,by linarith [ht.2]⟩)
    (fun t ht => hsecond' t ⟨ht.1,by linarith [ht.2]⟩)
    (fun t ht => hbound t ⟨ht.1,by linarith [ht.2]⟩)
  have hsPlus := secant_error_of_second_derivative
    (a := x) (b := x+h) (x := x) (M := M*(Real.log x)^(z-1))
    (by linarith) ⟨le_rfl,by linarith⟩ (by positivity)
    (fun t ht => hfirst t ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => hsecond' t ⟨by linarith [ht.1],ht.2⟩)
    (fun t ht => hbound t ⟨by linarith [ht.1],ht.2⟩)
  rw [show x-(x-h) = h by ring] at hsMinus
  rw [show x+h-x = h by ring] at hsPlus
  have hdMinus := (squarefreeRieszPrimitive_difference hz.le hxminus (by linarith : x-h ≤ x)).2
  have hdPlus := (squarefreeRieszPrimitive_difference hz.le hx (by linarith : x ≤ x+h)).1
  rw [show x-(x-h) = h by ring] at hdMinus
  rw [show x+h-x = h by ring] at hdPlus
  have hu := unsmooth_from_secants hh hdMinus hdPlus
    (he x ⟨by linarith,by linarith⟩)
    (he (x-h) (hbetween _ ⟨le_rfl,by linarith⟩))
    (he (x+h) (hbetween _ ⟨by linarith,le_rfl⟩)) hsMinus hsPlus
  have hbalance := unsmoothing_power_bound (l := Real.log x) (β := z-2-(K:ℝ)) (γ := z-1)
    (μ := z-2-H) (B := B) hx (by linarith) hC hM
    (by dsimp [K,B]; push_cast; linarith) (by dsimp [B]; linarith)
  have hfinal := hu.trans hbalance
  have hr : 0 ≤ x*(Real.log x)^(z-2-H) := by positivity
  simpa only [Real.norm_eq_abs,abs_of_nonneg hr,K,mul_assoc] using hfinal

end JointDickman

end OAI
