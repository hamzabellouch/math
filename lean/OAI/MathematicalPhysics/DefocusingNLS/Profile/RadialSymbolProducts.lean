import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol

namespace OAI

/-! Product estimates for the two polynomial coefficients of the actual linearized potential. -/

open Set
open scoped ContDiff
namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

def HasCartesianSymbol (σ : ℝ) (f : E → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, 1 ≤ ‖x‖ →
    ‖iteratedFDeriv ℝ k f x‖ ≤ C*‖x‖^(σ-(k : ℝ))

theorem HasCartesianSymbol.const (c : ℂ) : HasCartesianSymbol 0 (fun _ : E => c) := by
  refine ⟨contDiff_const,?_⟩
  intro k
  cases k with
  | zero => exact ⟨‖c‖,norm_nonneg _,by intro x hx; simp⟩
  | succ k =>
    refine ⟨0,le_rfl,?_⟩
    intro x hx
    simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,zero_mul,le_refl]

theorem HasCartesianSymbol.mul {σ τ : ℝ} {f g : E → ℂ}
    (hf : HasCartesianSymbol σ f) (hg : HasCartesianSymbol τ g) :
    HasCartesianSymbol (σ+τ) (fun x => f x*g x) := by
  refine ⟨hf.1.mul hg.1,?_⟩
  intro k
  choose C hC hCf using hf.2
  choose B hB hBg using hg.2
  let D := ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*C i*B (k-i)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (k-i)))
  refine ⟨D,hD,?_⟩
  intro x hx
  have hr : 0 < ‖x‖ := by linarith
  apply (norm_iteratedFDeriv_mul_le hf.1 hg.1 x (by simp : (k : ℕ∞ω) ≤ ∞)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1),
        ((k.choose i : ℝ)*C i*B (k-i))*‖x‖^(σ+τ-(k : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by have := Finset.mem_range.mp hi; omega
      have hki : ((k-i : ℕ) : ℝ)=(k : ℝ)-(i : ℝ) := Nat.cast_sub hik
      have hpow : ‖x‖^(σ-(i : ℝ))*‖x‖^(τ-((k-i : ℕ) : ℝ)) =
          ‖x‖^(σ+τ-(k : ℝ)) := by
        rw [← Real.rpow_add hr,hki]
        congr 1
        ring
      have hh := mul_le_mul
        (mul_le_mul_of_nonneg_left (hCf i x hx) (Nat.cast_nonneg (k.choose i)))
        (hBg (k-i) x hx) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (Real.rpow_nonneg hr.le _)))
      calc
        _ ≤ ((k.choose i : ℝ)*(C i*‖x‖^(σ-(i : ℝ))))*
            (B (k-i)*‖x‖^(τ-((k-i : ℕ) : ℝ))) := hh
        _ = ((k.choose i : ℝ)*C i*B (k-i))*
            (‖x‖^(σ-(i : ℝ))*‖x‖^(τ-((k-i : ℕ) : ℝ))) := by ring
        _ = _ := by rw [hpow]
    _ = _ := by rw [← Finset.sum_mul]

theorem HasCartesianSymbol.conj {σ : ℝ} {f : E → ℂ} (hf : HasCartesianSymbol σ f) :
    HasCartesianSymbol σ (fun x => star (f x)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hf.1,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := hf.2 k
  refine ⟨C,hC,?_⟩
  intro x hx
  have he := Complex.conjLIE.norm_iteratedFDeriv_comp_left f x k
  simpa only [Function.comp_def,Complex.conjLIE_apply,starRingEnd_apply] using he.le.trans (hb x hx)

theorem HasCartesianSymbol.const_mul {σ : ℝ} {f : E → ℂ}
    (hf : HasCartesianSymbol σ f) (c : ℂ) : HasCartesianSymbol σ (fun x => c*f x) := by
  simpa only [zero_add] using (HasCartesianSymbol.const c).mul hf

theorem HasCartesianSymbol.pow {σ : ℝ} {f : E → ℂ}
    (hf : HasCartesianSymbol σ f) (m : ℕ) :
    HasCartesianSymbol ((m : ℝ)*σ) (fun x => (f x)^m) := by
  induction m with
  | zero => simpa only [Nat.cast_zero,zero_mul,pow_zero] using HasCartesianSymbol.const 1
  | succ m ih =>
    have he : ((m+1 : ℕ) : ℝ)*σ=(m : ℝ)*σ+σ := by push_cast; ring
    simpa only [he,pow_succ] using ih.mul hf

theorem radialMatchedCartesian_hasCartesianSymbol (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n+radialInnerShootingThreshold) z)
      (n+radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z=0) :
    HasCartesianSymbol (-2*radialShootingA n) (radialMatchedCartesian n z) :=
  ⟨radialMatchedCartesian_contDiff n z hX hz,radialMatchedCartesian_symbol n z hX hz⟩

end DefocusingNLS

end OAI
