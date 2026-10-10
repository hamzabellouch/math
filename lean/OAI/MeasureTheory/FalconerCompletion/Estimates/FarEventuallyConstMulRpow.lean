import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereShift

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Filter Real
open scoped Topology

lemma far_eventually_const_mul_rpowND {a b C : ℝ} (hab : a < b) :
    ∀ᶠ R : ℝ in atTop, C*R^a ≤ R^b := by
  have ht : Tendsto (fun R : ℝ => C*R^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul C
    simpa only [neg_sub,mul_zero] using hh
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1),
    eventually_gt_atTop (0:ℝ)] with R hR hRp
  have he : C*R^a = (C*R^(a-b))*R^b := by
    rw [mul_assoc,← Real.rpow_add hRp]
    congr 2
    ring
  rw [he]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hR.le (Real.rpow_nonneg hRp.le _)

lemma far_tail_factorizationND (n J : ℕ) {A Λ : ℝ} (hΛ : 0<Λ) :
    Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) =
      Λ^(-(n:ℝ)/2)*(A^2/Λ)^(J+1)*A^(n+3) := by
  rw [Real.rpow_sub hΛ,Real.rpow_natCast,div_pow,
    show 2*(J+1)+n+3=2*(J+1)+(n+3) by omega,pow_add A (2*(J+1)) (n+3),pow_mul A 2 (J+1)]
  ring

lemma far_source_envelopeND (n J k : ℕ) {R A Λ θ β H E B : ℝ}
    (hR : 1≤R) (hβ : 0≤β) (hA : 1≤A)
    (hAup : A≤R^2) (hΛlow : R^β≤Λ) (hratio : A^2/Λ≤R^(-θ))
    (hH : 0≤H) (hE : 0≤E) :
    R^B*(H*Λ^(-(n:ℝ)/2)/(Λ/2)^k + E*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)) ≤
      (H*2^k)*R^(B-β*k) + E*R^(B+2*(n+3:ℕ)-θ*(J+1:ℕ)) := by
  have hRp : 0<R := by linarith
  have hΛone : 1≤Λ := (Real.one_le_rpow hR hβ).trans hΛlow
  have hΛ : 0<Λ := by linarith
  have hAn : 0≤A := by linarith
  have hgain : Λ^(-(n:ℝ)/2)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hΛone (by
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith)
  have hrecip : 1/Λ^k≤R^(-β*k) := by
    have hx : 0<(R^β)^k := pow_pos (Real.rpow_pos_of_pos hRp β) k
    have hh := div_le_div_of_nonneg_left (show (0:ℝ)≤1 by norm_num) hx
      (pow_le_pow_left₀ (Real.rpow_nonneg hRp.le β) hΛlow k)
    apply hh.trans_eq
    rw [← Real.rpow_natCast (R^β) k,← Real.rpow_mul hRp.le,
      show -β*(k:ℝ)=-(β*(k:ℝ)) by ring,Real.rpow_neg hRp.le,one_div]
  have hlead : H*Λ^(-(n:ℝ)/2)/(Λ/2)^k ≤ (H*2^k)*R^(-β*k) := by
    calc
      _ = (H*2^k)*(Λ^(-(n:ℝ)/2)*(1/Λ^k)) := by rw [div_pow,div_div_eq_mul_div]; ring
      _ ≤ (H*2^k)*(1*R^(-β*k)) := by gcongr
      _ = _ := by ring
  have htail : E*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3) ≤
      E*R^(-θ*(J+1:ℕ)+2*(n+3:ℕ)) := by
    calc
      _ = E*(Λ^(-(n:ℝ)/2)*(A^2/Λ)^(J+1)*A^(n+3)) := by
        rw [← far_tail_factorizationND n J hΛ]
        ring
      _ ≤ E*(1*(R^(-θ))^(J+1)*(R^2:ℝ)^(n+3)) := by gcongr
      _ = _ := by
        rw [← pow_mul,← Real.rpow_natCast (R^(-θ)) (J+1),← Real.rpow_mul hRp.le,
          ← Real.rpow_natCast R (2*(n+3))]
        simp only [Nat.cast_mul,Nat.cast_ofNat,one_mul]
        rw [← Real.rpow_add hRp]
  calc
    _ ≤ R^B*((H*2^k)*R^(-β*k)+E*R^(-θ*(J+1:ℕ)+2*(n+3:ℕ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hlead htail) (Real.rpow_nonneg hRp.le B)
    _ = _ := by
      rw [mul_add]
      congr 1
      · calc
          _ = (H*2^k)*(R^B*R^(-β*k)) := by ring
          _ = _ := by rw [← Real.rpow_add hRp]; congr 2; ring
      · calc
          _ = E*(R^B*R^(-θ*(J+1:ℕ)+2*(n+3:ℕ))) := by ring
          _ = _ := by rw [← Real.rpow_add hRp]; congr 2; ring

theorem far_source_arbitrary_powerND (n : ℕ) {θ β : ℝ} (hθ : 0<θ) (hβ : 0<β)
    (B T : ℝ) :
    ∃ J k : ℕ, ∀ H E : ℝ, 0≤H → 0≤E →
      ∀ᶠ R : ℝ in atTop, ∀ A Λ : ℝ,
      1≤A → A≤R^2 → R^β≤Λ → A^2/Λ≤R^(-θ) →
      R^B*(H*Λ^(-(n:ℝ)/2)/(Λ/2)^k + E*Λ^(-(n:ℝ)/2-(J+1:ℕ))*A^(2*(J+1)+n+3)) ≤ R^(-T) := by
  obtain ⟨J,hJ⟩ := exists_nat_gt ((B+T+2*(n+3:ℕ))/θ)
  obtain ⟨k,hk⟩ := exists_nat_gt ((B+T)/β)
  have hJe : B+2*((n+3:ℕ):ℝ)-θ*((J+1:ℕ):ℝ) < -T := by
    have hh := (div_lt_iff₀ hθ).mp hJ
    push_cast at hh ⊢
    nlinarith
  have hke : B-β*(k:ℝ) < -T := by
    have hh := (div_lt_iff₀ hβ).mp hk
    nlinarith
  refine ⟨J,k,?_⟩
  intro H E hH hE
  filter_upwards [far_eventually_const_mul_rpowND (C := 2*(H*2^k)) hke,
    far_eventually_const_mul_rpowND (C := 2*E) hJe,eventually_ge_atTop (1:ℝ)]
    with R hlead htail hR
  intro A Λ hA hAup hΛ hratio
  apply (far_source_envelopeND n J k hR hβ.le hA hAup hΛ hratio hH hE).trans
  nlinarith

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
