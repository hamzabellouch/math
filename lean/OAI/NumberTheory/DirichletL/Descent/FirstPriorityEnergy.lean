import OAI.NumberTheory.DirichletL.Descent.FirstToSecond
import OAI.NumberTheory.DirichletL.Descent.FirstPass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem first_fresh_real_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d core height Y).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
        (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2 := by
  unfold firstFreshSecondPoisson
  rw [←firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) rowMajorant Y hY,
    rowMajorant_tsum_eq_sum _ Y hY]
  let P := fun z=>firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z
  change (∑ z∈rowMajorantBall Y,rowMajorant (‖eisEmbedding z‖^2/Y)*(‖P z‖^2 : ℝ)).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re*‖P z‖^2
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma priority_norm_sum_sq {α : Type*} (s : Finset α) (f : α→ℂ) :
    ‖∑ i∈s,f i‖^2≤(s.card:ℝ)*∑ i∈s,‖f i‖^2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  apply hnorm.trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _=>(1:ℝ)) (fun i=>‖f i‖)

theorem first_fresh_priority_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (fun U=>primeMark slots lists a (A∪U)*H U) ω X c d core height Y).re ≤
    (2:ℝ)^slots.card * ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
        (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U) ω X c d core height Y).re := by
  rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
  calc
    _ ≤ ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
        ((slots.powerset.card:ℝ)*∑ J∈slots.powerset,
          ‖primeMark J lists a (A∪D) * firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U)
            (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (rowMajorant_nonneg _)
      rw [firstCoreInputRow_marked_priority]
      exact priority_norm_sum_sq _ _
    _ = _ := by
      simp_rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.mul_sum,norm_mul,mul_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      apply Finset.sum_congr rfl
      intro z hz
      ring

end
end SevenEighths.InverseMoment

end OAI
