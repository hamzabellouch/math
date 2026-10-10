import OAI.NumberTheory.DirichletL.Descent.FirstBlockEnergy
import OAI.NumberTheory.DirichletL.Descent.FirstFreshEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem firstBlockOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (selector : Finset ι → ℂ) (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) :
    ‖firstBlockOuterWeight p selector r D h‖ ≤ ‖crossCoeff r.1 r.2‖*‖selector D‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hm : ‖supportMobius (fun i => Ideal.span {p i}) D‖ = 1 := by
    have hs := congrArg norm (supportMobius_sq _ hprime hinj D)
    simp only [norm_mul,norm_one] at hs
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) D)]
  have hc : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [firstBlockOuterWeight,norm_mul,hm,mul_one]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc

def firstOldLabelCoefficient (hp : ∀ i,p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (c d : Eis) (f : Ideal Eis) : Finset ι → ℂ :=
  firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
    (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator f)) d

theorem first_block_old_label_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ j∈B,0 < v j) → ∀ (negative : Bool) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * firstBlockEnergy p hg F selector
        (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
        negative ω X t x.2) ≤
      M*K*Y^ε * ∑ r : RayCharacter × RayCharacter, ∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖) *
          ∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F B selector v ε₁ ε₂ hv negative C ω X t hX c d
    source rows w M Y hM hY hs hmap hrows hnorm hw
  calc
    _ = ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,∑ x∈source,
        ‖w x‖*‖firstBlockOuterWeight p selector r D x.2‖*
          ‖firstCommonColumn p hg F D
            (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
            negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
      simp only [firstBlockEnergy,Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          (M*K*Y^ε*∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ x∈source,
            ‖w x‖*‖firstCommonColumn p hg F D
              (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
              negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          have hh := mul_le_mul_of_nonneg_left
            (firstBlockOuterWeight_norm_le p hinj selector r D x.2) (norm_nonneg (w x))
          exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
            (if negative then r.1 else r.2) C ω X t hX c d source rows w M Y
              hM hY hs hmap hrows hnorm hw) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring_nf

end
end SevenEighths.InverseMoment

end OAI
