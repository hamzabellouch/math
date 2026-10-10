import OAI.NumberTheory.DirichletL.Descent.FirstCommonChild

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B,0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ source,Squarefree x.1) →
      (∀ x ∈ source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z ∈ rows,z ≠ 0) → (∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x ∈ source,‖w x‖ ≤ M) →
      (∑ x ∈ source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ∑ z ∈ rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
        (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply le_trans _ (hpush source rows (dilationLabel p B v ε₁ ε₂) w
    (dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)) M Y hM hY hs hmap hrows hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ C ω X t hX c d (ConcretePrimeRowBridge.idealGenerator x.1) x.2]
  simp only [norm_mul]
  have hr0 : ‖supportRay p χ D‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one χ _
  have hr : ‖if negative then star (supportRay p χ D) else supportRay p χ D‖ ≤ 1 := by
    cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,norm_star]
      using hr0
  have hb := beforeDilationLabel_norm_le_one (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂
    negative c d (ConcretePrimeRowBridge.idealGenerator x.1) D
  calc
    _ ≤ ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d
        (ConcretePrimeRowBridge.idealGenerator x.1) D‖ *
        ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (x.2*(ConcretePrimeRowBridge.idealGenerator x.1)^2*dilationLabel p B v ε₁ ε₂)‖ :=
      mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hb

end
end SevenEighths.InverseMoment

end OAI
