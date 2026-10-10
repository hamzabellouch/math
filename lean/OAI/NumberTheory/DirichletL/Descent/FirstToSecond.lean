import OAI.NumberTheory.DirichletL.Descent.FirstFreshEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFreshSecondPoisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F\D).powerset, ∑ U ∈ ((F\D)\G).powerset, ∑ V ∈ ((F\D)\G).powerset,
    if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
      (m*b0Label p B v ε₁ ε₂) (c*jLabel p B v ε₁ ε₂) d
      (firstCoreTest H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
      maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0

theorem firstFreshSecondPoisson_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) (hY : 0 < Y) :
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y =
    ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
      if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
        ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
        (firstCoreTest H (fun u => ω (Real.exp u))
          (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
        maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  unfold firstFreshSecondPoisson
  rw [← firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y hY]
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y]
  simp_rw [inputConjugateRow_fixed_pool p hg hinj F D]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F
    (firstCoreTwist negative χ Ψ r) ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i)
    (c*jLabel p B v ε₁ ε₂) d
    (firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D) rowMajorant Y hY

theorem first_fresh_core_energy_to_second
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis) (t : ℝ)
    (rows : Finset Eis) (Y : ℝ) (hY : 0 < Y)
    (hrows : ∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y)
    (hΨ : ‖Ψ (∏ i∈D,p i)‖ ≤ 1) :
    (∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) ≤
    (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re := by
  calc
    _ ≤ ∑ z∈rows,(32*512) * ∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
            (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d (-t) z hΨ
    _ = (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∑ z∈rows,‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact firstCoreInputRow_finite_le_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d r (-t) rows Y hY hrows

theorem first_fresh_old_labels_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), (∀ j∈B,0 < v j) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis),
      ‖Ψ (∏ i∈D,p i)‖ ≤ 1 → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H)
            c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ((32*512)*∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F D B v ε₁ ε₂ hv negative χ Ψ m hΨ H ω X t hX
    c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
      hs hmap hrows hnorm hw).trans
  exact mul_le_mul_of_nonneg_left
    (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative χ
      Ψ m H ω X c d t rows Y hY hnorm hΨ) (by positivity)

end
end SevenEighths.InverseMoment

end OAI
