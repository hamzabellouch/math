import OAI.NumberTheory.DirichletL.Descent.FirstMarkedZero

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem primeProductNorm_union_le_mul {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal] (A U : Finset ι) :
    primeProductNorm p (A∪U)≤primeProductNorm p A*primeProductNorm p U := by
  have he : A∪U=A∪(U\A) := by ext i;simp only [Finset.mem_union,Finset.mem_sdiff];tauto
  rw [he,primeProductNorm_union p A (U\A) Finset.disjoint_sdiff]
  exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp Finset.sdiff_subset)
    (primeProductNorm_pos p hp A).le

theorem whole_cube_marked_test_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (_hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (extra : Finset ι) (test : Finset ι→ℂ) (E G L : ℝ),0≤E → 0≤G → 0≤L →
      primeProductNorm p extra≤E → (∀ U,‖test U‖≤G) →
      (∀ U,test U≠0→primeProductNorm p U≤L) →
      ∀ U,‖primeMark slots lists a (extra∪U)*test U‖≤Cm*(E*L)^ε*G := by
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop slots lists a hslots ha extra test E G L hE hG hL he hb hs U
  by_cases hz : test U=0
  · simp only [hz,mul_zero,norm_zero];positivity
  have hnorm : primeProductNorm p (extra∪U)≤E*L :=
    (primeProductNorm_union_le_mul p hp extra U).trans
      (mul_le_mul he (hs U hz) (primeProductNorm_pos p hp U).le hE)
  have hnorm0 := (primeProductNorm_pos p hp (extra∪U)).le
  rw [norm_mul]
  calc
    _ ≤ (Cm*(primeProductNorm p (extra∪U))^ε)*G :=
      mul_le_mul (hmark p hp hcop slots lists a hslots ha _) (hb U) (norm_nonneg _) (by positivity)
    _ ≤ _ := by gcongr

theorem first_whole_cube_marked_zero_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ Cm : ℝ,0<Cm ∧ ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι) (C extra₁ extra₂ : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ f : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (E G₁ G₂ L K : ℝ),
      0≤E → 0≤G₁ → 0≤G₂ → 0≤L → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0→primeProductNorm p U≤L) → (∀ U,test₂ U≠0→primeProductNorm p U≤L) →
      ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W K‖ ≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (Cm*(E*L)^ε*G₁)*(Cm*(E*L)^ε*G₂) * |K| * ‖EisensteinSchwartzPoisson.paperRadialFourier W 0‖ else 0 := by
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cm,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C extra₁ extra₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ f slots lists a hslots ha test₁ test₂ W E G₁ G₂ L K hE hG₁ hG₂ hL he₁ he₂ hb₁ hb₂ hs₁ hs₂
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ L hE hG₁ hL he₁ hb₁ hs₁ _)
        (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ L hE hG₂ hL he₂ hb₂ hs₂ _)
        (norm_nonneg _) (by positivity)) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

end
end SevenEighths.InverseMoment

end OAI
