import OAI.NumberTheory.DirichletL.Descent.FirstWholeMarkedColumns

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_canonical_tail (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (Ct Cm : ℝ),0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hchar : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool : Finset ι) (b : CubeCoordinates ι),b.Admissible →
      ∀ (common divisor : Finset ι),Disjoint common b.support →
      ∀ (f : Ideal O),f≠0 →
      ∀ (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ : O) (extra₁ extra₂ : Finset ι) (E : ℝ) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ),
      0≤E → primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (slots : Set σ).PairwiseDisjoint lists → (∀ i∈slots,∀ k∈lists i,‖a i k‖≤1) →
      ∀ (test₁ test₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (G₁ G₂ Z M r ell V delta B j eta tau : ℝ),0≤G₁ → 0≤G₂ → 0<Z →
      (∀ U,‖test₁ U‖≤G₁) → (∀ U,‖test₂ U‖≤G₂) →
      (∀ U,test₁ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      (∀ U,test₂ U≠0 → primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f : ℝ)≤Z^(V+eta) → primeProductNorm p divisor≤Z^(delta+eta) →
      Z^(B-eta)≤primeProductNorm p common →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit)‖^2 →
      let residualPool := pool\(b.support∪common)
      let C₁ := canonicalCubeResidual p hg b common true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
      let C₂ := canonicalCubeResidual p hg b common false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U)
      let U₁ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.rightBit)‖^2*primeProductNorm p common)
      let U₂ := Z^(r+eta)/(‖eisEmbedding (aLabel p b.support b.leftBit)‖^2*primeProductNorm p common)
      let G₁' := Cm*(E*Z^(r+eta))^ε*G₁
      let G₂' := Cm*(E*Z^(r+eta))^ε*G₂
      let active := cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      let slow := Z^M/(primeProductNorm p divisor*primeProductNorm p active*U₁*U₂)
      let T := childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f)
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau))
      ‖∑' h : {h : O // h∉T},actualFirstKernel p hp hcop hg residualPool b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit C₁ C₂ W
        (fun _=>1) (fun _=>1) 1 1 (Z^M)
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) divisor) h.val‖ ≤
      (128*U₁)*(128*U₂)*(G₁'*G₂'*Z^M)*
        ((Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 slow)^2*(1+Z^tau)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_first_physical_tail order
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hchar pool b hb common divisor hcommon f hf0 Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V delta B j eta tau hG₁ hG₂ hZ
    htest₁ htest₂ hs₁ hs₂ hb₁ hb₂ hf hd hc hj residualPool C₁ C₂ U₁ U₂ G₁' G₂' active slow T
  have hdis : Disjoint residualPool (b.support∪common) := by
    apply Finset.disjoint_left.mpr
    intro i hi hi2
    exact (Finset.mem_sdiff.mp hi).2 hi2
  apply htail p hp hinj hcop hg hchar residualPool b.support common divisor b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (hdis.mono_right Finset.subset_union_left) f hf0 C₁ C₂ W
    G₁' G₂' Z M r ell V delta B j eta tau (by dsimp [G₁']; positivity) (by dsimp [G₂']; positivity) hZ
  · intro N hN
    exact (canonical_residual_norm p hg b common true Ψ₁ hΨ₁ m₁ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₁ test₁ E G₁ (Z^(r+eta)) hE hG₁
        (Real.rpow_pos_of_pos hZ _).le he₁ htest₁ hs₁ _)
  · intro N hN
    exact (canonical_residual_norm p hg b common false Ψ₂ hΨ₂ m₂ _ _ N).trans
      (hmark p hp hcop slots lists a hslots ha extra₂ test₂ E G₂ (Z^(r+eta)) hE hG₂
        (Real.rpow_pos_of_pos hZ _).le he₂ htest₂ hs₂ _)
  · exact hb₁
  · exact hb₂
  · exact hf
  · exact hd
  · exact hc
  · exact hj
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common true Ψ₁ m₁
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₁ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) true
    simp only [ite_true] at he
    exact he ▸ hn'
  · intro N hN hn
    have ht := canonical_residual_test_nonzero p hg b common false Ψ₂ m₂
      (ConcretePrimeRowBridge.idealGenerator f) _ N hn
    have hn' := hs₂ _ (mul_ne_zero_iff.mp ht).2
    have he := cube_whole_column_norm p b hb common N hcommon
      (hdis.mono_left (Finset.mem_powerset.mp hN)) false
    simp only [ite_false,Bool.false_eq_true] at he
    exact he ▸ hn'

end
end SevenEighths.InverseMoment

end OAI
