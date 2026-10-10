import OAI.NumberTheory.DirichletL.Descent.SecondSourceEncoding

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_drop_puncture (Ψ : Eis →* ℂ) (m d f k : Eis)
    (hd : d ∣ m*f) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*d) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  by_cases hz : ∃ i ∈ S, d ∈ Ideal.span {p i}
  · obtain ⟨i,hi,hdI⟩ := hz
    have hr : m*f ∈ Ideal.span {p i} := by
      obtain ⟨a,ha⟩ := hd
      rw [ha]
      exact Ideal.mul_mem_right _ _ hdI
    have hl : (m*d)*f ∈ Ideal.span {p i} := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdI)
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ (m*d) f k H S i hi hl,
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k H S i hi hr]
  · have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S d = 1 := by
      simp only [rowCoprimeMask,ite_eq_right hz]
    simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg S,hm,mul_one]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_drop_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m d f k : Eis) (hd : d ∣ m*f)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*d) f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_drop_puncture p hp hcop hg Ψ m d f k hd]

theorem canonicalMarkedSplit_original_lists (F V A : Finset ι) (Ψ : Eis →* ℂ)
    (m r c d e k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hA : ∀ i ∈ A, (m*r)*(c*e*∏ j ∈ V,p j) ∈ Ideal.span {p i}) :
    canonicalMarkedSplit p hp hcop hg F V A Ψ m r c d e k slots lists a W X =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*r)
          (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) := by
  unfold canonicalMarkedSplit
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ (m*r)
    (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) hA]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_first_divisor_dvd_child
    (B C D V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (m r e : Eis) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) D ∣
      ((m*b0Label p B v ε₁ ε₂)*r)*
        (((∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂)*e*∏ i ∈ V,p i) := by
  have hd := poisson_mask_generator_dvd p D (C∪B) hD
  rw [Finset.prod_union hCB] at hd
  have hb := cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv
  change (∏ i ∈ B,p i) ∣ jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂ at hb
  apply (hd.trans (mul_dvd_mul_left (∏ i ∈ C,p i) hb)).trans
  refine ⟨m*r*e*∏ i ∈ V,p i,?_⟩
  ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          primeSubsetGenerator (fun j => Ideal.span {p j}) E*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := primeSubsetGenerator (fun j => Ideal.span {p j}) E
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

theorem actual_second_split_fixed_family
    (F B C D G E V A : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (Ψ : Eis →* ℂ) (m k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
    canonicalMarkedSplit p hp hcop hg F V A Ψ
      (m*b0Label p B v ε₁ ε₂*d) r c d e k slots lists a W (primeProductNorm p V*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ ((m*b0Label p B v ε₁ ε₂)*r)
          (c*e*∏ i ∈ V,p i) (d*e*k) (slots\J) lists a W X := by
  dsimp only
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
  have hd := actual_first_divisor_dvd_child p B C D V hCB hD v ε₁ ε₂ hv m r e
  have hk := actual_second_extracted_support_killed p B C G E V A hEG hA v ε₁ ε₂ hv m
  have hm : (m*b0Label p B v ε₁ ε₂*d)*r = ((m*b0Label p B v ε₁ ε₂)*r)*d := by ring
  have hX : primeProductNorm p V*X/primeProductNorm p V = X := by
    field_simp [(primeProductNorm_pos p hp V).ne']
  unfold canonicalMarkedSplit
  rw [show m*b0Label p B v ε₁ ε₂*primeSubsetGenerator (fun i => Ideal.span {p i}) D *
      secondMaskQuotient p E G hEG = ((m*b0Label p B v ε₁ ε₂)*r)*d from hm]
  rw [hX]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_drop_puncture p hp hcop hg F Ψ _ d _ _ hd]
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ _ _ _ (slots\J) lists a W X hk]

end
end SevenEighths.InverseMoment

end OAI
