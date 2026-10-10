import OAI.NumberTheory.DirichletL.Descent.Poisson
import OAI.NumberTheory.DirichletL.Descent.Completion

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def finiteCanonicalMarkedRow (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedChildRow p hp hcop hg pool Ψ m
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X)) f k

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_actual_columns
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist Ψ m f k)
          (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W (primeProductNorm p U / X)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  have he := CanonicalRowCompletion.columnWeight_finset p hp hcop hg hpr U Ψ m f k
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X))
  symm
  convert he using 1 ; simp only [secondChildColumn, canonicalSourceCoefficient] ; ring

theorem secondChildSum_marked_canonical
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg (F \ V) Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ (A ∪ V)) a W (X / primeProductNorm p V) := by
  unfold secondChildSum finiteCanonicalMarkedRow fixedChildRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro N hN
  have hd : Disjoint V N := Finset.disjoint_left.mpr (fun i hi hn =>
    (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hN hn)).2 hi)
  have hn : primeProductNorm p (V ∪ N) / X = primeProductNorm p N / (X / primeProductNorm p V) := by
    rw [primeProductNorm_union p V N hd]
    simp only [div_div_eq_mul_div]
    ring
  have hmark := primeMark_priority slots lists a (A ∪ V) N
  simp only [primeMark_residual_lists] at hmark
  simp only [secondChildColumn, ← Finset.union_assoc, hn]
  rw [hmark]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_pool
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg (pool \ B) Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X :=
  fixedChildRow_restore_killed_pool p hp hcop hg pool B Ψ m f k _ hB

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMark_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

theorem secondChildSum_marked_fixed_pool
    (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    secondChildSum p hp hcop hg F V Ψ m r c d e k
      (fun U => primeMark slots lists a (A ∪ U) * W (primeProductNorm p U / X)) =
    ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
      finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
        (c * e * ∏ i ∈ V, p i) (d * e * k)
        (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V) := by
  rw [secondChildSum_marked_canonical]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hV (i : ι) (hi : i ∈ V) : (m * r) * (c * e * ∏ j ∈ V, p j) ∈ Ideal.span {p i} :=
    Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hi) (c * e)) (m * r))
  rw [finiteCanonicalMarkedRow_restore_pool p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV]
  have hlists : (fun i => lists i \ (A ∪ V)) = (fun i => (lists i \ A) \ V) := by
    funext i
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hlists]
  exact finiteCanonicalMarkedRow_restore_lists p hp hcop hg F V Ψ (m * r)
    (c * e * ∏ i ∈ V, p i) (d * e * k) _ _ _ _ _ hV

end
end SevenEighths.InverseMoment

end OAI
