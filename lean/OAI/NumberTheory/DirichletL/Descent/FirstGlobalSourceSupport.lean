import OAI.NumberTheory.DirichletL.Descent.FirstPhysicalFamily

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma first_squarefree_row_zero_mem (U : Finset ι) (i : ι) (hi : i∈U) (n : O)
    (hn : n∈Ideal.span {p i}) : finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg U n=0 := by
  unfold finiteSquarefreeRow
  apply Finset.prod_eq_zero hi
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn,MulChar.map_zero]

lemma canonicalCubeResidual_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ)
    (hn : ¬Disjoint U (b.support∪C)) : canonicalCubeResidual p hg b C negative Ψ m f H U=0 := by
  obtain ⟨i,hi,hib⟩ := Finset.not_disjoint_iff.mp hn
  rcases Finset.mem_union.mp hib with hib|hiC
  · have hm : cubeRadical p b.support∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hib)
    have hz : rowCoprimeMask (fun i=>Ideal.span {p i}) U (cubeRadical p b.support)=0 := by
      simp only [rowCoprimeMask,ite_eq_left_iff]
      intro hh
      exact False.elim (hh ⟨i,hi,hm⟩)
    simp only [canonicalCubeResidual,originalLabelColumn,hz,mul_zero,zero_mul]
  · have hm : aLabel p b.support (if negative then b.rightBit else b.leftBit)*(∏j∈C,p j)∈Ideal.span {p i} :=
      Ideal.mem_span_singleton.mpr (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiC) _)
    have hz := first_squarefree_row_zero_mem p hg U i hi _ hm
    simp only [canonicalCubeResidual,originalLabelColumn,hz,zero_pow (by norm_num : 4≠0),mul_zero,zero_mul]

lemma firstCanonicalCoefficient_zero_overlap (b : CubeCoordinates ι) (C U : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m d : O) (H : Finset ι→ℂ) (x : Ideal O×O)
    (hn : ¬Disjoint U (b.support∪C)) : firstCanonicalCoefficient p hp hcop hg b C negative Ψ m d H x U=0 := by
  have hz := canonicalCubeResidual_zero_overlap p hg b C U negative Ψ m
    (ConcretePrimeRowBridge.idealGenerator x.1) H hn
  cases negative <;>
    simp only [firstCanonicalCoefficient,firstBareCubeCoefficient,Bool.false_eq_true,ite_false,ite_true,
      cubeMinusCoefficient,cubePlusCoefficient,firstPassColumnMinus,firstPassColumnPlus,hz,mul_zero]

lemma firstCommonIndices_membership (F : Finset ι) (j : FirstCommonIndex ι) :
    j∈firstCommonIndices F ↔ j.2.1⊆F ∧ j.2.2.1⊆F\j.2.1 ∧ j.2.2.2⊆F\j.2.1 := by
  simp [firstCommonIndices]

lemma firstCommonIndices_mono {F G : Finset ι} (h : F⊆G) : firstCommonIndices F⊆firstCommonIndices G := by
  intro j hj
  rcases (firstCommonIndices_membership F j).mp hj with ⟨hd,hu,hv⟩
  exact (firstCommonIndices_membership G j).mpr ⟨hd.trans h,
    hu.trans (Finset.sdiff_subset_sdiff h le_rfl),hv.trans (Finset.sdiff_subset_sdiff h le_rfl)⟩

lemma firstCommonWeight_zero_outside (F G : Finset ι) (C₁ C₂ : Finset ι→ℂ) (h : O)
    (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0) (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (j : FirstCommonIndex ι) (hj : j∈firstCommonIndices G) (hjF : j∉firstCommonIndices F) :
    firstCommonWeight p hg C₁ C₂ h j=0 := by
  rcases (firstCommonIndices_membership G j).mp hj with ⟨hd,hu,hv⟩
  by_cases hleft : j.2.1∪j.2.2.1⊆F
  · have hright : ¬j.2.1∪j.2.2.2⊆F := by
      intro hr
      apply hjF
      apply (firstCommonIndices_membership F j).mpr
      refine ⟨Finset.Subset.trans Finset.subset_union_left hleft,?_,?_⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hleft (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hu hi)).2⟩
      · intro i hi
        exact Finset.mem_sdiff.mpr ⟨hr (Finset.mem_union_right _ hi),(Finset.mem_sdiff.mp (hv hi)).2⟩
    have hz := hC₂ _ (Finset.union_subset hd (hv.trans Finset.sdiff_subset)) hright
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul]
  · have hz := hC₁ _ (Finset.union_subset hd (hu.trans Finset.sdiff_subset)) hleft
    simp only [firstCommonWeight,firstCommonCoefficient,hz,mul_zero,zero_mul,star_zero]

theorem firstPhysicalCommonRows_fixed_pool (F G : Finset ι) (hFG : F⊆G)
    (C₁ C₂ : Finset ι→ℂ) (hC₁ : ∀U,U⊆G → ¬U⊆F → C₁ U=0)
    (hC₂ : ∀U,U⊆G → ¬U⊆F → C₂ U=0)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (A₁ A₂ C R K : ℝ) (d h : O) :
    firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h=
      firstPhysicalCommonRows p hg G C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed,firstPhysicalCommonRows_indexed]
  exact Finset.sum_subset (firstCommonIndices_mono hFG) (fun j hj hn=>by
    rw [firstCommonWeight_zero_outside p hg F G C₁ C₂ h hC₁ hC₂ j hj hn,zero_mul])

end
end SevenEighths.InverseMoment

end OAI
