import OAI.NumberTheory.DirichletL.Descent.WholePriorityPrincipal

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem first_selector_weighted_mass {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool A:Finset ι) (selector:Finset ι→ℂ) (E T S ε:ℝ)
    (hE:0≤E) (hT:0<T) (hS:0≤S) (hε:0≤ε)
    (hA:primeProductNorm p A≤E)
    (hselector:∀D∈pool.powerset,‖selector D‖≤S)
    (hsupport:∀D∈pool.powerset,selector D≠0→primeProductNorm p D≤T) :
    (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)≤
      128*T*S*(E*T)^ε := by
  have hfilter:(∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)=
      ∑D∈boundedPrimeSupports p pool T,‖selector D‖*(primeProductNorm p (A∪D))^ε:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro D hD hnot
    have hz:selector D=0:=by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hD,hsupport D hD h⟩)
    simp [hz]
  rw [hfilter]
  calc
    _≤∑D∈boundedPrimeSupports p pool T,S*(E*T)^ε:=by
      apply Finset.sum_le_sum
      intro D hD
      have hnorm:primeProductNorm p (A∪D)≤E*T:=
        (primeProductNorm_union_le_mul p hp A D).trans
          (mul_le_mul hA (Finset.mem_filter.mp hD).2 (primeProductNorm_pos p hp D).le hE)
      exact mul_le_mul (hselector D (Finset.mem_filter.mp hD).1)
        (Real.rpow_le_rpow (primeProductNorm_pos p hp _).le hnorm hε)
        (Real.rpow_nonneg (primeProductNorm_pos p hp _).le _) hS
    _= ((boundedPrimeSupports p pool T).card:ℝ)*S*(E*T)^ε:=by simp;ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj pool T hT) hS)
      (Real.rpow_nonneg (mul_nonneg hE hT.le) _)

theorem first_whole_extracted_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι) (hb:b.Admissible) (C extra:Finset ι) (he:extra⊆b.support)
    (negative:Bool) (B:ℝ) (hB:0≤B)
    (h₁:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (h₂:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))≤
      B^2*primeProductNorm p C := by
  have hbits:(if negative then b.rightDivisor else b.leftDivisor)⊆b.support:=by
    cases negative
    · exact hb.1
    · exact hb.2
  have hs:extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)⊆b.support∪C:=by
    exact Finset.union_subset (he.trans Finset.subset_union_left)
      (Finset.union_subset_union hbits (Finset.Subset.refl C))
  apply (primeProductNorm_mono p hp hs).trans
  apply (primeProductNorm_union_le_mul p hp b.support C).trans
  exact mul_le_mul_of_nonneg_right (cubeCoordinates_radical_bound p hp b B hB h₁ h₂)
    (primeProductNorm_pos p hp C).le

end SevenEighths.InverseMoment

end

end OAI
