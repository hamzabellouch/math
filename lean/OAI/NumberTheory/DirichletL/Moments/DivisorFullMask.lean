import OAI.NumberTheory.DirichletL.Moments.DivisorRows

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorFullMask
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O

 theorem annular_hasFiniteSupport (W : ℝ → ℂ) (b X : ℝ) (hX : 0 < X)
    (hs : Function.support W ⊆ Set.Iic b) :
    (fun I : Ideal O => W ((Ideal.absNorm I:ℝ)/X)).HasFiniteSupport := by
  apply (Ideal.finite_setOfPred_absNorm_le (S := O) (Nat.ceil (b*X))).subset
  intro I hI
  have hn := (div_le_iff₀ hX).mp (hs hI)
  exact_mod_cast hn.trans (Nat.le_ceil (b*X))

theorem rectangle_hasFiniteSupport (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (fun v : Ideal O × Ideal O => idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2).HasFiniteSupport := by
  have h₁ := (annular_hasFiniteSupport W₁ b₁ X₁ hX₁ hW₁).union
    (annular_hasFiniteSupport W₁ b₁ Y₁ hY₁ hW₁)
  have h₂ := (annular_hasFiniteSupport W₂ b₂ X₂ hX₂ hW₂).union
    (annular_hasFiniteSupport W₂ b₂ Y₂ hY₂ hW₂)
  apply (h₁.prod h₂).subset
  intro v hv
  constructor
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,zero_mul,sub_self])
  · by_contra hn
    simp only [Set.mem_union,Function.mem_support,not_or,not_not] at hn
    exact hv (by simp only [idealRectangle,hn.1,hn.2,mul_zero,sub_self])

theorem rectangle_tsum_sum {α : Type*} [Fintype α]
    (f : α → Ideal O → Ideal O → ℂ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O,∑' J : Ideal O,
      ∑ a, f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a,∑' I : Ideal O,∑' J : Ideal O,f a I J*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J := by
  have hs (a : α) : Summable (fun v : Ideal O × Ideal O =>
      f a v.1 v.2*idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ v.1 v.2) :=
    summable_of_hasFiniteSupport ((rectangle_hasFiniteSupport W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
      hW₁ hW₂ hX₁ hX₂ hY₁ hY₂).mul_right _)
  have hi (I : Ideal O) := Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod_factor I)
  simp_rw [hi]
  exact Summable.tsum_finsetSum (fun a (_ : a ∈ Finset.univ) => (hs a).prod)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem factorTuple_product (v : ι → Ideal O) (I J : Ideal O) :
    (∏ i,factorTuple v I J i)=(∏ i,v i)*I*J := by
  rw [Fintype.prod_sum_type,Fin.prod_univ_two]
  simp only [factorTuple,Sum.elim_inl,Sum.elim_inr,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,mul_assoc]

theorem full_mask_eq_allocated_rectangles (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O) (hD : Squarefree D)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑ v : (i : ι) → S i,(∏ i,β i (v i))*
      ∑' I : Ideal O,∑' J : Ideal O,
        (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
          rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
          idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  have he (v : (i : ι) → S i) (I J : Ideal O) :
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0) =
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a := by
    rw [← factorTuple_product]
    exact squarefree_mask_allocation D hD Finset.univ _
  simp_rw [he,Finset.sum_mul]
  simp_rw [rectangle_tsum_sum _ W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hW₁ hW₂ hX₁ hX₂ hY₁ hY₂]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

end SevenEighths.CenteredMomentDivisorFullMask

end

end OAI
