import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsSources
import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementFiniteReindex

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws

theorem product_sum_update {ι K : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K]
    (S : ι → Finset K) (μ : ι → K → ℝ) (r : ι) (B : Finset K) (ν : K → ℝ)
    (F : (ι → K) → ℝ) :
    (∑ x ∈ Fintype.piFinset S, (∏ i, μ i (x i))*
      ∑ b ∈ B, ν b*F (Function.update x r b)) =
      (∑ a ∈ S r, μ r a)*
        ∑ y ∈ Fintype.piFinset (Function.update S r B),
          (∏ i, Function.update μ r ν i (y i))*F y := by
  classical
  have hp (x : ι → K) (b : K) :
      (∏ i, μ i (x i))*(ν b*F (Function.update x r b)) =
        ((∏ i, Function.update μ r ν i ((Function.update x r b) i))*
          F (Function.update x r b))*μ r (x r) := by
    rw [Fintype.prod_eq_mul_prod_compl r (fun i => μ i (x i)),
      Fintype.prod_eq_mul_prod_compl r
        (fun i => Function.update μ r ν i ((Function.update x r b) i))]
    simp only [Function.update_self]
    have he : (∏ i ∈ ({r}ᶜ : Finset ι),
        Function.update μ r ν i ((Function.update x r b) i)) =
        ∏ i ∈ ({r}ᶜ : Finset ι), μ i (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hir : i ≠ r := by simpa only [Finset.mem_compl,Finset.mem_singleton] using hi
      simp only [Function.update_of_ne hir]
    rw [he]
    ring
  have he :
      (∑ z ∈ (Fintype.piFinset S) ×ˢ B,
        (∏ i, μ i (z.1 i))*(ν z.2*F (Function.update z.1 r z.2))) =
      ∑ z ∈ (Fintype.piFinset (Function.update S r B)) ×ˢ S r,
        ((∏ i, Function.update μ r ν i (z.1 i))*F z.1)*μ r z.2 := by
    apply Finset.sum_bij (fun z _ => (Function.update z.1 r z.2, z.1 r))
    · intro z hz
      obtain ⟨hx,hb⟩ := Finset.mem_product.mp hz
      refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr ?_, Fintype.mem_piFinset.mp hx r⟩
      intro i
      by_cases hi : i = r
      · subst i; simpa only [Function.update_self] using hb
      · simpa only [Function.update_of_ne hi] using Fintype.mem_piFinset.mp hx i
    · intro z hz w hw heq
      have he1 := congrArg Prod.fst heq
      have he2 := congrArg Prod.snd heq
      apply Prod.ext
      · funext i
        by_cases hi : i = r
        · subst i; exact he2
        · simpa only [Function.update_of_ne hi] using congrFun he1 i
      · simpa only [Function.update_self] using congrFun he1 r
    · intro z hz
      obtain ⟨hx,ha⟩ := Finset.mem_product.mp hz
      refine ⟨(Function.update z.1 r z.2,z.1 r), ?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
        · intro i
          by_cases hi : i = r
          · subst i; simpa only [Function.update_self] using ha
          · have h := Fintype.mem_piFinset.mp hx i
            simpa only [Function.update_of_ne hi] using h
        · simpa only [Function.update_self] using Fintype.mem_piFinset.mp hx r
      · apply Prod.ext
        · funext i
          by_cases hi : i = r <;> simp [hi]
        · simp only [Function.update_self]
    · intro z hz
      exact hp z.1 z.2
  simp only [Finset.sum_product] at he
  simp_rw [Finset.mul_sum] at ⊢
  rw [he]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem product_sum_update_normalized {ι K : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K]
    (S : ι → Finset K) (μ : ι → K → ℝ) (r : ι) (B : Finset K) (ν : K → ℝ)
    (hunit : ∑ a ∈ S r, μ r a = 1) (F : (ι → K) → ℝ) :
    (∑ x ∈ Fintype.piFinset S, (∏ i, μ i (x i))*
      ∑ b ∈ B, ν b*F (Function.update x r b)) =
        ∑ y ∈ Fintype.piFinset (Function.update S r B),
          (∏ i, Function.update μ r ν i (y i))*F y := by
  rw [product_sum_update, hunit, one_mul]

theorem product_sum_embed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (value : ∀ i, κ i → ℤ) (hinj : ∀ i, Function.Injective (value i))
    (w : ∀ i, κ i → ℝ) (μ : ι → ℤ → ℝ)
    (hμ : ∀ i a, μ i (value i a) = w i a) (F : (ι → ℤ) → ℝ) :
    (∑ x : ∀ i, κ i, (∏ i, w i (x i))*F (fun i => value i (x i))) =
      ∑ y ∈ Fintype.piFinset (fun i => Finset.univ.image (value i)),
        (∏ i, μ i (y i))*F y := by
  classical
  apply Finset.sum_bij (fun x _ i => value i (x i))
  · intro x hx
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨x i, Finset.mem_univ _, rfl⟩)
  · intro x hx y hy hxy
    funext i
    exact hinj i (congrFun hxy i)
  · intro y hy
    have he : ∀ i, ∃ a : κ i, value i a = y i := by
      intro i
      obtain ⟨a,ha,hval⟩ := Finset.mem_image.mp (Fintype.mem_piFinset.mp hy i)
      exact ⟨a,hval⟩
    choose x hx using he
    exact ⟨x, Finset.mem_univ _, funext hx⟩
  · intro x hx
    simp only [hμ]

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
