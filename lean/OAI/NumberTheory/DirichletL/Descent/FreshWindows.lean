import OAI.NumberTheory.DirichletL.Descent.SecondWholeKernel
import OAI.NumberTheory.DirichletL.Descent.SecondPass

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem fresh_ratio_of_source_support (W : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n) (hw : W (g*v*n) ≠ 0) :
    n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)) := by
  have hgp : 0 < g := hg₀.trans_le hg.1
  have hvp : 0 < v := hv₀.trans_le hv.1
  have hghi : 0 < g₁ := hgp.trans_le hg.2
  have hvhi : 0 < v₁ := hvp.trans_le hv.2
  have hsource := hs hw
  constructor
  · apply (div_le_iff₀ (mul_pos hghi hvhi)).mpr
    calc
      a ≤ g*v*n := hsource.1
      _ ≤ (g₁*v₁)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.2 hv.2 hvp.le hghi.le) hn
      _ = _ := by ring
  · apply (le_div_iff₀ (mul_pos hg₀ hv₀)).mpr
    calc
      _ = (g₀*v₀)*n := by ring
      _ ≤ g*v*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.1 hv.1 hv₀.le hgp.le) hn
      _ ≤ b := hsource.2

theorem fresh_window_eq_one (W ω : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n)
    (hω : ∀ n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)), ω n = 1)
    (hw : W (g*v*n) ≠ 0) : ω n = 1 :=
  hω n (fresh_ratio_of_source_support W a b g₀ g₁ v₀ v₁ g v n hs hg₀ hv₀ hg hv hn hw)

theorem secondChildKernelPair_insert_fresh {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (K : Finset ι → Finset ι → ℂ) (ω₁ ω₂ : Finset ι → ℂ)
    (hω : ∀ N ∈ (F \ V).powerset, ∀ M ∈ (F \ V).powerset,
      K (V ∪ N) (V ∪ M) ≠ 0 → ω₁ (V ∪ N) = 1 ∧ ω₂ (V ∪ M) = 1) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (ω₁ S)*ω₂ T*K S T) := by
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hK : K (V ∪ N) (V ∪ M) = 0
  · simp only [hK,mul_zero]
  · obtain ⟨h1,h2⟩ := hω N hN M hM hK
    simp only [h1,h2,star_one,one_mul]

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
