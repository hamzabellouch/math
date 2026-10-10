import OAI.NumberTheory.DirichletL.Descent.Canonical
import OAI.NumberTheory.DirichletL.Descent.SecondEnergy

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem marked_input_smoothed_second_poisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F A : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : Eis, W (‖eisEmbedding z‖ ^ 2 / Y) *
      (‖inputConjugateRow p hg F Ψ m c d
        (fun U => H U * primeMark slots lists a (A ∪ U)) z‖ ^ 2 : ℝ)) =
      ∑ G ∈ F.powerset, ∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
        if Disjoint U V then overlapPairWeight p hg Ψ m c d
          (fun U => H U * primeMark slots lists a (A ∪ U)) G U V *
          maskedSecondDual p hg hp hinj G U V W Y else 0 :=
  inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ m c d _ W Y hY

def canonicalMarkedSplit (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
      (c * e * ∏ i ∈ V, p i) (d * e * k)
      (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V)

theorem secondActualPair_marked_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (F A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U / X₁))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U / X₂)) =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z, V) *
        star (canonicalMarkedSplit p hp hcop hg F V A₁ (secondRayMinus Ψ₁ z)
          m r c d e k slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ (secondRayPlus Ψ₂ z)
          m r c d e (-k) slots₂ lists₂ a₂ W₂ X₂ := by
  rw [secondActualPair_eq_children p hp hcop hg hinj hc hpr]
  simp only [secondChildSum_marked_fixed_pool, canonicalMarkedSplit]

end
end SevenEighths.InverseMoment

end OAI
