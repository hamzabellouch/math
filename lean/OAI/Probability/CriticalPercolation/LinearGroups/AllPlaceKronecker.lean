import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.ArchimedeanDetection
import OAI.Probability.CriticalPercolation.LinearGroups.PadicDetection

namespace OAI

section
noncomputable section
open Set Function Cardinal Polynomial
open scoped Classical

namespace CriticalPercolation.Arithmetic

lemma algebraic_of_all_complex_embeddings_bounded {K : Type} [Field K] [CharZero K]
    [Countable K] (x : K) (h : ∀ f : K →+* ℂ, ‖f x‖≤1) : IsAlgebraic ℚ x := by
  by_contra hn
  obtain ⟨f,hf⟩ := exists_complex_embedding_norm_gt_one x hn
  exact hf.not_ge (h f)

lemma uncountable_padic_closure (p : ℕ) [Fact p.Prime] :
    Uncountable (AlgebraicClosure (Padic p)) := by
  let : Uncountable (Padic p) := uncountable_complete_normed_field (Padic p)
  exact (algebraMap (Padic p) (AlgebraicClosure (Padic p))).injective.uncountable

lemma root_of_unity_of_all_places {K : Type} [Field K] [CharZero K] [Countable K]
    (x : K) (hx : x≠0)
    (hc : ∀ f : K →+* ℂ, ‖f x‖≤1)
    (hp : ∀ (p : ℕ) (_ : Fact p.Prime) (f : K →+* AlgebraicClosure (Padic p)),
      spectralNorm (Padic p) (AlgebraicClosure (Padic p)) (f x)≤1) :
    ∃ n : ℕ, 0<n ∧ x^n=1 := by
  have halg : IsAlgebraic ℚ x := algebraic_of_all_complex_embeddings_bounded x hc
  let A := IntermediateField.adjoin ℚ ({x}:Set K)
  let : FiniteDimensional ℚ A := IntermediateField.adjoin.finiteDimensional halg.isIntegral
  let : NumberField A := ⟨⟩
  let a : A := ⟨x,IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton x)⟩
  have hcA : ∀ f : A →+* ℂ, ‖f a‖≤1 := by
    intro f
    let : Uncountable ℂ := uncountable_complete_normed_field ℂ
    obtain ⟨g,hg⟩ := exists_extension_of_countable (K:=K) f
    have he : g x=f a := RingHom.congr_fun hg a
    exact he ▸ hc g
  have hi : IsIntegral ℤ a := by
    apply integral_of_all_padic_embeddings
    intro p hp' f
    let : Fact p.Prime := hp'
    let : Uncountable (AlgebraicClosure (Padic p)) := uncountable_padic_closure p
    obtain ⟨g,hg⟩ := exists_extension_of_countable (K:=K) f
    have he : g x=f a := RingHom.congr_fun hg a
    exact he ▸ hp p hp' g
  obtain ⟨n,hn,he⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one A ℂ
    (x:=a) (fun hz => hx (congrArg Subtype.val hz)) hi hcA
  exact ⟨n,hn,congrArg Subtype.val he⟩

end CriticalPercolation.Arithmetic
end
end

end OAI
