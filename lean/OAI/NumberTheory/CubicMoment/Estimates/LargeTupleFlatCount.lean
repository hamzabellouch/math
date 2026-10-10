import OAI.NumberTheory.CubicMoment.Estimates.FlatTripleCount
import OAI.NumberTheory.CubicMoment.Estimates.LargeTuplePieceWitness

namespace OAI

/-! The log-log count for flat triples applied to the actual nonzero
large-row partition pieces, with the original product cutoff intact. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def largePrimeTupleFlatBoxSet (i j : ℕ) (ℓ : ℤ) (ξ : ℝ) (Ct G : ℕ) (H X : ℝ) :
    Finset ((Fin i ⊕ Fin j) → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :=
  Finset.univ.filter (fun d => largePrimeTuplePiece i j ℓ ξ Ct H X d ≠ 0 ∧
    ∃ B : ℝ, (∀ a, largeTupleNormScale (fun a => (d a).val) a ≤ B) ∧
      B^3 ≤ (∏ a, largeTupleNormScale (fun a => (d a).val) a)*(1+Real.log X)^G)

theorem largePrimeTupleFlatBoxSet_count (i j : ℕ) (hij : i+j = 3) (G : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ), 1 ≤ X →
      ((largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X).card:ℝ) ≤
        K*(1+Real.log (1+Real.log X))^3 := by
  obtain ⟨K,hK,hcount⟩ := flatTripleIndexSet_loglog_count G
  refine ⟨K,hK,?_⟩
  intro ℓ ξ Ct H X hX
  let M := normPartitionCount (Real.exp primeProductWeights.radius*X)
  let e : (Fin i ⊕ Fin j) ≃ Fin 3 := (Fintype.equivFin _).trans
    (finCongr (by simpa only [Fintype.card_sum,Fintype.card_fin] using hij))
  let F : ((Fin i ⊕ Fin j) → Fin M) → (Fin 3 → Fin M) := fun d b => d (e.symm b)
  have hF : Function.Injective F := by
    intro d c h
    funext a
    have hh := congrFun h (e a)
    simpa only [F,e.symm_apply_apply] using hh
  have hp (d : (Fin i ⊕ Fin j) → Fin M) :
      (∏ b, tripleNormScale (fun b => (F d b).val) b) =
        ∏ a, largeTupleNormScale (fun a => (d a).val) a := by
    symm
    apply Fintype.prod_equiv e
    intro a
    simp only [F,e.symm_apply_apply,tripleNormScale,largeTupleNormScale]
  have hsub : (largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X).image F ⊆
      flatTripleIndexSet M G X := by
    intro f hf
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨_,hne,B,hB,hflat⟩ := Finset.mem_filter.mp hd
    obtain ⟨q,_hq,hqne⟩ := largePrimeTuplePiece_witness d hne
    have hrange := largePrimeTuplePiece_scale_product (zero_lt_one.trans_le hX) d hqne
    change X/(2*2^(i+j)) ≤ (∏ a, largeTupleNormScale (fun a => (d a).val) a) ∧
      (∏ a, largeTupleNormScale (fun a => (d a).val) a) ≤ 3*X at hrange
    rw [hij] at hrange
    norm_num only [pow_succ,pow_zero,mul_one] at hrange
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,B,?_,?_⟩
    · rw [hp]
      simpa using hrange.1
    · rw [hp]
      exact hrange.2
    · intro b
      change largeTupleNormScale (fun a => (d a).val) (e.symm b) ≤ B
      exact hB _
    · rw [hp]
      exact hflat
  calc
    _ = (((largePrimeTupleFlatBoxSet i j ℓ ξ Ct G H X).image F).card:ℝ) := by
      rw [Finset.card_image_of_injective _ hF]
    _ ≤ ((flatTripleIndexSet M G X).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ _ := hcount M X hX

end CubicFirstMoment

end

end OAI
