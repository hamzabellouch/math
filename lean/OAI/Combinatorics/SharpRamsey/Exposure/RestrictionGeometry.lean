import Mathlib
import OAI.Combinatorics.SharpRamsey.Exposure.RestrictionBudget

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section

lemma count_injective_restriction {I J : Type} [Fintype I] [Fintype J]
    (e : I↪J) (P : J→Prop) :
    (univ.filter (fun i=>P (e i))).card≤(univ.filter P).card := by
  calc
    _ = ((univ.filter (fun i=>P (e i))).image e).card := by
      rw [card_image_of_injective _ e.injective]
    _ ≤ _ := card_le_card (by
      intro j hj
      obtain ⟨i,hi,rfl⟩:=mem_image.mp hj
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩)

variable {Ω Θ α : Type} [Fintype Ω] [Fintype Θ] [Fintype α]

def prefixSet {N m : ℕ} (hm : m≤N) : Finset (Fin N) :=
  univ.image (Fin.castLE hm)

lemma prefixSet_card {N m : ℕ} (hm : m≤N) : (prefixSet hm).card=m := by
  rw [prefixSet,card_image_of_injective _ (Fin.castLE_injective hm),card_univ,Fintype.card_fin]

lemma prefix_budget {N m : ℕ} (hm : m≤N)
    (p : Law Ω) (θ : Ω→Θ) (F : Ω→Fin N→α)
    (D : Θ→Fin N→Finset α) (J : ℝ)
    (hD : ∀ x,p.mass x≠0→∀ i,F x i∈D (θ x) i)
    (hJ : ∀ z i,Real.log (D z i).card≤J) :
    (∑ z,(p.map θ).mass z*((m:ℝ)*J-entropy ((p.cond θ z).map
      (orderedTuple (fun _=>prefixSet hm) hm θ F))))≤
    ∑ z,(p.map θ).mass z*((N:ℝ)*J-entropy ((p.cond θ z).map F)) := by
  convert ordered_restriction_budget hm p θ F D J hD hJ (fun _=>prefixSet hm)
    (fun _ _=>prefixSet_card hm) using 1
  all_goals congr!
end
end SharpLogRamsey.Selection

end

end OAI
