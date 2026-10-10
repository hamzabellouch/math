import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.FiniteHeaderUnion

namespace OAI

section
namespace SharpLogRamsey.PublicFamilies
open Finset Real
open scoped Classical
noncomputable section

theorem size_header_library {α β : Type*} (A B : ℕ) (Good : ℕ → ℕ → Prop)
    (Size : Finset α → Prop) (Eligible : Finset α → Finset β → Prop)
    (Capture : Finset α → Finset α → Prop) (L : ℝ) (hL : 0≤L)
    (h : ∀ a≤A,∀ b≤B,Good a b → ∃ F : Finset (Finset α),
      (∀ W∈F,Size W) ∧
      (∀ S T,S.card=a → T.card=b → Eligible S T → ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤L) :
    ∃ F : Finset (Finset α),(∀ W∈F,Size W) ∧
      (∀ S T,S.card≤A → T.card≤B → Good S.card T.card → Eligible S T →
        ∃ W∈F,Capture S W) ∧
      log ((F.card:ℝ)+1)≤log ((((A+1)*(B+1):ℕ):ℝ)+1)+L := by
  let I := Fin (A+1) × Fin (B+1)
  have hex : ∀ j : I,∃ F : Finset (Finset α),
      (∀ W∈F,Size W) ∧
      (Good j.1 j.2 → ∀ S T,S.card=(j.1:ℕ) → T.card=(j.2:ℕ) → Eligible S T →
        ∃ W∈F,Capture S W) ∧ log ((F.card:ℝ)+1)≤L := by
    intro j
    by_cases hg : Good j.1 j.2
    · obtain ⟨F,hFs,hFc,hFl⟩ := h j.1 (by omega) j.2 (by omega) hg
      exact ⟨F,hFs,fun _ => hFc,hFl⟩
    · refine ⟨∅,by simp,?_,by simpa using hL⟩
      exact fun hh => False.elim (hg hh)
  choose F hF using hex
  refine ⟨univ.biUnion F,?_,?_,?_⟩
  · intro W hW
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hW
    exact (hF j).1 W hj
  · intro S T hSA hTB hg he
    let j : I := (⟨S.card,by omega⟩,⟨T.card,by omega⟩)
    obtain ⟨W,hW,hcap⟩ := (hF j).2.1 hg S T rfl rfl he
    exact ⟨W,mem_biUnion.mpr ⟨j,mem_univ _,hW⟩,hcap⟩
  · have hh := union_log_bound (univ : Finset I) F L hL (fun j _ => (hF j).2.2)
    simp only [card_univ,I,Fintype.card_prod,Fintype.card_fin] at hh
    exact hh

end
end SharpLogRamsey.PublicFamilies

end

end OAI
