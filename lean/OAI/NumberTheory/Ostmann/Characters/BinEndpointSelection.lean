import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters

theorem common_bin_many_endpoints {α β:Type*} [DecidableEq α] [Fintype β] [Nonempty β]
    (S:Finset α) (F:α→β→ℂ) (c:ℝ) (hlarge:∀a∈S,c≤‖∑b,F a b‖) :
    ∃b:β,S.card≤Fintype.card β *
      (S.filter (fun a=>c≤(Fintype.card β:ℝ)*‖F a b‖)).card := by
  classical
  choose choice hchoice using fun a:α=>exists_bin_norm (F a)
  let fiber := fun b:β=>S.filter (fun a=>choice a=b)
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun b:β=>(fiber b).card) Finset.univ_nonempty
  have hsum : S.card=∑b:β,(fiber b).card :=
    Finset.card_eq_sum_card_fiberwise (f:=choice) (fun _ _=>Finset.mem_univ _)
  have hsub : fiber b⊆S.filter (fun a=>c≤(Fintype.card β:ℝ)*‖F a b‖) := by
    intro a ha
    obtain ⟨haS,hab⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_filter.mpr ⟨haS,?_⟩
    exact (hlarge a haS).trans (by simpa only [hab] using hchoice a)
  refine ⟨b,?_⟩
  calc
    S.card = ∑j:β,(fiber j).card := hsum
    _ ≤ ∑_j:β,(fiber b).card := Finset.sum_le_sum (fun j hj=>hmax j hj)
    _ = Fintype.card β*(fiber b).card := by simp
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card hsub)

end Ostmann.Characters

end

end OAI
