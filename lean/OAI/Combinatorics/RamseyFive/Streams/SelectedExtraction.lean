import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OrderedExtraction

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α Ω : Type*} [Fintype α] [Fintype Ω]

lemma mem_occurrences_iff {n l : ℕ} (s : Fin n→α) (f : Fin l→α) :
    s∈occurrences f ↔ ∃ e:Fin l ↪o Fin n,∀ i,s (e i)=f i := by
  constructor
  · intro h
    obtain ⟨I,_,hI⟩:=Finset.mem_biUnion.mp h
    exact ⟨I.val.orderEmbOfFin I.property,(Finset.mem_filter.mp hI).2⟩
  · rintro ⟨e,he⟩
    let I : Finset (Fin n) := Finset.univ.map e.toEmbedding
    have hI : I.card=l := by simp [I]
    have hei : I.orderEmbOfFin hI=e := by
      symm
      apply Finset.orderEmbOfFin_unique' hI
      intro j
      simp [I]
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨I,hI⟩,Finset.mem_univ _,?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j=>by rw [hei];exact he j⟩

lemma occurrences_trans {n m l : ℕ} (s : Fin n→α) (f : Fin m→α) (g : Fin l→α)
    (hf : s∈occurrences f) (hg : f∈occurrences g) : s∈occurrences g := by
  obtain ⟨e,he⟩:=(mem_occurrences_iff s f).mp hf
  obtain ⟨d,hd⟩:=(mem_occurrences_iff f g).mp hg
  apply (mem_occurrences_iff s g).mpr
  exact ⟨d.trans e,fun i=>(he (d i)).trans (hd i)⟩

theorem retained_entropy [Nonempty α] {N n l : ℕ} (hn : n≤N) (hl : l≤n)
    (p : Law Ω) (stream : Ω→Fin N→α) (x : Ω→Fin n→α) (S : Ω→Finset (Fin n))
    (hselect : ∀ a,0<p a→stream a∈occurrences (x a))
    (C : ℝ) (hC : 0≤C) (hdens : ∀ s,map p stream s≤C/(Fintype.card α:ℝ)^N) :
    -Real.log (2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l) ≤
      entropy (map p (fun a=>retainedTuple hl (x a) (S a))) := by
  have hh := selected_entropy (hl.trans hn)
    (pair p stream (fun a=>retainedTuple hl (x a) (S a))) C hC
    (by simpa only [first_pair] using hdens) id (by
      intro s f hp
      obtain ⟨a,ha,he⟩:=map_positive p (fun a=>(stream a,retainedTuple hl (x a) (S a))) (s,f) hp
      cases he
      exact Or.inl (occurrences_trans _ _ _ (hselect a ha) (retainedTuple_occurs hl _ _)))
  simpa only [second_pair] using hh
end
end SharpRamseyFive.SelectedTuple

end OAI
