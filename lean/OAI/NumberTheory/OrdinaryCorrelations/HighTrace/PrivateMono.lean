import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Cylinder

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder.Cylinder
open Finset Classical
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]

omit [∀ p, Fintype (Ω p)] in
lemma private_mono {A A' : Finset (Cylinder Ω)} (h : A' ⊆ A) (hp : Private A) : Private A' := by
  intro e he
  obtain ⟨p,hpe,hpriv⟩ := hp e (h he)
  exact ⟨p,hpe,fun f hf hpf => hpriv f (h hf) hpf⟩

lemma exists_private_family (E : Finset (Cylinder Ω)) (c : Cylinder Ω)
    (t : ℕ) (ht : 0 < t) (hc : t ≤ rank E c) :
    ∃ A ⊆ E, A.card=t ∧ (∀ e ∈ A, e ≤ c) ∧ Private A := by
  obtain ⟨A,hA,hcard⟩ := (Finset.le_sup_iff ht).mp hc
  have hmem := mem_filter.mp hA
  have hAE : A ⊆ E := mem_powerset.mp hmem.1
  obtain ⟨A',hA',hcard'⟩ := exists_subset_card_eq hcard
  exact ⟨A',hA'.trans hAE,hcard',fun e he => hmem.2.1 e (hA' he),
    private_mono hA' hmem.2.2⟩
end OrdinaryCorrelations.SourceCylinder.Cylinder

end

end OAI
