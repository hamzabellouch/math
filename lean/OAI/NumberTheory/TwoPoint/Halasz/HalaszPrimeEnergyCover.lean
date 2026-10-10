import OAI.NumberTheory.TwoPoint.Halasz.HalaszAvoidPrimes

namespace OAI

/-! Cover each pair of good long tuples by a prime at which both
remain nonsingular. This is a cover of solutions, not just of tuples. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_fiber_energy_cover {α ι : Type*} {k : ℕ}
    (F : Finset α) (S : Finset ι) (G : ι → Finset α) (f : α → Fin k → ℤ)
    (hcover : ∀ x∈F, ∀ y∈F, f x=f y → ∃ i∈S, x∈G i ∧ y∈G i) :
    halaszFiberEnergy F f≤∑ i∈S, halaszFiberEnergy (G i) f := by
  let T := fun i => ((G i×ˢG i).filter (fun xy => f xy.1=f xy.2))
  have hsub : ((F×ˢF).filter (fun xy => f xy.1=f xy.2))⊆S.biUnion T := by
    intro xy hxy
    obtain ⟨hxy,hf⟩ := mem_filter.mp hxy
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    obtain ⟨i,hi,hxi,hyi⟩ := hcover xy.1 hx xy.2 hy hf
    exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨mem_product.mpr ⟨hxi,hyi⟩,hf⟩⟩
  calc
    halaszFiberEnergy F f = ((F×ˢF).filter (fun xy => f xy.1=f xy.2)).card :=
      (halasz_cross_count_self F f).symm
    _ ≤ (S.biUnion T).card := card_le_card hsub
    _ ≤ ∑ i∈S, (T i).card := card_biUnion_le
    _ = _ := sum_congr rfl (fun i _ => halasz_cross_count_self (G i) f)

noncomputable def halaszResidueGoodTuples {n N ℓ : ℕ}
    (L : Fin ℓ → Fin n) (p : ℕ) : Finset (Fin n → Fin N) :=
  univ.filter (fun x => Function.Injective (fun i => (((x (L i)).val+1:ℕ):ZMod p)))

theorem halasz_distinct_energy_prime_cover {n k N ℓ R r : ℕ} (hR : 0<R)
    (hN : N≤R^r) (P : Finset ℕ) (hP : ∀ p∈P, p.Prime ∧ R≤p)
    (hcard : 2*(ℓ^2*r)<P.card) (L : Fin ℓ → Fin n) :
    halaszFiberEnergy (halaszGoodLongTuples (N := N) L) (halaszVinogradovFrequency k) ≤
      ∑ p∈P, halaszFiberEnergy (halaszResidueGoodTuples (N := N) L p)
        (halaszVinogradovFrequency k) := by
  apply halasz_fiber_energy_cover
  intro x hx y hy _
  have hxI := (mem_filter.mp hx).2
  have hyI := (mem_filter.mp hy).2
  obtain ⟨p,hp,hxp,hyp⟩ := halasz_exists_good_prime hR hN P hP hcard
    (x ∘ L) (y ∘ L) hxI hyI
  exact ⟨p,hp,mem_filter.mpr ⟨mem_univ _,hxp⟩,mem_filter.mpr ⟨mem_univ _,hyp⟩⟩

end TwoPointCorrelations

end OAI
