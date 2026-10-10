import OAI.Combinatorics.Ramsey.CycleClique.Construction.CEConnectivity
import OAI.Combinatorics.Ramsey.CycleClique.Construction.CECycleExtension
import OAI.Combinatorics.Ramsey.CycleClique.Construction.PublishedInputs

namespace OAI

/-! The application-sized Chvátal–Erdős theorem: alpha at most two. -/

namespace CycleClique.Construction
theorem ce_exists_longest_cycle {V : Type*} [Fintype V] {H : SimpleGraph V}
    (hcard : 6 ≤ Fintype.card V) (hα : ¬ HasIndependent H 3) :
    ∃ r, 2 ≤ r ∧ ∃ c : Fin (r + 1) → V, Function.Injective c ∧
      (∀ i, H.Adj (c i) (c (cycleNext i))) ∧
      ∀ q, HasCycle H q → q ≤ r + 1 := by
  classical
  let f : Fin 6 → V := fun i => (Fintype.equivFin V).symm (Fin.castLE hcard i)
  have hf : Function.Injective f := (Fintype.equivFin V).symm.injective.comp
    (Fin.castLE_injective hcard)
  have hthree : HasCycle H 3 := by
    rcases triangle_upper (H.comap f) with h | h
    · exact h.map f hf (fun h => h)
    · exact False.elim (hα (h.map f hf (fun h => h)))
  let N := Fintype.card V
  have hex : ∃ d, ∃ q, HasCycle H q ∧ q + d = N :=
    ⟨N - 3, 3, hthree, by dsimp [N]; omega⟩
  obtain ⟨q, hq, hqd⟩ := Nat.find_spec hex
  have hmax : ∀ t, HasCycle H t → t ≤ q := by
    intro t ht
    have htcard : t ≤ N := ht.card_le
    have hm := Nat.find_min' hex
      (show ∃ q, HasCycle H q ∧ q + (N - t) = N from
        ⟨t, ht, Nat.add_sub_of_le htcard⟩)
    omega
  have hq3 : 3 ≤ q := hmax 3 hthree
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨c, hc, he⟩ := hq
  exact ⟨r, by omega, c, hc, he, hmax⟩

/-- Chvátal–Erdős (1972), Theorem 1, in the precise specialization used by
the conditional Ramsey development. -/
theorem ceAlphaTwo_proved : CEAlphaTwo := by
  intro V _ H hcard hconn hdel hα
  classical
  obtain ⟨r, hr, c, hc, he, hmax⟩ := ce_exists_longest_cycle hcard hα
  by_cases hsurj : Function.Surjective c
  · have hn : r + 1 = Fintype.card V := by
      simpa using Fintype.card_of_bijective ⟨hc, hsurj⟩
    exact hn ▸ (show HasCycle H (r + 1) from ⟨c, hc, he⟩)
  · change ¬ ∀ v, ∃ i, c i = v at hsurj
    push Not at hsurj
    obtain ⟨x, hx⟩ := hsurj
    let S : Finset V := Finset.univ.image c
    have hSmem : ∀ v, v ∈ S ↔ v ∈ Set.range c := by simp [S]
    have hScard : S.card = r + 1 := by
      simpa [S] using Finset.card_image_of_injective Finset.univ hc
    have hxS : x ∉ S := by
      intro h
      obtain ⟨i, hi⟩ := (hSmem x).mp h
      exact hx i hi
    obtain ⟨l, hl, g, hg, hg0, hgl, hgout⟩ := ce_external_ear hconn hdel S
      (by omega) x hxS
    apply False.elim
    apply ce_external_ear_impossible hr hl hc he hmax hα hg ((hSmem _).mp hg0)
      ((hSmem _).mp hgl)
    intro i hi hil k heq
    apply hgout i hi hil
    rw [← heq]
    exact (hSmem _).mpr ⟨k, rfl⟩

end CycleClique.Construction

end OAI
