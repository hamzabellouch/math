import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceCellSumsNatural

namespace OAI

noncomputable section
namespace Ostmann.Characters.HigherBiasSource

theorem exists_good_cell_target_lists (c : ℝ) (hc : 0<c) :
    ∃ b0 : ℝ, 1≤b0 ∧ ∃ N : ℕ, 0<N ∧ ∀ (b T : ℝ) (I : Finset ℤ),
      b0≤b → (∀ x∈I,b≤(x:ℝ) ∧ (x:ℝ)≤Real.exp 1*b) → c*b≤(I.card:ℝ) →
      (N:ℝ)≤T/b →
      ∃ l : List ℤ, (∀ x∈l,x∈I) ∧ |(l.sum:ℝ)-T|≤6/c ∧
        T/(6*b)≤(l.length:ℝ) ∧ (l.length:ℝ)≤2*T/b := by
  obtain ⟨N,hN,hNat⟩ := exists_natural_cell_target_lists c hc
  refine ⟨max 1 (2/c),le_max_left _ _,N,hN,?_⟩
  intro b T I hb hband hcard hT
  classical
  have hb1 : 1≤b := (le_max_left _ _).trans hb
  have hb0 : 0<b := lt_of_lt_of_le zero_lt_one hb1
  have hlarge : 2≤c*b := by
    have hh := (le_max_right (1:ℝ) (2/c)).trans hb
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith
  have hnonneg (x : ℤ) (hx : x∈I) : 0≤x := by
    have hh := (hband x hx).1
    exact_mod_cast (show (0:ℝ)≤x by linarith)
  have hcast (x : ℤ) (hx : x∈I) : ((x.toNat:ℕ):ℝ)=(x:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hnonneg x hx)
  let S := I.image Int.toNat
  have hScard : S.card=I.card := Finset.card_image_of_injOn (by
    intro x hx y hy hxy
    have hh := congrArg (fun n:ℕ => (n:ℤ)) hxy
    simpa only [Int.toNat_of_nonneg (hnonneg x hx),Int.toNat_of_nonneg (hnonneg y hy)] using hh)
  have hSband : ∀x∈S,b≤(x:ℝ) ∧ (x:ℝ)≤3*b := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    rw [hcast y hy]
    refine ⟨(hband y hy).1,(hband y hy).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by have := Real.exp_one_lt_d9; linarith) hb0.le
  obtain ⟨l,hmem,herr,hlenlo,hlenhi⟩ := hNat b T S hb1 hlarge hSband
    (by simpa only [hScard] using hcard) hT
  have hsum : (l.map (fun x:ℕ => (x:ℤ))).sum=(l.sum:ℤ) := by
    simp
  refine ⟨l.map (fun x:ℕ => (x:ℤ)),?_,?_,by simpa using hlenlo,by simpa using hlenhi⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp (hmem y hy)
    rw [←he,Int.toNat_of_nonneg (hnonneg z hz)]
    exact hz
  · simpa only [hsum,Int.cast_natCast] using herr

end Ostmann.Characters.HigherBiasSource

end

end OAI
