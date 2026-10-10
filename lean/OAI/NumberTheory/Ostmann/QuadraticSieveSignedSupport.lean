import OAI.NumberTheory.Ostmann.QuadraticSieve

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def signedSquarefreeUpTo (U : ℕ) : Finset ℤ := by
  classical
  exact (Finset.Icc (-(U : ℤ)) (U : ℤ)).filter (fun u => u ≠ 0 ∧ Squarefree u)

@[simp] theorem mem_signedSquarefreeUpTo {U : ℕ} {u : ℤ} :
    u ∈ signedSquarefreeUpTo U ↔
      -(U : ℤ) ≤ u ∧ u ≤ (U : ℤ) ∧ u ≠ 0 ∧ Squarefree u := by
  classical
  simp only [signedSquarefreeUpTo, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem mem_signedSquarefreeUpTo_iff_natAbs {U : ℕ} {u : ℤ} :
    u ∈ signedSquarefreeUpTo U ↔ u.natAbs ≤ U ∧ u ≠ 0 ∧ Squarefree u.natAbs := by
  rw [mem_signedSquarefreeUpTo, Int.squarefree_natAbs]
  have hbound : u.natAbs ≤ U ↔ -(U : ℤ) ≤ u ∧ u ≤ (U : ℤ) := by
    constructor
    · intro h
      have hz : (u.natAbs : ℤ) ≤ (U : ℤ) := by exact_mod_cast h
      rwa [Int.natCast_natAbs, abs_le] at hz
    · intro h
      have hz : (u.natAbs : ℤ) ≤ (U : ℤ) := by
        rw [Int.natCast_natAbs]
        exact abs_le.mpr h
      exact_mod_cast hz
  rw [hbound]
  tauto

theorem squarefree_odd_factor {n : ℕ} (hn : Squarefree n) :
    ∃ e v : ℕ, (e = 1 ∨ e = 2) ∧ 1 ≤ v ∧ v ≤ n ∧ Odd v ∧
      Squarefree v ∧ n = e * v := by
  by_cases ho : Odd n
  · exact ⟨1, n, Or.inl rfl, Nat.pos_of_ne_zero hn.ne_zero, le_rfl, ho, hn,
      (one_mul n).symm⟩
  · have hmod : n % 2 ≠ 1 := by simpa only [Nat.odd_iff] using ho
    have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨v, hv⟩ := hdvd
    have hsplit := Nat.squarefree_mul_iff.mp (show Squarefree (2 * v) by rwa [← hv])
    refine ⟨2, v, Or.inr rfl, Nat.pos_of_ne_zero hsplit.2.2.ne_zero, ?_,
      Nat.coprime_two_left.mp hsplit.1, hsplit.2.2, hv⟩
    omega

def signedSquarefreeMultipliers : Finset ℤ := {-2, -1, 1, 2}

@[simp] theorem mem_signedSquarefreeMultipliers {c : ℤ} :
    c ∈ signedSquarefreeMultipliers ↔ c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2 := by
  simp [signedSquarefreeMultipliers]

@[simp] theorem card_signedSquarefreeMultipliers : signedSquarefreeMultipliers.card = 4 := by
  norm_num [signedSquarefreeMultipliers]

theorem signedSquarefreeMultiplier_ne_zero {c : ℤ} (hc : c ∈ signedSquarefreeMultipliers) :
    c ≠ 0 := by
  rcases mem_signedSquarefreeMultipliers.mp hc with rfl | rfl | rfl | rfl <;> norm_num

theorem signedSquarefreeMultiplier_injective {c : ℤ}
    (hc : c ∈ signedSquarefreeMultipliers) :
    Function.Injective (fun v : ℕ => c * (v : ℤ)) := by
  intro v w h
  exact_mod_cast mul_left_cancel₀ (signedSquarefreeMultiplier_ne_zero hc) h

theorem exists_signedSquarefree_factor {U : ℕ} {u : ℤ}
    (hu : u ∈ signedSquarefreeUpTo U) :
    ∃ c ∈ signedSquarefreeMultipliers, ∃ v ∈ oddSquarefreeUpTo U, u = c * (v : ℤ) := by
  obtain ⟨hU, hu0, hsq⟩ := mem_signedSquarefreeUpTo_iff_natAbs.mp hu
  obtain ⟨e, v, he, hv1, hvn, hvo, hvsq, hev⟩ := squarefree_odd_factor hsq
  have hv : v ∈ oddSquarefreeUpTo U :=
    mem_oddSquarefreeUpTo.mpr ⟨hv1, hvn.trans hU, hvo, hvsq⟩
  have hcast : (u.natAbs : ℤ) = (e : ℤ) * (v : ℤ) := by exact_mod_cast hev
  by_cases hnonneg : 0 ≤ u
  · refine ⟨(e : ℤ), ?_, v, hv, (Int.eq_natAbs_of_nonneg hnonneg).trans hcast⟩
    rcases he with rfl | rfl <;> norm_num [signedSquarefreeMultipliers]
  · refine ⟨-(e : ℤ), ?_, v, hv, ?_⟩
    · rcases he with rfl | rfl <;> norm_num [signedSquarefreeMultipliers]
    · have hneg : u = -(u.natAbs : ℤ) := by
        rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hnonneg), neg_neg]
      rw [hneg, hcast, neg_mul]

theorem signedSquarefreeUpTo_subset_biUnion (U : ℕ) :
    signedSquarefreeUpTo U ⊆
      signedSquarefreeMultipliers.biUnion
        (fun c => (oddSquarefreeUpTo U).image (fun v : ℕ => c * (v : ℤ))) := by
  classical
  intro u hu
  obtain ⟨c, hc, v, hv, huv⟩ := exists_signedSquarefree_factor hu
  exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_image.mpr ⟨v, hv, huv.symm⟩⟩

end Ostmann.QuadraticSieve

end OAI
