import OAI.NumberTheory.CubicMoment.Decomposition.StoppingCount

namespace OAI

/-! The first stopping bin is selected from actual finite prime bins.
Only the final bin and its selected count are exposed as outer indices. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeBin (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) : Finset Eisenstein :=
  s.filter (fun p => b p = j)

def primeBinPrefix (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) : Finset Eisenstein :=
  s.filter (fun p => b p < j)

def primeSurrogate (s : Finset Eisenstein) (b : Eisenstein → ℕ) (ell : ℕ → ℝ) : ℝ :=
  ∏ p ∈ s, ell (b p)

lemma primeBinPrefix_succ (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) :
    primeBinPrefix s b (j+1) = primeBinPrefix s b j ∪ primeBin s b j := by
  ext p
  by_cases hp : p ∈ s
  · simp only [primeBinPrefix,primeBin,Finset.mem_filter,Finset.mem_union,hp,true_and]
    omega
  · simp [primeBinPrefix,primeBin,hp]

lemma primeBinPrefix_disjoint (s : Finset Eisenstein) (b : Eisenstein → ℕ) (j : ℕ) :
    Disjoint (primeBinPrefix s b j) (primeBin s b j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  omega

lemma primeSurrogate_prefix_succ (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) (j : ℕ) :
    primeSurrogate (primeBinPrefix s b (j+1)) b ell =
      primeSurrogate (primeBinPrefix s b j) b ell * ell j^(primeBin s b j).card := by
  rw [primeBinPrefix_succ,primeSurrogate,
    Finset.prod_union (primeBinPrefix_disjoint s b j)]
  congr 1
  calc
    _ = ∏ _p ∈ primeBin s b j, ell j := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.prod_const _

lemma first_crossing_index (f : ℕ → ℝ) {Z : ℝ} (h0 : f 0 < Z)
    {m : ℕ} (hm : Z ≤ f m) :
    ∃ j : ℕ, j < m ∧ f j < Z ∧ Z ≤ f (j+1) := by
  have hex : ∃ k : ℕ, Z ≤ f k := ⟨m,hm⟩
  let k := Nat.find hex
  have hk : 0 < k := by
    by_contra h
    have he : k = 0 := Nat.eq_zero_of_not_pos h
    have hf := Nat.find_spec hex
    change Z ≤ f k at hf
    rw [he] at hf
    exact (not_le_of_gt h0) hf
  have hkm : k ≤ m := Nat.find_min' hex hm
  refine ⟨k-1,by omega,?_,?_⟩
  · exact lt_of_not_ge (Nat.find_min hex (Nat.sub_lt hk (by decide)))
  · rw [Nat.sub_add_cancel hk]
    exact Nat.find_spec hex

/-- Exact selection of the first bin and the first count within it.
The terminal bin contributes no occupancy-vector outer index. -/
theorem first_prime_bin (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) {m : ℕ} (hb : ∀ p ∈ s, b p < m)
    (hell : ∀ j < m, 1 < ell j) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (hend : Z ≤ R*primeSurrogate s b ell) :
    ∃ j < m, ∃ k : ℕ, 1 ≤ k ∧ k ≤ (primeBin s b j).card ∧
      (R*primeSurrogate (primeBinPrefix s b j) b ell)*ell j^k/ell j < Z ∧
      Z ≤ (R*primeSurrogate (primeBinPrefix s b j) b ell)*ell j^k := by
  let f := fun j => R*primeSurrogate (primeBinPrefix s b j) b ell
  have h0 : f 0 < Z := by simpa [f,primeSurrogate,primeBinPrefix] using hstart
  have hm : Z ≤ f m := by
    have hset : primeBinPrefix s b m = s := by
      apply Finset.filter_true_of_mem
      exact hb
    simpa only [f,hset] using hend
  obtain ⟨j,hjm,hj,hjnext⟩ := first_crossing_index f h0 hm
  have hRj : 0 < R*primeSurrogate (primeBinPrefix s b j) b ell := by
    apply mul_pos hR
    apply Finset.prod_pos
    intro p hp
    exact zero_lt_one.trans (hell _ (hb p (Finset.mem_filter.mp hp).1))
  have hendj : Z ≤ (R*primeSurrogate (primeBinPrefix s b j) b ell)*
      ell j^(primeBin s b j).card := by
    simpa only [f,primeSurrogate_prefix_succ,mul_assoc] using hjnext
  obtain ⟨k,hk,hks,hprev,hhit,_⟩ := first_bin_crossing hRj (hell j hjm) hj hendj
  exact ⟨j,hjm,k,hk,hks,hprev,hhit⟩

end CubicFirstMoment

end

end OAI
