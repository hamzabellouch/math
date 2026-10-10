import OAI.Probability.ContinuumTransition.InnerGrand

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature
open Classical

theorem occupation_disjoint_eq_fiber {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : κ → Set Space) (hd : Pairwise (fun k l => Disjoint (A k) (A l)))
    (c : ι → κ) (x : ι → Space) (hx : ∀ i, x i ∈ A (c i)) (k : κ) :
    occupation (A k) x = (Fintype.card {i // c i = k} : ℝ) := by
  unfold occupation
  congr 1
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro i
  constructor
  · intro hik
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) (hx i) hik
  · intro he
    simpa only [he] using hx i

theorem card_eq_sum_fibers {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] (c : ι → κ) :
    (Fintype.card ι : ℝ) = ∑ k, (Fintype.card {i // c i = k} : ℝ) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    sum_comp_eq_sum_fibres c (fun _ => (1 : ℝ))

theorem kacLower_grid_double_lower {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u) :
    (gridIndices m 1).card*((1-kacRowError C R u)/u^3) ≤
      ∑ k ∈ gridIndices (m+N) 1, ∑ l ∈ gridIndices (m+N) 1,
        kacLower C R u (gridCenter u k) (gridCenter u l) := by
  have hrow (k : Lattice) (hk : k ∈ gridIndices m 1) :
      (1-kacRowError C R u)/u^3 ≤
        ∑ l ∈ gridIndices (m+N) 1, kacLower C R u (gridCenter u k) (gridCenter u l) := by
    apply (div_le_iff₀ (pow_pos hu 3)).2
    have hh := kacLower_row hC hR hu (gridCenter u k) (gridIndices (m+N) 1)
      (interior_grid_cover hu hN hk)
    simpa only [kacRowError, mul_comm] using hh
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg (gridIndices_mono (Nat.le_add_right m N))
  intro k _ _
  exact Finset.sum_nonneg (fun l _ => le_max_left _ _)

theorem kac_energy_lower_fixed {C : NNReal} (hC : LipschitzWith C kernel)
    {R u : ℝ} (hR : 0 < R) (hu : 0 < u) {N m : ℕ} (hN : R+u ≤ (N : ℝ)*u)
    {ι : Type} [Fintype ι] (x : ι → Space) (n : ℕ)
    (hx : ∀ i, x i ∈ ⋃ k ∈ gridIndices (m+N) 1, innerGridBox u k)
    (hn : ∀ k ∈ gridIndices (m+N) 1, occupation (innerGridBox u k) x = (n : ℝ)) :
    ((gridIndices m 1).card*(n : ℝ)^2*((1-kacRowError C R u)/u^3)-
      (gridIndices (m+N) 1).card*n*scaledKernel R 0)/2 ≤
        gibbsEnergy (fun x y => scaledKernel R (x-y)) x := by
  let s := gridIndices (m+N) 1
  have hchoice (i : ι) : ∃ k : s, x i ∈ innerGridBox u k := by
    obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.mp (hx i)
    exact ⟨⟨k,hk⟩,hxk⟩
  choose c hc using hchoice
  have hcard (k : s) : (Fintype.card {i // c i = k} : ℝ) = n := by
    rw [← occupation_disjoint_eq_fiber (fun k : s => innerGridBox u k)
      (fun k l hkl => innerGridBox_disjoint hu (fun h => hkl (Subtype.ext h))) c x hc k]
    exact hn k k.property
  have htotal : (Fintype.card ι : ℝ) = s.card*n := by
    calc
      (Fintype.card ι : ℝ) = ∑ k : s, (Fintype.card {i // c i = k} : ℝ) := card_eq_sum_fibers c
      _ = s.card*n := by simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
  have hbound := kac_energy_lower hC hR c (fun k : s => gridCenter u k) x
    (fun i => gridBox_center_distance hu (innerGridBox_subset_gridBox _ _ (hc i)))
  have hsum : (∑ k : s, ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l)*
      (Fintype.card {i // c i = k} : ℝ)*(Fintype.card {i // c i = l} : ℝ)) =
      (∑ k ∈ s, ∑ l ∈ s, kacLower C R u (gridCenter u k) (gridCenter u l))*(n : ℝ)^2 := by
    simp only [hcard]
    simp_rw [mul_assoc, ← pow_two]
    simp_rw [← Finset.sum_mul]
    congr 1
    calc
      _ = ∑ k ∈ s, ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l) :=
        Finset.sum_coe_sort s (fun k => ∑ l : s, kacLower C R u (gridCenter u k) (gridCenter u l))
      _ = _ := Finset.sum_congr rfl (fun k _ =>
        Finset.sum_coe_sort s (fun l => kacLower C R u (gridCenter u k) (gridCenter u l)))
  rw [hsum, htotal] at hbound
  have hr := mul_le_mul_of_nonneg_right (kacLower_grid_double_lower (m := m) hC hR hu hN) (sq_nonneg (n : ℝ))
  change (gridIndices m 1).card*((1-kacRowError C R u)/u^3)*(n : ℝ)^2 ≤ _ at hr
  dsimp only [s] at hbound
  nlinarith only [hbound,hr]

end ContinuumTemperature
end

end OAI
