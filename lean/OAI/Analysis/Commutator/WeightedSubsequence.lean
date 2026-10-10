import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open Filter Finset

open scoped Topology

namespace Kadison.PositiveWOT

theorem exists_weighted_subsequence (q : ℕ → ℕ → ℝ)
    (hq : ∀ n j,0≤q n j) (ht : ∀ j,Tendsto (fun n => q n j) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ ∀ j,∃ C : ℝ,∀ N,
      ∑ k∈range N,((k:ℝ)+1)*q (u k) j≤C := by
  have hev (k : ℕ) : ∀ᶠ n in atTop,∀ j∈range (k+1),
      q n j≤(1/2:ℝ)^k/((k:ℝ)+1) := by
    apply (eventually_all_finset (range (k+1))).mpr
    intro j _
    exact ((ht j).eventually_lt_const (by positivity : (0:ℝ)<(1/2:ℝ)^k/((k:ℝ)+1))).mono
      fun _ h => h.le
  obtain ⟨u,hu,huq⟩ := Tendsto.subseq_mem (V:=fun k => {n | ∀ j∈range (k+1),
    q n j≤(1/2:ℝ)^k/((k:ℝ)+1)}) hev (tendsto_id (α:=ℕ) : Tendsto id atTop atTop)
  refine ⟨u,hu,?_⟩
  intro j
  let z (k : ℕ) : ℝ := ((k:ℝ)+1)*q (u k) j
  have hz (k : ℕ) : 0≤z k := mul_nonneg (by positivity) (hq _ _)
  have hsmall (k : ℕ) (hjk : j≤k) : z k≤(1/2:ℝ)^k := by
    have h := huq k j (mem_range.mpr (by omega))
    dsimp [z]
    simpa only [mul_comm,id_eq] using (le_div_iff₀ (by positivity : (0:ℝ)<(k:ℝ)+1)).mp h
  refine ⟨(∑ k∈range j,z k)+2,?_⟩
  intro N
  change (∑ k∈range N,z k)≤_
  rcases le_total N j with hNj|hjN
  · have hh : (∑ k∈range N,z k)≤∑ k∈range j,z k :=
      sum_le_sum_of_subset_of_nonneg (range_mono hNj) (fun k _ _ => hz k)
    linarith
  · rw [←sum_range_add_sum_Ico z hjN]
    refine add_le_add le_rfl ?_
    calc
      (∑ k∈Ico j N,z k)≤∑ k∈Ico j N,(1/2:ℝ)^k :=
        sum_le_sum (fun k hk => hsmall k (mem_Ico.mp hk).1)
      _ ≤ ∑ k∈range N,(1/2:ℝ)^k := sum_le_sum_of_subset_of_nonneg
        (by intro k hk; exact mem_range.mpr (mem_Ico.mp hk).2) (by intros; positivity)
      _ ≤ 2 := sum_geometric_two_le N

end Kadison.PositiveWOT

end

end
end

end OAI
