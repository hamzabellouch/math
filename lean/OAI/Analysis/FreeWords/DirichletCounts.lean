import Mathlib

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators

noncomputable section

def dirichletCount (N k : ℕ) : ℕ :=
  (((Finset.range N) ×ˢ (Finset.range N)).filter (fun x => x.1+x.2=k)).card

theorem dirichletCount_low {N k : ℕ} (hk : k < N) : dirichletCount N k = k+1 := by
  classical
  rw [dirichletCount, ← Finset.card_range (k+1)]
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hx ⊢
    omega
  · intro x hx y hy he
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hx hy
    apply Prod.ext he
    omega
  · intro k' hk'
    have hk' : k' < k+1 := Finset.mem_range.mp hk'
    refine ⟨(k',k-k'), ?_, rfl⟩
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range]
    omega

theorem dirichletCount_reflect {N k : ℕ} (hN : 0 < N) (hk : k ≤ 2*(N-1)) :
    dirichletCount N k = dirichletCount N (2*(N-1)-k) := by
  classical
  unfold dirichletCount
  apply Finset.card_bij (fun x _ => (N-1-x.1,N-1-x.2))
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hx ⊢
    omega
  · intro x hx y hy he
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hx hy
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    apply Prod.ext <;> dsimp at h1 h2 ⊢ <;> omega
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hx
    refine ⟨(N-1-x.1,N-1-x.2), ?_, ?_⟩
    · simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_range]
      omega
    · apply Prod.ext <;> dsimp <;> omega

theorem dirichletCount_high {N k : ℕ} (hk : k < N-1) :
    dirichletCount N (N+k) = N-1-k := by
  have hN : 0 < N := by omega
  rw [dirichletCount_reflect hN (by omega),dirichletCount_low (by omega)]
  omega

theorem sum_squares_succ_real (N : ℕ) :
    ∑ k ∈ Finset.range N, ((k:ℝ)+1)^2 = (N:ℝ)*((N:ℝ)+1)*(2*(N:ℝ)+1)/6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

theorem dirichletCount_energy {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range (2*N-1), (dirichletCount N k : ℝ)^2 =
      (2*(N:ℝ)^3+(N:ℝ))/3 := by
  have hsize : 2*N-1 = N+(N-1) := by omega
  rw [hsize, Finset.sum_range_add]
  have h1 : ∑ k ∈ Finset.range N, (dirichletCount N k : ℝ)^2 =
      (N:ℝ)*((N:ℝ)+1)*(2*(N:ℝ)+1)/6 := by
    simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun n : ℕ => (n:ℝ)^2)
      (dirichletCount_low (Finset.mem_range.mp hk))), Nat.cast_add,Nat.cast_one]
    exact sum_squares_succ_real N
  have h2 : ∑ k ∈ Finset.range (N-1), (dirichletCount N (N+k) : ℝ)^2 =
      ((N:ℝ)-1)*(N:ℝ)*(2*(N:ℝ)-1)/6 := by
    have hsum : ∑ k ∈ Finset.range (N-1), (dirichletCount N (N+k) : ℝ)^2 =
        ∑ k ∈ Finset.range (N-1), ((k:ℝ)+1)^2 := by
      rw [← Finset.sum_range_reflect (fun k => (dirichletCount N (N+k) : ℝ)^2)]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [dirichletCount_high (by omega)]
      have he : N-1-(N-1-1-k) = k+1 := by omega
      rw [he, Nat.cast_add,Nat.cast_one]
    rw [hsum,sum_squares_succ_real,Nat.cast_sub (by omega),Nat.cast_one]
    ring
  rw [h1,h2]
  ring

end

end KKFreeWords
end

end OAI
