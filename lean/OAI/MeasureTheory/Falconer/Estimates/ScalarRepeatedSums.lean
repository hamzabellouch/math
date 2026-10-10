import OAI.MeasureTheory.Falconer.Estimates.ScalarRuzsa

namespace OAI

/-! Rounding errors for repeated scalar sumsets. Only one interval of
integer carries is required, so the loss is linear in the number of terms. -/
namespace Falconer
open scoped Pointwise

theorem scalar_nsum_floor (δ : ℝ) (X : Finset ℝ) (n : ℕ)
    {x : ℝ} (hx : x ∈ n • X) :
    ∃ z ∈ n • scalarCells δ X, ∃ k : ℤ,
      0 ≤ k ∧ k ≤ (n : ℤ) ∧ ⌊x/δ⌋ = z+k := by
  classical
  induction n generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact ⟨0,by simp,0,by norm_num,by norm_num,by simp⟩
  | succ n ih =>
    rw [succ_nsmul] at hx
    obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨z,hz,k,hk0,hkn,hk⟩ := ih ha
    have hbq : ⌊b/δ⌋ ∈ scalarCells δ X := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have hmem : z+⌊b/δ⌋ ∈ (n+1) • scalarCells δ X := by
      rw [succ_nsmul]
      exact Finset.add_mem_add hz hbq
    rw [add_div]
    rcases floor_add_carry (a/δ) (b/δ) with he | he
    · refine ⟨z+⌊b/δ⌋,hmem,k,hk0,by omega,?_⟩
      omega
    · refine ⟨z+⌊b/δ⌋,hmem,k+1,by omega,by omega,?_⟩
      omega

theorem scalar_signed_sum_cells_subset (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    scalarCells δ (m • X-n • X) ⊆
      (m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ) := by
  classical
  intro w hw
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_sub.mp hx
  obtain ⟨z,hz,k,hk0,hkm,hk⟩ := scalar_nsum_floor δ X m ha
  obtain ⟨v,hv,l,hl0,hln,hl⟩ := scalar_nsum_floor δ X n hb
  rw [sub_div]
  rcases floor_sub_carry (a/δ) (b/δ) with he | he
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · apply Finset.mem_add.mpr
    exact ⟨z-v,Finset.sub_mem_sub hz hv,k-l-1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩

theorem scalar_signed_sum_card (δ : ℝ) (X : Finset ℝ) (m n : ℕ) :
    (scalarCells δ (m • X-n • X)).card ≤
      (m+n+2)*(m • scalarCells δ X-n • scalarCells δ X).card := by
  classical
  have hc : (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card = m+n+2 := by
    rw [Int.card_Icc]
    omega
  calc
    _ ≤ ((m • scalarCells δ X-n • scalarCells δ X)+Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card :=
      Finset.card_le_card (scalar_signed_sum_cells_subset δ X m n)
    _ ≤ (m • scalarCells δ X-n • scalarCells δ X).card*
        (Finset.Icc (-(n : ℤ)-1) (m : ℤ)).card := Finset.card_add_le
    _ = _ := by rw [hc,Nat.mul_comm]

end Falconer

end OAI
