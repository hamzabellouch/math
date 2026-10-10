import OAI.Combinatorics.PolynomialVacuum.Algebra.BraidEndomorphisms

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

noncomputable def braidTrain (c : ℂ) (X : ℕ → ℂ) (k : ℕ) :
    ℕ → Module.End ℂ (SpinTensor ℕ ℂ)
  | 0 => 1
  | m+1 => braidTrain c X (k+1) m * siteR k c (X k)

def swapSite {α : Type*} (j : ℕ) (X : ℕ → α) : ℕ → α := X ∘ Equiv.swap j (j+1)

@[simp] theorem swapSite_left {α : Type*} (j : ℕ) (X : ℕ → α) : swapSite j X j=X (j+1) := by
  simp [swapSite]
@[simp] theorem swapSite_right {α : Type*} (j : ℕ) (X : ℕ → α) : swapSite j X (j+1)=X j := by
  simp [swapSite]
theorem swapSite_other {α : Type*} {i j : ℕ} (hij : i≠j) (hij' : i≠j+1) (X : ℕ → α) :
    swapSite j X i=X i := by simp [swapSite,Equiv.swap_apply_of_ne_of_ne hij hij']

theorem braidTrain_congr (c : ℂ) {X Y : ℕ → ℂ} (k m : ℕ)
    (h : ∀ i, k ≤ i → i < k+m → X i=Y i) : braidTrain c X k m=braidTrain c Y k m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih =>
    simp only [braidTrain]
    rw [ih (k+1) (fun i hi hi' => h i (by omega) (by omega)),h k (by omega) (by omega)]

theorem braidTrain_far_left (c : ℂ) (X : ℕ → ℂ) (j k m : ℕ) (hjk : j+1 < k) (x y : ℂ) :
    siteR j x y*braidTrain c X k m=braidTrain c X k m*siteR j x y := by
  induction m generalizing k with
  | zero => simp [braidTrain]
  | succ m ih =>
    simp only [braidTrain]
    rw [← mul_assoc,ih (k+1) (by omega),mul_assoc,
      siteR_far_comm (Or.inl hjk),← mul_assoc]

 

theorem braidTrain_spectator_swap (c : ℂ) (X : ℕ → ℂ) (k d m : ℕ) :
    siteR (k+d) (X (k+d)) (X (k+d+1)) * braidTrain c X k (d+(m+2)) =
      braidTrain c (swapSite (k+d) X) k (d+(m+2)) *
        siteR (k+d+1) (X (k+d)) (X (k+d+1)) := by
  induction d generalizing k with
  | zero =>
    simp only [Nat.add_zero,Nat.zero_add]
    have hc := braidTrain_far_left c X k (k+1+1) m (by omega) (X k) (X (k+1))
    have ht : braidTrain c (swapSite k X) (k+1+1) m=braidTrain c X (k+1+1) m := by
      apply braidTrain_congr
      intro i hi hi'
      exact swapSite_other (by omega) (by omega) X
    simp only [braidTrain,swapSite_left,swapSite_right,ht]
    calc
      siteR k (X k) (X (k+1)) *
        (braidTrain c X (k+1+1) m * siteR (k+1) c (X (k+1)) * siteR k c (X k)) =
        braidTrain c X (k+1+1) m *
          (siteR k (X k) (X (k+1))*siteR (k+1) c (X (k+1))*siteR k c (X k)) := by
            rw [← mul_assoc,← mul_assoc,hc]; simp only [mul_assoc]
      _ = _ := by rw [siteR_yang_baxter]; simp only [mul_assoc]
  | succ d ih =>
    have hp : k+(d+1)=(k+1)+d := by omega
    have hl : (d+1)+(m+2)=(d+(m+2))+1 := by omega
    have ho : swapSite (k+(d+1)) X k=X k := swapSite_other (by omega) (by omega) X
    rw [hl,braidTrain,braidTrain]
    simp only [ho]
    calc
      siteR (k+(d+1)) (X (k+(d+1))) (X (k+(d+1)+1)) *
          (braidTrain c X (k+1) (d+(m+2))*siteR k c (X k)) =
        (braidTrain c (swapSite (k+(d+1)) X) (k+1) (d+(m+2))*
          siteR (k+(d+1)+1) (X (k+(d+1))) (X (k+(d+1)+1)))*siteR k c (X k) := by
            rw [← mul_assoc,hp,ih (k+1)]
      _ = _ := by
        rw [mul_assoc,siteR_far_comm (Or.inr (by omega)),← mul_assoc]

end PolynomialVacuumAlgebra

end OAI
