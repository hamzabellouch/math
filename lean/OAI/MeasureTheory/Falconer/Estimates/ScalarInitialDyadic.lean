import OAI.MeasureTheory.Falconer.Estimates.ScalarInitialChildren
import Mathlib.Data.Nat.Log

namespace OAI

/-! Dyadic branching counts with a retained close pair. This provides
 finite tags for the bottom-up scalar tree regularization. -/
namespace Falconer

 theorem scalar_initial_dyadic_children (E : Finset ℝ) (lo hi : ℕ)
    (hsize : 2050 ≤ E.card)
    (hsep : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → (1/2:ℝ)^hi ≤ |x-y|)
    (hdiam : ∀ x ∈ E, ∀ y ∈ E, |x-y| ≤ (1/2:ℝ)^lo) :
    ∃ F ⊆ E, ∃ k n : ℕ, 1 ≤ k ∧ F.card = 2^k ∧ E.card ≤ 2050*F.card ∧
      lo+3 < n ∧ n+6 ≤ hi ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → 8*(1/2:ℝ)^n < |x-y|) ∧
      ∃ x ∈ F, ∃ y ∈ F, x ≠ y ∧ |x-y| ≤ 16*(1/2:ℝ)^n := by
  classical
  obtain ⟨G,hGE,hGcard,hG2,n,hn0,hn1,hGs,x,hx,y,hy,hxy,hpair⟩ :=
    scalar_initial_children E lo hi hsize hsep hdiam
  let k := Nat.log 2 G.card
  have hk : 1 ≤ k := Nat.log_pos (by decide) hG2
  have hR2 : 2 ≤ 2^k := by
    calc
      2 = 2^1 := rfl
      _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hR : 2^k ≤ G.card := Nat.pow_log_le_self 2 (by omega)
  have hpG : ({x,y} : Finset ℝ) ⊆ G := by simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]; exact ⟨hx,hy⟩
  have hpc : ({x,y} : Finset ℝ).card = 2 := by simp [hxy]
  obtain ⟨F,hpF,hFG,hFc⟩ := Finset.exists_subsuperset_card_eq hpG (by rwa [hpc]) hR
  have hGc : G.card ≤ 2*(2^k) := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) G.card
    simpa only [k,pow_succ,Nat.mul_comm] using hh.le
  refine ⟨F,hFG.trans hGE,k,n,hk,hFc,?_,hn0,hn1,?_,x,?_,y,?_,hxy,hpair⟩
  · calc
      E.card ≤ 1025*G.card := hGcard
      _ ≤ 1025*(2*(2^k)) := Nat.mul_le_mul_left _ hGc
      _ = 2050*F.card := by rw [hFc]; ring
  · exact fun x hx y hy hxy => hGs x (hFG hx) y (hFG hy) hxy
  · exact hpF (by simp)
  · exact hpF (by simp)

end Falconer

end OAI
