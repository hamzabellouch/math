import OAI.MeasureTheory.Falconer.Recursion.ScalarBinaryBranch
import OAI.MeasureTheory.Falconer.Recursion.ScalarBranchGrowth

namespace OAI

/-! Iterating the actual binary switching construction. The final points
 remain in one fixed-fold sumset, while their number grows at every level. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_binary_growth {N k J : ℕ} (f : (Fin N → Bool) → ℝ)
    (A : Finset ℝ) (hf : ∀ w, f w ∈ A)
    (ε R ell b : ℕ → ℝ) (L : ℕ → ℕ) (hJ : 0 < J)
    (hε : ∀ n < N, 0 < ε n) (hb : ∀ n ≤ N, 0 < b n)
    (hlo : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      ell n ≤ |f (Function.update w n true)-f w|)
    (hhi : ∀ n : Fin N, ∀ w, ScalarBinaryTail n w →
      |f (Function.update w n true)-f w| ≤ R n)
    (hR : ∀ n < N, R n ≤ (L n:ℝ)*ε n)
    (hsize : ∀ n < N, (2*L n+1)*J ≤ k)
    (hmargin : ∀ n < N, b (n+1)+2*(J:ℝ)*ε n ≤ ell n)
    (hgap : ∀ n < N, b (n+1)+2*(J:ℝ)*R n ≤ b n) :
    ∃ E : Finset ℝ, E ⊆ k • A ∧ E.card = (J+1)^N ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ y → b N ≤ |x-y| := by
  let P : ℕ → (Fin k → Fin N → Bool) → Prop :=
    fun n c => ∀ i, ScalarBinaryTail n (c i)
  let root : Fin k → Fin N → Bool := fun _ _ => false
  have hroot : P 0 root := fun _ _ _ => rfl
  have hstep : ∀ n < N, ∀ c, P n c →
      ∃ F : Finset (Fin k → Fin N → Bool), F.card = J+1 ∧
        (∀ d ∈ F, P (n+1) d) ∧
        (∀ d ∈ F, |scalarBinarySum f d-scalarBinarySum f c| ≤ (J:ℝ)*R n) ∧
        (∀ d ∈ F, ∀ d' ∈ F, d ≠ d' → b (n+1) ≤ |scalarBinarySum f d-scalarBinarySum f d'|) := by
    intro n hn c hc
    let n' : Fin N := ⟨n,hn⟩
    obtain ⟨e,_,htail,hmotion,hsep⟩ := scalar_binary_branch f c n' hc (hε n hn)
      (hlo n') (hhi n') (L n) J hJ (hR n hn) (hsize n hn) (hmargin n hn)
    let child := fun j => scalarBinaryStep c n' ((Finset.range j).image e)
    have hinj : Set.InjOn child (Finset.range (J+1) : Set ℕ) := by
      intro i hi j hj hij
      by_contra hne
      have hs := hsep i (by have := Finset.mem_range.mp hi; omega)
        j (by have := Finset.mem_range.mp hj; omega) hne
      change b (n+1) ≤ |scalarBinarySum f (child i)-scalarBinarySum f (child j)| at hs
      rw [hij,sub_self,abs_zero] at hs
      exact (not_le_of_gt (hb (n+1) (by omega))) hs
    refine ⟨(Finset.range (J+1)).image child,?_,?_,?_,?_⟩
    · rw [Finset.card_image_of_injOn hinj,Finset.card_range]
    · intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      exact htail j (by have := Finset.mem_range.mp hj; omega)
    · intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hjJ : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have hk : 0 < k := (Nat.mul_pos (by omega) hJ).trans_le (hsize n hn)
      let i0 : Fin k := ⟨0,hk⟩
      have hRn : 0 ≤ R n := (abs_nonneg _).trans (hhi n' (c i0) (hc i0))
      exact (hmotion j hjJ).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hjJ) hRn)
    · intro d hd d' hd' hne
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd'
      exact hsep i (by have := Finset.mem_range.mp hi; omega)
        j (by have := Finset.mem_range.mp hj; omega) (fun hij => hne (congrArg child hij))
  obtain ⟨S,hcard,_,hsep⟩ := scalar_finite_branch_growth (scalarBinarySum f) P N (J+1)
    (fun n => (J:ℝ)*R n) b root hroot hb (by simpa only [mul_assoc] using hgap) hstep
  have hinj : Set.InjOn (scalarBinarySum f) (S : Set (Fin k → Fin N → Bool)) := by
    intro c hc d hd heq
    by_contra hne
    have hs := hsep c hc d hd hne
    rw [heq,sub_self,abs_zero] at hs
    exact (not_le_of_gt (hb N le_rfl)) hs
  refine ⟨S.image (scalarBinarySum f),?_,?_,?_⟩
  · intro x hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
    exact scalar_binary_sum_mem f A hf c
  · rw [Finset.card_image_of_injOn hinj,hcard]
  · intro x hx y hy hxy
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    exact hsep c hc d hd (fun hcd => hxy (congrArg (scalarBinarySum f) hcd))

end Falconer

end OAI
