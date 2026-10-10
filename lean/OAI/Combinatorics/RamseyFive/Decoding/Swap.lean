import Mathlib

namespace OAI

namespace SharpRamseyFive.RepresentativeAverage
open scoped BigOperators Classical
variable {B A : Type*} [Fintype B] [Fintype A]

noncomputable def swapAt (b : B) : ((B → A) × A) ≃ ((B → A) × A) :=
  Function.Involutive.toPerm (fun z => (Function.update z.1 b z.2,z.1 b)) (by
    intro z
    apply Prod.ext
    · funext c
      by_cases h : c=b
      · subst c
        simp
      · simp [Function.update_of_ne h]
    · simp)

theorem selected_sum (f : (B → A) → B → A → ℝ)
    (hown : ∀ s b a i,f (Function.update s b a) b i=f s b i) :
    (Fintype.card A:ℝ)*(∑s,∑b,f s b (s b))=∑s,∑b,∑a,f s b a := by
  have hb (b : B) : (∑s : B → A,∑_a : A,f s b (s b))=∑s : B → A,∑a : A,f s b a := by
    have hh := Fintype.sum_equiv (swapAt (A := A) b)
      (fun z => f z.1 b (z.1 b)) (fun z => f z.1 b z.2) (by
        intro z
        simp only [swapAt,Function.Involutive.toPerm,Equiv.coe_fn_mk]
        exact (hown z.1 b z.2 (z.1 b)).symm)
    simpa only [Fintype.sum_prod_type] using hh
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑b,∑s : B → A,∑_a : A,f s b (s b) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [Finset.sum_comm]
    _ = ∑b,∑s : B → A,∑a : A,f s b a := Finset.sum_congr rfl fun b _ => hb b
    _ = _ := Finset.sum_comm

theorem all_sum_le_twice_unselected (f : (B → A) → B → A → ℝ)
    (hf : ∀ s b a,0≤f s b a)
    (hown : ∀ s b a i,f (Function.update s b a) b i=f s b i)
    (hsize : 2≤Fintype.card A) :
    (∑s,∑b,∑a,f s b a) ≤ 2*(∑s,∑b,∑a∈Finset.univ.erase (s b),f s b a) := by
  have hs := selected_sum f hown
  have hsplit : (∑s,∑b,∑a,f s b a)=
      (∑s,∑b,f s b (s b))+(∑s,∑b,∑a∈Finset.univ.erase (s b),f s b a) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.add_sum_erase Finset.univ (f s b) (Finset.mem_univ (s b))).symm
  have hsel : 0≤∑s,∑b,f s b (s b) := by
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun b _ => hf s b (s b)
  have hsizeR : (2:ℝ)≤Fintype.card A := by exact_mod_cast hsize
  nlinarith [mul_le_mul_of_nonneg_right hsizeR hsel]

end SharpRamseyFive.RepresentativeAverage

end OAI
