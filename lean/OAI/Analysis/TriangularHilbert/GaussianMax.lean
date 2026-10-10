import OAI.Analysis.TriangularHilbert.FiniteAbel

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma intMax_strong (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) :
    (∑ n ∈ s, intMax D f n * Real.sqrt (intMax D f n)) ≤
      18*Real.sqrt 2 * ∑ m ∈ D, f m*Real.sqrt (f m) := by
  choose r hr using intMax_attained D f
  apply int_intervals_strong D s f (intMax D f) hf (fun n _ => intMax_nonneg D f hf n) r
  intro n _
  rw [hr n,intAverage]
  exact le_of_eq (div_mul_cancel₀ _ (by positivity))

lemma intInterval_filter (n : ℤ) (N r : ℕ) (hr : r ≤ N) :
    (intInterval n N).filter (fun m => (m-n).natAbs ≤ r) = intInterval n r := by
  ext m
  simp only [Finset.mem_filter,mem_intInterval_iff_dist]
  exact ⟨And.right,fun h => ⟨h.trans hr,h⟩⟩

lemma intInterval_sum_fin (n : ℤ) (N : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ intInterval n N, f m) = ∑ i : Fin (2*N+1), f (n-(N:ℤ)+(i:ℕ)) := by
  symm
  apply Finset.sum_bij (fun (i : Fin (2*N+1)) _ => n-(N:ℤ)+(i:ℕ))
  · intro i _
    rw [mem_intInterval]
    have hi := i.isLt
    constructor <;> omega
  · intro i _ j _ he
    apply Fin.ext
    omega
  · intro m hm
    rw [mem_intInterval] at hm
    refine ⟨⟨(m-(n-(N:ℤ))).toNat,by omega⟩,Finset.mem_univ _,?_⟩
    dsimp
    omega
  · intro i _
    rfl

lemma intInterval_weighted_le (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) (hdec : ∀ r, g (r+1) ≤ g r) :
    (∑ m ∈ D, f m*g (m-n).natAbs) ≤
      intMax D f n * ∑ m ∈ intInterval n (supportRadius D n), g (m-n).natAbs := by
  classical
  let N := supportRadius D n
  have hD : D ⊆ intInterval n N := by
    intro m hm
    rw [mem_intInterval_iff_dist]
    exact (Finset.le_sup (f := fun k : ℤ => (k-n).natAbs) hm)
  have he : (∑ m ∈ D, f m*g (m-n).natAbs) =
      ∑ m ∈ intInterval n N, (if m ∈ D then f m else 0)*g (m-n).natAbs := by
    simp only [ite_mul,zero_mul,Finset.sum_ite,Finset.sum_const_zero,add_zero]
    congr 1
    ext m
    simp only [Finset.mem_filter]
    exact ⟨fun hm => ⟨hD hm,hm⟩,And.right⟩
  rw [he]
  have hw := weighted_prefix_le (intInterval n N) (fun m => (m-n).natAbs)
    (fun m => if m ∈ D then f m else 0) (fun _ => intMax D f n) g N
    (fun m hm => (mem_intInterval_iff_dist m n N).mp hm) (hg N) (fun r _ => hdec r) ?_
  · simpa only [← Finset.mul_sum] using hw
  · intro r hr
    rw [intInterval_filter n N r hr]
    have he' : (∑ m ∈ intInterval n r, if m ∈ D then f m else 0) = ∑ m ∈ D ∩ intInterval n r, f m := by
      rw [Finset.sum_ite,Finset.sum_const_zero,add_zero]
      congr 1
      ext m
      simp only [Finset.mem_filter,Finset.mem_inter,and_comm]
    rw [he',Finset.sum_const,card_intInterval,nsmul_eq_mul]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,mul_comm] using sum_interval_le_intMax D f hf n r
end
end TriangularHilbert
end

end OAI
