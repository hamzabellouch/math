import OAI.Analysis.TriangularHilbert.FiniteVitali

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def intInterval (n : ℤ) (r : ℕ) : Finset ℤ := Finset.Icc (n-r) (n+r)

lemma mem_intInterval (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ n-(r:ℤ) ≤ m ∧ m ≤ n+r := Finset.mem_Icc

lemma center_mem_intInterval (n : ℤ) (r : ℕ) : n ∈ intInterval n r := by
  rw [mem_intInterval]; constructor <;> omega

lemma card_intInterval (n : ℤ) (r : ℕ) : (intInterval n r).card = 2*r+1 := by
  rw [intInterval,Int.card_Icc]
  have he : n+(r:ℤ)+1-(n-r) = ((2*r+1 : ℕ):ℤ) := by push_cast; ring
  rw [he,Int.toNat_natCast]

lemma interval_inter_center {a b : ℤ} {r s : ℕ}
    (hab : ((intInterval a r : Set ℤ) ∩ (intInterval b s : Set ℤ)).Nonempty)
    (hrs : r ≤ s) : a ∈ intInterval b (3*s) := by
  obtain ⟨m,hm,hm'⟩ := hab
  have hm1 := (mem_intInterval m a r).mp hm
  have hm2 := (mem_intInterval m b s).mp hm'
  rw [mem_intInterval]
  constructor <;> push_cast <;> omega

lemma int_intervals_weak (D s : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (r : ℤ → ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hav : ∀ n ∈ s, ρ * (2*(r n:ℝ)+1) ≤ ∑ m ∈ D ∩ intInterval n (r n), f m) :
    ρ * (s.card:ℝ) ≤ 3 * ∑ m ∈ D, f m := by
  classical
  obtain ⟨u,hu,hd,hcov⟩ := finite_disjoint_selection s
    (fun n => (intInterval n (r n) : Set ℤ)) (fun n => (r n : ℝ))
    (fun n _ => ⟨n,center_mem_intInterval n (r n)⟩)
  have hcover : s ⊆ u.biUnion (fun n => intInterval n (3*r n)) := by
    intro a ha
    obtain ⟨b,hb,hab,hrs⟩ := hcov a ha
    exact Finset.mem_biUnion.mpr ⟨b,hb,interval_inter_center hab (by exact_mod_cast hrs)⟩
  have hc : (s.card:ℝ) ≤ 3*∑ n ∈ u, (2*(r n:ℝ)+1) := by
    have h1 := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le : (u.biUnion (fun n => intInterval n (3*r n))).card ≤ _)
    have h2 : (∑ n ∈ u, (intInterval n (3*r n)).card) ≤ ∑ n ∈ u, 3*(2*r n+1) := by
      apply Finset.sum_le_sum
      intro n _
      rw [card_intInterval]
      omega
    have h3 : (s.card:ℝ) ≤ (∑ n ∈ u, 3*(2*r n+1):ℕ) := by exact_mod_cast h1.trans h2
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,Finset.mul_sum] using h3
  have hdis : (↑u : Set ℤ).PairwiseDisjoint (fun n => D ∩ intInterval n (r n)) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro m hm hm'
    exact Set.disjoint_left.mp (hd a ha b hb hab) (Finset.mem_inter.mp hm).2 (Finset.mem_inter.mp hm').2
  have hsubset : u.biUnion (fun n => D ∩ intInterval n (r n)) ⊆ D := by
    intro m hm
    obtain ⟨n,_,hn⟩ := Finset.mem_biUnion.mp hm
    exact (Finset.mem_inter.mp hn).1
  have hsum : (∑ n ∈ u, ∑ m ∈ D ∩ intInterval n (r n), f m) ≤ ∑ m ∈ D, f m := by
    rw [← Finset.sum_biUnion hdis]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m hm _ => hf m hm)
  calc
    _ ≤ ρ*(3*∑ n ∈ u, (2*(r n:ℝ)+1)) := mul_le_mul_of_nonneg_left hc hρ
    _ = 3*∑ n ∈ u, ρ*(2*(r n:ℝ)+1) := by rw [← Finset.mul_sum]; ring
    _ ≤ 3*∑ n ∈ u, ∑ m ∈ D ∩ intInterval n (r n), f m :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun n hn => hav n (hu hn))) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by norm_num)
end
end TriangularHilbert
end

end OAI
