import OAI.Analysis.TriangularHilbert.IntStrong

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

lemma mem_intInterval_iff_dist (m n : ℤ) (r : ℕ) :
    m ∈ intInterval n r ↔ (m-n).natAbs ≤ r := by
  rw [mem_intInterval]
  have he : (m-n).natAbs ≤ r ↔ |m-n| ≤ (r:ℤ) := by
    rw [← Int.natCast_natAbs]
    omega
  rw [he,abs_le]
  constructor <;> intro h <;> constructor <;> omega

def supportRadius (D : Finset ℤ) (n : ℤ) : ℕ := D.sup (fun m => (m-n).natAbs)

def intAverage (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) (r : ℕ) : ℝ :=
  (∑ m ∈ D ∩ intInterval n r, f m)/(2*(r:ℝ)+1)

lemma intAverage_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) (r : ℕ) :
    0 ≤ intAverage D f n r := by
  exact div_nonneg (Finset.sum_nonneg (fun m hm => hf m (Finset.mem_inter.mp hm).1)) (by positivity)

lemma inter_intInterval_of_supportRadius_le (D : Finset ℤ) (n : ℤ) {r : ℕ}
    (hr : supportRadius D n ≤ r) : D ∩ intInterval n r = D := by
  apply Finset.inter_eq_left.mpr
  intro m hm
  rw [mem_intInterval_iff_dist]
  exact (Finset.le_sup hm).trans hr

def intMax (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  (Finset.range (supportRadius D n+1)).sup' (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)

lemma intAverage_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : intAverage D f n r ≤ intMax D f n := by
  by_cases hr : r ≤ supportRadius D n
  · exact Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hr))
  · have hb : supportRadius D n ≤ r := le_of_lt (lt_of_not_ge hr)
    have hm : intAverage D f n r ≤ intAverage D f n (supportRadius D n) := by
      unfold intAverage
      rw [inter_intInterval_of_supportRadius_le D n hb,
        inter_intInterval_of_supportRadius_le D n le_rfl]
      apply div_le_div_of_nonneg_left (Finset.sum_nonneg hf) (by positivity)
      exact_mod_cast (by omega : 2*supportRadius D n+1 ≤ 2*r+1)
    exact hm.trans (Finset.le_sup' _ (Finset.mem_range.mpr (Nat.lt_succ_self _)))

lemma intMax_nonneg (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m) (n : ℤ) :
    0 ≤ intMax D f n := (intAverage_nonneg D f hf n 0).trans (intAverage_le_intMax D f hf n 0)

lemma intMax_attained (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) :
    ∃ r : ℕ, intMax D f n = intAverage D f n r := by
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_sup'
    (s := Finset.range (supportRadius D n+1)) (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)
  exact ⟨r,hr⟩

lemma sum_interval_le_intMax (D : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ m ∈ D, 0 ≤ f m)
    (n : ℤ) (r : ℕ) : (∑ m ∈ D ∩ intInterval n r, f m) ≤ intMax D f n*(2*(r:ℝ)+1) := by
  exact (div_le_iff₀ (by positivity : 0 < 2*(r:ℝ)+1)).mp (intAverage_le_intMax D f hf n r)
end
end TriangularHilbert
end

end OAI
