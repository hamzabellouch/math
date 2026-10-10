import OAI.Analysis.FreeEntropy.MatrixSpectralMoments

namespace OAI

noncomputable section
open Finset
namespace FiniteEntropySeparation
variable {p d : ℕ}
 def badSpectrum (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) : Finset (Fin d) :=
    univ.filter (fun j => ∀l,δ < |x j-y l|)
 def clusterLabel [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) (j : Fin d) : Fin p :=
    if h : ∃l,|x j-y l|≤δ then h.choose else 0
 theorem clusterLabel_close [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ) (j : Fin d)
    (hj : j∉badSpectrum y δ x) : |x j-y (clusterLabel y δ x j)|≤δ := by
  have he : ∃l,|x j-y l|≤δ := by simpa [badSpectrum,not_forall,not_lt] using hj
  simp only [clusterLabel,dite_eq_left he]
  exact he.choose_spec
 theorem clusterLabel_separated [NeZero p] (y : Fin p → ℝ) (δ Δ : ℝ) (x : Fin d → ℝ)
    (hy : ∀i j,i≠j → Δ≤|y i-y j|) (hδ : δ≤Δ/4)
    {j k : Fin d} (hj : j∉badSpectrum y δ x) (hk : k∉badSpectrum y δ x)
    (hjk : clusterLabel y δ x j≠clusterLabel y δ x k) : Δ/2≤|x j-x k| := by
  have hj' := clusterLabel_close y δ x j hj
  have hk' := clusterLabel_close y δ x k hk
  have hy' := hy _ _ hjk
  have ht : |y (clusterLabel y δ x j)-y (clusterLabel y δ x k)|≤
      |x j-y (clusterLabel y δ x j)|+|x j-x k|+|x k-y (clusterLabel y δ x k)| := by
    calc
      _ = |-(x j-y (clusterLabel y δ x j))+(x j-x k)+(x k-y (clusterLabel y δ x k))| := by congr 1; ring
      _ ≤ |-(x j-y (clusterLabel y δ x j))|+|x j-x k|+|x k-y (clusterLabel y δ x k)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by rw [abs_neg]
  linarith
 theorem badSpectrum_product_bound (y : Fin p → ℝ) {δ : ℝ} (hδ : 0≤δ) (x : Fin d → ℝ) :
    ((badSpectrum y δ x).card:ℝ)*δ^(2*p) ≤ ∑j : Fin d,(∏l : Fin p,(x j-y l))^2 := by
  have hb j (hj : j∈badSpectrum y δ x) : δ^(2*p)≤(∏l : Fin p,(x j-y l))^2 := by
    have hh : δ^p≤|∏l : Fin p,(x j-y l)| := by
      rw [abs_prod]
      have hp := prod_le_prod₀ (fun _ (_ : _∈(univ:Finset (Fin p))) => hδ)
        (fun l (_ : l∈(univ:Finset (Fin p))) => ((mem_filter.mp hj).2 l).le)
      simpa using hp
    have := pow_le_pow_left₀ (pow_nonneg hδ p) hh 2
    simpa [← pow_mul,sq_abs,Nat.mul_comm] using this
  calc
    _ = ∑j∈badSpectrum y δ x,δ^(2*p) := by simp
    _ ≤ ∑j∈badSpectrum y δ x,(∏l : Fin p,(x j-y l))^2 := sum_le_sum hb
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
 theorem clusterLabel_rank_bound [NeZero p] (y : Fin p → ℝ) (δ : ℝ) (x : Fin d → ℝ)
    (q : Fin p → ℝ → ℝ)
    (hq : ∀l r,|r-y l|≤δ → (3:ℝ)/4≤q l r^2)
    (hm : ∀l,(∑j : Fin d,q l (x j)^2)≤9*(d:ℝ)/(8*p))
    (hb : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/(2*p)) (l : Fin p) :
    (p:ℝ)*((univ.filter (fun j => clusterLabel y δ x j=l)).card:ℝ)≤2*d := by
  classical
  have hp : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  let S := univ.filter (fun j => clusterLabel y δ x j=l)
  let B := badSpectrum y δ x
  have hgood : ((S\B).card:ℝ)*(3/4:ℝ)≤∑j : Fin d,q l (x j)^2 := by
    calc
      _ = ∑j∈S\B,(3/4:ℝ) := by simp
      _ ≤ ∑j∈S\B,q l (x j)^2 := by
        apply sum_le_sum
        intro j hj
        have he : clusterLabel y δ x j=l := (mem_filter.mp (mem_sdiff.mp hj).1).2
        have hh := clusterLabel_close y δ x j (mem_sdiff.mp hj).2
        rw [he] at hh
        exact hq l (x j) hh
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hcard : (S.card:ℝ)≤((S\B).card:ℝ)+(B.card:ℝ) := by
    exact_mod_cast (card_le_card (show S⊆(S\B)∪B by intro j hj; by_cases h:j∈B <;> simp [hj,h])).trans (card_union_le _ _)
  have hgood' := hgood.trans (hm l)
  have hbad : (p:ℝ)*(B.card:ℝ)≤(d:ℝ)/2 := by
    dsimp [B]
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<2*p)).mp hb
    nlinarith
  have hgood'' : (p:ℝ)*((S\B).card:ℝ)≤3*(d:ℝ)/2 := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ)<8*p)).mp hgood'
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hcard hp.le
  change (p:ℝ)*(S.card:ℝ)≤2*d
  nlinarith
end FiniteEntropySeparation

end

end OAI
