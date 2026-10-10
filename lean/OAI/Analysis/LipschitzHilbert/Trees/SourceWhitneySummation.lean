import OAI.Analysis.LipschitzHilbert.Geometry.SourceWhitneyPacking
import OAI.Analysis.LipschitzHilbert.Trees.SourceShortDyadicBudget

namespace OAI

/-! Summation of the local short-tree bounds over the Whitney partition:
total small-cell length and the large-cell geometric tail. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

/-- Summing the far-strip decay over the large Whitney intervals costs
only an absolute factor, including all possible integer scales. -/
theorem large_whitney_ratio_sum {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0<L)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hW : ∀ p∈S, Whitney tiles x ell p.1 p.2)
    (hlarge : ∀ p∈S, L≤scale p.1) :
    (∑ p∈S, (L/scale p.1)^2) ≤ 18 := by
  classical
  let K := S.image Prod.fst
  have hmaps : ∀ p∈S, p.1∈K := fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hK (k) (hk : k∈K) : L≤scale k := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hk
    exact hlarge p hp
  have hrow (k) (hk : k∈K) :
      (∑ p∈S.filter (fun p => p.1=k), (L/scale p.1)^2) ≤ 9*(L/scale k)^2 := by
    let T := S.filter (fun p => p.1=k)
    have htW : ∀ p∈T, Whitney tiles x ell p.1 p.2 :=
      fun p hp => hW p (Finset.mem_filter.mp hp).1
    have htlevel : ∀ p∈T, p.1=k := fun _ hp => (Finset.mem_filter.mp hp).2
    have hsum : (∑ p∈T, scale p.1) = (T.card:ℝ)*scale k := by
      calc
        _ = ∑ _p∈T, scale k := Finset.sum_congr rfl (fun p hp => by rw [htlevel p hp])
        _ = _ := by simp
    have hbudget := finite_length_budget tiles x ell hL.le (scale_pos k).le hcenters T htW
      (fun p hp => le_of_eq (congrArg scale (htlevel p hp)))
    rw [hsum] at hbudget
    have hcard : (T.card:ℝ)≤9 := (mul_le_mul_iff_left₀ (scale_pos k)).mp (by
      nlinarith only [hbudget,hK k hk])
    calc
      _ = (T.card:ℝ)*(L/scale k)^2 := by
        calc
          _ = ∑ _p∈T, (L/scale k)^2 :=
            Finset.sum_congr rfl (fun p hp => by rw [htlevel p hp])
          _ = _ := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  calc
    _ = ∑ k∈K, ∑ p∈S.filter (fun p => p.1=k), (L/scale p.1)^2 :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ k∈K, 9*(L/scale k)^2 := Finset.sum_le_sum hrow
    _ = 9*∑ k∈K, (L/scale k)^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ 9*2 := mul_le_mul_of_nonneg_left (finite_large_scale_square_sum L hL K hK) (by norm_num)
    _ = _ := by norm_num

def shortWhitneyWeight (L r : ℝ) : ℝ := if r≤L then r else L*(L/r)^2

/-- The small-cell contribution and large-cell tail together have total
weight at most `27L`. -/
theorem short_whitney_weight_sum {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L : ℝ} (hL : 0<L)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hW : ∀ p∈S, Whitney tiles x ell p.1 p.2) :
    (∑ p∈S, shortWhitneyWeight L (scale p.1)) ≤ 27*L := by
  classical
  let small := S.filter (fun p => scale p.1≤L)
  let large := S.filter (fun p => ¬scale p.1≤L)
  have hs := small_length_budget tiles x ell hL.le hcenters small
    (fun p hp => hW p (Finset.mem_filter.mp hp).1)
    (fun _ hp => (Finset.mem_filter.mp hp).2)
  have hl := large_whitney_ratio_sum tiles x ell hL hcenters large
    (fun p hp => hW p (Finset.mem_filter.mp hp).1)
    (fun p hp => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hp).2))
  have heq : (∑ p∈S, shortWhitneyWeight L (scale p.1)) =
      (∑ p∈small, scale p.1)+L*(∑ p∈large, (L/scale p.1)^2) := by
    simp only [shortWhitneyWeight,Finset.sum_ite,small,large,Finset.mul_sum]
  rw [heq]
  nlinarith only [hs,hl,hL]

/-- Local strip estimates with the manuscript's two decay regimes sum to
the required top-area bound. -/
theorem sum_short_strip_bounds {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) {c L W A : ℝ} (hL : 0<L) (hW : 0≤W) (hA : 0≤A)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2) (S : Finset (ℤ×ℤ))
    (hWhitney : ∀ p∈S, Whitney tiles x ell p.1 p.2) (mass : ℤ×ℤ → ℝ)
    (hsmall : ∀ p∈S, scale p.1≤L → mass p≤A*W*scale p.1)
    (hlarge : ∀ p∈S, L<scale p.1 → mass p≤A*W*L*(L/scale p.1)^2) :
    (∑ p∈S, mass p) ≤ 27*A*L*W := by
  have hpoint (p) (hp : p∈S) : mass p≤(A*W)*shortWhitneyWeight L (scale p.1) := by
    by_cases h : scale p.1≤L
    · simpa only [shortWhitneyWeight,ite_eq_left h] using hsmall p hp h
    · have hb := hlarge p hp (lt_of_not_ge h)
      simpa only [shortWhitneyWeight,ite_eq_right h,mul_assoc] using hb
  calc
    _ ≤ ∑ p∈S, (A*W)*shortWhitneyWeight L (scale p.1) := Finset.sum_le_sum hpoint
    _ = (A*W)*∑ p∈S, shortWhitneyWeight L (scale p.1) := (Finset.mul_sum _ _ _).symm
    _ ≤ (A*W)*(27*L) := mul_le_mul_of_nonneg_left
      (short_whitney_weight_sum tiles x ell hL hcenters S hWhitney) (mul_nonneg hA hW)
    _ = _ := by ring

end LipschitzHilbert.SourceWhitney

end

end OAI
