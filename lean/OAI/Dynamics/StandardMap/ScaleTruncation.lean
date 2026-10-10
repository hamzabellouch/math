import OAI.Dynamics.StandardMap.ProductDistances

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma min_tree_chain {a b c x y e : ℝ} (he : 0≤e)
    (hx : min a b-e≤x) (hy : min x c-e≤y) : min a (min b c)-2*e≤y := by
  have ha : min a (min b c)≤a := min_le_left _ _
  have hb : min a (min b c)≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hc : min a (min b c)≤c := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : min a (min b c)-e≤x := by have := le_min ha hb; linarith
  have h2 : min a (min b c)-e≤ min x c := le_min h1 (by linarith)
  linarith
lemma productDistance_cut_wings (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let D := (n:ℝ)-min (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
    (s:ℝ)-D≤productDistance k z i (i-(s:ℤ)) ∧
      (s:ℝ)-D≤productDistance k z i (i+(s:ℤ)) := by
  dsimp only
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  have hL := productDistance_triangle k hk z i (i-(s:ℤ)) (i-(n:ℤ))
  have hR := productDistance_triangle k hk z i (i+(s:ℤ)) (i+(n:ℤ))
  have bL := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
  have bR := productDistance_le k hk z (i+(s:ℤ)) (i+(n:ℤ))
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast] at bL bR
  rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at bL
  rw [show (i:ℝ)+n-((i:ℝ)+s)=(n:ℝ)-s by ring,abs_of_nonneg (by linarith)] at bR
  have hminL := min_le_left (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  have hminR := min_le_right (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  constructor <;> linarith
lemma productDistance_truncation (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let g := productDistance k z
    let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
    let loss := g i (i-(n:ℤ))+g i (i+(n:ℤ))-g (i-(n:ℤ)) (i+(n:ℤ))
    min loss (2*(s:ℝ)-2*D)-6≤g i (i-(s:ℤ))+g i (i+(s:ℤ))-g (i-(s:ℤ)) (i+(s:ℤ)) := by
  let g := productDistance k z
  let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
  let B := fun u v => g i u+g i v-g u v
  change min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D)-6≤B (i-(s:ℤ)) (i+(s:ℤ))
  have ht (u v w : ℤ) : min (B u v) (B v w)-3≤B u w := productDistance_tree k hk z i u v w
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  obtain ⟨hcL,hcR⟩ := productDistance_cut_wings k hk z i n s hsn
  have hwL : (n:ℝ)-D≤g i (i-(n:ℤ)) := by
    dsimp only [D]; have := min_le_left (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hwR : (n:ℝ)-D≤g i (i+(n:ℤ)) := by
    dsimp only [D]; have := min_le_right (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hbL : g (i-(s:ℤ)) (i-(n:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
    simp only [Int.cast_sub,Int.cast_natCast] at hh
    rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hbR : g (i+(n:ℤ)) (i+(s:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i+(n:ℤ)) (i+(s:ℤ))
    simp only [Int.cast_add,Int.cast_natCast] at hh
    rw [show (i:ℝ)+s-((i:ℝ)+n)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hBL : 2*(s:ℝ)-2*D≤B (i-(s:ℤ)) (i-(n:ℤ)) := by
    change (s:ℝ)-D≤g i (i-(s:ℤ)) at hcL
    dsimp only [B]; linarith
  have hBR : 2*(s:ℝ)-2*D≤B (i+(n:ℤ)) (i+(s:ℤ)) := by
    change (s:ℝ)-D≤g i (i+(s:ℤ)) at hcR
    dsimp only [B]; linarith
  have hh := min_tree_chain (by norm_num : (0:ℝ)≤3)
    (ht (i-(s:ℤ)) (i-(n:ℤ)) (i+(n:ℤ)))
    (ht (i-(s:ℤ)) (i+(n:ℤ)) (i+(s:ℤ)))
  have hmin : min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D) ≤
      min (B (i-(s:ℤ)) (i-(n:ℤ))) (min (B (i-(n:ℤ)) (i+(n:ℤ))) (B (i+(n:ℤ)) (i+(s:ℤ)))) := by
    exact le_min ((min_le_right _ _).trans hBL)
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hBR))
  linarith
end StandardMapEntropy

end OAI
