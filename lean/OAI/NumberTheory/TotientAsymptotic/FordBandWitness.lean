import OAI.NumberTheory.TotientAsymptotic.FordBandNormality

namespace OAI

/-! All sieve hypotheses for the distinguished factor in an actual Ford band. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma band_factor_data {n : ℕ} {Z T V : ℝ} (hZ : 1 < Z) (hZT : Z < T)
    (hT : T ≤ largestPrimeFactor n) (hV : (largestPrimeFactor n:ℝ) ≤ V) :
    2 ≤ partBetween n Z V ∧ T ≤ largestPrimeFactor (partBetween n Z V) ∧
      partBelow n Z*partBetween n Z V=n := by
  have hn : 2 ≤ n := two_le_of_one_lt_largest (by exact_mod_cast hZ.trans (hZT.trans_le hT))
  have hZP := hZT.trans_le hT
  refine ⟨band_factor_ge_two hn hZP hV,?_,?_⟩
  · rwa [largestPrimeFactor_band hn hZP hV]
  · exact (partBelow_band_split n (hZP.le.trans hV)).trans
      (partBelow_all_of_largest_le (by omega) hV)

lemma ford_band_conditions {b k D r : ℕ} {y S : ℝ} {Y U : ℕ → ℝ} {t : ShiftedPair b}
    (hk : k ≤ b) (i : Fin k) (hi : i.val+1=k)
    (hy : 0 ≤ y) (hp : FordComparisonParameters b y S D r Y U)
    (h : FordComparisonConditions b y S D r Y U t) :
    CollisionBandConditions
      (partBelow (t.left (Fin.castLE hk i)-1) (Y k))
      (partBelow (t.right (Fin.castLE hk i)-1) (Y k))
      i y (U (k-1)) (Y k) (Y (k-1)) (fordBandCap k y S Y) (fordBand hk t Y) := by
  let j := Fin.castLE hk i
  have hj : j.val=k-1 := by dsimp [j]; omega
  have hk0 : 1 ≤ k := by omega
  obtain ⟨hnl,hnr,hne,hUl,hYl,hUr,hYr,_,_⟩ := h.2.1 j
  rw [hj] at hUl hYl hUr hYr
  have hgap := hp.2.2.2.2.1 (k-1) (Finset.mem_range.mpr (by omega : k-1 < b))
  have hkm : k-1+1=k := by omega
  rw [hkm] at hgap
  have hZ1 : 1 < Y k := (ford_scale_bounds hp).1.trans_le (ford_cutoff_ge_S hp hk)
  have hleft := band_factor_data hZ1 hgap.1 hUl hYl
  have hright := band_factor_data hZ1 hgap.1 hUr hYr
  let a := partBelow (t.left j-1) (Y k)
  let c := partBelow (t.right j-1) (Y k)
  let f := fordBand hk t Y
  have hal : a*f.1 i=t.left j-1 := hleft.2.2
  have hcr : c*f.2 i=t.right j-1 := hright.2.2
  have hlp : a*f.1 i+1=t.left j := by rw [hal]; exact Nat.sub_add_cancel (by have := hnl.1.two_le; omega)
  have hrp : c*f.2 i+1=t.right j := by rw [hcr]; exact Nat.sub_add_cancel (by have := hnr.1.two_le; omega)
  change CollisionBandConditions a c i y (U (k-1)) (Y k) (Y (k-1)) (fordBandCap k y S Y) f
  constructor
  · exact Finset.prod_pos (fun j _ => partBetween_pos _ _ _)
  · exact ford_band_product_eq hk hp h
  · exact hleft.1
  · exact hright.1
  · exact hleft.2.1
  · exact hright.2.1
  · rw [hlp]; exact hnl.1
  · rw [hrp]; exact hnr.1
  · rw [hlp,hrp]; exact hne
  · rw [hal]; exact ford_left_shift_le_y hy hp h j
  · rw [hcr]; exact ford_right_shift_le_y hy hp h j
  · exact ford_band_omega hk hk0 hp h
  · intro p hmem
    rw [ford_band_product hk hp h] at hmem
    exact partBetween_support _ _ _ hmem
  · exact ford_band_squarefree hk hp h

end TotientAsymptotic

end

end OAI
