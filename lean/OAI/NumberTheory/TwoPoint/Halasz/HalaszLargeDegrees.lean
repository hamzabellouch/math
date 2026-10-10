import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedWeights
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDegreeSaving

namespace OAI

/-! The block of middle Taylor degrees supplying a quadratic total saving. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

def halaszLargeDegreeMap (m : ℕ) (hm : 1≤m) (i : Fin (2*m+1)) : Fin (12*m) :=
  ⟨8*m-1+i.val,by omega⟩

lemma halasz_large_degree_map_injective {m : ℕ} (hm : 1≤m) :
    Function.Injective (halaszLargeDegreeMap m hm) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  dsimp only [halaszLargeDegreeMap] at hv
  omega

def halaszLargeDegrees (m : ℕ) (hm : 1≤m) : Finset (Fin (12*m)) :=
  univ.image (halaszLargeDegreeMap m hm)

lemma halasz_large_degrees_card {m : ℕ} (hm : 1≤m) :
    (halaszLargeDegrees m hm).card=2*m+1 := by
  rw [halaszLargeDegrees,card_image_of_injective _ (halasz_large_degree_map_injective hm)]
  simp

lemma halasz_large_degrees_range {m : ℕ} (hm : 1≤m) {j : Fin (12*m)}
    (hj : j∈halaszLargeDegrees m hm) : 8*m≤j.val+1 ∧ j.val+1≤10*m := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp hj
  dsimp only [halaszLargeDegreeMap]
  have hi := i.isLt
  omega

theorem halasz_large_degree_weight_product {m r M : ℕ} (hm : 8≤m)
    (hr : 1≤r) (hM : 1≤M) {t z N lam : ℝ} (hN : 1≤N)
    (hz : N≤z) (hzhi : z≤2*N) (ht : |t|=N^lam)
    (hscale : N^(1/4:ℝ)≤2*(M:ℝ))
    (hlo : 6*(m:ℝ)-6≤lam) (hhi : lam≤6*m) :
    (∏ j : Fin (12*m),halaszNormalizedWeight r M (halaszLogCoefficient t z) j)≤
      (halaszLogWeightCost (12*m) r)^(12*m)*N^(-((2*m+1:ℕ):ℝ)*((m:ℝ)-6)) := by
  have hm1 : 1≤m := by omega
  have hdeg (j : Fin (12*m)) (hj : j∈halaszLargeDegrees m hm1) :
      (m:ℝ)-6≤min (((j.val:ℝ)+1)/4)
        (min (((j.val:ℝ)+1)-lam) (lam-((j.val:ℝ)+1)/2)) := by
    have hj' := halasz_large_degrees_range hm1 hj
    apply halasz_large_degree_saving (by exact_mod_cast hm) hlo hhi
    · exact_mod_cast hj'.1
    · exact_mod_cast hj'.2
  have hh := halasz_log_selected_weight_product hr hM hN hz hzhi ht hscale
    (halaszLargeDegrees m hm1)
    (η := (m:ℝ)-6)
    (fun j hj => by have hd := (le_min_iff.mp (hdeg j hj)).1; linarith)
    (fun j hj => (le_min_iff.mp (le_min_iff.mp (hdeg j hj)).2).1)
    (fun j hj => by have hd := (le_min_iff.mp (le_min_iff.mp (hdeg j hj)).2).2; linarith)
  simpa only [halasz_large_degrees_card] using hh

end TwoPointCorrelations

end OAI
