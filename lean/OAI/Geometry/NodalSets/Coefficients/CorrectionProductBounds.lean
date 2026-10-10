import OAI.Geometry.NodalSets.Elliptic.WeightedDivergenceBounds

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma correction_product_bound (f v : Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v) (x : Yau.Jets.Coord)
    (r b : ℕ) {N A B H : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 < H)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(137*i+128)*H⁻¹)
    (hvb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i v x‖ ≤ B*N^(i+b)*H) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*v y) x‖ ≤ (2:ℝ)^r*A*B*N^(137*r+128+b) := by
  have h := scaled_frequency_product f v hf hv x r 137 128 b (by linarith) hA hB
    (by positivity) hH.le hfb (fun i hi ↦ (hvb i hi).trans (by gcongr; omega))
  simpa [inv_mul_cancel₀ hH.ne'] using h

theorem compact_multiplier_frequency_bound (q : Yau.Jets.Coord → ℝ) (hq : ContDiff ℝ ∞ q)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (v : Yau.Jets.Coord → ℝ), ContDiff ℝ ∞ v →
      ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B → ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i, i ≤ r → ‖iteratedFDeriv ℝ i v x‖ ≤ B*N^(137*i+a)) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (fun y ↦ q y*v y) x‖ ≤ C*B*N^(137*i+a) := by
  obtain ⟨G,hG,hgb⟩ := compact_real_derivative_bound q hq hQ r
  refine ⟨(2:ℝ)^r*G,by positivity,?_⟩
  intro v hv N B hN hB a x hx hb i hi
  have h := scaled_frequency_product q v hq hv x i 137 0 a (N := N) (by linarith) hG.le hB
    (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun j hj ↦ (hgb j (by omega) x hx).trans (by
      have hp : 1 ≤ N^(137*j+0) := one_le_pow₀ hN
      simpa using le_mul_of_one_le_right hG.le hp))
    (fun j hj ↦ by simpa using hb j (by omega))
  simp only [Nat.add_zero,mul_one] at h
  exact h.trans (by gcongr; norm_num)

theorem weighted_divergence_finite_frequency_bound (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (V : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) → ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B →
      ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i j, j ≤ r+1 → ‖iteratedFDeriv ℝ j (fun y ↦ V y i) x‖ ≤ B*N^(137*j+a)) →
      ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i (Yau.weightedDiv gamma V) x‖ ≤ C*B*N^(137*i+a+137) := by
  have hb (i : Fin (r+1)) := weighted_divergence_frequency_bound gamma hg hgn hQ i.val
  choose c hc hbound using hb
  let C : ℝ := 1+∑ i, c i
  have hc0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg (fun i _ ↦ (hc i).le)
  refine ⟨C,by dsimp [C]; linarith,?_⟩
  intro V hV N B hN hB a x hx hb i hi
  have h := hbound ⟨i,by omega⟩ V hV N B hN hB a x hx (fun l j hj ↦ hb l j (by omega))
  have hsum := Finset.single_le_sum (fun j _ ↦ (hc j).le)
    (Finset.mem_univ (⟨i,by omega⟩ : Fin (r+1)))
  have hci : c ⟨i,by omega⟩ ≤ C := by dsimp [C]; linarith
  exact h.trans (by gcongr)

end
end Yau.Target

end OAI
