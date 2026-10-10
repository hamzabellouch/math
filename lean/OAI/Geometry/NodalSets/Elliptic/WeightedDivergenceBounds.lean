import OAI.Geometry.NodalSets.Elliptic.LocalFrequencyLeibniz
import OAI.Geometry.NodalSets.Elliptic.RoundDenominatorDerivatives

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma scaled_frequency_product (f g : Yau.Jets.Coord → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : Yau.Jets.Coord)
    (r s a b : ℕ) {N A B H K : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hH : 0 ≤ H) (hK : 0 ≤ K)
    (hfb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i f x‖ ≤ A*N^(s*i+a)*H)
    (hgb : ∀ i, i ≤ r → ‖iteratedFDeriv ℝ i g x‖ ≤ B*N^(s*i+b)*K) :
    ‖iteratedFDeriv ℝ r (fun y ↦ f y*g y) x‖ ≤
      (2:ℝ)^r*A*B*N^(s*r+a+b)*(H*K) :=
  scaled_frequency_product_on f g isOpen_univ hf.contDiffOn hg.contDiffOn x (mem_univ x)
    r s a b hN hA hB hH hK hfb hgb

theorem weighted_divergence_frequency_bound (gamma : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) (r : ℕ) :
    ∃ C > 0, ∀ (V : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) → ∀ (N B : ℝ), 1 ≤ N → 0 ≤ B →
      ∀ (a : ℕ) (x : Yau.Jets.Coord), x ∈ Q →
      (∀ i j, j ≤ r+1 → ‖iteratedFDeriv ℝ j (fun y ↦ V y i) x‖ ≤ B*N^(137*j+a)) →
      ‖iteratedFDeriv ℝ r (Yau.weightedDiv gamma V) x‖ ≤ C*B*N^(137*r+a+137) := by
  obtain ⟨G,hG,hgb⟩ := compact_real_derivative_bound gamma hg hQ (r+1)
  obtain ⟨I,hI,hib⟩ := compact_real_derivative_bound (fun x ↦ (gamma x)⁻¹) (hg.inv hgn) hQ r
  refine ⟨(2:ℝ)^r*I*(4*((2:ℝ)^(r+1)*G)),by positivity,?_⟩
  intro V hV N B hN hB a x hx hv
  have hN0 : 0 ≤ N := by linarith
  let W : Fin 4 → Yau.Jets.Coord → ℝ := fun i y ↦ gamma y*V y i
  have hW (i : Fin 4) : ContDiff ℝ ∞ (W i) := hg.mul (hV i)
  have hw (i : Fin 4) (j : ℕ) (hj : j ≤ r+1) :
      ‖iteratedFDeriv ℝ j (W i) x‖ ≤ ((2:ℝ)^(r+1)*G*B)*N^(137*j+a) := by
    have h := scaled_frequency_product gamma (fun y ↦ V y i) hg (hV i) x j 137 0 a
      hN0 hG.le hB (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
      (fun k hk ↦ (hgb k (by omega) x hx).trans (by
        have hp : 1 ≤ N^(137*k+0) := one_le_pow₀ hN
        simpa using le_mul_of_one_le_right hG.le hp))
      (fun k hk ↦ by simpa using hv i k (by omega))
    simp only [Nat.add_zero,mul_one] at h
    exact h.trans (by gcongr; norm_num)
  let div : Yau.Jets.Coord → ℝ := fun y ↦ ∑ i : Fin 4, fderiv ℝ (W i) y (Pi.single i 1)
  have hpartial (i : Fin 4) : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (W i) y (Pi.single i 1)) :=
    ((hW i).fderiv_right (by simp)).clm_apply contDiff_const
  have hdiv : ContDiff ℝ ∞ div := ContDiff.sum (fun i _ ↦ hpartial i)
  have hdb (j : ℕ) (hj : j ≤ r) :
      ‖iteratedFDeriv ℝ j div x‖ ≤ (4*((2:ℝ)^(r+1)*G*B))*N^(137*j+(a+137)) := by
    have hb (i : Fin 4) := (real_partial_iterated_bound (W i) (hW i) x i j).trans
      (hw i (j+1) (by omega))
    dsimp [div]
    rw [iteratedFDeriv_fun_sum_apply (fun i _ ↦
      ((hpartial i).of_le
        (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top))).contDiffAt)]
    have h := (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun i _ ↦ hb i))
    simpa [show 137*(j+1)+a = 137*j+(a+137) by omega,mul_assoc] using h
  have h := scaled_frequency_product (fun y ↦ (gamma y)⁻¹) div (hg.inv hgn) hdiv x r 137 0 (a+137) (B := 4*((2:ℝ)^(r+1)*G*B))
    hN0 hI.le (by positivity) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun j hj ↦ (hib j hj x hx).trans (by
      have hp : 1 ≤ N^(137*j+0) := one_le_pow₀ hN
      simpa using le_mul_of_one_le_right hI.le hp))
    (fun j hj ↦ by simpa using hdb j hj)
  convert h using 1 <;> first | rfl | simp only [Nat.add_zero,mul_one,Nat.add_assoc]; ring

end
end Yau.Target

end OAI
