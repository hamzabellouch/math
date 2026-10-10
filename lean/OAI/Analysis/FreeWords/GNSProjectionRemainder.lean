import Mathlib
import OAI.Analysis.FreeWords.GNSCutBridge
import OAI.Analysis.FreeWords.GNSSingleWords
import OAI.Analysis.FreeWords.ScalarExpansion

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

namespace FreePartitions

variable (P : FreePartitions τ r d)

theorem single_projection_remainder (hτ : FaithfulTracial τ) (hd : 1 ≤ d)
    (a : Fin r → Fin d) :
    ‖(List.ofFn (fun j => P.e j (a j))).prod -
      (List.ofFn (fun j => P.centered j (a j))).prod‖ ≤
        (2:ℝ)^r*(3*r+1)*decay d^r := by
  have hn : (List.ofFn (id : Fin r → Fin r)).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hc : ‖(d:ℂ)⁻¹‖ = decay d^2 := by rw [decay_sq]; simp
  have h := projection_word_remainder (f := fun j => P.centered j (a j))
    (List.ofFn (id : Fin r → Fin r)) hn (decay_nonneg d) (decay_le_one hd) hc
    (IsStarProjection.norm_le 1 (IsStarProjection.one A))
    (fun s hs hsn => P.single_centered_word_norm hτ hd a s hsn
      (List.Pairwise.isChain (hn.sublist hs)))
  simpa only [List.length_ofFn, List.map_ofFn, Function.comp_def, id_eq,
    centered, add_sub_cancel] using h

def forwardSum (W : Multiset (Fin d)) : A :=
  ∑ a : Fin r → Fin d, if tupleLabels a = W then
    (List.ofFn (fun j => P.e j (a j))).prod else 0

theorem forwardSum_remainder (hτ : FaithfulTracial τ) (hd : 1 ≤ d)
    (W : Multiset (Fin d)) :
    ‖P.forwardSum W - P.centeredSum W‖ ≤
      (r.factorial:ℝ)*(2:ℝ)^r*(3*r+1)*decay d^r := by
  classical
  have he : P.forwardSum W - P.centeredSum W =
      ∑ a ∈ tupleFiber r W, ((List.ofFn (fun j => P.e j (a j))).prod -
        (List.ofFn (fun j => P.centered j (a j))).prod) := by
    simp only [forwardSum, centeredSum, tupleFiber, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs <;> simp
  rw [he]
  calc
    _ ≤ ∑ a ∈ tupleFiber r W, (2:ℝ)^r*(3*r+1)*decay d^r :=
      norm_sum_le_of_le _ (fun a _ => P.single_projection_remainder hτ hd a)
    _ = ((tupleFiber r W).card:ℝ)*((2:ℝ)^r*(3*r+1)*decay d^r) := by simp
    _ ≤ (r.factorial:ℝ)*((2:ℝ)^r*(3*r+1)*decay d^r) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast tupleFiber_card r W)
        (mul_nonneg (by positivity) (pow_nonneg (decay_nonneg d) r))
    _ = _ := by ring

end FreePartitions

end

end KKFreeWords
end

end OAI
