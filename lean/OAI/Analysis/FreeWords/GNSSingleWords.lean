import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore
import OAI.Analysis.FreeWords.GNSCutBridge
import OAI.Analysis.FreeWords.GNSCutNorms
import OAI.Analysis.FreeWords.GNSRows
import OAI.Analysis.FreeWords.SingleCutNorm

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

namespace FreePartitions

variable (P : FreePartitions τ r d)

theorem create_norm (hτ : τ 1 = 1) (j : Fin r) (a : Fin d) :
    ‖P.create j a‖ ≤ decay d := (P.create_row hτ j).norm_le (decay_nonneg d) a

theorem annihilate_norm (hτ : τ 1 = 1) (j : Fin r) (a : Fin d) :
    ‖P.annihilate j a‖ ≤ decay d := by
  exact (norm_star (P.create j a)).le.trans (P.create_norm hτ j a)

theorem preserve_norm (hd : 1 ≤ d) (j : Fin r) (a : Fin d) :
    ‖P.preserve j a‖ ≤ 2 := by
  change ‖preservationOp τ P.S j (P.centered j a)‖ ≤ _
  rw [P.preservation_eq_compress]
  let Q := (headSpace τ P.S j).starProjection
  have hQ : ‖Q‖ ≤ 1 := (headSpace τ P.S j).starProjection_norm_le
  have hz : ‖(d:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hd)
  have hL : ‖τ.gnsStarAlgHom (P.e j a) - (d:ℂ)⁻¹ • 1‖ ≤ 2 := by
    apply (norm_sub_le _ _).trans
    have hscalar : ‖(d:ℂ)⁻¹ • (1 : τ.GNS →L[ℂ] τ.GNS)‖ ≤ 1 := by
      rw [norm_smul]
      exact (mul_le_mul hz ContinuousLinearMap.norm_id_le (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    linarith [(P.gns_projection j a).norm_le]
  calc
    _ ≤ ‖Q‖ * ‖τ.gnsStarAlgHom (P.e j a) - (d:ℂ)⁻¹ • 1‖ * ‖Q‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * 2 * 1 := mul_le_mul (mul_le_mul hQ hL (norm_nonneg _) zero_le_one)
      hQ (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

theorem single_centered_word_norm (hτ : FaithfulTracial τ) (hd : 1 ≤ d)
    (a : Fin r → Fin d) (w : List (Fin r)) (hw : w ≠ [])
    (hchain : w.IsChain (· ≠ ·)) :
    ‖(w.map (fun j => P.centered j (a j))).prod‖ ≤
      (3*w.length+1:ℝ) * decay d ^ (w.length-1) := by
  have hc : w.IsChain (CutCompatible (fun j => P.create j (a j))
      (fun j => P.annihilate j (a j)) (fun j => P.preserve j (a j))) :=
    hchain.imp (fun _ _ hij => P.cutCompatible hτ.1 a hij)
  have hprod : (w.map (fun j => P.letter j (a j))).prod =
      cutSum (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
        (fun j => P.preserve j (a j)) w := by
    rw [← product_eq_cutSum _ _ _ _ hc]
    simp only [P.letter_eq hτ.1]
  have hm : (w.map (fun j => P.centered j (a j))).prod ∈
      reductionAlgebra τ (reducedSpace τ P.S) := by
    apply list_prod_mem
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact (mem_reductionAlgebra _ _).mpr
      (copy_commutes_reducedProjection hτ.1 (P.centered_mem j (a j)))
  have he := letterOp_product (fun j => P.centered j (a j))
    (fun j => copy_commutes_reducedProjection hτ.1 (P.centered_mem j (a j))) w hw
  rw [← norm_compressed (reducedSpace τ P.S) vacuum_mem_reducedSpace hτ.2.2
    _ ((mem_reductionAlgebra _ _).mp hm)]
  change ‖letterOp τ P.S ((w.map (fun j => P.centered j (a j))).prod)‖ ≤ _
  rw [← he]
  change ‖(w.map (fun j => P.letter j (a j))).prod‖ ≤ _
  rw [hprod]
  exact norm_cutSum_le_simple _ _ _ w ContinuousLinearMap.norm_id_le (decay_nonneg d) (decay_le_one hd) hw
    (fun j => P.create_norm hτ.1 j (a j)) (fun j => P.annihilate_norm hτ.1 j (a j))
    (fun j => P.preserve_norm hd j (a j))

end FreePartitions

end

end KKFreeWords
end

end OAI
