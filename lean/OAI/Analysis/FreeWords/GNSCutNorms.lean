import Mathlib
import OAI.Analysis.FreeWords.FreeWordCore
import OAI.Analysis.FreeWords.CutNorms
import OAI.Analysis.FreeWords.GNSRows
import OAI.Analysis.FreeWords.GNSCutBridge

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {r d : ℕ}

def decay (d : ℕ) : ℝ := Real.sqrt ((d:ℝ)⁻¹)

theorem decay_nonneg (d : ℕ) : 0 ≤ decay d := Real.sqrt_nonneg _

theorem decay_sq (d : ℕ) : decay d ^ 2 = (d:ℝ)⁻¹ := Real.sq_sqrt (by positivity)

theorem decay_le_one {d : ℕ} (hd : 1 ≤ d) : decay d ≤ 1 := by
  apply (Real.sqrt_le_one).mpr
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hd)

namespace FreePartitions

variable (P : FreePartitions τ r d)

theorem create_row (hτ : τ 1 = 1) (j : Fin r) :
    RowSqBound (P.create j) (decay d ^ 2) := by
  rw [decay_sq]
  exact P.creation_row hτ j

theorem annihilate_col (hτ : τ 1 = 1) (j : Fin r) :
    ColSqBound (P.annihilate j) (decay d ^ 2) :=
  (P.create_row hτ j).star_col (sq_nonneg _)

theorem noPresCut_norm (hτ : τ 1 = 1) (W : Multiset (Fin d)) (q : ℕ) (hq : q ≤ r) :
    ‖∑ a : Fin r → Fin d, if tupleLabels a = W then
      noPresCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j)) q else 0‖ ≤
      Real.sqrt ((q.factorial:ℝ) * (r-q).factorial) * decay d ^ r := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hq
  simpa only [Nat.add_sub_cancel_left] using
    sum_noPresCut_norm p q W P.create P.annihilate (decay_nonneg d)
      (P.create_row hτ) (P.annihilate_col hτ)

theorem presCut_norm (hτ : τ 1 = 1) (W : Multiset (Fin d)) (j : Fin r) :
    ‖∑ a : Fin r → Fin d, if tupleLabels a = W then
      presCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
        (fun j => P.preserve j (a j)) j else 0‖ ≤
      (Real.sqrt ((j.val.factorial:ℝ) * (r-1-j).factorial) +
        decay d ^ 2 * Real.sqrt (((j.val+1).factorial:ℝ) * (r-j).factorial)) *
        decay d ^ (r-1) := by
  rcases j with ⟨q, hq⟩
  obtain ⟨p, hr⟩ := Nat.exists_eq_add_of_le (show q+1 ≤ r by omega)
  have hr' : r = q+(p+1) := by omega
  clear hr
  subst r
  have hj : (⟨q,hq⟩ : Fin (q+(p+1))) = Fin.natAdd q 0 := by ext; simp
  have h := sum_presCut_norm p q W P.create P.annihilate P.preserve (decay_nonneg d)
    (P.create_row hτ) (P.annihilate_col hτ)
    (fun c => τ.gnsStarAlgHom (P.e (Fin.natAdd q 0) c))
    (P.gns_projection _) (P.gns_projection_orthogonal _) (P.gns_projection_sum _)
    (headSpace τ P.S (Fin.natAdd q 0)).starProjection
    (headSpace τ P.S (Fin.natAdd q 0)).starProjection_norm_le (d:ℂ)⁻¹
    (P.preservation_eq_compress _)
  rw [hj]
  have hd : ‖(d:ℂ)⁻¹‖ = decay d ^ 2 := by rw [decay_sq]; simp
  simpa only [hd, Fin.val_natAdd, Fin.val_zero, Nat.add_zero,
    show q+(p+1)-1-q=p by omega, show q+(p+1)-q=p+1 by omega,
    show q+(p+1)-1=q+p by omega, show q+p-q=p by omega] using h

theorem centeredSum_cut_bound (hτ : FaithfulTracial τ) (hr : r ≠ 0)
    (W : Multiset (Fin d)) :
    ‖P.centeredSum W‖ ≤
      (∑ q : Fin (r+1), Real.sqrt ((q.val.factorial:ℝ) * (r-q).factorial) * decay d ^ r) +
      ∑ j : Fin r, (Real.sqrt ((j.val.factorial:ℝ) * (r-1-j).factorial) +
        decay d ^ 2 * Real.sqrt (((j.val+1).factorial:ℝ) * (r-j).factorial)) *
        decay d ^ (r-1) := by
  rw [P.norm_centeredSum hτ hr W]
  have he : (∑ a : Fin r → Fin d, if tupleLabels a = W then
      (List.ofFn (fun j => P.letter j (a j))).prod else 0) =
      (∑ q : Fin (r+1), ∑ a : Fin r → Fin d, if tupleLabels a = W then
        noPresCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j)) q else 0) +
      ∑ j : Fin r, ∑ a : Fin r → Fin d, if tupleLabels a = W then
        presCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
          (fun j => P.preserve j (a j)) j else 0 := by
    rw [Finset.sum_comm (f := fun (q : Fin (r+1)) (a : Fin r → Fin d) => if tupleLabels a = W then
      noPresCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j)) q else 0),
      Finset.sum_comm (f := fun (j : Fin r) (a : Fin r → Fin d) => if tupleLabels a = W then
      presCut (fun j => P.create j (a j)) (fun j => P.annihilate j (a j))
        (fun j => P.preserve j (a j)) j else 0), ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    split_ifs with h
    · exact P.product_letter_eq_cuts hτ.1 a
    · simp only [Finset.sum_const_zero, add_zero]
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun q _ => P.noPresCut_norm hτ.1 W q (by omega))
  · apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun j _ => P.presCut_norm hτ.1 W j)

end FreePartitions

end

end KKFreeWords
end

end OAI
