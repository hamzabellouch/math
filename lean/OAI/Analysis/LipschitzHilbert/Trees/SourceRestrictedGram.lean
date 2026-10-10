import OAI.Analysis.LipschitzHilbert.Trees.SourceGramSchur
import Mathlib.Data.Int.Interval

namespace OAI

/-! Schur control of the comparable-scale part of a Gram expansion.
The other scale pairs are left for the selected-tree geometric estimate. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem restricted_gram_energy {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ι → E) (near : ι → ι → Prop) [DecidableRel near] (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C) :
    (∑ i, ∑ j, if near i j then (inner ℂ (v i) (v j)).re else 0)≤
      C*∑ i, ‖v i‖^2 := by
  let G := fun i j => if near i j then (1:ℝ) else 0
  have hG : ∀ i j, 0≤G i j := by intro i j; dsimp [G]; split_ifs <;> norm_num
  have hsymG : ∀ i j, G i j=G j i := by intro i j; simp only [G,hsym i j]
  have hrowG : ∀ i, ∑ j, G i j≤C := by
    intro i
    simpa only [G,Finset.sum_boole] using hrow i
  calc
    _ ≤ ∑ i, ∑ j, G i j*‖v i‖*‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases h : near i j
      · simpa only [h,ite_true,G,one_mul] using
          (Complex.re_le_norm (inner ℂ (v i) (v j))).trans (norm_inner_le_norm (𝕜 := ℂ) (v i) (v j))
      · simp only [h,ite_false,G,zero_mul,le_refl]
    _ ≤ _ := symmetric_matrix_energy (fun i => ‖v i‖) G C hG hsymG hrowG

/-- A bounded interval of integer scale indices has uniformly bounded
cardinality, including scales at either endpoint of a finite family. -/
theorem finite_scale_neighbor_count {N : ℕ} (i : Fin N) (gap : ℕ) :
    (Finset.univ.filter (fun j : Fin N => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))).card≤
      2*gap+1 := by
  let e : Fin N ↪ ℤ := ⟨fun j => j.val,fun a b h => Fin.ext (Int.ofNat_inj.mp h)⟩
  let S := Finset.univ.filter (fun j : Fin N => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ))
  have hs : S.map e ⊆ Finset.Icc ((i.val:ℤ)-gap) ((i.val:ℤ)+gap) := by
    intro z hz
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hz
    have hj' := (abs_le.mp (Finset.mem_filter.mp hj).2)
    apply Finset.mem_Icc.mpr
    change (i.val:ℤ)-gap ≤ j.val ∧ (j.val:ℤ) ≤ i.val+gap
    omega
  have hcard := Finset.card_le_card hs
  have hlen : (Finset.Icc ((i.val:ℤ)-gap) ((i.val:ℤ)+gap)).card=2*gap+1 := by
    have h := Int.card_Icc_of_le (a := (i.val:ℤ)-gap) (b := (i.val:ℤ)+gap) (by omega)
    omega
  simpa only [Finset.card_map,hlen,S] using hcard

theorem comparable_scale_gram_energy {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : Fin N → E) (gap : ℕ) :
    (∑ i, ∑ j, if |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ)
      then (inner ℂ (v i) (v j)).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*∑ i, ‖v i‖^2 := by
  apply restricted_gram_energy v (fun i j => |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ)) _
  · intro i j
    rw [abs_sub_comm]
  · intro i
    exact_mod_cast finite_scale_neighbor_count i gap

end LipschitzHilbert

end

end OAI
