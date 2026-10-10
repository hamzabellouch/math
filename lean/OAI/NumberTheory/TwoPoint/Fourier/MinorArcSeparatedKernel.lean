import OAI.NumberTheory.TwoPoint.Fourier.MinorArcPhaseRepresentatives

namespace OAI

/-! A finite Vinogradov kernel bound on a separated set of phases. -/

namespace TwoPointCorrelations

open Finset

lemma minor_arc_kernel_le (L α : ℝ) : minorArcGeometricBound L α ≤ L := by
  unfold minorArcGeometricBound
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem minor_arc_separated_kernel {ι : Type*} (S : Finset ι) (θ : ι → ℝ)
    (δ V : ℝ) (hδ : 0 < δ) (hV : 0 ≤ V)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      δ ≤ dist (θ i : UnitAddCircle) (θ j : UnitAddCircle)) :
    (∑ i ∈ S, minorArcGeometricBound V (θ i)) ≤
      2 * V + (2 / δ) * (1 + Real.log (⌈(1 / 2 : ℝ) / δ⌉₊ : ℝ)) := by
  let x := fun i => θ i - (round (θ i) : ℝ)
  apply minor_arc_packing_sum S x (fun i => minorArcGeometricBound V (θ i))
    δ V (1 / 2) hδ hV
  · intro i hi j hj hij
    exact (hsep i hi j hj hij).trans (minor_arc_centered_difference (θ i) (θ j))
  · intro i _
    exact minor_arc_centered_small (θ i)
  · intro i _
    exact minor_arc_kernel_le V (θ i)
  · intro i _ hxi
    have hnorm : ‖(θ i : UnitAddCircle)‖ = |x i| := UnitAddCircle.norm_eq
    have hb := minor_arc_geometric_circle (L := V) (hnorm.symm ▸ hxi)
    apply (hb.trans (min_le_right _ _)).trans
    rw [hnorm]
    exact one_div_le_one_div_of_le hxi (by linarith)

theorem minor_arc_rational_block (S : Finset ℤ) (α : ℝ) (a q : ℤ)
    (hq : 0 < q) (hcop : IsCoprime q a) (V : ℝ) (hV : 0 ≤ V)
    (hwidth : ∀ m ∈ S, ∀ n ∈ S, |((m - n : ℤ) : ℝ)| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hb := minor_arc_separated_kernel S (fun n => (n : ℝ) * α)
    (1 / (2 * (q : ℝ))) V (by positivity) hV
    (fun m hm n hn hmn => minor_arc_pair_spacing hq hcop hmn (hwidth m hm n hn) happrox)
  have hceil : ⌈(1 / 2 : ℝ) / (1 / (2 * (q : ℝ)))⌉₊ = q.toNat := by
    rw [show (1 / 2 : ℝ) / (1 / (2 * (q : ℝ))) = (q : ℝ) by field_simp]
    exact Nat.ceil_intCast q
  have hcast : (q.toNat : ℝ) = q := by exact_mod_cast Int.toNat_of_nonneg hq.le
  rw [hceil, hcast] at hb
  have he : 2 / (1 / (2 * (q : ℝ))) = 4 * (q : ℝ) := by field_simp; norm_num
  rw [he] at hb
  exact hb

end TwoPointCorrelations

end OAI
