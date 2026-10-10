import OAI.Analysis.PlanarPacking.BasisQuadrature
import OAI.Analysis.PlanarPacking.BasisIntervals

namespace OAI

/-!
# Entries of the cardinal interpolation operator

The columns of the interpolation operator are cardinal basis functions, and
certified quadrature controls their value and derivative entries.
-/

namespace SharpPlanar
open IntegerBasis IntegerIntervals IntegerGrid


noncomputable def columnVector (n : Node) (d : Bool) : X := lp.single 1 (n,d) 1

lemma density_column (n : Node) (d : Bool) (j : ℕ) (t : ℝ) :
    density (positiveData (columnVector n d)) j t = basisFunction d n.val j t := by
  classical
  unfold density positiveData columnVector
  simp only [Complex.ofReal_zero, zero_mul, zero_add]
  rw [tsum_eq_single n]
  · cases d <;> simp [basisFunction,lp.single_apply]
  · intro k hk
    have hf : (k,false) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    have ht : (k,true) ≠ (n,d) := fun h => hk (congrArg Prod.fst h)
    simp [Pi.single_eq_of_ne hf,Pi.single_eq_of_ne ht]

lemma K_column_integral (n : Node) (d e : Bool) (m : ℕ) :
    K (positiveData (columnVector n d)) (if e then 1 else 0) m =
      (∑ j : Fin 6, pieceIntegral (complexBasisMoment d e n.val j.val m) j.val).re := by
  unfold K positiveData
  simp only [Complex.ofReal_zero,zero_mul,zero_add]
  rw [← Finset.sum_range (fun j => pieceIntegral (complexBasisMoment d e n.val j m) j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  unfold pieceIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [complexBasisMoment_ofReal,show density { C := 0, c₀ := 0, d₀ := 0, x := columnVector n d } j t = basisFunction d n.val j t from density_column n d j t]
  unfold kernelMoment basisMoment
  (cases e <;> simp); ring


lemma K_column_rule_error {n : Node} {m : ℕ} (hn : n.val ≤ 100) (hm : m ≤ 100)
    (d e : Bool) :
    |K (positiveData (columnVector n d)) (if e then 1 else 0) m -
      (momentRuleValue quadraturePoint fejerWeight n.val m d e).re| < 1/10^22 := by
  rw [K_column_integral,← basis_rule_value]
  exact (Complex.abs_re_le_norm _).trans_lt (complexBasis_rule_error hn hm d e)

lemma S_column_value (n m : Node) (d : Bool) :
    S (columnVector n d) (m,false) = -K (positiveData (columnVector n d)) 0 m.val / Q m.val := by
  simp [S_apply,Scoords]
lemma S_column_derivative (n m : Node) (d : Bool) :
    S (columnVector n d) (m,true) =
      (D m.val * K (positiveData (columnVector n d)) 0 m.val -
        K (positiveData (columnVector n d)) 1 m.val) / Q m.val := by
  simp [S_apply,Scoords]

end SharpPlanar

end OAI
