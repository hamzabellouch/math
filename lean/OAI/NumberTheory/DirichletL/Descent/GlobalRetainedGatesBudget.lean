import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesCaps
import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesChildren

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseInitialArithmetic InverseSecondSourceBlocks
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

 theorem source_cell_exponent_cap {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0) (Z Lcap : ℝ) (hZ : 1<Z)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (d : BlockIndex) (hd : d∈keys p source) (i : Fin 4) :
    secondCellExponent Z d i≤Lcap := by
  obtain ⟨x,hx⟩ := (mem_keys_iff p source d).mp hd
  have hs : scales d i≤outerNorms p x i := by
    simpa only [one_mul,scales] using (le_div_iff₀ (dyadScale_pos _)).mp (cell_ratios p hp source hk d x hx i).1
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [second_cell_scale_rpow Z d i hZ]
  exact hs.trans (hnorm x (cell_subset p source d hx) i)

theorem source_cell_mass_gate {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (hk : ∀x∈source,x.second.frequency≠0)
    (Z Lcap ell Ractive j t eta eps pi : ℝ) (hZ : 1<Z) (hj : 0≤j) (heps : 0≤eps)
    (hnorm : ∀x∈source,∀i,outerNorms p x i≤Z^Lcap)
    (hbudget : eps*(ell+Ractive/2+t+Lcap+11*eta/2)≤pi) :
    ∀d∈keys p source,eps*(secondCount ell Ractive j t
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro d hd
  have hg := source_cell_exponent_cap p hp source hk Z Lcap hZ hnorm d hd 0
  have htheta := secondCellExponent_nonneg Z d 1 hZ
  apply le_trans (mul_le_mul_of_nonneg_left (show
    secondCount ell Ractive j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2≤
      ell+Ractive/2+t+Lcap+11*eta/2 by unfold secondCount; linarith) heps) hbudget

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
