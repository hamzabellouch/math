import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.OrientedTreePotential

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module PivotTree
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma projective_card_pos_of_five (hd : finrank K V=5) :
    0<Fintype.card (ℙ K V) := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V (show finrank K V=4+1 from hd)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,pow_zero]
  omega

omit [FiniteDimensional K V] in
lemma ambient_pivotPotential (hd : finrank K V=5) (σ : ℝ)
    (hq : Real.exp σ=Nat.card K) :
    pivotPotential (K:=K) (V:=V) (Finset.univ,Finset.univ)≤3*σ+Real.log 4 := by
  have hq2 : 2≤Nat.card K := Finite.one_lt_card (α:=K)
  have ha := projective_card_pos_of_five hd
  have hb := projective_card_pos_of_five (K:=K) (V:=Dual K V) (by simpa using hd)
  have hA := projective_card_le_two_pow (d:=4) hd hq2
  have hB := projective_card_le_two_pow (K:=K) (V:=Dual K V) (d:=4) (by simpa using hd) hq2
  have hl : Real.log (Nat.card K:ℝ)=σ := by rw [←hq,Real.log_exp]
  have hh := initial_potential (Nat.card K:ℝ) (Fintype.card (ℙ K V))
    (Fintype.card (ℙ K (Dual K V))) (by exact_mod_cast (show 1≤Nat.card K by omega))
    (by exact_mod_cast ha) (by exact_mod_cast hb) (by exact_mod_cast hA) (by exact_mod_cast hB)
  simpa only [pivotPotential,Finset.card_univ,hl] using hh
end SharpRamseyFive.ProjectiveIncidence

end OAI
