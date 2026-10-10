import OAI.Geometry.NodalSets.Elliptic.CorrugationAnnulusBoxes

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def corrugationAnnulusPacking (r J : ℝ) (n : ℕ) : Set Coord :=
  ⋃ p ∈ (Finset.univ : Finset (Fin n × Fin n)), corrugationAnnulusBox r J p.1 p.2

lemma corrugationAnnulusPacking_compact (r J : ℝ) (n : ℕ) :
    IsCompact (corrugationAnnulusPacking r J n) := by
  simp only [corrugationAnnulusPacking,Finset.mem_univ,iUnion_true]
  exact isCompact_iUnion (fun _ ↦ isCompact_Icc)

lemma corrugationAnnulusPacking_volume {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J) (n : ℕ) :
    volume (corrugationAnnulusPacking r J n) = ENNReal.ofReal ((n:ℝ)^2*r^2/(256*J^2)) := by
  have hd : Set.PairwiseDisjoint ((Finset.univ : Finset (Fin n × Fin n)) : Set (Fin n × Fin n))
      (fun p ↦ corrugationAnnulusBox r J p.1 p.2) := by
    intro p _ q _ hpq
    apply corrugationAnnulusBox_disjoint hJ (p.1.val,p.2.val) (q.1.val,q.2.val)
    intro he
    exact hpq (Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he)))
  rw [corrugationAnnulusPacking,measure_biUnion_finset hd (fun _ _ ↦ measurableSet_Icc)]
  simp_rw [corrugationAnnulusBox_volume hr hJ]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
  rw [show ((n*n:ℕ):ℝ≥0∞) = ENNReal.ofReal ((n:ℝ)^2) by simp [pow_two],
    ← ENNReal.ofReal_mul (sq_nonneg (n:ℝ))]
  congr 1
  ring

lemma corrugationAnnulusPacking_volume_lower {r J : ℝ} (hr : 0 < r) (hJ : 0 < J)
    (hlarge : 2 ≤ J*r) :
    ENNReal.ofReal (r^4/1024) ≤ volume (corrugationAnnulusPacking r J ⌊J*r⌋₊) := by
  rw [corrugationAnnulusPacking_volume hr.le hJ]
  apply ENNReal.ofReal_le_ofReal
  have hn : J*r/2 ≤ (⌊J*r⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (J*r)
    linarith
  have hn0 : (0:ℝ) ≤ ⌊J*r⌋₊ := by positivity
  apply (le_div_iff₀ (by positivity : 0 < 256*J^2)).mpr
  have hsq : (J*r/2)^2 ≤ (⌊J*r⌋₊:ℝ)^2 := sq_le_sq' (by linarith [mul_pos hJ hr]) hn
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg r)
  nlinarith only [hh]

end
end Yau.Geometry

end OAI
