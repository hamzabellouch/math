import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import OAI.Geometry.NodalSets.Charts.CorrugationFrameOperatorBounds
import OAI.Geometry.NodalSets.Elliptic.CorrugationAnnulusCell

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def corrugationAnnulusBox (r J : ℝ) (j k : ℕ) : Set Coord :=
  Icc ![-r,-r,((j:ℝ)+1/16)/J,(k:ℝ)/J]
      ![r,r,((j:ℝ)+3/32)/J,((k:ℝ)+1/32)/J]

lemma corrugationAnnulusBox_fast {r J : ℝ} (hJ : 0 < J) (j k : ℕ)
    {v : Coord} (hv : v ∈ corrugationAnnulusBox r J j k) :
    J*v 2-(j:ℝ) ∈ Icc (1/16:ℝ) (3/32) ∧
    J*v 3-(k:ℝ) ∈ Icc (0:ℝ) (1/32) := by
  have h2 : ((j:ℝ)+1/16)/J ≤ v 2 ∧ v 2 ≤ ((j:ℝ)+3/32)/J := ⟨hv.1 2,hv.2 2⟩
  have h3 : (k:ℝ)/J ≤ v 3 ∧ v 3 ≤ ((k:ℝ)+1/32)/J := ⟨hv.1 3,hv.2 3⟩
  have h2a := (div_le_iff₀ hJ).mp h2.1
  have h2b := (le_div_iff₀ hJ).mp h2.2
  have h3a := (div_le_iff₀ hJ).mp h3.1
  have h3b := (le_div_iff₀ hJ).mp h3.2
  constructor <;> constructor <;> linarith

lemma corrugationAnnulusBox_norm {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J)
    {n : ℕ} (hn : (n:ℝ) ≤ J*r) (j k : Fin n)
    {v : Coord} (hv : v ∈ corrugationAnnulusBox r J j k) : ‖v‖ ≤ r := by
  have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
  have hk : (k:ℝ)+1 ≤ n := by exact_mod_cast k.isLt
  have h2 := corrugationAnnulusBox_fast hJ j k hv
  apply (pi_norm_le_iff_of_nonneg hr).mpr
  intro i
  have hlo := hv.1 i
  have hhi := hv.2 i
  fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Fin.reduceFinMk] at hlo hhi ⊢
  · exact abs_le.mpr ⟨hlo,hhi⟩
  · exact abs_le.mpr ⟨hlo,hhi⟩
  · change |v 2| ≤ r
    have hj0 : (0:ℝ) ≤ j := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h2.1.1,h2.1.2]
  · change |v 3| ≤ r
    have hk0 : (0:ℝ) ≤ k := by positivity
    rw [abs_le]
    constructor <;> nlinarith [h2.2.1,h2.2.2]

lemma corrugationAnnulusBox_disjoint {r J : ℝ} (hJ : 0 < J)
    (p q : ℕ × ℕ) (hpq : p ≠ q) :
    Disjoint (corrugationAnnulusBox r J p.1 p.2) (corrugationAnnulusBox r J q.1 q.2) := by
  apply Set.disjoint_left.mpr
  intro v hv hw
  have hp := corrugationAnnulusBox_fast hJ p.1 p.2 hv
  have hq := corrugationAnnulusBox_fast hJ q.1 q.2 hw
  have he : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra h
    simp only [not_or,not_not] at h
    exact hpq (Prod.ext h.1 h.2)
  rcases he with he | he
  · rcases lt_or_gt_of_ne he with he | he
    · have hh : (p.1:ℝ)+1 ≤ q.1 := by exact_mod_cast he
      linarith [hp.1.1,hp.1.2,hq.1.1,hq.1.2]
    · have hh : (q.1:ℝ)+1 ≤ p.1 := by exact_mod_cast he
      linarith [hp.1.1,hp.1.2,hq.1.1,hq.1.2]
  · rcases lt_or_gt_of_ne he with he | he
    · have hh : (p.2:ℝ)+1 ≤ q.2 := by exact_mod_cast he
      linarith [hp.2.1,hp.2.2,hq.2.1,hq.2.2]
    · have hh : (q.2:ℝ)+1 ≤ p.2 := by exact_mod_cast he
      linarith [hp.2.1,hp.2.2,hq.2.1,hq.2.2]

lemma corrugationAnnulusBox_volume {r J : ℝ} (hr : 0 ≤ r) (hJ : 0 < J) (j k : ℕ) :
    volume (corrugationAnnulusBox r J j k) = ENNReal.ofReal (r^2/(256*J^2)) := by
  rw [corrugationAnnulusBox,Real.volume_Icc_pi]
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]
  have h1 : r- -r = 2*r := by ring
  have h2 : ((j:ℝ)+3/32)/J-((j:ℝ)+1/16)/J = 1/(32*J) := by ring
  have h3 : ((k:ℝ)+1/32)/J-(k:ℝ)/J = 1/(32*J) := by ring
  rw [h1,h2,h3]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(32*J)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*r)]
  congr 1
  ring

end
end Yau.Geometry

end OAI
