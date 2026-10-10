import Mathlib
import OAI.Analysis.AffineBernstein.SigmaCapHelpers
import OAI.Analysis.AffineBernstein.AffineFamily

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
section NormalizedSigmaDependencies

section NormalizedCellGeometry
open Metric
/-- The literal fixed cell of bounds.tex. -/
def normalizedCell (k : ℕ) : Set (Space k) := {s | ∀ i, s i ∈ Icc (1/2) 2}
/-- The open positive neighbourhood used for differentiating support functions. -/
def normalizedCellDomain (k : ℕ) : Set (Space k) := {s | ∀ i, s i ∈ Ioo (1/4) 4}

lemma isOpen_normalizedCellDomain (k : ℕ) : IsOpen (normalizedCellDomain k) := by
  have he : normalizedCellDomain k = ⋂ i : Fin k, {s : Space k | s i ∈ Ioo (1/4) 4} := by
    ext s; simp [normalizedCellDomain]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ i))

lemma convex_normalizedCellDomain (k : ℕ) : Convex ℝ (normalizedCellDomain k) := by
  intro x hx y hy a b ha hb hab i
  change 1/4 < a*x i+b*y i ∧ a*x i+b*y i < 4
  exact (convex_Ioo (1/4:ℝ) 4) (hx i) (hy i) ha hb hab

lemma isCompact_normalizedCell (k : ℕ) : IsCompact (normalizedCell k) := by
  convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc (1/2:ℝ) 2))) using 1
  ext s
  simp only [normalizedCell,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_univ_pi,Set.mem_Icc]
  rfl

lemma normalizedCell_subset_domain (k : ℕ) : normalizedCell k ⊆ normalizedCellDomain k := by
  intro s hs i
  have := hs i
  constructor <;> linarith [this.1,this.2]

lemma normalizedCell_margin {k : ℕ} {s : Space k} (hs : s ∈ normalizedCell k) :
    closedBall s (1/8:ℝ) ⊆ normalizedCellDomain k := by
  intro t ht i
  have hdist : |t i-s i| ≤ 1/8 := by
    have hh := (PiLp.norm_apply_le (t-s) i).trans (mem_closedBall.mp ht)
    simpa only [dist_eq_norm,PiLp.sub_apply,Real.norm_eq_abs] using hh
  obtain ⟨hl,hu⟩ := abs_le.mp hdist
  have hh := hs i
  constructor <;> linarith [hh.1,hh.2]

lemma capTiltedForm_eq_sum {k : ℕ} (j : Fin k) (s : Space k) :
    capTiltedForm j s = (∑ i, s i) + s j := by
  simp only [capTiltedForm_apply,capTiltedCovector,add_mul,one_mul,Finset.sum_add_distrib]
  simp [Pi.single_apply,ite_mul]

lemma capTiltedForm_coord_bound {k : ℕ} {s : Space k} {b : ℝ}
    (hs : ∀ i, s i ≤ b) (j : Fin k) : capTiltedForm j s ≤ ((k:ℝ)+1)*b := by
  rw [capTiltedForm_eq_sum]
  have hh : (∑ i : Fin k, s i) ≤ (k:ℝ)*b := by
    calc
      _ ≤ ∑ _i : Fin k, b := Finset.sum_le_sum (fun i _ => hs i)
      _ = _ := by simp
  linarith [hs j]

lemma capTiltedForm_center {k : ℕ} (j : Fin k) :
    capTiltedForm j (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) = (k:ℝ)+1 := by
  rw [capTiltedForm_eq_sum]
  simp

lemma capTiltedCovector_one_le {k : ℕ} (j i : Fin k) : 1 ≤ capTiltedCovector j i := by
  by_cases he : i=j <;> simp [capTiltedCovector,he]
end NormalizedCellGeometry



end NormalizedSigmaDependencies
end AffineBernstein
end

end OAI
