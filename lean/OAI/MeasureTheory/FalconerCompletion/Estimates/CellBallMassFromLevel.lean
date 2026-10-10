import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SuffixDescendants

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

lemma cell_ball_mass_from_level (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ρ] (P : CellPath d) (n : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (C₀ hi : ℝ) (hC : 0 ≤ C₀) (hhi : 0 ≤ hi)
    (hcells : ∀ Q ∈ dyadicPaths n, 0 < ρ (treeCell Q) → (ρ (treeCell Q)).toReal ≤ hi) :
    ρ.real (ball x (C₀/(2:ℝ)^n) ∩ treeCell P) ≤ (2*C₀+2*(d:ℝ)+7)^d*hi := by
  classical
  let T := (dyadicPaths (d:=d) n).filter fun Q =>
    dist (treeCenter Q) x ≤ (C₀+(d+1:ℝ))/(2:ℝ)^n
  have hT : T ⊆ dyadicPaths n := Finset.filter_subset _ _
  have hcover : ball x (C₀/(2:ℝ)^n) ∩ treeCell P ⊆ leafUnion T := by
    intro z hz
    have hroot : z ∈ treeCell [] := by simpa using treeCell_subset_take P 0 hz.2
    rw [←treeCell_cover_root n] at hroot
    obtain ⟨Q,hQ,hzQ⟩ := mem_iUnion₂.mp hroot
    have hlen := (mem_dyadicPaths n Q).mp hQ
    have hdist := ambientGridCell_dist_le hzQ (treeCenter_mem Q)
    change dist (treeCenter Q) z ≤ (d+1:ℝ)/(2:ℝ)^Q.length at hdist
    rw [hlen] at hdist
    have hb : dist (treeCenter Q) x ≤ (C₀+(d+1:ℝ))/(2:ℝ)^n := by
      calc
        _ ≤ dist (treeCenter Q) z+dist z x := dist_triangle _ _ _
        _ ≤ (d+1:ℝ)/(2:ℝ)^n+C₀/(2:ℝ)^n := add_le_add hdist (mem_ball.mp hz.1).le
        _ = _ := by ring
    exact mem_iUnion₂.mpr ⟨Q,Finset.mem_filter.mpr ⟨hQ,hb⟩,hzQ⟩
  have hcard : (T.card:ℝ) ≤ (2*C₀+2*(d:ℝ)+7)^d := by
    have hh := treeCenter_ball_card T hT x (show 0 ≤ (C₀+(d+1:ℝ))/(2:ℝ)^n by positivity)
      (fun Q hQ => (Finset.mem_filter.mp hQ).2)
    convert hh using 1
    congr 1
    field_simp
    ring
  calc
    _ ≤ (ρ (leafUnion T)).toReal := measureReal_mono hcover
    _ = ∑ Q ∈ T, (ρ (treeCell Q)).toReal := restriction_total_mass_real ρ hT
    _ ≤ ∑ _Q ∈ T, hi := by
      apply Finset.sum_le_sum
      intro Q hQ
      by_cases hp : 0 < ρ (treeCell Q)
      · exact hcells Q (hT hQ) hp
      · simp only [not_lt,nonpos_iff_eq_zero] at hp
        simpa only [hp,ENNReal.toReal_zero] using hhi
    _ = (T.card:ℝ)*hi := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hhi

lemma conditional_ball_from_profile (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    {m : ℝ → ℝ} {N B : ℕ} {s sig : ℝ}
    (hr : RegularizedProfileData ρ N B s sig m) {p n : ℕ}
    (hpN : p ≤ N) (hnN : n ≤ N) (P : CellPath d) (hP : P.length=p)
    (hpos : 0 < ρ (treeCell P)) (x : EuclideanSpace ℝ (Fin d)) :
    (classConditional ρ P).real (ball x ((2:ℝ)^n)⁻¹) ≤
      (2*(d:ℝ)+9)^d*((2:ℝ)^N)^(m p-m n+2*(d+1:ℝ)*sig) := by
  let := hr.probability
  have hp := (hr.cells p hpN P hP hpos).1
  have hm := cell_ball_mass_from_level ρ P n x 1
    (((2:ℝ)^N)^((d+1:ℝ)*sig)*((2:ℝ)^N)^(-m n)) (by norm_num) (by positivity)
    (fun Q hQ hq => (hr.cells n hnN Q ((mem_dyadicPaths n Q).mp hQ) hq).2)
  simp only [one_div] at hm
  have hp' : 0 < (ρ (treeCell P)).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hlo : 0 < ((2:ℝ)^N)^(-(d+1:ℝ)*sig)*((2:ℝ)^N)^(-m p) := by positivity
  have he : (classConditional ρ P).real (ball x ((2:ℝ)^n)⁻¹) =
      ρ.real (ball x ((2:ℝ)^n)⁻¹ ∩ treeCell P)/(ρ (treeCell P)).toReal := by
    simp only [classConditional,measureReal_def,Measure.smul_apply,ENNReal.smul_def,
      smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal,NNReal.coe_inv,
      ENNReal.coe_toNNReal_eq_toReal,Measure.restrict_apply measurableSet_ball,div_eq_mul_inv]
    ring
  rw [he]
  have hh := div_le_div₀ (by positivity) hm hlo hp
  apply hh.trans_eq
  have hR : 0 < (2:ℝ)^N := by positivity
  norm_num only [mul_one,one_mul] at *
  rw [mul_div_assoc,←Real.rpow_add hR,←Real.rpow_add hR,←Real.rpow_sub hR]
  congr 1 <;> ring_nf
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
