import OAI.Geometry.CylinderCovering.Angular.Family
import OAI.Geometry.CylinderCovering.Angular.SamplingArea
import OAI.Geometry.CylinderCovering.Convexity.GeneralCapCoverage

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace TriangularCovering.AngularSampling

theorem compatible_sampled_cover {n : ℕ} (hn : 0 < n)
    (v q L : ℕ → ℝ)
    (hv0 : v 0 = -1) (hvn : v n = 1)
    (hv : ∀ j, j ≤ n → |v j| ≤ 1)
    (hinc : ∀ j < n, v j < v (j+1))
    (hq : ∀ j < n, v j ≤ q j ∧ q j ≤ v (j+1))
    (hL0 : L 0 = 0) (hLn : L n = 0)
    (hleft : ∀ j < n, nodeAlpha (q j)-v j*nodeBeta (q j) = L j)
    (hright : ∀ j < n, nodeAlpha (q j)-v (j+1)*nodeBeta (q j) = L (j+1))
    {ε : ℝ} (he0 : 0 < ε) (he1 : ε ≤ 1/14000)
    (hmesh : ∀ j < n, ∀ p ∈ Icc (v j) (v (j+1)), |q j-p| ≤ ε^2) :
    ∃ C : Fin (2*n) → TriCylinder,
      AngularFamily.PrescribedFamily C ε
        (fun j => v j) (fun j => v (j+1))
        (fun j => nodeAlpha (q j)) (fun j => nodeBeta (q j))
        (fun j => 1/2+ε^2*(η+d (q j))) ∧
      Covers C ∧
      |totalArea C/H-(1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 ∧
      totalArea C < A_min/2 ∧ relativeCost C < 1/2 := by
  have hqabs : ∀ j < n, |q j| ≤ 1 := by
    intro j hj
    exact abs_le.mpr ⟨(abs_le.mp (hv j hj.le)).1.trans (hq j hj).1,
      (hq j hj).2.trans (abs_le.mp (hv (j+1) hj)).2⟩
  have hpabs : ∀ j < n, ∀ p ∈ Icc (v j) (v (j+1)), |p| ≤ 1 := by
    intro j hj p hp
    exact abs_le.mpr ⟨(abs_le.mp (hv j hj.le)).1.trans hp.1,
      hp.2.trans (abs_le.mp (hv (j+1) hj)).2⟩
  have hcoeff : ∀ j < n, ∀ p ∈ Icc (v j) (v (j+1)),
      |nodeAlpha (q j)-(1+p^2)/4| ≤ 1*ε^2 ∧
        |nodeBeta (q j)-p/2| ≤ 1*ε^2 := by
    intro j hj p hp
    have hα := nodeAlpha_lipschitz (hqabs j hj) (hpabs j hj p hp)
    have hβ := nodeBeta_lipschitz (q j) p
    change |nodeAlpha (q j)-nodeAlpha p| ≤ _ ∧
      |nodeBeta (q j)-nodeBeta p| ≤ _
    constructor <;> nlinarith only [hα,hβ,hmesh j hj p hp,sq_nonneg ε]
  have hcap : ∀ j < n, ∀ p ∈ Icc (v j) (v (j+1)),
      1/2+ε^2*((p^2+p^4)/16+η)-1*ε^4 ≤
        1/2+ε^2*(η+d (q j)) := by
    intro j hj p hp
    have hd := d_lipschitz (hqabs j hj) (hpabs j hj p hp)
    have hdiff : d p-d (q j) ≤ ε^2 := by
      linarith only [(abs_le.mp hd).1,hmesh j hj p hp]
    have hm := mul_le_mul_of_nonneg_left hdiff (sq_nonneg ε)
    have hdp : d p=(p^2+p^4)/16 := by unfold d; ring
    rw [hdp] at hm
    nlinarith only [hm]
  have hab : ∀ j : Fin n, v j < v (j+1) := fun j => hinc j j.isLt
  have hR : ∀ j : Fin n, 0 < 1/2+ε^2*(η+d (q j)) := by
    intro j
    have hd := (d_bounds (hqabs j j.isLt)).1
    have hc : 0 ≤ η+d (q j) := by unfold η; linarith only [hd]
    positivity
  let C := AngularFamily.family ε
    (fun j : Fin n => v j) (fun j => v (j+1))
    (fun j => nodeAlpha (q j)) (fun j => nodeBeta (q j))
    (fun j => 1/2+ε^2*(η+d (q j))) hab hR
  have hC : Covers C := by
    apply AngularFamily.covers_of_coordinate_hits
    intro x y t hx hy
    have hc := CylinderCovering.GeneralCap.coordinate_coverage hn v
      (fun j => nodeAlpha (q j)) (fun j => nodeBeta (q j)) L
      (fun j _ => 1/2+ε^2*(η+d (q j))) hv0 hvn hv hL0 hLn hinc hleft hright
      he0 (by linarith only [he1] : ε ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num [η] : 0 < η) (by norm_num [η] : η ≤ 1/480)
      (by unfold η; linarith only [he1] : (10+4*(1:ℝ))*ε ≤ η) hcoeff hcap hx hy
    rcases hc with ⟨j,hj,p,hp,hr,hrT,hy'⟩ | ⟨j,hj,p,hp,hr,hrT,hx'⟩
    · left
      refine ⟨⟨j,hj⟩,hr,hrT,?_,?_⟩
      · have h := mul_le_mul_of_nonneg_right hp.1 hr
        dsimp
        nlinarith only [h,hy']
      · have h := mul_le_mul_of_nonneg_right hp.2 hr
        dsimp
        nlinarith only [h,hy']
    · right
      refine ⟨⟨j,hj⟩,hr,hrT,?_,?_⟩
      · have h := mul_le_mul_of_nonneg_right hp.1 hr
        dsimp
        nlinarith only [h,hx']
      · have h := mul_le_mul_of_nonneg_right hp.2 hr
        dsimp
        nlinarith only [h,hx']
  have heabs : |ε| ≤ 1 := by rw [abs_of_pos he0]; linarith only [he1]
  have harea : |totalArea C/H-(1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by
    dsimp [C]
    rw [AngularFamily.total_area]
    exact sampled_sum_error v (fun j => q j) heabs hv0 hvn hv
      (fun j => hq j j.isLt) (fun j => hmesh j j.isLt)
  have hratio : totalArea C/H < 1/2 := by
    have hup := (abs_le.mp harea).2
    have he2 : ε^2 ≤ (1/14000:ℝ)^2 := by nlinarith only [he0,he1]
    have hcoef : 14*ε^2 < (13/6000:ℝ) := by nlinarith only [he2]
    have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos he0) (sub_neg.mpr hcoef)
    nlinarith only [hup,hneg]
  refine ⟨C,AngularFamily.family_prescribed _ _ _ _ _ _ _ _,hC,harea,?_,?_⟩
  · rw [projection_minimum]
    have h := (div_lt_iff₀ H_pos).mp hratio
    linarith only [h]
  · exact (relativeCost_le_totalArea C).trans_lt hratio

end TriangularCovering.AngularSampling

end

end OAI
