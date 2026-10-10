import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Angular.Taylor
import OAI.Geometry.CylinderCovering.Angular.AreaRefinement
import OAI.Geometry.CylinderCovering.Angular.ConstructionDefinitions

namespace OAI

noncomputable section
namespace TriangularCovering
open Set MeasureTheory

lemma term_remainder_sharp {ε a b : ℝ} (he : |ε| ≤ 1)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hab : a ≤ b) :
    |normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))|
      ≤ (b-a)/2*ε^4 := by
  have hc := coeff_bounds ha hb
  have hM0 : 0 ≤ cutoffCoeff a b := by
    have := hc.2.2.2.1
    dsimp [η] at this
    linarith
  have hM1 : cutoffCoeff a b ≤ 1/4 := by
    have := hc.2.2.2.2
    dsimp [η] at this
    linarith
  have hD0 : 0 ≤ speedSq a b := by unfold speedSq; positivity
  have hD1 : speedSq a b ≤ 1 := by
    have ha2 : (alpha a b)^2 ≤ 1/4 := by nlinarith only [hc.1,hc.2.1]
    have hb2 : (beta a b)^2 ≤ 1/4 := by
      nlinarith only [(abs_le.mp hc.2.2.1).1,(abs_le.mp hc.2.2.1).2]
    dsimp [speedSq]
    linarith only [ha2,hb2]
  have he2 : ε^2 ≤ 1 := by nlinarith only [(abs_le.mp he).1,(abs_le.mp he).2]
  have hh := AngularTaylor.bounded_product_remainder
    (sq_nonneg ε) he2 hM0 hM1 hD0 hD1
  have hid : normalizedTerm ε a b - (b-a)*(1/4+ε^2*(cutoffCoeff a b-speedSq a b/8)) =
      (b-a)*((1/2+ε^2*cutoffCoeff a b)^2 / Real.sqrt (1+ε^2*speedSq a b) -
        (1/4+ε^2*(cutoffCoeff a b-speedSq a b/8))) := by
    dsimp [normalizedTerm,cutoff]
    ring
  rw [hid,abs_mul,abs_of_nonneg (sub_nonneg.mpr hab)]
  have h := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hab)
  calc
    _ ≤ (b-a)*((47/128)*(ε^2)^2) := h
    _ ≤ (b-a)/2*ε^4 := by
      have := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg (ε^2))
      nlinarith only [this]

lemma mesh_term_remainder_sharp {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2+ε^2 * coefficientSum N)| ≤ ε^4 := by
  let f : Fin N → ℝ := fun j => step N*(1/4+ε^2*
    (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))
  have hsum : (∑ j : Fin N, f j) = 1/2+ε^2*coefficientSum N := by
    dsimp [f,coefficientSum]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib,Finset.mul_sum]
    have heq : (∑ j : Fin N, step N * (ε^2 *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8))) =
        ∑ j : Fin N, ε^2 * (step N *
        (cutoffCoeff (mesh N j) (mesh N (j+1))-speedSq (mesh N j) (mesh N (j+1))/8)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    congr 1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have := count_step hN
    linarith only [this]
  rw [← hsum,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N, |normalizedTerm ε (mesh N j) (mesh N (j+1))-f j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin N, step N/2*ε^4 := by
      apply Finset.sum_le_sum
      intro j _
      have hab : mesh N j ≤ mesh N (j+1) := (mesh_strict hN j).le
      have h := term_remainder_sharp he (mesh_abs_le hN j.isLt.le)
        (mesh_abs_le hN j.isLt) hab
      simpa only [mesh_succ,f] using h
    _ = ε^4 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      calc
        (N : ℝ)*(step N/2*ε^4) = ((N : ℝ)*step N)/2*ε^4 := by ring
        _ = ε^4 := by rw [count_step hN]; ring

lemma uniform_scalar_sum_sharp {ε : ℝ} {N : ℕ} (he : |ε| ≤ 1) (hN : 0 < N)
    (hstep : step N ≤ ε^2) :
    |(∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 := by
  have hR := mesh_term_remainder_sharp he hN
  have hC := coefficientSum_error_sharp hN
  have hc : |ε^2*(coefficientSum N+13/6000)| ≤ ε^4 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc
      ε^2*|coefficientSum N+13/6000| ≤ ε^2*step N :=
        mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      _ ≤ ε^2*ε^2 := mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ = ε^4 := by ring
  have hid : (∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
      (1/2-(13/6000:ℝ)*ε^2) =
      ((∑ j : Fin N, normalizedTerm ε (mesh N j) (mesh N (j+1))) -
        (1/2+ε^2*coefficientSum N)) + ε^2*(coefficientSum N+13/6000) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (by linarith only [hR,hc])

lemma finiteFamily_expansion_sharp {ε : ℝ} (he : 0 < ε) (hε : ε ≤ 1) :
    |totalArea (finiteFamily ε he)/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 2*ε^4 := by
  rw [finiteFamily_total]
  exact uniform_scalar_sum_sharp (by rwa [abs_of_pos he])
    (ceil_count_pos he) (ceil_step_le he)

lemma finiteFamily_ratio_lt_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    totalArea (finiteFamily ε he)/H < 1/2 := by
  have hε : ε ≤ 1 := by linarith only [hsmall]
  have hr := (abs_le.mp (finiteFamily_expansion_sharp he hε)).2
  have hesq : ε^2 ≤ (1/2000:ℝ)^2 :=
    (sq_le_sq₀ he.le (by norm_num)).2 hsmall
  have hc : 2*ε^2 < (13/6000:ℝ) := by norm_num at hesq; linarith only [hesq]
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos he) (sub_neg.mpr hc)
  nlinarith only [hr,hneg]

lemma finiteFamily_strict_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    totalArea (finiteFamily ε he) < A_min/2 := by
  rw [projection_minimum]
  have h := (div_lt_iff₀ H_pos).mp (finiteFamily_ratio_lt_closed he hsmall)
  linarith only [h]

lemma finiteFamily_relative_lt_closed {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ 1/2000) :
    relativeCost (finiteFamily ε he) < 1/2 :=
  (relativeCost_le_totalArea _).trans_lt (finiteFamily_ratio_lt_closed he hsmall)

lemma finiteFamily_explicit (ε : ℝ) (he : 0 < ε) :
    ExplicitAngularFamily ε (finiteFamily ε he) := by
  intro j
  simp only [lowerAngularIndex,upperAngularIndex,finiteFamily,Function.comp_apply,
    Fin.cast_cast,Fin.cast_eq_self,Fin.append_left,Fin.append_right]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem angularArea_result : AngularAreaStatement := by
  intro ε he hε
  exact ⟨finiteFamily ε he,finiteFamily_explicit ε he,finiteFamily_total ε he,
    finiteFamily_expansion_sharp he hε⟩

theorem explicitAngular_result : ExplicitAngularStatement := by
  refine ⟨projection_minimum,?_⟩
  intro ε he hsmall
  have hη : ε ≤ η/2 := by norm_num [η]; exact hsmall
  have hε : ε ≤ 1 := by linarith only [hsmall]
  exact ⟨finiteFamily ε he,finiteFamily_explicit ε he,finiteFamily_covers he hη,
    finiteFamily_expansion_sharp he hε,finiteFamily_strict_closed he hsmall,
    finiteFamily_relative_lt_closed he hsmall⟩

end TriangularCovering

end

end OAI
