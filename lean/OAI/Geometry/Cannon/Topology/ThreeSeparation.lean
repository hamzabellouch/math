import Mathlib
import OAI.Geometry.Cannon.Topology.ThreeMarksAvoidTwo
import OAI.Geometry.Cannon.Conformal.MarkedChart

namespace OAI

section
noncomputable section
namespace CannonFiniteNormalization
open Set Metric Topology CannonMobius
open scoped OnePoint

lemma three_separation {X : Type*} [MetricSpace X] (v : Fin 3 → X)
    (hv : Function.Injective v) :
    ∃ s : ℝ,0<s ∧ ∀ i j,i≠j → s≤dist (v i) (v j) := by
  let s:=min (dist (v 0) (v 1)) (min (dist (v 0) (v 2)) (dist (v 1) (v 2)))
  have hpos (i j : Fin 3) (hij : i≠j) : 0<dist (v i) (v j):=dist_pos.mpr (hv.ne hij)
  refine ⟨s,lt_min (hpos 0 1 (by decide)) (lt_min (hpos 0 2 (by decide)) (hpos 1 2 (by decide))),?_⟩
  have h01 : s≤dist (v 0) (v 1):=min_le_left _ _
  have h02 : s≤dist (v 0) (v 2):=(min_le_right _ _).trans (min_le_left _ _)
  have h12 : s≤dist (v 1) (v 2):=(min_le_right _ _).trans (min_le_right _ _)
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact h01
  · exact h02
  · rwa [dist_comm]
  · exact h12
  · rwa [dist_comm]
  · rwa [dist_comm]

theorem uniform_relative_chart_selection :
    ∃ C : ℝ,1≤C ∧ ∀ {X : Type*},∀ [MetricSpace X],
    ∀ (f : X → Sphere) (v : Fin 3 → X) (s : ℝ),0<s →
      (∀ i j,i≠j → s≤dist (v i) (v j)) → (∀ i,f (v i)=std i) →
    ∀ (o b : X) (R : ℝ), R ≤ s / 2 → R≤dist o b →
      ∃ i : Fin 3,R≤dist o (v i) ∧ ∃ u : X,R≤dist o u ∧
        ∃ x p : ℂ,markedChart i (f o)=(x:Sphere) ∧
          markedChart i (f u)=(p:Sphere) ∧ dist x p≤C*dist (f o) (f b) := by
  obtain ⟨t,ht,hstd⟩:=three_separation std std_injective
  let δ:=t/4
  have hδ : 0<δ:=by dsimp [δ]; positivity
  obtain ⟨B,hB,hbound⟩:=coordinate_bound_away_pole hδ
  let C:=max 1 (max (B^2+4) ((B+4)/δ))
  have hC : 1≤C:=le_max_left _ _
  have hC1 : B^2+4≤C:=(le_max_left _ _).trans (le_max_right _ _)
  have hC2 : (B+4)/δ≤C:=(le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro X _ f v s hs hv hmark o b R hRs hb
  obtain ⟨i,hi,hfi⟩:=three_marks_two_metrics v std hv hstd o (f o)
  have hdist (y : Sphere) : dist (markedChart i y) ∞=dist y (std i) := by
    rw [←markedChart_pole i]
    exact (markedChart_isometry i).dist_eq _ _
  have hxo : markedChart i (f o)≠∞ := by
    intro he
    have hh:=hdist (f o)
    rw [he,dist_self] at hh
    linarith
  obtain ⟨x,hx⟩:=OnePoint.ne_infty_iff_exists.mp hxo
  have hxn : ‖x‖≤B := by
    apply hbound
    rw [hx,hdist]
    exact (by dsimp [δ]; linarith : δ≤t/2).trans hfi
  by_cases hsmall : dist (f o) (f b)<δ
  · have hbfar : δ≤dist (markedChart i (f b)) ∞ := by
      rw [hdist]
      have hh:=dist_triangle (f o) (f b) (std i)
      dsimp [δ] at *
      linarith
    have hbfin : markedChart i (f b)≠∞ := by intro he; rw [he,dist_self] at hbfar; linarith
    obtain ⟨p,hp⟩:=OnePoint.ne_infty_iff_exists.mp hbfin
    refine ⟨i,hRs.trans hi,b,hb,x,p,hx.symm,hp.symm,?_⟩
    have hpn : ‖p‖≤B:=hbound p (by rwa [hp])
    calc
      dist x p ≤ (B^2+4)*dist (x:Sphere) (p:Sphere):=coordinate_comparison (by linarith) hxn hpn
      _ = (B^2+4)*dist (f o) (f b):=by rw [hx,hp,(markedChart_isometry i).dist_eq]
      _ ≤ C*dist (f o) (f b):=mul_le_mul_of_nonneg_right hC1 dist_nonneg
  · obtain ⟨j,hj,hij⟩:=three_marks_avoid_two_points v hv o (v i)
    have hne : i≠j := by intro he; rw [he,dist_self] at hij; linarith
    obtain ⟨p,hp,hpn⟩:=markedChart_other i j hne
    refine ⟨i,hRs.trans hi,v j,hRs.trans hj,x,p,hx.symm,by rw [hmark,hp],?_⟩
    calc
      dist x p ≤ ‖x‖+‖p‖:=dist_le_norm_add_norm _ _
      _ ≤ B+4:=add_le_add hxn hpn
      _ = ((B+4)/δ)*δ:=by field_simp
      _ ≤ ((B+4)/δ)*dist (f o) (f b):=mul_le_mul_of_nonneg_left (le_of_not_gt hsmall) (by positivity)
      _ ≤ C*dist (f o) (f b):=mul_le_mul_of_nonneg_right hC2 dist_nonneg
end CannonFiniteNormalization

end
end

end OAI
