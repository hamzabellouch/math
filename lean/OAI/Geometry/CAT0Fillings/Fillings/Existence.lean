import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.GeneralPush
import OAI.Geometry.CAT0Fillings.Prism.ClosedFamily

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
universe u

lemma IsCAT0.exists_lipschitz_contraction {X : Type u} [MetricSpace X]
    (hX : IsCAT0 X) (o : X) (R : ℝ≥0) (hR : ∀ x, dist o x ≤ R) :
    ∃ f : ClosedCylinder X → X, LipschitzWith (1+R) f ∧
      (∀ x, f (⟨0,by constructor <;> norm_num⟩,x) = o) ∧
      (∀ x, f (⟨1,by constructor <;> norm_num⟩,x) = x) := by
  obtain ⟨s,hs,hseg,hcomp⟩ := hX
  have hsame (x y : X) (t : Icc (0:ℝ) 1) : dist (s o x t) (s o y t) ≤ t.val*dist x y := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg t.2.1 dist_nonneg)).mp
    calc dist (s o x t) (s o y t)^2 ≤
        (t.val*dist o x-t.val*dist o y)^2 +
          t.val*t.val*(dist x y^2-(dist o x-dist o y)^2) := hcomp o x y t t t.2 t.2
      _ = (t.val*dist x y)^2 := by ring
  refine ⟨fun p => s o p.2 p.1,?_,fun x => (hs o x).1,fun x => (hs o x).2⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hdspace : dist p.2 q.2 ≤ dist p q := le_max_right _ _
  have hdtime : |p.1.val-q.1.val| ≤ dist p q := by
    change dist (p.1.val) (q.1.val) ≤ max (dist p.1 q.1) (dist p.2 q.2)
    exact le_max_left _ _
  calc
    dist (s o p.2 p.1) (s o q.2 q.1) ≤
        dist (s o p.2 p.1) (s o q.2 p.1) + dist (s o q.2 p.1) (s o q.2 q.1) :=
      dist_triangle _ _ _
    _ ≤ p.1.val*dist p.2 q.2+|p.1.val-q.1.val| *dist o q.2 := by
      rw [hseg o q.2 p.1 q.1 p.1.2 q.1.2]
      exact add_le_add (hsame p.2 q.2 p.1) le_rfl
    _ ≤ dist p.2 q.2+|p.1.val-q.1.val| *(R:ℝ) := by
      exact add_le_add (mul_le_of_le_one_left dist_nonneg p.1.2.2)
        (mul_le_mul_of_nonneg_left (hR _) (abs_nonneg _))
    _ ≤ dist p q+dist p q*(R:ℝ) :=
      add_le_add hdspace (mul_le_mul_of_nonneg_right hdtime R.coe_nonneg)
    _ = (↑(1+R):ℝ)*dist p q := by push_cast; ring

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem IsCAT0.exists_integral_filling (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T := by
  classical
  let o : X := Classical.choice inferInstance
  let R : ℝ≥0 := ⟨Metric.diam (Set.univ : Set X),Metric.diam_nonneg⟩
  have hR (x : X) : dist o x ≤ R :=
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  obtain ⟨f,hf,hf0,hf1⟩ := hX.exists_lipschitz_contraction o R hR
  let : Nonempty (ClosedCylinder X) := ⟨(⟨0,by constructor <;> norm_num⟩,o)⟩
  obtain ⟨C,hd,hC,hs,heq⟩ := hT.2.1
  let S := pushCurrent f (closedPrismFamily C)
  have hb : boundarySucc S = T := by
    funext b π
    by_cases hab : Admissible b π
    · dsimp [S]
      rw [pushCurrent_boundarySucc _ hf,pushCurrent_apply _ _ hab,
        closedPrismFamily_boundary_cycle hT.1 hT.2.1 hz C hs heq _ _
          (admissible_comp hab hf)]
      simp only [Function.comp_apply,hf0,hf1]
      have hz' : T (fun _ => b o) (fun j _ => π j o) = 0 :=
        hT.1.eq_zero_of_const_coord
          ⟨BoundedLip.const _,fun j => ⟨0,LipschitzWith.const _⟩⟩ 0 (π 0 o) (fun _ => rfl)
      rw [hz',sub_zero]
    · simp only [boundarySucc,ite_eq_right hab,hT.1.offDomain b π hab]
  refine ⟨S,⟨?_,?_,?_,?_⟩,hb⟩
  · exact pushCurrent_isMetricCurrent (closedPrismFamily_current C hs) hf
  · exact integerRectifiable_push (closedPrismFamily_rectifiable C hd hs) hf
  · rw [hb]
    exact hT.1
  · rw [hb]
    exact hT.2.1

end CAT0Fillings
end
end

end OAI
