import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.GeneralPush
import OAI.Geometry.CAT0Fillings.Prism.ClosedFamily
import OAI.Geometry.CAT0Fillings.Prism.ConeMass

namespace OAI

section
section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set
open scoped NNReal

lemma IsCAT0.exists_mixed_contraction {X : Type*} [MetricSpace X]
    (hX : IsCAT0 X) (o : X) (R : ℝ≥0) (hR : ∀ x, dist o x ≤ R) :
    ∃ f : ℝ × X → X, LipschitzWith (1+R) f ∧
      (∀ x, LipschitzWith R (fun t : ℝ => f (t,x))) ∧
      (∀ t, LipschitzWith 1 (fun x : X => f (t,x))) ∧
      (∀ x, f (0,x) = o) ∧ (∀ x, f (1,x) = x) := by
  obtain ⟨s,hs,hseg,hcomp⟩ := hX
  let a : ℝ → Icc (0:ℝ) 1 := projIcc 0 1 (by norm_num)
  have ha : LipschitzWith 1 a := LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1)
  let f : ℝ × X → X := fun p => s o p.2 (a p.1)
  have hspace (t : ℝ) : LipschitzWith 1 (fun x : X => f (t,x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    have hh : dist (f (t,x)) (f (t,y)) ≤ (a t).val*dist x y := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg (a t).2.1 dist_nonneg)).mp
      calc
        _ ≤ ((a t).val*dist o x-(a t).val*dist o y)^2 +
            (a t).val*(a t).val*(dist x y^2-(dist o x-dist o y)^2) :=
          hcomp o x y (a t) (a t) (a t).2 (a t).2
        _ = _ := by ring
    exact hh.trans (mul_le_of_le_one_left dist_nonneg (a t).2.2)
  have htime (x : X) : LipschitzWith R (fun t : ℝ => f (t,x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    change dist (s o x (a t)) (s o x (a r)) ≤ _
    rw [hseg o x (a t) (a r) (a t).2 (a r).2]
    have hh : |(a t).val-(a r).val| ≤ dist t r := by
      simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq,Real.dist_eq] using ha.dist_le_mul t r
    calc
      _ ≤ dist t r * (R:ℝ) := mul_le_mul hh (hR x) dist_nonneg dist_nonneg
      _ = _ := mul_comm _ _
  refine ⟨f,?_,htime,hspace,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : dist (f p) (f (p.1,q.2)) ≤ dist p.2 q.2 := by simpa using (hspace p.1).dist_le_mul p.2 q.2
    have h2 : dist (f (p.1,q.2)) (f q) ≤ (R:ℝ)*dist p.1 q.1 := (htime q.2).dist_le_mul _ _
    calc
      _ ≤ dist p.2 q.2 + (R:ℝ)*dist p.1 q.1 := (dist_triangle _ _ _).trans (add_le_add h1 h2)
      _ ≤ dist p q + (R:ℝ)*dist p q := add_le_add (le_max_right _ _)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) R.coe_nonneg)
      _ = _ := by push_cast; ring
  · intro x
    dsimp [f,a]
    rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]
    exact (hs o x).1
  · intro x
    dsimp [f,a]
    rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]
    exact (hs o x).2
end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem IsCAT0.exists_integral_filling_mass_le (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (o : X) (R : ℝ≥0) (hR : ∀ x, dist o x ≤ R) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S ≤ (k+2:ℝ)*(R:ℝ)*mass T := by
  classical
  obtain ⟨f,hf,ht,hs,hf0,hf1⟩ := hX.exists_mixed_contraction o R hR
  let g : ClosedCylinder X → X := f ∘ cylinderEmbed
  have hg : LipschitzWith (1+R) g := by
    simpa only [mul_one] using hf.comp cylinderEmbed_isometry.lipschitzWith
  let F : ℝ × X → X := g ∘ cylinderClamp
  have hF : LipschitzWith (1+R) F := by simpa only [mul_one] using hg.comp cylinderClamp_lipschitz
  have hFt (x : X) : LipschitzWith R (fun t : ℝ => F (t,x)) := by
    have ha := (LipschitzWith.subtype_val (Icc (0:ℝ) 1)).comp
      (LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1))
    simpa only [mul_one,Function.comp_def,F,g,cylinderEmbed,cylinderClamp] using (ht x).comp ha
  have hFs (t : ℝ) : LipschitzWith 1 (fun x : X => F (t,x)) := by
    dsimp only [F,g,cylinderEmbed,cylinderClamp,Function.comp_def]
    exact hs _
  let : Nonempty (ClosedCylinder X) := ⟨(⟨0,by constructor <;> norm_num⟩,o)⟩
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT.2.1
  let S := pushCurrent g (closedPrismFamily C)
  have hb : boundarySucc S = T := by
    funext b π
    by_cases hab : Admissible b π
    · dsimp [S]
      rw [pushCurrent_boundarySucc _ hg,pushCurrent_apply _ _ hab,
        closedPrismFamily_boundary_cycle hT.1 hT.2.1 hz C hCS heq _ _
          (admissible_comp hab hg)]
      simp only [Function.comp_apply,g,cylinderEmbed,hf0,hf1]
      have hz' : T (fun _ => b o) (fun j _ => π j o) = 0 :=
        hT.1.eq_zero_of_const_coord
          ⟨BoundedLip.const _,fun j => ⟨0,LipschitzWith.const _⟩⟩ 0 (π 0 o) (fun _ => rfl)
      rw [hz',sub_zero]
    · simp only [boundarySucc,ite_eq_right hab,hT.1.offDomain b π hab]
  refine ⟨S,⟨pushCurrent_isMetricCurrent (closedPrismFamily_current C hCS) hg,
    integerRectifiable_push (closedPrismFamily_rectifiable C hd hCS) hg,
    hb ▸ hT.1,hb ▸ hT.2.1⟩,hb,?_⟩
  have hseq : S = pushCurrent F (prismFamily C) := (pushCurrent_comp hg).symm
  rw [hseq]
  convert mass_prismFamily_cone_le hT.1 C hd hC hCS heq hF hFt hFs using 1
  push_cast
  ring

end CAT0Fillings
end
end

end OAI
