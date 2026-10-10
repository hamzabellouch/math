import OAI.Probability.InvariantIsing.Fields.FieldSpinVariance
import OAI.Probability.InvariantIsing.Magnetic.MagneticCurvatureLower

namespace OAI

/-! Conditional overlap increments are bounded by their variance
increments, uniformly in all preceding scalar-field levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldSpinTransition_sub (ζ : ℝ) (v : ℝ≥0) {F a b : ℝ → ℝ}
    (hF : Measurable F) (hg : HasLinearGrowth F) (ha : Measurable a) (hb : Measurable b)
    {A B : ℝ} (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (z : ℝ) :
    fieldSpinTransition ζ v F (fun u => a u - b u) z =
      fieldSpinTransition ζ v F a z - fieldSpinTransition ζ v F b z := by
  have he := integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments z v) hF hg ζ
  let : IsProbabilityMeasure ((gaussianReal z v).tilted (fun u => ζ * F u)) :=
    isProbabilityMeasure_tilted he
  exact integral_sub
    (Integrable.of_bound ha.aestronglyMeasurable A
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using haB u))
    (Integrable.of_bound hb.aestronglyMeasurable B
      (ae_of_all _ fun u => by simpa only [Real.norm_eq_abs] using hbB u))

theorem fieldScalarSquares_increment_le (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1)
    {V : ℝ} (hV : ∀ av ∈ L, (av.2 : ℝ) ≤ V) (i : Fin L.length) (z : ℝ) :
    fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.succ z -
      fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i.castSucc z ≤
        ((L.get i).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  induction L generalizing z with
  | nil => exact Fin.elim0 i
  | cons av L ih =>
    have ht := fun bv hb => hL bv (List.mem_cons_of_mem av hb)
    have htζ := fun bv hb => hζ bv (List.mem_cons_of_mem av hb)
    have htV := fun bv hb => hV bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L ht measurable_logCosh logCosh_linearGrowth
    have hmean := fieldScalarMean_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    have hreg := fieldScalarSquares_regular L ht measurable_logCosh logCosh_linearGrowth
      (by change Measurable (fun x : ℝ => Real.tanh x); simp only [Real.tanh_eq]; fun_prop)
      field_abs_tanh_le_one
    refine Fin.cases ?_ (fun j => ?_) i
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0) z -
        (fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
          (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh) z)^2 ≤ _
      have hzero : fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh 0 =
          fun y => (fieldScalarMean L (fun z => Real.log (Real.cosh z)) Real.tanh y)^2 := by
        funext y
        exact fieldScalarSquares_zero _ _ _ _
      rw [hzero]
      exact fieldSpinTransition_variance_le av.1
        ⟨(hL av List.mem_cons_self).le, hζ av List.mem_cons_self⟩ av.2
        (hV av List.mem_cons_self) hval.1 (fieldScalarLogCosh_lipschitz L ht)
        hmean.1 hmean.2 (fieldScalarLogCoshMean_dist_le L ht htζ) z
    · have hb (j : Fin (L.length + 1)) (u : ℝ) :
          |fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j u| ≤ 1 := by
        rw [abs_of_nonneg ((hreg j).2 u).1]
        exact ((hreg j).2 u).2
      change fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.succ) z -
        fieldSpinTransition av.1 av.2 _
          (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.castSucc) z ≤ _
      rw [← fieldSpinTransition_sub av.1 av.2 hval.1 hval.2
        (hreg j.succ).1 (hreg j.castSucc).1 (hb j.succ) (hb j.castSucc)]
      calc
        _ ≤ fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
            (fun _ => ((L.get j).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V)) z :=
          fieldSpinTransition_mono_test av.1 av.2 _
            ((hreg j.succ).1.sub (hreg j.castSucc).1) measurable_const
            (fun u => (abs_sub _ _).trans (add_le_add (hb j.succ u) (hb j.castSucc u)))
            (fun _ => le_rfl) (fun u => ih ht htζ htV j u) z
        _ = _ := fieldSpinTransition_const av.1 av.2 hval.1 hval.2 _ z

theorem fieldScalarOverlaps_increment_le (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) (hζ : ∀ av ∈ L, av.1 ≤ 1)
    {V : ℝ} (hV : ∀ av ∈ L, (av.2 : ℝ) ≤ V) (i : Fin L.length) :
    fieldScalarOverlaps L root (fun z => Real.log (Real.cosh z)) Real.tanh i.succ -
      fieldScalarOverlaps L root (fun z => Real.log (Real.cosh z)) Real.tanh i.castSucc ≤
        ((L.get i).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V) := by
  have ht : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hreg := fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    ht field_abs_tanh_le_one
  have hi (j : Fin (L.length + 1)) : Integrable
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j)
      (gaussianReal 0 root) := by
    apply Integrable.of_bound (hreg j).1.aestronglyMeasurable 1
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg ((hreg j).2 z).1]
      exact ((hreg j).2 z).2
  unfold fieldScalarOverlaps
  rw [← integral_sub (hi i.succ) (hi i.castSucc)]
  have hb := integral_mono ((hi i.succ).sub (hi i.castSucc)) (integrable_const _)
    (fieldScalarSquares_increment_le L hL hζ hV i)
  simpa only [integral_const, probReal_univ, one_smul, Pi.sub_apply] using hb

end InvariantIsing

end

end OAI
