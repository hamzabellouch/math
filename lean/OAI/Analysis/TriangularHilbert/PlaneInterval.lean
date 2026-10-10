import OAI.Analysis.TriangularHilbert.JointMeasurable

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section

lemma intervalIntegrable_of_clamped {f g : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hg : StronglyMeasurable g) (hbound : ∀ t, ‖g t‖ ≤ C)
    (he : ∀ t ∈ Set.Icc a b, f t = g t) : IntervalIntegrable f volume a b := by
  have hi : IntervalIntegrable g volume a b :=
    intervalIntegrable_const.mono_fun' hg.aestronglyMeasurable (Eventually.of_forall hbound)
  apply hi.congr
  rw [Set.uIoc_of_le hab]
  exact fun t ht => (he t ⟨ht.1.le,ht.2⟩).symm

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma planeTime_intervalIntegrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) (α : Three → ℝ) (hα : ∀ w, 0 < α w)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatVariance A h u p (fun z => α z*t) v w) d) volume a b) ∧
    (∀ v w, IntervalIntegrable (fun t => planeIntegral (fun p => heatCost A h u p (fun z => α z*t) v w) d) volume a b) := by
  let T : ℝ → ℝ := fun t => max a (min b t)
  have hT : Continuous T := by unfold T; fun_prop
  have hTl (t : ℝ) : a ≤ T t := le_max_left _ _
  have hTu (t : ℝ) : T t ≤ b := max_le hab (min_le_left _ _)
  have hTe (t : ℝ) (ht : t ∈ Set.Icc a b) : T t = t := by
    simp [T,min_eq_right ht.2,max_eq_right ht.1]
  let σ : ℝ → Three → ℝ := fun t w => α w*T t
  have hσ : Continuous σ := by apply continuous_pi; intro w; exact continuous_const.mul hT
  have hpos (t : ℝ) (w : Three) : 0 < σ t w := mul_pos (hα w) (ha.trans_le (hTl t))
  obtain ⟨l,r,hl,hlr,hlo,hhi⟩ := finite_variance_bounds α hα
  obtain ⟨B,hB,_,hbound⟩ := exists_heat_uniform_majorant A hh (mul_pos hl ha)
    (show l*a ≤ r*b from mul_le_mul hlr hab ha.le (hl.trans_le hlr).le) (abs_nonneg d) u
  have hb t z : HeatAtBounds A h u (chart 2 d z) (σ t) (B z) :=
    hbound 2 d z le_rfl (σ t)
      (fun w => mul_le_mul (hlo w) (hTl t) ha.le (hα w).le)
      (fun w => mul_le_mul (hhi w) (hTu t) (ha.trans_le (hTl t)).le (hl.trans_le hlr).le)
  have hp : Continuous (fun q : ℝ × (ℝ×ℝ) => chart 2 d q.2) :=
    (chart_continuous 2).comp (continuous_const.prodMk continuous_snd)
  have hσq : Continuous (fun q : ℝ × (ℝ×ℝ) => σ q.1) := hσ.comp continuous_fst
  have hclamp (f : ℝ → (Three → ℝ) → ℝ)
      (hm : Measurable (fun q : ℝ × (ℝ×ℝ) => f q.1 (chart 2 d q.2)))
      (hbo : ∀ t z, ‖f t (chart 2 d z)‖ ≤ B z) :
      StronglyMeasurable (fun t => planeIntegral (f t) d) ∧
      ∀ t, ‖planeIntegral (f t) d‖ ≤ ∫ z, B z :=
    ⟨hm.stronglyMeasurable.integral_prod_right,fun t => norm_integral_le_of_norm_le hB (Eventually.of_forall (hbo t))⟩
  constructor
  · intro v w
    have hc := hclamp (fun t p => heatVariance A h u p (σ t) v w)
      (continuous_heatVariance_param A hh u hp hσq (fun q z => hpos q.1 z) v w).measurable
      (fun t z => (hb t z).variance v w)
    apply intervalIntegrable_of_clamped hab hc.1 hc.2
    intro t ht
    simp only [σ,hTe t ht]
  · intro v w
    have hc := hclamp (fun t p => heatCost A h u p (σ t) v w)
      (measurable_heatCost_param A hh u hp hσq (fun q z => hpos q.1 z) v w)
      (fun t z => (hb t z).cost v w)
    apply intervalIntegrable_of_clamped hab hc.1 hc.2
    intro t ht
    simp only [σ,hTe t ht]
end
end TriangularHilbert.Heat
end

end OAI
