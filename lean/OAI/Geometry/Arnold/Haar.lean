import OAI.Geometry.Arnold.Tangent

namespace OAI

universe uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter

open scoped BigOperators
open MeasureTheory Set Filter

namespace ArnoldCounterexample.CriticalBound

/-- Compactness supplies the uniform domination needed to differentiate a
parameter integral. This gives differentiation under the Haar integral. -/
theorem hasDerivAt_integral_of_compact
    {G : Type uG} [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    {F F' : ℝ → G → ℝ}
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ t g, HasDerivAt (fun s ↦ F s g) (F' t g) t) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ g, F s g ∂μ) (∫ g, F' t g ∂μ) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set G))).exists_bound_of_continuousOn
    (hF'.continuousOn : ContinuousOn (Function.uncurry F') (Icc (t - 1) (t + 1) ×ˢ univ))
  have hcont (s : ℝ) : Continuous (F s) := hF.comp (continuous_const.prodMk continuous_id)
  have hcont' (s : ℝ) : Continuous (F' s) := hF'.comp (continuous_const.prodMk continuous_id)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Icc (t - 1) (t + 1)) (bound := fun _ : G ↦ C) ?_ ?_ ?_
    (hcont' t).aestronglyMeasurable ?_ (integrable_const C) ?_).2
  · exact Icc_mem_nhds (by linarith) (by linarith)
  · exact Filter.Eventually.of_forall (fun s ↦ (hcont s).aestronglyMeasurable)
  · exact (hcont t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact Filter.Eventually.of_forall (fun g s hs ↦ hC (s, g) ⟨hs, mem_univ g⟩)
  · exact Filter.Eventually.of_forall (fun g s _ ↦ hd s g)

/-- The integral of a smooth infinitesimal right-translation is zero. Unlike
a manifold Stokes interface, this is proved directly from Haar invariance and
differentiation under a finite integral. -/
theorem integral_derivative_right_translate_eq_zero
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasure μ] [μ.IsMulRightInvariant]
    (c : ℝ → G) (hc : Continuous c) (f : G → ℝ) (hf : Continuous f)
    (D : ℝ → G → ℝ) (hD : Continuous (Function.uncurry D))
    (hd : ∀ t g, HasDerivAt (fun s ↦ f (g * c s)) (D t g) t) (t : ℝ) :
    ∫ g, D t g ∂μ = 0 := by
  have h := hasDerivAt_integral_of_compact μ
    (F := fun s g ↦ f (g * c s)) (F' := D)
    (by fun_prop) hD hd t
  have heq : (fun s ↦ ∫ g, f (g * c s) ∂μ) = fun _ : ℝ ↦ ∫ g, f g ∂μ := by
    funext s
    exact integral_mul_right_eq_self f (c s)
  rw [heq] at h
  exact h.unique (hasDerivAt_const t _)

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound

abbrev RM := Matrix (Fin 5) (Fin 5) ℝ
abbrev O5 := Matrix.orthogonalGroup (Fin 5) ℝ

lemma orthogonal_row_sq (A : O5) (i : Fin 5) : ∑ j, (A.val i j) ^ 2 = 1 := by
  have h := congrFun (congrFun A.property.2 i) i
  simpa [Matrix.mul_apply, Matrix.star_apply, pow_two] using h

lemma orthogonal_entry_abs_le_one (A : O5) (i j : Fin 5) : |A.val i j| ≤ 1 := by
  have hj : (A.val i j) ^ 2 ≤ ∑ k, (A.val i k) ^ 2 :=
    Finset.single_le_sum (fun k _ ↦ sq_nonneg (A.val i k)) (Finset.mem_univ j)
  rw [orthogonal_row_sq] at hj
  exact (sq_le_one_iff_abs_le_one _).mp hj

/-- The actual real orthogonal matrix group is compact; no compact Lie-group
or integration-on-manifolds library is being assumed. -/
theorem isCompact_orthogonalGroup : IsCompact (Matrix.orthogonalGroup (Fin 5) ℝ : Set RM) := by
  have hc : IsCompact (Set.Icc (fun _ _ : Fin 5 ↦ (-1 : ℝ)) (fun _ _ : Fin 5 ↦ (1 : ℝ))) :=
    isCompact_Icc
  have hclosed : IsClosed (Matrix.orthogonalGroup (Fin 5) ℝ : Set RM) := isClosed_unitary
  apply hc.of_isClosed_subset hclosed
  intro A hA
  constructor <;> intro i j
  · exact (abs_le.mp (orthogonal_entry_abs_le_one ⟨A, hA⟩ i j)).1
  · exact (abs_le.mp (orthogonal_entry_abs_le_one ⟨A, hA⟩ i j)).2

instance o5_compactSpace : CompactSpace O5 :=
  isCompact_iff_compactSpace.mp isCompact_orthogonalGroup

instance o5_measurableSpace : MeasurableSpace O5 := borel O5
instance o5_borelSpace : BorelSpace O5 := ⟨rfl⟩

def haar : Measure O5 := (Measure.haar : Measure O5).inv

example : IsFiniteMeasure haar := by dsimp [haar]; infer_instance
example : haar.IsMulRightInvariant := by dsimp [haar]; infer_instance
example : haar.IsOpenPosMeasure := by dsimp [haar]; infer_instance

end ArnoldCounterexample.CriticalBound

open scoped Matrix.Norms.Operator ContDiff

namespace ArnoldCounterexample.CriticalBound

local instance : @ContinuousStar RM
    (Matrix.linftyOpNormedRing (n := Fin 5) (α := ℝ)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace _ := ⟨by
  change Continuous (fun A : RM ↦ A.transpose)
  fun_prop⟩

instance haar_finite : IsFiniteMeasure haar := by dsimp [haar]; infer_instance
instance haar_rightInvariant : haar.IsMulRightInvariant := by dsimp [haar]; infer_instance
instance haar_openPos : haar.IsOpenPosMeasure := by dsimp [haar]; infer_instance

/-- The actual one-parameter subgroup generated by a skew real matrix. -/
def expCurve (X : RM) (hX : star X = -X) (t : ℝ) : O5 :=
  ⟨NormedSpace.exp (t • X), NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (by
    rw [skewAdjoint.mem_iff, star_smul, star_trivial, hX, smul_neg])⟩

lemma expCurve_continuous (X : RM) (hX : star X = -X) : Continuous (expCurve X hX) := by
  exact (differentiable_exp_smul_const ℝ X).continuous.subtype_mk _

lemma right_expCurve_hasDerivAt (X : RM) (hX : star X = -X) (A : O5) (t : ℝ) :
    HasDerivAt (fun s ↦ ((A * expCurve X hX s : O5) : RM))
      (((A * expCurve X hX t : O5) : RM) * X) t := by
  convert! (hasDerivAt_exp_smul_const X t).const_mul (A : RM) using 1
  exact mul_assoc _ _ _

/-- Integration kills every left-invariant directional derivative of a C1
ambient function on this compact orthogonal group. -/
theorem integral_fderiv_mul_skew_eq_zero (f : RM → ℝ) (hf : ContDiff ℝ ∞ f)
    (X : RM) (hX : star X = -X) :
    ∫ A : O5, fderiv ℝ f (A : RM) ((A : RM) * X) ∂haar = 0 := by
  let D : ℝ → O5 → ℝ := fun t A ↦
    fderiv ℝ f ((A * expCurve X hX t : O5) : RM)
      (((A * expCurve X hX t : O5) : RM) * X)
  have hparam : Continuous (fun p : ℝ × O5 ↦ ((p.2 * expCurve X hX p.1 : O5) : RM)) := by
    exact continuous_subtype_val.comp
      (continuous_snd.mul ((expCurve_continuous X hX).comp continuous_fst))
  have hD : Continuous (Function.uncurry D) := by
    exact (hf.continuous_fderiv (by simp)).comp hparam |>.clm_apply
      (hparam.mul continuous_const)
  have hd (t : ℝ) (A : O5) : HasDerivAt (fun s ↦ f ((A * expCurve X hX s : O5) : RM))
      (D t A) t := by
    exact ((hf.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t
      (right_expCurve_hasDerivAt X hX A t)
  have h := integral_derivative_right_translate_eq_zero haar
    (expCurve X hX) (expCurve_continuous X hX) (fun A : O5 ↦ f (A : RM))
    (hf.continuous.comp continuous_subtype_val) D hD hd 0
  simpa [D, expCurve] using h

end ArnoldCounterexample.CriticalBound

end

end OAI
