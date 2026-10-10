import OAI.Analysis.CircleDomains.Topology.LogarithmicDiskLift

namespace OAI

/-! Two explicit argument cuts give local logarithmic branches on any
topological source of a continuous punctured-disk map. No local
connectedness of the source is needed for this chart construction. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

def logarithmicCutChart (a : ℝ) (w : ℂ) : ℂ :=
  ((AddCircle.equivIco (1 : ℝ) a (normalizedArgument w) : ℝ) : ℂ) +
    ((-Real.log ‖w‖ : ℝ) : ℂ) * Complex.I

theorem logarithmicCutChart_nonneg (a : ℝ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    0 ≤ (logarithmicCutChart a w).im := by
  change 0 ≤ (((AddCircle.equivIco (1 : ℝ) a (normalizedArgument w) : ℝ) : ℂ) +
    ((-Real.log ‖w‖ : ℝ) : ℂ) * Complex.I).im
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add] using neg_nonneg.mpr (Real.log_nonpos (norm_nonneg w) hw)

theorem logarithmicCutChart_projection (a : ℝ) {w : ℂ} (hw : w ≠ 0) :
    diskRayProjection (logarithmicCutChart a w) = w := by
  apply Complex.ext_norm_arg
  · rw [diskRayProjection_norm]
    simp only [logarithmicCutChart, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add, neg_neg]
    exact Real.exp_log (norm_pos_iff.mpr hw)
  · apply Complex.arg_coe_angle_eq_iff.mp
    apply (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective
    change normalizedArgument (diskRayProjection (logarithmicCutChart a w)) =
      normalizedArgument w
    rw [diskRayProjection_argument]
    simp only [logarithmicCutChart, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    exact AddCircle.coe_equivIco

theorem continuousAt_logarithmicCutChart (a : ℝ) {w : ℂ} (hw : w ≠ 0)
    (ha : normalizedArgument w ≠ (a : UnitAddCircle)) :
    ContinuousAt (logarithmicCutChart a) w := by
  have hangle := continuous_subtype_val.continuousAt.comp
    ((AddCircle.continuousAt_equivIco (1 : ℝ) a ha).comp
      (continuousAt_normalizedArgument hw))
  exact (Complex.continuous_ofReal.continuousAt.comp hangle).add
    ((Complex.continuous_ofReal.continuousAt.comp
      ((continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr hw)).neg)).mul_const _)

def logarithmicCutDomain {X : Type*} (F : X → ℂ) (S : Set X) (a : ℝ) : Set X :=
  {x | x ∈ S ∧ normalizedArgument (F x) ≠ (a : UnitAddCircle)}

theorem isOpen_logarithmicCutDomain {X : Type*} [TopologicalSpace X]
    (F : X → ℂ) (hF : Continuous F) {S : Set X} (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (a : ℝ) : IsOpen (logarithmicCutDomain F S a) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have harg : ContinuousAt (fun y => normalizedArgument (F y)) x :=
    (continuousAt_normalizedArgument (h0 x hx.1)).comp hF.continuousAt
  exact inter_mem (hS.mem_nhds hx.1)
    (harg.eventually (isOpen_ne.mem_nhds hx.2))

theorem logarithmicCutDomain_cover {X : Type*} (F : X → ℂ) (S : Set X) :
    S ⊆ logarithmicCutDomain F S 0 ∪ logarithmicCutDomain F S (1 / 2) := by
  intro x hx
  by_cases h : normalizedArgument (F x) = (0 : UnitAddCircle)
  · right
    refine ⟨hx, ?_⟩
    rw [h]
    intro he
    have hh := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (0 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)
      (show (1 / 2 : ℝ) ∈ Ico 0 (0 + 1) by norm_num)).mp he
    norm_num at hh
  · exact Or.inl ⟨hx, h⟩

end CircleDomainRigidity

end

end OAI
