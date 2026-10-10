import OAI.Geometry.SurfaceImmersion.Whitney.RegularPathCornerChart

namespace OAI

/-! Reversing both chart coordinates interchanges the two horizontal
orientations without changing the actual surface branches. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q} {t : ℝ}
namespace RegularPathCornerChart

def reflect (C : RegularPathCornerChart γ t) : RegularPathCornerChart γ t := by
  let e : Base ≃L[ℝ] Base := ContinuousLinearEquiv.neg ℝ
  let q := C.chart.trans e.toHomeomorph.toOpenPartialHomeomorph
  let l := C.leftParameter.trans (Homeomorph.neg ℝ)
  let r := C.rightParameter.trans (Homeomorph.neg ℝ)
  have hql : ContMDiffOn planeModel 𝓘(ℝ,Base) ∞ q q.source :=
    e.contDiff.contMDiff.comp_contMDiffOn (C.chart_smooth.mono inter_subset_left)
  have hqr : ContMDiffOn 𝓘(ℝ,Base) planeModel ∞ q.symm q.target :=
    C.inverse_smooth.comp e.symm.contDiff.contMDiff.contMDiffOn (fun _ hx => hx.2)
  have hlf : ContDiff ℝ ∞ l := contDiff_neg.comp C.left_parameter_smooth
  have hrf : ContDiff ℝ ∞ r := contDiff_neg.comp C.right_parameter_smooth
  have hli : ContDiff ℝ ∞ l.symm := C.left_inverse_smooth.comp contDiff_neg
  have hri : ContDiff ℝ ∞ r.symm := C.right_inverse_smooth.comp contDiff_neg
  have hlm : StrictMono l ∨ StrictAnti l := by
    rcases C.left_monotone with h | h
    · exact Or.inr (fun _ _ hxy => neg_lt_neg (h hxy))
    · exact Or.inl (fun _ _ hxy => neg_lt_neg (h hxy))
  have hrm : StrictMono r ∨ StrictAnti r := by
    rcases C.right_monotone with h | h
    · exact Or.inr (fun _ _ hxy => neg_lt_neg (h hxy))
    · exact Or.inl (fun _ _ hxy => neg_lt_neg (h hxy))
  refine ⟨q,hql,hqr,(fun x => -C.leftGraph (-x)),(fun x => -C.rightGraph (-x)),
    (C.left_smooth.comp contDiff_neg).neg,(C.right_smooth.comp contDiff_neg).neg,
    l,r,hlf,hrf,hli,hri,hlm,hrm,C.lower,C.upper,C.lower_pos,C.lower_lt,C.lt_upper,C.upper_lt_one,
    ?_,?_,?_⟩
  · intro u hu
    have h := C.left_chart u hu
    refine ⟨⟨h.1,mem_univ _⟩,?_⟩
    change -C.chart (γ.extend u) = ![-C.leftParameter u,-C.leftGraph (- -C.leftParameter u)]
    rw [h.2]
    ext i
    fin_cases i <;> simp
  · intro u hu
    have h := C.right_chart u hu
    refine ⟨⟨h.1,mem_univ _⟩,?_⟩
    change -C.chart (γ.extend u) = ![-C.rightParameter u,-C.rightGraph (- -C.rightParameter u)]
    rw [h.2]
    ext i
    fin_cases i <;> simp
  · change -C.leftParameter t = -C.rightParameter t
    rw [C.parameter_match]

@[simp] lemma reflect_leftParameter_apply (C : RegularPathCornerChart γ t) (u : ℝ) :
    C.reflect.leftParameter u = -C.leftParameter u := rfl

@[simp] lemma reflect_rightParameter_apply (C : RegularPathCornerChart γ t) (u : ℝ) :
    C.reflect.rightParameter u = -C.rightParameter u := rfl

@[simp] lemma reflect_lower (C : RegularPathCornerChart γ t) : C.reflect.lower = C.lower := rfl
@[simp] lemma reflect_upper (C : RegularPathCornerChart γ t) : C.reflect.upper = C.upper := rfl

lemma reflect_left_strictMono (C : RegularPathCornerChart γ t) (h : StrictAnti C.leftParameter) :
    StrictMono C.reflect.leftParameter := fun _ _ hxy => neg_lt_neg (h hxy)
lemma reflect_left_strictAnti (C : RegularPathCornerChart γ t) (h : StrictMono C.leftParameter) :
    StrictAnti C.reflect.leftParameter := fun _ _ hxy => neg_lt_neg (h hxy)
lemma reflect_right_strictMono (C : RegularPathCornerChart γ t) (h : StrictAnti C.rightParameter) :
    StrictMono C.reflect.rightParameter := fun _ _ hxy => neg_lt_neg (h hxy)
lemma reflect_right_strictAnti (C : RegularPathCornerChart γ t) (h : StrictMono C.rightParameter) :
    StrictAnti C.reflect.rightParameter := fun _ _ hxy => neg_lt_neg (h hxy)

end RegularPathCornerChart
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
