import OAI.Geometry.SurfaceImmersion.Whitney.EqualIndexFrameFilling
import OAI.Geometry.SurfaceImmersion.Geometry.PlaneDefectInterpolation

namespace OAI

/-! Compact frame fillings are preserved by a homotopy whose only zeros stay
inside the fixed compact core. The pasting retains exact exterior values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def defectFrame (N : Base → Base) (x : Base) : Base →L[ℝ] FrameTarget :=
  axisNormalFrame 1 (N x 0) (N x 1)

lemma defectFrame_smooth {N : Base → Base} (hN : ContDiff ℝ ∞ N) :
    ContDiff ℝ ∞ (defectFrame N) := by
  have h : ContDiff ℝ ∞ (fun x => (![0,N x 0,N x 1] : FrameTarget)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (contDiff_apply ℝ ℝ 0).comp hN
    · exact (contDiff_apply ℝ ℝ 1).comp hN
  exact contDiff_const.add (contDiff_const.smulRight h)

lemma defectFrame_injective {N : Base → Base} {x : Base} (hN : N x ≠ 0) :
    Function.Injective (defectFrame N x) := by
  apply axisNormalFrame_injective (by norm_num)
  by_contra hn
  push Not at hn
  apply hN
  ext i
  fin_cases i
  · exact hn.1
  · exact hn.2

/-- The filling changes the frame only on a compact subset of the prescribed
open set; every point of that open set becomes regular. -/
def HasRelativeDefectFilling (N : Base → Base) (U : Set Base) : Prop :=
  ∃ (A : Base → Base →L[ℝ] FrameTarget) (K : Set Base),
    ContDiff ℝ ∞ A ∧ IsCompact K ∧ K ⊆ U ∧
    (∀ x ∈ U, Function.Injective (A x)) ∧
    ∀ x ∉ K, A x = defectFrame N x

theorem relativeDefectFilling_homotopy
    {H : ℝ → Base → Base} (hH : ContDiff ℝ ∞ (fun z : ℝ × Base => H z.1 z.2))
    {U Z : Set Base} (hU : IsOpen U) (hZ : IsCompact Z) (hZU : Z ⊆ U)
    (hz : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ U, x ∉ Z → H s x ≠ 0)
    (hfill : HasRelativeDefectFilling (H 1) U) :
    HasRelativeDefectFilling (H 0) U := by
  obtain ⟨B,K,hB,hK,hKU,hBI,hBe⟩ := hfill
  obtain ⟨χ,hχ,hχc,hχr,hχs,hχone⟩ :=
    CollarVelocity.compact_cutoff (hK.union hZ) hU (union_subset hKU hZU)
  let Q := fun s x => defectFrame (H s) x
  let A := fun x => B x+Q (χ x) x-Q 1 x
  have hQc : ContDiff ℝ ∞ (fun x => Q (χ x) x) :=
    defectFrame_smooth (hH.comp (hχ.prodMk contDiff_id))
  have hQ1 : ContDiff ℝ ∞ (Q 1) :=
    defectFrame_smooth (hH.comp (contDiff_const.prodMk contDiff_id))
  refine ⟨A,K ∪ tsupport χ,(hB.add hQc).sub hQ1,hK.union hχc,
    union_subset hKU hχs,?_,?_⟩
  · intro x hx
    by_cases he : χ x = 1
    · have hAB : A x = B x := by simp [A,he]
      rw [hAB]
      exact hBI x hx
    · have hxK : x ∉ K := fun hk => he (hχone x (Or.inl hk))
      have hxZ : x ∉ Z := fun hz' => he (hχone x (Or.inr hz'))
      have hAQ : A x = Q (χ x) x := by
        dsimp only [A]
        rw [hBe x hxK]
        dsimp [Q]
        abel
      rw [hAQ]
      exact defectFrame_injective (hz (χ x) (hχr x) x hx hxZ)
  · intro x hx
    have hxK : x ∉ K := fun h => hx (Or.inl h)
    have hxχ : x ∉ tsupport χ := fun h => hx (Or.inr h)
    have hχ0 : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
    dsimp only [A]
    rw [hχ0,hBe x hxK]
    dsimp [Q]
    abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
