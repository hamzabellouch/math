import OAI.Geometry.NodalSets.Elliptic.RealFinCubeFubini
import OAI.Geometry.NodalSets.Elliptic.RealL2DifferenceQuotient
import OAI.Geometry.NodalSets.Elliptic.RealTransportDerivatives

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem real_compact_continuous_memLp {n : ℕ} (u : Coord n → ℝ)
    (hu : Continuous u) (hc : HasCompactSupport u) : MemLp u 2 volume :=
  (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mpr
    ((hu.pow 2).integrable_of_hasCompactSupport (by
      convert hc.mul_right (f' := u) using 1
      first | rfl | (ext x; simp [pow_two])))

theorem realDifferenceQuotient_smooth {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (realDifferenceQuotient i h u) :=
  contDiff_const.mul ((hu.comp (contDiff_id.add contDiff_const)).sub hu)

theorem realDifferenceQuotient_compact {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hc : HasCompactSupport u) :
    HasCompactSupport (realDifferenceQuotient i h u) :=
  ((hc.comp_homeomorph (Homeomorph.addRight (Pi.single i h))).sub hc).mul_left

theorem realDifferenceQuotient_partial {n : ℕ} (i j : Fin n) (h : ℝ)
    (u : Coord n → ℝ) (hu : ContDiff ℝ ∞ u) (x : Coord n) :
    coordPartial (realDifferenceQuotient i h u) x j =
      realDifferenceQuotient i h (fun y ↦ coordPartial u y j) x := by
  have ht : ContDiff ℝ ∞ (fun y ↦ u (y+Pi.single i h)) :=
    hu.comp (contDiff_id.add contDiff_const)
  unfold realDifferenceQuotient
  rw [real_coordPartial_const_mul _ (ht.sub hu)]
  unfold coordPartial
  rw [fderiv_fun_sub (ht.differentiable (by simp) x) (hu.differentiable (by simp) x),
    fderiv_comp_add_right]
  rfl

theorem realDifferenceQuotient_tsupport {n : ℕ} (i : Fin n) (h : ℝ)
    (u : Coord n → ℝ) {K : Set (Coord n)} (hK : IsClosed K)
    (hs : tsupport u ⊆ K) (ht : ∀ x, x+Pi.single i h ∈ tsupport u → x ∈ K) :
    tsupport (realDifferenceQuotient i h u) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have h1 : u x=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (hs h))
  have h2 : u (x+Pi.single i h)=0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hn (ht x h))
  exact hx (by simp [realDifferenceQuotient,h1,h2])

def realCenteredCube (n : ℕ) (r : ℝ) : Set (Coord n) :=
  Set.univ.pi (fun _ ↦ Set.Icc (-r) r)

theorem realCenteredCube_isCompact (n : ℕ) (r : ℝ) : IsCompact (realCenteredCube n r) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

theorem realCenteredCube_mono {n : ℕ} {r R : ℝ} (h : r ≤ R) :
    realCenteredCube n r ⊆ realCenteredCube n R := by
  intro x hx j hj
  have hjx := hx j hj
  exact ⟨(neg_le_neg h).trans hjx.1,hjx.2.trans h⟩

theorem realCenteredCube_shift {n : ℕ} (i : Fin n) {r R h : ℝ}
    (hh : |h| ≤ R-r) {x : Coord n} (hx : x+Pi.single i h ∈ realCenteredCube n r) :
    x ∈ realCenteredCube n R := by
  intro j hj
  have hxj := hx j hj
  have hhr : r ≤ R := by linarith [abs_nonneg h]
  by_cases he : j=i
  · subst j
    simp only [Pi.add_apply,Pi.single_eq_same,mem_Icc] at hxj
    have hh' := abs_le.mp hh
    constructor <;> linarith
  · simp only [Pi.add_apply,Pi.single_eq_of_ne he,add_zero,mem_Icc] at hxj
    exact ⟨(neg_le_neg hhr).trans hxj.1,hxj.2.trans hhr⟩

theorem realDifferenceQuotient_halfCube_support {n : ℕ} (i : Fin n) (h : ℝ)
    (hh : |h| ≤ 1/2) (u : Coord n → ℝ)
    (hs : tsupport u ⊆ realCenteredCube n (1/2)) :
    tsupport (realDifferenceQuotient i h u) ⊆ Yau.Geometry.realFinCube n := by
  apply realDifferenceQuotient_tsupport i h u (realCenteredCube_isCompact n 1).isClosed
    (hs.trans (realCenteredCube_mono (by norm_num)))
  intro x hx
  exact realCenteredCube_shift i (by linarith) (hs hx)

end
end Yau

end OAI
