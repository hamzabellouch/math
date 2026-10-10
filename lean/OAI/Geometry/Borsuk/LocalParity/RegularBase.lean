import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.SymmetricEntries
import OAI.Geometry.Borsuk.Support.PurityGeometry
import OAI.Geometry.Borsuk.LocalParity.Sard
import OAI.Geometry.Borsuk.SphereGeometry.HemisphereChart
import OAI.Geometry.Borsuk.Projectors.SimplexPoint

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open Set
open scoped RealInnerProductSpace
section RegularBase
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def baseCoordinates (f : E → ι → ℝ) (w : E) (e : W →ₗᵢ[ℝ] E)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : W → W :=
  fun v => WithLp.toLp 2 (fun j => f (hemisphereChart w e v) (a j.succ).val)

omit [DecidableEq ι] in
lemma Admissible.baseCoordinates_contDiff {f : E → ι → ℝ} (hf : Admissible f)
    {w : E} (hw : ‖w‖ = 1) (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪w,e v⟫ = 0)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) : ContDiff ℝ (⊤ : ℕ∞) (baseCoordinates f w e a) := by
  apply (contDiff_piLp 2).mpr
  intro j
  exact (hf.smooth (a j.succ).val).comp (hemisphereChart_contDiff w e hw he)

noncomputable def facetPoint {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) : ι → ℝ :=
  fun i => if hi : i ∈ I then simplexPoint z (a.symm ⟨i,hi⟩) else 0

omit [Fintype ι] in
lemma facetPoint_apply {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) (j : Fin (k+1)) :
    facetPoint a z (a j).val = simplexPoint z j := by
  simp [facetPoint]

omit [Fintype ι] in
lemma facetPoint_pos {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {z : W} (hz : z ∈ simplexInterior k) :
    ∀ i ∈ I, 0 < facetPoint a z i := by
  intro i hi
  simp only [facetPoint,dite_eq_left hi]
  exact simplexPoint_pos hz _

omit [Fintype ι] in
lemma facetPoint_zero {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) {i : ι} (hi : i ∉ I) :
    facetPoint a z i = 0 := by simp [facetPoint,hi]

lemma facetPoint_sum {I : Finset ι} (a : Fin (k+1) ≃ ↥I) (z : W) : ∑ i, facetPoint a z i = 1 := by
  have h : ∑ i, facetPoint a z i = ∑ i : ↥I, simplexPoint z (a.symm i) := by
    calc
      _ = ∑ i ∈ I, facetPoint a z i := (Finset.sum_subset (Finset.subset_univ I)
        (fun i _ hi => facetPoint_zero a z hi)).symm
      _ = ∑ i : ↥I, facetPoint a z i.val := (Finset.sum_coe_sort I _).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => by simp [facetPoint])
  rw [h,Equiv.sum_comp a.symm]
  exact simplexPoint_sum z

lemma Admissible.exists_regular_facet_point {f : E → ι → ℝ} (hf : Admissible f)
    {I : Finset ι} (a : Fin (k+1) ≃ ↥I) {w : E} (hw : ‖w‖ = 1)
    (hwi : ∀ i ∈ I, 0 < f w i) :
    ∃ (e : W →ₗᵢ[ℝ] E) (z : W), (∀ v, ⟪w,e v⟫ = 0) ∧
      (∀ u, ⟪w,u⟫ = 0 → ∃ v, e v = u) ∧ z ∈ simplexInterior k ∧
      (∀ v, baseCoordinates f w e a v = z → (fderiv ℝ (baseCoordinates f w e a) v).det ≠ 0) ∧
      (orientedLevel f w (facetPoint a z)).Finite := by
  obtain ⟨e,he,hes⟩ := orthogonal_frame k hw
  obtain ⟨z,hz,hr⟩ := exists_regular_value (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).differentiable (by simp)) (simplexInterior_isOpen k) (simplexInterior_nonempty k)
  refine ⟨e,z,he,hes,hz,hr,?_⟩
  let K := orientedLevel f w (facetPoint a z)
  have hI : I.Nonempty := ⟨(a 0).val,(a 0).property⟩
  have hp : K ⊆ {u | 0 < ⟪w,u⟫} := fun u hu =>
    hf.orientedLevel_inner_pos hI hw hwi (facetPoint_pos a hz) hu
  have hcont : ContinuousOn (hemisphereInverse w e) K := (hemisphereInverse_continuousOn w e).mono hp
  have hc := (hf.orientedLevel_compact w (facetPoint a z)).image_of_continuousOn hcont
  have hK : ∀ v ∈ hemisphereInverse w e '' K, baseCoordinates f w e a v = z := by
    rintro v ⟨u,hu,rfl⟩
    ext j
    change f (hemisphereChart w e (hemisphereInverse w e u)) (a j.succ).val = z j
    rw [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),hu.2.1,facetPoint_apply,simplexPoint_succ]
  have hfin := compact_regular_level_finite (baseCoordinates f w e a)
    ((hf.baseCoordinates_contDiff hw e he a).of_le (by simp)) hc hK hr
  apply (Set.finite_image_iff ?_).mp hfin
  intro u hu v hv huv
  have hh := congrArg (hemisphereChart w e) huv
  rwa [hemisphereChart_inverse w e hw he hes hu.1 (hp hu),
    hemisphereChart_inverse w e hw he hes hv.1 (hp hv)] at hh
end RegularBase
end BorsukNine

end OAI
