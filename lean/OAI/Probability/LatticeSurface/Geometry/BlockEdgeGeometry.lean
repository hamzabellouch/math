import Mathlib
import OAI.Probability.LatticeSurface.Convexity.RadialExposure
import OAI.Probability.LatticeSurface.Geometry.BlockFacetGeometry
import OAI.Probability.LatticeSurface.Geometry.BlockVolume
import OAI.Probability.LatticeSurface.Geometry.EdgeCoordinates
import OAI.Probability.LatticeSurface.Geometry.FacetExposure
import OAI.Probability.LatticeSurface.Geometry.TriangularCover
import OAI.Probability.LatticeSurface.Geometry.TriangularGeometry

namespace OAI

open MeasureTheory

open scoped ENNReal

noncomputable section

namespace TriangularLipschitz

end TriangularLipschitz

namespace FacetExposure

end FacetExposure

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

namespace TriangularLipschitz

end TriangularLipschitz

open MeasureTheory Set

open scoped ENNReal

noncomputable section

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace EdgeCoordinates

end EdgeCoordinates

namespace TriangularLipschitz

noncomputable def edgeOffset (L : ℕ) (τ : ℝ) (s : Vertex → ℝ) (x : Vertex) : ℝ :=
  if x ∈ interior L then 0 else τ*s x

lemma exists_filling_edge_coordinates {L n : ℕ}
    (e : {x : Vertex // x ∈ interior L} ≃ Fin (n+1))
    {x y : Vertex} (hy : y ∈ interior L) (hxy : x ≠ y) {τ : ℝ} (hτ : |τ|=1) :
    ∃ E : Filling L ≃ₗ[ℝ] (Fin (n+1) → ℝ),
      MeasurePreserving E ∧ (∀ z, ‖E.symm z‖ ≤ 2*‖z‖) ∧
      ∀ s a, E a 0 = τ*(filledHeight L s a y-filledHeight L s a x)+edgeOffset L τ s x := by
  classical
  by_cases hx : x ∈ interior L
  · obtain ⟨E,hE,hEn,hE0⟩ := EdgeCoordinates.exists_edge_coordinates e ⟨y,hy⟩
      (some ⟨x,hx⟩) τ hτ (by intro i hi he; cases hi; exact hxy (congrArg Subtype.val he))
    refine ⟨E,hE,hEn,?_⟩
    intro s a
    simpa [filledHeight,edgeOffset,hx,hy] using hE0 a
  · obtain ⟨E,hE,hEn,hE0⟩ := EdgeCoordinates.exists_edge_coordinates e ⟨y,hy⟩
      none τ hτ (by simp)
    refine ⟨E,hE,hEn,?_⟩
    intro s a
    simp only [hE0,Option.elim_none,sub_zero,filledHeight,dite_eq_left hy,dite_eq_right hx,edgeOffset,ite_eq_right hx]
    ring

lemma filling_projection_width {L n : ℕ} {x y : Vertex} {τ : ℝ} (s : Vertex → ℝ)
    (hτ : |τ|=1) (hx : x ∈ box L) (hy : y ∈ box L) (hxy : Adj x y)
    (E : Filling L ≃ₗ[ℝ] (Fin (n+1) → ℝ))
    (hE0 : ∀ s a, E a 0 = τ*(filledHeight L s a y-filledHeight L s a x)+edgeOffset L τ s x) :
    ∀ z ∈ E '' fillingPolytope L s,
      z 0 ∈ Set.Icc (1+edgeOffset L τ s x-2) (1+edgeOffset L τ s x) := by
  rintro z ⟨a,ha,rfl⟩
  rw [hE0]
  have h := ha x hx y hy hxy
  have h' : |τ*(filledHeight L s a y-filledHeight L s a x)| ≤ 1 := by
    rw [abs_mul,hτ,one_mul,abs_sub_comm]; exact h
  obtain ⟨h₁,h₂⟩ := abs_le.mp h'
  exact ⟨by linarith,by linarith⟩

lemma filling_facet_ball {L n : ℕ} {x y : Vertex} {s : Vertex → ℝ} {τ β : ℝ}
    (hτ : |τ|=1) (hβ : 0 < β)
    (E : Filling L ≃ₗ[ℝ] (Fin (n+1) → ℝ))
    (hEn : ∀ z, ‖E.symm z‖ ≤ 2*‖z‖)
    (hE0 : ∀ s a, E a 0 = τ*(filledHeight L s a y-filledHeight L s a x)+edgeOffset L τ s x)
    (a₀ : Filling L)
    (hfacet : τ*(filledHeight L s a₀ y-filledHeight L s a₀ x)=1)
    (hother : ∀ v ∈ box L, ∀ w ∈ box L, Adj v w → s(v,w) ≠ s(x,y) →
      |filledHeight L s a₀ v-filledHeight L s a₀ w| ≤ 1-β/2) :
    ∃ q₀ : Fin n → ℝ, ∀ q ∈ Metric.ball q₀ (β/16),
      Fin.cons (1+edgeOffset L τ s x) q ∈ E '' fillingPolytope L s := by
  let q₀ : Fin n → ℝ := fun i => E a₀ i.succ
  refine ⟨q₀,?_⟩
  intro q hq
  let z : Fin (n+1) → ℝ := Fin.cons (1+edgeOffset L τ s x) q
  let a := E.symm z
  have hb : E a₀ 0=1+edgeOffset L τ s x := by rw [hE0,hfacet]
  have hnorm : ‖z-E a₀‖ ≤ ‖q-q₀‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [z,hb,norm_nonneg]
    · exact norm_le_pi_norm (q-q₀) j
  have ha : ‖a-a₀‖ ≤ 2*‖q-q₀‖ := by
    have heq : a-a₀=E.symm (z-E a₀) := by simp [a]
    rw [heq]
    exact (hEn _).trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  have hq' : ‖q-q₀‖ < β/16 := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  have hsign : τ*(filledHeight L s a y-filledHeight L s a x)=1 := by
    have h := hE0 s a
    have hz : E a 0=1+edgeOffset L τ s x := by simp [a,z]
    linarith
  have habs : |filledHeight L s a x-filledHeight L s a y| ≤ 1 := by
    have h := congrArg abs hsign
    rw [abs_mul,hτ,one_mul,abs_one,abs_sub_comm] at h
    exact h.le
  refine ⟨a,filling_of_small_perturbation_on_facet habs hother (by linarith),?_⟩
  exact E.apply_symm_apply z

end TriangularLipschitz

namespace TriangularLipschitz

lemma linearCoordinates_measurableEmbedding {L n : ℕ}
    (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ)) : MeasurableEmbedding E :=
  E.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding

lemma filling_volume_image {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ))
    (hE : MeasurePreserving E) (s : Vertex → ℝ) :
    volume (E '' fillingPolytope L s) = fillingVolume L s := by
  have h := hE.measure_preimage_emb (linearCoordinates_measurableEmbedding E) (E '' fillingPolytope L s)
  simpa only [Set.preimage_image_eq _ E.injective, fillingVolume] using h.symm

lemma isCompact_filling_image {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ)) (s : Vertex → ℝ) :
    IsCompact (E '' fillingPolytope L s) :=
  (isCompact_fillingPolytope L s).image E.toContinuousLinearEquiv.continuous

lemma convex_filling_image {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ)) (s : Vertex → ℝ) :
    Convex ℝ (E '' fillingPolytope L s) :=
  (convex_fillingPolytope L s).linear_image E.toLinearMap

lemma filling_image_volume_bound {L n : ℕ} (E : Filling L ≃ₗ[ℝ] (Fin n → ℝ))
    (hE : MeasurePreserving E) (s : Vertex → ℝ) :
    (volume (E '' fillingPolytope L s)).toReal ≤
      (volume (Metric.closedBall (0 : Filling L) (2*L))).toReal := by
  rw [filling_volume_image E hE]
  have h : (fillingVolume L s).toReal ≤
      (volume (Metric.closedBall (fun _ => s (0,0) : Filling L) (2*L))).toReal :=
    ENNReal.toReal_mono measure_closedBall_lt_top.ne
      (measure_mono (fillingPolytope_subset_closedBall L s))
  simpa only [Measure.addHaar_closedBall_center] using h

def meanHeight (L : ℕ) (s : Vertex → ℝ) (x : Vertex) : ℝ :=
  (∫ a in fillingPolytope L s, filledHeight L s a x)/(fillingVolume L s).toReal

lemma integrableOn_filledHeight (L : ℕ) (s : Vertex → ℝ) (x : Vertex) :
    IntegrableOn (fun a => filledHeight L s a x) (fillingPolytope L s) :=
  (continuous_filledHeight L s x).continuousOn.integrableOn_compact (isCompact_fillingPolytope L s)

lemma meanHeight_fixed {L : ℕ} {s : Vertex → ℝ} {x : Vertex}
    (hvol : 0 < fillingVolume L s) (hx : x ∉ interior L) : meanHeight L s x=s x := by
  have hv : (fillingVolume L s).toReal ≠ 0 :=
    (ENNReal.toReal_pos hvol.ne' (fillingVolume_lt_top L s).ne).ne'
  simp only [meanHeight,filledHeight_fixed _ _ _ hx, setIntegral_const,smul_eq_mul,
    Measure.real, fillingVolume] at hv ⊢
  exact mul_div_cancel_left₀ _ hv

lemma coordinate_meanHeight {L n : ℕ} {x y : Vertex} {τ : ℝ}
    (E : Filling L ≃ₗ[ℝ] (Fin (n+1) → ℝ)) (hE : MeasurePreserving E)
    (hE0 : ∀ s a, E a 0 = τ*(filledHeight L s a y-filledHeight L s a x)+edgeOffset L τ s x)
    (s : Vertex → ℝ) (hvol : 0 < fillingVolume L s) :
    (∫ z in E '' fillingPolytope L s, z 0)/(volume (E '' fillingPolytope L s)).toReal =
      τ*(meanHeight L s y-meanHeight L s x)+edgeOffset L τ s x := by
  have hv : (fillingVolume L s).toReal ≠ 0 :=
    (ENNReal.toReal_pos hvol.ne' (fillingVolume_lt_top L s).ne).ne'
  have hdiff : IntegrableOn (fun a => filledHeight L s a y-filledHeight L s a x)
      (fillingPolytope L s) :=
    (integrableOn_filledHeight L s y).sub (integrableOn_filledHeight L s x)
  have hconst : IntegrableOn (fun _ : Filling L => edgeOffset L τ s x) (fillingPolytope L s) :=
    continuousOn_const.integrableOn_compact (isCompact_fillingPolytope L s)
  rw [filling_volume_image E hE, hE.setIntegral_image_emb (linearCoordinates_measurableEmbedding E)]
  simp_rw [hE0 s]
  rw [integral_add (hdiff.const_mul τ) hconst, integral_const_mul,
    integral_sub (integrableOn_filledHeight L s y) (integrableOn_filledHeight L s x),setIntegral_const]
  simp only [meanHeight, smul_eq_mul, Measure.real]
  change (_+ (fillingVolume L s).toReal*_) / (fillingVolume L s).toReal = _
  field_simp

end TriangularLipschitz

end
end

end OAI
