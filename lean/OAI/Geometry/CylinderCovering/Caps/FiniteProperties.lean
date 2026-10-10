import OAI.Geometry.CylinderCovering.Caps.Symmetry
import OAI.Geometry.CylinderCovering.Footprints.Footprints
import OAI.Geometry.CylinderCovering.Radial.SetProjection

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite

lemma halfheightFootprint_compact (ρ e M m : ℝ) :
    IsCompact (RadialFootprints.halfheightFootprint ρ e M m) := by
  have heq : RadialFootprints.halfheightFootprint ρ e M m =
      {p : ℝ × ℝ | p.1 ∈ Icc (-e) (M+e) ∧
        p.2 ∈ Icc (m*p.1-ρ*(p.1+2*e)) (m*p.1+ρ*(p.1+2*e))} := by
    ext p
    simp only [RadialFootprints.halfheightFootprint, mem_ofPred_eq, mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨h1,h2⟩, by constructor <;> linarith⟩
    · rintro ⟨⟨h1,h2⟩,h3,h4⟩
      exact ⟨⟨h1,h2⟩, by constructor <;> linarith⟩
  rw [heq]
  exact Footprints.isCompact_closedBand
    (f := fun u => m*u-ρ*(u+2*e)) (g := fun u => m*u+ρ*(u+2*e))
    (by fun_prop) (by fun_prop) _ _

lemma halfheightFootprint_convex (ρ e M m : ℝ) :
    Convex ℝ (RadialFootprints.halfheightFootprint ρ e M m) := by
  intro x hx y hy a b ha hb hab
  simp only [RadialFootprints.halfheightFootprint, mem_ofPred_eq, mem_Icc, abs_le,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at *
  have he : a*e+b*e=e := by rw [← add_mul, hab, one_mul]
  have hM : a*(M+e)+b*(M+e)=M+e := by rw [← add_mul, hab, one_mul]
  have hρe : a*(2*ρ*e)+b*(2*ρ*e)=2*ρ*e := by rw [← add_mul, hab, one_mul]
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hx.1.1 ha,
      mul_le_mul_of_nonneg_left hy.1.1 hb, he]
  · linarith only [mul_le_mul_of_nonneg_left hx.1.2 ha,
      mul_le_mul_of_nonneg_left hy.1.2 hb, hM]
  · nlinarith only [mul_le_mul_of_nonneg_left hx.2.1 ha,
      mul_le_mul_of_nonneg_left hy.2.1 hb, hρe]
  · nlinarith only [mul_le_mul_of_nonneg_left hx.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2 hb, hρe]

lemma firstAxis_norm (δ r : ℝ) : ‖firstAxis δ r‖ = 1 := by
  apply TriangularCovering.unit_norm
  intro hz
  have := congrArg (fun z : Space => z 0) hz
  simp [firstRaw] at this

lemma firstFoot_coordinateAffine :
    firstFoot = RadialProjection.coordinateAffine (0 : Space)
      (!₂[0,0,height]) (!₂[0,1/2,0]) := by
  funext p
  ext i
  fin_cases i <;> simp [firstFoot, RadialProjection.coordinateAffine] <;> ring

theorem firstBase_properties (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    BaseProperties (firstAxis δ (midpoint N i)) (firstBase δ R N i) := by
  have hfoot : IsCompact (foot δ R N i) :=
    halfheightFootprint_compact _ _ _ _
  have hvfoot : Convex ℝ (foot δ R N i) :=
    halfheightFootprint_convex _ _ _ _
  have hc : IsCompact (firstBase δ R N i) := by
    unfold firstBase
    rw [firstFoot_coordinateAffine]
    exact RadialProjection.affine_projection_isCompact _ _ _ _ hfoot
  refine ⟨firstAxis_norm _ _, hc, ?_, hc.measurableSet, ?_, ?_⟩
  · unfold firstBase
    rw [firstFoot_coordinateAffine]
    exact (hvfoot.affine_image _).linear_image (TriangularCovering.projLinear _)
  · unfold firstBase
    rw [firstFoot_coordinateAffine]
    exact RadialProjection.affine_projection_finite _ _ _ _ (firstAxis_norm _ _) hfoot
  · rintro z ⟨p,hp,rfl⟩
    exact TriangularCovering.projection_perp (firstAxis_norm _ _) p

theorem secondBase_properties (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    BaseProperties (secondAxis δ (midpoint N i)) (secondBase δ R N i) :=
  secondBase_properties_of_first (firstBase_properties δ R N i)

theorem base_properties (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    BaseProperties (firstAxis δ (midpoint N i)) (firstBase δ R N i) ∧
    BaseProperties (secondAxis δ (midpoint N i)) (secondBase δ R N i) :=
  ⟨firstBase_properties δ R N i, secondBase_properties δ R N i⟩

end CylinderCovering.HalfheightFinite

end

end OAI
