import OAI.Geometry.CylinderCovering.Footprints.ShapesDefinitions
import OAI.Geometry.CylinderCovering.Radial.Triangle
import OAI.Geometry.CylinderCovering.Footprints.Footprints

namespace OAI

open Set

namespace CylinderCovering.Footprints

lemma absoluteFootprint_not_convex {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 < A) (hB : 0 ≤ B) :
    ¬ Convex ℝ (absoluteFootprint m M d A B) :=
  not_convex_absoluteFootprint hM hd hA hB

lemma affineFootprint_half_eq_region (m M d A : ℝ) :
    affineFootprint m M d A (A/2) =
      RadialTriangle.region (-A*d) (M+A*d) m d := by
  ext p
  simp only [affineFootprint, RadialTriangle.region, mem_ofPred_eq]
  have heq : d/2*p.1+(A/2)*d^2 = d/2*(p.1- -A*d) := by ring
  rw [heq]

lemma affineFootprint_half_eq_convexHull {m M d A : ℝ}
    (hd : 0 < d) (hlength : 0 < M+2*A*d) :
    affineFootprint m M d A (A/2) =
      convexHull ℝ (range (RadialTriangle.vertices (-A*d) (M+A*d) m d)) := by
  rw [affineFootprint_half_eq_region]
  exact RadialTriangle.region_eq_convexHull (by linarith) hd

lemma affineFootprint_half_vertices_independent {m M d A : ℝ}
    (hd : 0 < d) (hlength : 0 < M+2*A*d) :
    AffineIndependent ℝ (RadialTriangle.vertices (-A*d) (M+A*d) m d) :=
  RadialTriangle.vertices_affineIndependent (by linarith) hd

lemma affineFootprint_convex (m M d A B : ℝ) :
    Convex ℝ (affineFootprint m M d A B) := convex_affineFootprint m M d A B

lemma affineFootprint_interior_nonempty {m M d A B : ℝ}
    (hM : 0 ≤ M) (hd : 0 < d) (hA : 0 ≤ A) (hB : A/2 < B)
    (hlength : 0 < M+2*A*d) :
    (interior (affineFootprint m M d A B)).Nonempty := by
  let S : Set (ℝ × ℝ) := {p | -A*d < p.1 ∧ p.1 < M+A*d ∧
    |p.2-m*p.1| < d/2*p.1+B*d^2}
  have hSopen : IsOpen S := by
    change IsOpen {p : ℝ × ℝ | -A*d < p.1 ∧ p.1 < M+A*d ∧
      |p.2-m*p.1| < d/2*p.1+B*d^2}
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_fst continuous_const).inter
        (isOpen_lt (show Continuous (fun p : ℝ × ℝ => |p.2-m*p.1|) by fun_prop)
          (show Continuous (fun p : ℝ × ℝ => d/2*p.1+B*d^2) by fun_prop)))
  have hsub : S ⊆ affineFootprint m M d A B := by
    rintro p ⟨hp₁,hp₂,hp₃⟩
    exact ⟨hp₁.le,hp₂.le,hp₃.le⟩
  have hBpos : 0 < B := by linarith
  have hwidth : 0 < d/2*(M/2)+B*d^2 := by positivity
  have hp : (M/2,m*(M/2)) ∈ S := by
    change -A*d < M/2 ∧ M/2 < M+A*d ∧
      |m*(M/2)-m*(M/2)| < d/2*(M/2)+B*d^2
    simpa only [sub_self,abs_zero] using
      (show -A*d < M/2 ∧ M/2 < M+A*d ∧ 0 < d/2*(M/2)+B*d^2 from
        ⟨by linarith,by linarith,hwidth⟩)
  refine ⟨(M/2,m*(M/2)), interior_mono hsub ?_⟩
  rwa [hSopen.interior_eq]

lemma affineFootprint_boundary_mem {m M d A B u : ℝ}
    (hu₁ : -A*d ≤ u) (hu₂ : u ≤ M+A*d) (hw : 0 ≤ d/2*u+B*d^2) :
    (u,m*u-(d/2*u+B*d^2)) ∈ affineFootprint m M d A B ∧
      (u,m*u+(d/2*u+B*d^2)) ∈ affineFootprint m M d A B := by
  constructor <;> refine ⟨hu₁,hu₂,?_⟩
  · change |m*u-(d/2*u+B*d^2)-m*u| ≤ d/2*u+B*d^2
    have he : m*u-(d/2*u+B*d^2)-m*u = -(d/2*u+B*d^2) := by ring
    rw [he,abs_neg,abs_of_nonneg hw]
  · change |m*u+(d/2*u+B*d^2)-m*u| ≤ d/2*u+B*d^2
    have he : m*u+(d/2*u+B*d^2)-m*u = d/2*u+B*d^2 := by ring
    rw [he,abs_of_nonneg hw]

lemma affine_width_pos {d A B u : ℝ} (hd : 0 < d)
    (hB : A/2 < B) (hu : -A*d ≤ u) : 0 < d/2*u+B*d^2 := by
  have h₁ := mul_le_mul_of_nonneg_left hu (show 0 ≤ d/2 by positivity)
  have h₂ := mul_pos (sub_pos.mpr hB) (sq_pos_of_pos hd)
  nlinarith

lemma affineFootprint_eq_convexHull_trapezoid {m M d A B : ℝ}
    (hd : 0 < d) (hB : A/2 < B) (hlength : 0 < M+2*A*d) :
    affineFootprint m M d A B = convexHull ℝ (range (trapezoidVertices m M d A B)) := by
  let l := -A*d
  let r := M+A*d
  let f := fun u : ℝ => m*u-(d/2*u+B*d^2)
  let g := fun u : ℝ => m*u+(d/2*u+B*d^2)
  have hlr : l < r := by dsimp [l,r]; linarith
  apply le_antisymm
  · intro p hp
    obtain ⟨hu₁,hu₂,hv⟩ := hp
    rcases abs_le.mp hv with ⟨hv₁,hv₂⟩
    let t : ℝ := (p.1-l)/(r-l)
    let s : ℝ := (p.2-f p.1)/(g p.1-f p.1)
    have hden : 0 < r-l := sub_pos.mpr hlr
    have hwidth : 0 < g p.1-f p.1 := by
      have := affine_width_pos hd hB hu₁
      dsimp [g,f]
      linarith
    have ht₀ : 0 ≤ t := div_nonneg (by dsimp [l]; linarith) hden.le
    have ht₁ : t ≤ 1 := by
      apply (div_le_one hden).mpr
      dsimp [r]
      linarith
    have hs₀ : 0 ≤ s := div_nonneg (by dsimp [f]; linarith) hwidth.le
    have hs₁ : s ≤ 1 := by
      apply (div_le_one hwidth).mpr
      dsimp [g,f]
      linarith
    have ht : (1-t)*l+t*r = p.1 := by
      dsimp [t]
      field_simp [ne_of_gt hden]
      ring
    have hs : (1-s)*f p.1+s*g p.1 = p.2 := by
      dsimp [s]
      field_simp [ne_of_gt hwidth]
      ring
    have hf : (1-t)*f l+t*f r = f p.1 := by
      dsimp [f]
      linear_combination (m-d/2)*ht
    have hg : (1-t)*g l+t*g r = g p.1 := by
      dsimp [g]
      linear_combination (m+d/2)*ht
    let w : Fin 4 → ℝ := ![(1-t)*(1-s),(1-t)*s,t*(1-s),t*s]
    refine mem_convexHull_of_exists_fintype w (trapezoidVertices m M d A B) ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> dsimp [w]
      · exact mul_nonneg (sub_nonneg.mpr ht₁) (sub_nonneg.mpr hs₁)
      · exact mul_nonneg (sub_nonneg.mpr ht₁) hs₀
      · exact mul_nonneg ht₀ (sub_nonneg.mpr hs₁)
      · exact mul_nonneg ht₀ hs₀
    · simp [w,Fin.sum_univ_succ]
      ring
    · exact fun i => mem_range_self i
    · apply Prod.ext
      · change (∑ i : Fin 4, w i • trapezoidVertices m M d A B i).1 = p.1
        simp [w,trapezoidVertices,Fin.sum_univ_succ]
        calc
          _ = (1-t)*l+t*r := by dsimp [l,r]; ring
          _ = p.1 := ht
      · change (∑ i : Fin 4, w i • trapezoidVertices m M d A B i).2 = p.2
        simp [w,trapezoidVertices,Fin.sum_univ_succ]
        calc
          _ = (1-s)*((1-t)*f l+t*f r)+s*((1-t)*g l+t*g r) := by
            dsimp [l,r,f,g]
            ring
          _ = (1-s)*f p.1+s*g p.1 := by rw [hf,hg]
          _ = p.2 := hs
  · refine convexHull_min ?_ (affineFootprint_convex m M d A B)
    rintro _ ⟨i,rfl⟩
    have hleft := affineFootprint_boundary_mem (m := m) (M := M) (d := d) (A := A)
      (B := B) le_rfl hlr.le (affine_width_pos hd hB le_rfl).le
    have hright := affineFootprint_boundary_mem (m := m) (M := M) (d := d) (A := A)
      (B := B) hlr.le le_rfl (affine_width_pos hd hB hlr.le).le
    fin_cases i
    · exact hleft.1
    · exact hleft.2
    · exact hright.1
    · exact hright.2

lemma trapezoidVertices_injective {m M d A B : ℝ}
    (hd : 0 < d) (hB : A/2 < B) (hlength : 0 < M+2*A*d) :
    Function.Injective (trapezoidVertices m M d A B) := by
  have hlr : -A*d < M+A*d := by linarith
  have hl := affine_width_pos hd hB (le_refl (-A*d))
  have hr := affine_width_pos hd hB hlr.le
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [trapezoidVertices]
  all_goals nlinarith

lemma trapezoid_vertical_sides (m M d A B : ℝ) :
    trapezoidVertices m M d A B 1 - trapezoidVertices m M d A B 0 =
        (0,2*(d/2*(-A*d)+B*d^2)) ∧
      trapezoidVertices m M d A B 3 - trapezoidVertices m M d A B 2 =
        (0,2*(d/2*(M+A*d)+B*d^2)) := by
  constructor <;> ext <;> simp [trapezoidVertices] <;> ring

section AffineImages
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma affineFootprint_image_eq_convexHull (f : (ℝ × ℝ) →ᵃ[ℝ] E)
    {m M d A B : ℝ} (hd : 0 < d) (hB : A/2 < B) (hlength : 0 < M+2*A*d) :
    f '' affineFootprint m M d A B =
      convexHull ℝ (range (f ∘ trapezoidVertices m M d A B)) := by
  rw [affineFootprint_eq_convexHull_trapezoid hd hB hlength,
    f.image_convexHull, ← range_comp]

lemma trapezoid_image_vertices_injective (f : (ℝ × ℝ) →ᵃ[ℝ] E)
    (hf : Function.Injective f) {m M d A B : ℝ}
    (hd : 0 < d) (hB : A/2 < B) (hlength : 0 < M+2*A*d) :
    Function.Injective (f ∘ trapezoidVertices m M d A B) :=
  hf.comp (trapezoidVertices_injective hd hB hlength)

end AffineImages

theorem footprint_shapes : ShapeStatement := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m M d A B hM hd hA hB
    exact absoluteFootprint_not_convex hM hd hA hB
  · intro m M d A hd hlength
    exact ⟨affineFootprint_half_eq_convexHull hd hlength,
      affineFootprint_half_vertices_independent hd hlength⟩
  · intro m M d A B hd hB hlength
    exact ⟨affineFootprint_eq_convexHull_trapezoid hd hB hlength,
      trapezoidVertices_injective hd hB hlength, trapezoid_vertical_sides m M d A B⟩
  · intro m M d A B hM hd hA hB hlength
    exact affineFootprint_interior_nonempty hM hd hA hB hlength

end CylinderCovering.Footprints

end OAI
