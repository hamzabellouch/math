import OAI.Geometry.CylinderCovering.Caps.FiniteDefinitions
import OAI.Geometry.CylinderCovering.Footprints.Shapes
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

open Set
open scoped InnerProductSpace
noncomputable section
namespace CylinderCovering.HalfheightFinite.Shape

lemma height_pos : 0 < height := by unfold height; positivity

lemma foot_eq_affine (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    foot δ R N i = Footprints.affineFootprint (midpoint N i) (maxCap R N i)
      (2 * halfwidth N) (δ / 4) (δ / 4) := by
  ext p
  simp only [foot, RadialFootprints.halfheightFootprint,
    Footprints.affineFootprint, mem_ofPred_eq, mem_Icc, collar]
  have h₁ : -(δ * halfwidth N / 2) = -(δ / 4) * (2 * halfwidth N) := by ring
  have h₂ : δ * halfwidth N / 2 = δ / 4 * (2 * halfwidth N) := by ring
  have h₃ : halfwidth N * (p.1 + 2 * (δ * halfwidth N / 2)) =
      2 * halfwidth N / 2 * p.1 + δ / 4 * (2 * halfwidth N)^2 := by ring
  rw [h₃, h₁, h₂]
  tauto

def firstFootLinear : (ℝ × ℝ) →ₗ[ℝ] Space where
  toFun := firstFoot
  map_add' p q := by ext i; fin_cases i <;> simp [firstFoot] <;> ring
  map_smul' c p := by ext i; fin_cases i <;> simp [firstFoot] <;> ring

def secondFootLinear : (ℝ × ℝ) →ₗ[ℝ] Space where
  toFun p := !₂[p.2/2,0,-height*p.1]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c p := by ext i; fin_cases i <;> simp <;> ring

def secondFootAffine : (ℝ × ℝ) →ᵃ[ℝ] Space where
  toFun := secondFoot
  linear := secondFootLinear
  map_vadd' p q := by
    ext i
    fin_cases i <;> simp [secondFoot, secondFootLinear] <;> ring

def projectionLinear (u : Space) : Space →ₗ[ℝ] Space :=
  LinearMap.id - (innerₛₗ ℝ u).smulRight u

lemma projectionLinear_apply (u z : Space) :
    projectionLinear u z = TriangularCovering.projection u z := rfl

def firstProjectedAffine (δ r : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  (projectionLinear (firstAxis δ r)).toAffineMap.comp firstFootLinear.toAffineMap

def secondProjectedAffine (δ r : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  (projectionLinear (secondAxis δ r)).toAffineMap.comp secondFootAffine

lemma firstRaw_ne_zero (δ r : ℝ) : firstRaw δ r ≠ 0 := by
  intro h
  have h₀ := congrArg (fun z : Space => z 0) h
  norm_num [firstRaw] at h₀

lemma secondRaw_ne_zero (δ r : ℝ) : secondRaw δ r ≠ 0 := by
  intro h
  have h₁ := congrArg (fun z : Space => z 1) h
  norm_num [secondRaw] at h₁

lemma firstAxis_zero_ne (δ r : ℝ) : firstAxis δ r 0 ≠ 0 := by
  simp [firstAxis, firstRaw]

lemma secondAxis_one_ne (δ r : ℝ) : secondAxis δ r 1 ≠ 0 := by
  simp [secondAxis, secondRaw]

lemma projection_injective_on_coordinate_plane {u p q : Space} {i : Fin 3}
    (hu : u i ≠ 0) (hp : p i = 0) (hq : q i = 0)
    (heq : TriangularCovering.projection u p = TriangularCovering.projection u q) : p = q := by
  have hi := congrArg (fun z : Space => z i) heq
  simp only [TriangularCovering.projection, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, hp, hq, zero_sub] at hi
  have hin : inner ℝ u p = inner ℝ u q := mul_right_cancel₀ hu (neg_inj.mp hi)
  simpa only [TriangularCovering.projection, hin, sub_left_inj] using heq

lemma firstProjectedAffine_injective (δ r : ℝ) :
    Function.Injective (firstProjectedAffine δ r) := by
  intro p q h
  have hpq : firstFoot p = firstFoot q :=
    projection_injective_on_coordinate_plane (firstAxis_zero_ne δ r) (by simp [firstFoot])
      (by simp [firstFoot]) h
  have h₁ := congrArg (fun z : Space => z 1) hpq
  have h₂ := congrArg (fun z : Space => z 2) hpq
  change p.2 / 2 = q.2 / 2 at h₁
  change height * p.1 = height * q.1 at h₂
  apply Prod.ext
  · exact mul_left_cancel₀ (ne_of_gt height_pos) h₂
  · linarith

lemma secondProjectedAffine_injective (δ r : ℝ) :
    Function.Injective (secondProjectedAffine δ r) := by
  intro p q h
  have hpq : secondFoot p = secondFoot q :=
    projection_injective_on_coordinate_plane (secondAxis_one_ne δ r) (by simp [secondFoot])
      (by simp [secondFoot]) h
  have h₀ := congrArg (fun z : Space => z 0) hpq
  have h₂ := congrArg (fun z : Space => z 2) hpq
  change p.2 / 2 = q.2 / 2 at h₀
  change height * (1-p.1) = height * (1-q.1) at h₂
  apply Prod.ext
  · have := mul_left_cancel₀ (ne_of_gt height_pos) h₂
    linarith
  · linarith

lemma firstBase_eq_image (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    firstBase δ R N i = firstProjectedAffine δ (midpoint N i) '' foot δ R N i := by
  rw [firstBase, image_image]
  rfl

lemma secondBase_eq_image (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    secondBase δ R N i = secondProjectedAffine δ (midpoint N i) '' foot δ R N i := by
  rw [secondBase, image_image]
  rfl

def coordinateVertices (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Fin 4 → ℝ × ℝ :=
  Footprints.trapezoidVertices (midpoint N i) (maxCap R N i)
    (2 * halfwidth N) (δ / 4) (δ / 4)

def firstVertices (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Fin 4 → Space :=
  firstProjectedAffine δ (midpoint N i) ∘ coordinateVertices δ R N i

def secondVertices (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) : Fin 4 → Space :=
  secondProjectedAffine δ (midpoint N i) ∘ coordinateVertices δ R N i

lemma halfwidth_pos {N : ℕ} (hN : 0 < N) : 0 < halfwidth N := by
  unfold halfwidth
  positivity

lemma radial_length_pos {δ M : ℝ} {N : ℕ} (hδ : 0 < δ) (hM : 0 ≤ M)
    (hN : 0 < N) : 0 < M + 2 * (δ / 4) * (2 * halfwidth N) := by
  have := halfwidth_pos hN
  positivity

lemma coordinate_shape {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} (i : Fin N)
    (hδ : 0 < δ) (hM : 0 ≤ maxCap R N i) :
    foot δ R N i = convexHull ℝ (range (coordinateVertices δ R N i)) ∧
      Function.Injective (coordinateVertices δ R N i) := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hd : 0 < 2 * halfwidth N := mul_pos (by norm_num) (halfwidth_pos hN)
  have hpad : δ / 4 / 2 < δ / 4 := by linarith
  have hlen := radial_length_pos hδ hM hN
  rw [foot_eq_affine]
  exact ⟨Footprints.affineFootprint_eq_convexHull_trapezoid hd hpad hlen,
    Footprints.trapezoidVertices_injective hd hpad hlen⟩

theorem projected_shape {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} (i : Fin N)
    (hδ : 0 < δ) (hM : 0 ≤ maxCap R N i) :
    firstBase δ R N i = convexHull ℝ (range (firstVertices δ R N i)) ∧
    secondBase δ R N i = convexHull ℝ (range (secondVertices δ R N i)) ∧
    Function.Injective (firstVertices δ R N i) ∧
    Function.Injective (secondVertices δ R N i) := by
  obtain ⟨hfoot, hinj⟩ := coordinate_shape i hδ hM
  refine ⟨?_, ?_, (firstProjectedAffine_injective δ (midpoint N i)).comp hinj,
    (secondProjectedAffine_injective δ (midpoint N i)).comp hinj⟩
  · rw [firstBase_eq_image, hfoot, (firstProjectedAffine δ (midpoint N i)).image_convexHull,
      ← range_comp]
    rfl
  · rw [secondBase_eq_image, hfoot, (secondProjectedAffine δ (midpoint N i)).image_convexHull,
      ← range_comp]
    rfl

lemma vertical_triangle_independent {l r a b c : ℝ} (hlr : l < r) (hab : a < b) :
    AffineIndependent ℝ ![(l,a),(l,b),(r,c)] := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hv j
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hv
  have hx := congrArg (fun p : ℝ × ℝ => p.1) hv
  have hy := congrArg (fun p : ℝ × ℝ => p.2) hv
  simp [Fin.sum_univ_succ] at hw hx hy
  have hw₂' : (r-l) * w 2 = 0 := by linear_combination hx-l*hw
  have hw₂ : w 2 = 0 := (mul_eq_zero.mp hw₂').resolve_left (ne_of_gt (sub_pos.mpr hlr))
  have hw₁' : (b-a) * w 1 = 0 := by linear_combination hy-a*hw-(c-a)*hw₂
  have hw₁ : w 1 = 0 := (mul_eq_zero.mp hw₁').resolve_left (ne_of_gt (sub_pos.mpr hab))
  fin_cases j <;> simp_all

lemma coordinate_nondegenerate {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} (i : Fin N)
    (hδ : 0 < δ) (hM : 0 ≤ maxCap R N i) :
    AffineIndependent ℝ ![coordinateVertices δ R N i 0,
      coordinateVertices δ R N i 1, coordinateVertices δ R N i 2] := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hd : 0 < 2 * halfwidth N := mul_pos (by norm_num) (halfwidth_pos hN)
  have hpad : δ / 4 / 2 < δ / 4 := by linarith
  have hlen := radial_length_pos hδ hM hN
  have hwidth := Footprints.affine_width_pos hd hpad (le_refl (-(δ/4)*(2*halfwidth N)))
  apply vertical_triangle_independent
  · linarith
  · linarith

theorem projected_nondegenerate {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} (i : Fin N)
    (hδ : 0 < δ) (hM : 0 ≤ maxCap R N i) :
    AffineIndependent ℝ ![firstVertices δ R N i 0,
      firstVertices δ R N i 1, firstVertices δ R N i 2] ∧
    AffineIndependent ℝ ![secondVertices δ R N i 0,
      secondVertices δ R N i 1, secondVertices δ R N i 2] := by
  have h := coordinate_nondegenerate i hδ hM
  constructor
  · convert h.map' (firstProjectedAffine δ (midpoint N i))
      (firstProjectedAffine_injective δ (midpoint N i)) using 1
    ext j
    fin_cases j <;> rfl
  · convert h.map' (secondProjectedAffine δ (midpoint N i))
      (secondProjectedAffine_injective δ (midpoint N i)) using 1
    ext j
    fin_cases j <;> rfl

lemma coordinate_parallel_sides (δ : ℝ) (R : ℝ → ℝ) (N : ℕ) (i : Fin N) :
    coordinateVertices δ R N i 1 - coordinateVertices δ R N i 0 =
      (0, 2 * halfwidth N * collar δ N) ∧
    coordinateVertices δ R N i 3 - coordinateVertices δ R N i 2 =
      (0, 2 * halfwidth N * (maxCap R N i + 3 * collar δ N)) := by
  constructor <;> ext <;>
    simp [coordinateVertices, Footprints.trapezoidVertices, collar] <;> ring

private lemma affine_side (f : (ℝ × ℝ) →ᵃ[ℝ] Space) {p q : ℝ × ℝ} {a : ℝ}
    (h : p - q = (0,a)) : f p - f q = a • f.linear (0,1) := by
  calc
    f p - f q = f.linear (p-q) := (f.linearMap_vsub p q).symm
    _ = f.linear (a • (0,1)) := by rw [h]; congr 1; ext <;> simp
    _ = a • f.linear (0,1) := f.linear.map_smul a (0,1)

private lemma affine_vertical_ne_zero (f : (ℝ × ℝ) →ᵃ[ℝ] Space)
    (hf : Function.Injective f) : f.linear (0,1) ≠ 0 := by
  intro h
  have heq : f.linear (0,1) = f.linear (0,0) := by
    change f.linear (0,1) = f.linear 0
    rw [map_zero]
    exact h
  have := (f.linear_injective_iff.mpr hf) heq
  norm_num at this

theorem projected_parallel_sides {δ : ℝ} {R : ℝ → ℝ} {N : ℕ} (i : Fin N)
    (hδ : 0 < δ) (hM : 0 ≤ maxCap R N i) :
    0 < 2 * halfwidth N * collar δ N ∧
    0 < 2 * halfwidth N * (maxCap R N i + 3 * collar δ N) ∧
    ∃ vU vL : Space, vU ≠ 0 ∧ vL ≠ 0 ∧
      firstVertices δ R N i 1 - firstVertices δ R N i 0 =
        (2 * halfwidth N * collar δ N) • vU ∧
      firstVertices δ R N i 3 - firstVertices δ R N i 2 =
        (2 * halfwidth N * (maxCap R N i + 3 * collar δ N)) • vU ∧
      secondVertices δ R N i 1 - secondVertices δ R N i 0 =
        (2 * halfwidth N * collar δ N) • vL ∧
      secondVertices δ R N i 3 - secondVertices δ R N i 2 =
        (2 * halfwidth N * (maxCap R N i + 3 * collar δ N)) • vL := by
  have hρ := halfwidth_pos (Nat.zero_lt_of_lt i.isLt)
  have he : 0 < collar δ N := by unfold collar; positivity
  obtain ⟨hl,hr⟩ := coordinate_parallel_sides δ R N i
  refine ⟨by positivity, by positivity,
    (firstProjectedAffine δ (midpoint N i)).linear (0,1),
    (secondProjectedAffine δ (midpoint N i)).linear (0,1),
    affine_vertical_ne_zero _ (firstProjectedAffine_injective δ (midpoint N i)),
    affine_vertical_ne_zero _ (secondProjectedAffine_injective δ (midpoint N i)),
    affine_side _ hl, affine_side _ hr, affine_side _ hl, affine_side _ hr⟩

theorem family_shape {δ : ℝ} (hδ : 0 < δ) {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1) 1)) (hR0 : ∀ r ∈ Icc (-1:ℝ) 1, 0 ≤ R r)
    {N : ℕ} (i : Fin N) :
    firstBase δ R N i = convexHull ℝ (range (firstVertices δ R N i)) ∧
    secondBase δ R N i = convexHull ℝ (range (secondVertices δ R N i)) ∧
    Function.Injective (firstVertices δ R N i) ∧
    Function.Injective (secondVertices δ R N i) := by
  apply projected_shape i hδ
  exact RadialRiemann.capMax_nonneg (by norm_num) hR hR0 i

end CylinderCovering.HalfheightFinite.Shape

end

end OAI
