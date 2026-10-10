import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarRecorder
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarAnisotropic
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.OrderedSweep

namespace OAI

/-! Rational parking columns and filled translation tubes for the planar
processor. The same horizontal compression used by the recorder leaves a
quantitative gap between every two parking columns. -/

noncomputable section

namespace ForcedComputation.PlanarRouting

open ShearFlows Set
open scoped BigOperators

def centerQ (R : RationalBox 2) (j : Fin 2) : ℚ := (R.lower j + R.upper j) / 2

def halfWidthQ (R : RationalBox 2) (j : Fin 2) : ℚ := (R.upper j - R.lower j) / 2

@[simp] theorem centerQ_cast (R : RationalBox 2) (j : Fin 2) :
    (centerQ R j : ℝ) = R.center j := by simp [centerQ, RationalBox.center]

@[simp] theorem halfWidthQ_cast (R : RationalBox 2) (j : Fin 2) :
    (halfWidthQ R j : ℝ) = R.halfWidth j := by simp [halfWidthQ, RationalBox.halfWidth]

def recenter (R : RationalBox 2) (p : Fin 2 → ℚ) : RationalBox 2 :=
  ⟨fun j => p j - halfWidthQ R j, fun j => p j + halfWidthQ R j⟩

theorem recenter_center (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (recenter R p).center = fun j => (p j : ℝ) := by
  funext j
  dsimp [recenter, RationalBox.center]
  push_cast
  ring

theorem recenter_halfWidth (R : RationalBox 2) (p : Fin 2 → ℚ) (j : Fin 2) :
    (recenter R p).halfWidth j = R.halfWidth j := by
  dsimp [recenter, RationalBox.halfWidth, halfWidthQ]
  push_cast
  ring

theorem recenter_positive {R : RationalBox 2} (hR : R.positive) (p : Fin 2 → ℚ) :
    (recenter R p).positive := by
  intro j
  have := hR j
  dsimp [recenter, halfWidthQ]
  linarith

theorem recenter_image (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (fun x : Plane => x + ((fun j => (p j : ℝ)) - R.center)) '' R.carrier =
      (recenter R p).carrier := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply RationalBox.mem_carrier_iff.mpr
    intro j
    rw [recenter_center, recenter_halfWidth]
    have he : (x + ((fun j => (p j : ℝ)) - R.center)) j - (p j : ℝ) =
        x j - R.center j := by simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [he]
    exact RationalBox.mem_carrier_iff.mp hx j
  · intro hy
    let x : Plane := y - ((fun j => (p j : ℝ)) - R.center)
    refine ⟨x, RationalBox.mem_carrier_iff.mpr ?_, ?_⟩
    · intro j
      have hj := RationalBox.mem_carrier_iff.mp hy j
      rw [recenter_center, recenter_halfWidth] at hj
      have he : x j - R.center j = y j - (p j : ℝ) := by
        dsimp [x]
        ring
      rw [he]
      exact hj
    · exact sub_add_cancel _ _

/-- A filled tube containing every intermediate translated rectangle. -/
def translationTube (R : RationalBox 2) (p : Fin 2 → ℚ) : RationalBox 2 :=
  ⟨fun j => min (R.lower j) ((recenter R p).lower j),
    fun j => max (R.upper j) ((recenter R p).upper j)⟩

theorem translationTube_positive {R : RationalBox 2} (hR : R.positive) (p : Fin 2 → ℚ) :
    (translationTube R p).positive := by
  intro j
  exact (min_le_left _ _).trans_lt ((hR j).trans_le (le_max_left _ _))

theorem translationPath_mem_tube {R : RationalBox 2} {x : Plane} (hx : x ∈ R.carrier)
    (p : Fin 2 → ℚ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    x + θ • ((fun j => (p j : ℝ)) - R.center) ∈ (translationTube R p).carrier := by
  have hy : x + ((fun j => (p j : ℝ)) - R.center) ∈ (recenter R p).carrier := by
    rw [← recenter_image]
    exact mem_image_of_mem _ hx
  intro j
  have hlo₀ : ((translationTube R p).lower j : ℝ) ≤ x j := by
    calc
      ((translationTube R p).lower j : ℝ) ≤ (R.lower j : ℝ) := by
        exact_mod_cast (min_le_left (R.lower j) ((recenter R p).lower j))
      _ ≤ x j := (hx j).1
  have hhi₀ : x j ≤ ((translationTube R p).upper j : ℝ) :=
    (hx j).2.trans (by exact_mod_cast (le_max_left (R.upper j) ((recenter R p).upper j)))
  have hlo₁ : ((translationTube R p).lower j : ℝ) ≤
      x j + ((p j : ℝ) - R.center j) := by
    calc
      ((translationTube R p).lower j : ℝ) ≤ ((recenter R p).lower j : ℝ) := by
        exact_mod_cast (min_le_right (R.lower j) ((recenter R p).lower j))
      _ ≤ x j + ((p j : ℝ) - R.center j) := (hy j).1
  have hhi₁ : x j + ((p j : ℝ) - R.center j) ≤ ((translationTube R p).upper j : ℝ) :=
    (hy j).2.trans (by exact_mod_cast (le_max_right (R.upper j) ((recenter R p).upper j)))
  change ((translationTube R p).lower j : ℝ) ≤ x j + θ * ((p j : ℝ) - R.center j) ∧
    x j + θ * ((p j : ℝ) - R.center j) ≤ ((translationTube R p).upper j : ℝ)
  constructor <;> nlinarith [hθ.1, hθ.2]

def parkingScale (n : ℕ) : ℚ := 1 / (64 * (n + 1))

def parkingCenter (n : ℕ) (i : Fin n) : Fin 2 → ℚ :=
  ![1 / 2 + ((i.val : ℚ) + 1) / (4 * ((n : ℚ) + 1)), 3 / 4]

/-- This contains the whole four-shear trajectory, not only its endpoints. -/
def parkingBox (n : ℕ) (κ : ℚ) (i : Fin n) : RationalBox 2 :=
  letI := ShearFlows.neZeroTwo
  ⟨![parkingCenter n i 0 - parkingScale n * κ, 3 / 4 - (3 / 8) * κ],
    ![parkingCenter n i 0 + parkingScale n * κ, 3 / 4 + (3 / 8) * κ]⟩

theorem parkingScale_pos (n : ℕ) : 0 < parkingScale n := by
  unfold parkingScale
  positivity

theorem parkingScale_le (n : ℕ) : parkingScale n ≤ 1 / 64 := by
  unfold parkingScale
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have : (0 : ℚ) ≤ n := by positivity
  nlinarith

theorem parkingCenter_bounds (n : ℕ) (i : Fin n) :
    (1 / 2 : ℚ) < parkingCenter n i 0 ∧ parkingCenter n i 0 < 3 / 4 := by
  have hn : (0 : ℚ) < n + 1 := by positivity
  have hi : (i.val : ℚ) < n := by exact_mod_cast i.isLt
  change 1 / 2 < 1 / 2 + ((i.val : ℚ) + 1) / (4 * (n + 1)) ∧
    1 / 2 + ((i.val : ℚ) + 1) / (4 * (n + 1)) < 3 / 4
  constructor
  · have hp : (0 : ℚ) < ((i.val : ℚ) + 1) / (4 * (n + 1)) := by positivity
    linarith
  · have hp : ((i.val : ℚ) + 1) / (4 * (n + 1)) < 1 / 4 := by
      apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 4 * (n + 1))).mpr
      linarith
    linarith

theorem parkingCenter_gap {n : ℕ} {i j : Fin n} (hij : i < j) :
    16 * parkingScale n ≤ parkingCenter n j 0 - parkingCenter n i 0 := by
  have hden : (0 : ℚ) < 4 * (n + 1) := by positivity
  have hij' : (i.val : ℚ) + 1 ≤ j.val := by exact_mod_cast hij
  have he : parkingCenter n j 0 - parkingCenter n i 0 =
      ((j.val : ℚ) - i.val) / (4 * (n + 1)) := by
    dsimp [parkingCenter]
    ring
  have hs : 16 * parkingScale n = 1 / (4 * (n + 1)) := by
    dsimp [parkingScale]
    field_simp
    ring
  rw [he, hs]
  exact (div_le_div_iff_of_pos_right hden).mpr (by linarith)

theorem parkingBox_positive {n : ℕ} {κ : ℚ} (hκ : 0 < κ) (i : Fin n) :
    (parkingBox n κ i).positive := by
  have hp := mul_pos (parkingScale_pos n) hκ
  intro j
  fin_cases j <;> dsimp [parkingBox] <;> linarith

theorem parkingBox_bounds {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 64)
    (i : Fin n) {x : Plane} (hx : x ∈ (parkingBox n κ i).carrier) :
    (3 / 8 : ℝ) < x 0 ∧ x 0 < 7 / 8 ∧ 2 / 3 < x 1 ∧ x 1 < 4 / 5 := by
  have hs : (0 : ℝ) < parkingScale n := by exact_mod_cast parkingScale_pos n
  have hs' : (parkingScale n : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr (parkingScale_le n)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hk : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hk' : (κ : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hκ'
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hc := parkingCenter_bounds n i
  have hc₀ : (1 / 2 : ℝ) < parkingCenter n i 0 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hc.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hc₁ : (parkingCenter n i 0 : ℝ) < 3 / 4 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hc.2
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hx₀ := hx 0
  have hx₁ := hx 1
  dsimp [parkingBox] at hx₀ hx₁
  push_cast at hx₀ hx₁
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_le_mul hs' hk' hk (by norm_num : (0 : ℝ) ≤ 1 / 64)]

theorem parkingBox_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i < j) :
    (parkingBox n κ i).upper 0 + parkingScale n ≤ (parkingBox n κ j).lower 0 := by
  have hs := parkingScale_pos n
  have hg := parkingCenter_gap hij
  have hk : parkingScale n * κ ≤ parkingScale n * (1 / 64) :=
    mul_le_mul_of_nonneg_left hκ hs.le
  dsimp [parkingBox]
  nlinarith

theorem parkingBox_separation {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i ≠ j) :
    PositivelySeparated (parkingBox n κ i).carrier (parkingBox n κ j).carrier := by
  apply EndpointGap.separated (δ := parkingScale n) ?_ (parkingScale_pos n)
  rcases lt_or_gt_of_ne hij with h | h
  · exact ⟨0, Or.inl (parkingBox_gap hκ h)⟩
  · exact ⟨0, Or.inr (parkingBox_gap hκ h)⟩

theorem recenter_subset_parking {n : ℕ} {κ : ℚ}
    (R : RationalBox 2) (i : Fin n)
    (hx : R.halfWidth 0 ≤ (parkingScale n : ℝ) * κ)
    (hy : R.halfWidth 1 ≤ (3 / 8 : ℝ) * κ) :
    (recenter R (parkingCenter n i)).carrier ⊆ (parkingBox n κ i).carrier := by
  intro x hxR
  have hm := RationalBox.mem_carrier_iff.mp hxR
  rw [recenter_center] at hm
  have h₀ := abs_le.mp ((hm 0).trans (by simpa only [recenter_halfWidth] using hx))
  have h₁ := abs_le.mp ((hm 1).trans (by simpa only [recenter_halfWidth] using hy))
  intro j
  fin_cases j
  · dsimp [parkingBox]
    push_cast
    constructor <;> linarith
  · dsimp [parkingBox, parkingCenter] at h₁ ⊢
    push_cast at h₁ ⊢
    constructor <;> linarith

theorem low_rectangle_parking_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {R : RationalBox 2} (hR : R.upper 1 ≤ 19 / 64) (i : Fin n) :
    EndpointGap (1 / 4) R (parkingBox n κ i) := by
  refine ⟨1, Or.inl ?_⟩
  dsimp [parkingBox]
  linarith

/-- The actual anisotropic scaling path of an instruction stays in its parking
box. Both input and output widths are used, since either reciprocal factor
may be large. -/
theorem instruction_scaling_mem_parking {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ)
    (i : Fin n) (r : Instruction) (hr : 0 < r.factor)
    (himage : r.affine '' r.source.carrier = r.target.carrier)
    (hsx : r.source.halfWidth 0 ≤ (parkingScale n : ℝ) * (κ : ℝ) / 2)
    (htx : r.target.halfWidth 0 ≤ (parkingScale n : ℝ) * (κ : ℝ) / 2)
    (hsy : r.source.halfWidth 1 ≤ (3 / 8 : ℝ) * (κ : ℝ) / 2)
    (hty : r.target.halfWidth 1 ≤ (3 / 8 : ℝ) * (κ : ℝ) / 2)
    {x : Plane} (hx : x ∈ r.source.carrier) (t : ℝ) :
    PlanarHamiltonian.anisotropicRoute (parkingScale n) (3 / 8) r.factor
      (fun j => (parkingCenter n i j : ℝ))
      (x + ((fun j => (parkingCenter n i j : ℝ)) - r.source.center)) t ∈
        (parkingBox n κ i).carrier := by
  let p : Plane := fun j => (parkingCenter n i j : ℝ)
  let w : Plane := x + (p - r.source.center)
  have ha : (0 : ℝ) < parkingScale n := by exact_mod_cast parkingScale_pos n
  have hμ : (0 : ℝ) < r.factor := by exact_mod_cast hr
  have hk : (0 : ℝ) ≤ (κ : ℝ) / 2 :=
    div_nonneg (by exact_mod_cast hκ) (by norm_num)
  have hy : r.affine x ∈ r.target.carrier := by
    rw [← himage]
    exact mem_image_of_mem _ hx
  have hx' := RationalBox.mem_carrier_iff.mp hx
  have hy' := RationalBox.mem_carrier_iff.mp hy
  have h₀ : |(w 0 - p 0) / (parkingScale n : ℝ)| ≤ (κ : ℝ) / 2 := by
    have he : w 0 - p 0 = x 0 - r.source.center 0 := by dsimp [w]; ring
    rw [he, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (by nlinarith [(hx' 0).trans hsx])
  have h₁ : |(w 1 - p 1) / (3 / 8 : ℝ)| ≤ (κ : ℝ) / 2 := by
    have he : w 1 - p 1 = x 1 - r.source.center 1 := by dsimp [w]; ring
    rw [he, abs_div]
    norm_num
    nlinarith [(hx' 1).trans hsy]
  have h₂ : |(r.factor : ℝ) * ((w 0 - p 0) / (parkingScale n : ℝ))| ≤
      (κ : ℝ) / 2 := by
    have he : (r.factor : ℝ) * ((w 0 - p 0) / (parkingScale n : ℝ)) =
        (r.affine x 0 - r.target.center 0) / (parkingScale n : ℝ) := by
      dsimp [w, Instruction.affine]
      ring
    rw [he, abs_div, abs_of_pos ha]
    exact (div_le_iff₀ ha).mpr (by nlinarith [(hy' 0).trans htx])
  have h₃ : |((w 1 - p 1) / (3 / 8 : ℝ)) / (r.factor : ℝ)| ≤ (κ : ℝ) / 2 := by
    have he : ((w 1 - p 1) / (3 / 8 : ℝ)) / (r.factor : ℝ) =
        (r.affine x 1 - r.target.center 1) / (3 / 8 : ℝ) := by
      dsimp [w, Instruction.affine]
      ring
    rw [he, abs_div]
    norm_num
    nlinarith [(hy' 1).trans hty]
  have hb := PlanarHamiltonian.anisotropicRoute_bound ha.le (by norm_num) hμ hk p w
    h₀ h₁ h₂ h₃ t
  change PlanarHamiltonian.anisotropicRoute (parkingScale n) (3 / 8) r.factor p w t ∈ _
  intro j
  fin_cases j
  · have hh := abs_le.mp hb.1
    dsimp [parkingBox]
    push_cast
    have hp₀ : p 0 = (parkingCenter n i 0 : ℝ) := rfl
    rw [hp₀] at hh
    constructor <;> nlinarith
  · have hh := abs_le.mp hb.2
    dsimp [parkingBox]
    push_cast
    have hp₁ : p 1 = (3 / 4 : ℝ) := by norm_num [p, parkingCenter]
    rw [hp₁] at hh
    constructor <;> nlinarith

end ForcedComputation.PlanarRouting

end

end OAI
