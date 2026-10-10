import OAI.Geometry.RCD.Sobolev.DirichletContractions

namespace OAI

/-! # Weak maximum principle for the constructed Dirichlet solutions -/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A Dirichlet solution of a nonnegative functional is nonnegative. The
proof uses the actual positive-part contraction and its energy inequality. -/
theorem dirichlet_solution_nonneg (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (F : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ)
    (hpositive : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) → 0 ≤ F φ)
    (f : SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f.val φ.val = F φ) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f.val x := by
  let φ : ℝ → ℝ := fun x => max x 0
  have hφ : LipschitzWith 1 φ :=
    (LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).max_const 0
  have hφ0 : φ 0 = 0 := max_self 0
  let u := SobolevSpace.compContraction μ hQ hφ hφ0 f.val
  have hu : u ∈ SobolevSpace.dirichlet μ hQ Ω :=
    SobolevSpace.compContraction_mem_dirichlet μ hQ hφ hφ0 Ω f.val f.property
  let v : SobolevSpace.dirichlet μ hQ Ω := ⟨u - f.val,
    (SobolevSpace.dirichlet μ hQ Ω).sub_mem hu f.property⟩
  have hucoe : SobolevSpace.toLp μ hQ u =ᵐ[μ]
      fun x => max (SobolevSpace.toLp μ hQ f.val x) 0 :=
    hφ.coeFn_compLp hφ0 (SobolevSpace.toLp μ hQ f.val)
  have hvnonneg : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ v.val x := by
    filter_upwards [hucoe, Lp.coeFn_sub (SobolevSpace.toLp μ hQ u)
      (SobolevSpace.toLp μ hQ f.val)] with x hx hvx
    change 0 ≤ (SobolevSpace.toLp μ hQ (u - f.val)) x
    rw [map_sub, hvx, Pi.sub_apply, hx]
    exact sub_nonneg.mpr (le_max_left _ _)
  have hF := hpositive v hvnonneg
  have htest := hsolve v
  have he := SobolevSpace.energy_compContraction_le μ hQ hφ hφ0 f.val
  have he' : energyForm μ hQ u u ≤ energyForm μ hQ f.val f.val := by
    rw [energyForm_self, energyForm_self]
    exact mul_le_mul_of_nonneg_left he (by norm_num)
  have hcomm := energyForm_comm μ hQ u f.val
  have hvenergy : energyForm μ hQ v.val v.val ≤ 0 := by
    change energyForm μ hQ (u - f.val) (u - f.val) ≤ 0
    change energyForm μ hQ f.val (u - f.val) = F v at htest
    rw [energyForm_sub_right] at htest
    simp only [energyForm_sub_left, energyForm_sub_right]
    linarith
  have hnorm := (hbound v).trans (mul_nonpos_of_nonneg_of_nonpos hP hvenergy)
  have hlp : SobolevSpace.toLp μ hQ v.val = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hnorm (sq_nonneg _)))
  have hvzero : u - f.val = 0 := Subtype.ext hlp
  have huf := sub_eq_zero.mp hvzero
  rw [huf] at hucoe
  filter_upwards [hucoe] with x hx
  rw [hx]
  exact le_max_right _ _

/-- The positive solution exists for every positive continuous source. -/
theorem exists_nonnegative_dirichlet_solution (Ω : Set X) {P : ℝ} (hP : 0 ≤ P)
    (hbound : ∀ f : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ f.val‖ ^ 2 ≤ P * energyForm μ hQ f.val f.val)
    (F : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ)
    (hpositive : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) → 0 ≤ F φ) :
    ∃ f : SobolevSpace.dirichlet μ hQ Ω,
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        energyForm μ hQ f.val φ.val = F φ) ∧
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ f.val x) := by
  obtain ⟨f, hf, _⟩ := existsUnique_dirichlet_solution μ hQ Ω hP hbound F
  exact ⟨f, hf, dirichlet_solution_nonneg μ hQ Ω hP hbound F hpositive f hf⟩

end RegularPointCoordinates

end

end OAI
