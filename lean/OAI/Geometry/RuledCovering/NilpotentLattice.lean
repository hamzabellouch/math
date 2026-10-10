import OAI.Geometry.RuledCovering.SpecializedCover

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A square-zero planar operator has an orthonormal shear frame, with no bound
on the shear coefficient. -/
lemma nilpotent_frame (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ d : ℝ, ∀ z : Plane,
      R.symm (A (R z)) = vec2 (d * z 1) 0 := by
  classical
  have hAA (x : Plane) : A (A x) = 0 := by
    have hh := congrArg (fun T : Plane →L[ℝ] Plane => T x) hA
    exact hh
  have hex : ∃ u : Plane, ‖u‖ = 1 ∧ A u = 0 := by
    by_cases hz : A = 0
    · refine ⟨vec2 1 0, ?_, by simp [hz]⟩
      simp [vec2, EuclideanSpace.norm_eq]
    · have hx : ∃ x : Plane, A x ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        apply ContinuousLinearMap.ext
        exact h
      obtain ⟨x, hx⟩ := hx
      refine ⟨‖A x‖⁻¹ • A x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      · simp [hAA]
  obtain ⟨u, hu, hAu⟩ := hex
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp i.property)
    have hj : j = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp j.property)
    subst i
    subst j
    simp [hu]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Plane ≃ₗᵢ[ℝ] Plane := b.repr.symm
  have hb0 : b 0 = u := hb 0 (by simp)
  have hrepr0 : b.repr (A (b 0)) = 0 := by rw [hb0, hAu, map_zero]
  let W : Plane →ₗ[ℝ] Plane := b.repr.toLinearMap.comp (A.toLinearMap.comp b.repr.symm.toLinearMap)
  have he0 : vec2 1 0 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hW0 : W (vec2 1 0) = 0 := by
    change b.repr (A (b.repr.symm (vec2 1 0))) = 0
    rw [he0, b.repr_symm_single]
    exact hrepr0
  have hWW (z : Plane) : W (W z) = 0 := by
    simp [W, hAA]
  have hexp (z : Plane) : z = z 0 • vec2 1 0 + z 1 • vec2 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hWexp (z : Plane) : W z = z 1 • W (vec2 0 1) := by
    nth_rw 1 [hexp z]
    rw [map_add, map_smul, map_smul, hW0, smul_zero, zero_add]
  have hz11 : W (vec2 0 1) 1 = 0 := by
    have hs := congrArg (fun z : Plane => z 1) (hWW (vec2 0 1))
    rw [hWexp (W (vec2 0 1))] at hs
    change W (vec2 0 1) 1 * W (vec2 0 1) 1 = 0 at hs
    exact mul_self_eq_zero.mp hs
  refine ⟨R, W (vec2 0 1) 0, fun z => ?_⟩
  change W z = _
  rw [hWexp]
  ext i
  fin_cases i
  · change z 1 * W (vec2 0 1) 0 = W (vec2 0 1) 0 * z 1
    ring
  · change z 1 * W (vec2 0 1) 1 = 0
    rw [hz11, mul_zero]

def shearLinear : Coordinates →ₗ[ℝ] Coordinates where
  toFun p := ![p 1, 0]
  map_add' p q := by ext i; fin_cases i <;> simp
  map_smul' c p := by ext i; fin_cases i <;> simp

def shearCLM : Coordinates →L[ℝ] Coordinates := shearLinear.toContinuousLinearMap

/-- A sliding-row lattice for every real shear; the retained radius is finite
but no smallness of the derivative is imposed. -/
theorem nilpotent_lattice_model (d : ℝ) :
    LatticeModel (d • shearCLM) 1 ((1+|d|)/2) := by
  intro n hn p r hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨i,j,hi,hj⟩ := sliding_rows_cover (r*d)
    ((n:ℝ)*p 0 + r*d*((n:ℝ)*p 1)) ((n:ℝ)*p 1)
  have hrd : |r*d| ≤ |d| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_right hr (abs_nonneg d)
  have hd0 : |(n:ℝ)*p 0-i| ≤ (1+|d|)/2 := by
    have heq : (n:ℝ)*p 0-i =
        ((n:ℝ)*p 0+r*d*((n:ℝ)*p 1)-(i+r*d*j))-r*d*((n:ℝ)*p 1-j) := by ring
    rw [heq]
    exact (abs_sub _ _).trans (by
      rw [abs_mul]
      have hm := mul_le_mul hrd hj (abs_nonneg _) (abs_nonneg d)
      linarith)
  let b : Coordinates := ![(i:ℝ)/n,(j:ℝ)/n]
  let : NeZero n := ⟨hn.ne'⟩
  have hb : b ∈ coordinateGrid n := by
    apply BoxIntegral.unitPartition.mem_smul_span_iff.mpr
    intro k
    fin_cases k
    · exact ⟨i, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
    · exact ⟨j, by simp [b, mul_div_cancel₀ _ hnR.ne']⟩
  refine ⟨b,hb,?_,?_⟩
  · rw [dist_eq_norm, norm_sub_rev]
    apply norm_le_of_scaled_coordinates hnR (by positivity)
    intro k
    fin_cases k
    · simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hd0
    · have hj' : |(n:ℝ)*p 1-j| ≤ (1+|d|)/2 := by linarith [abs_nonneg d]
      simpa [b, mul_sub, mul_div_cancel₀ _ hnR.ne'] using hj'
  · have hbnd : ‖p-b+r • (d • shearCLM) (p-b)‖ ≤ (1/2:ℝ)/n := by
      apply norm_le_of_scaled_coordinates hnR (by norm_num)
      intro k
      fin_cases k
      · convert hi using 1
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
        ring
      · convert hj using 1
        congr 1
        simp [b,shearCLM,shearLinear,Matrix.vecHead,Matrix.vecTail]
        field_simp
    convert hbnd using 1
    ring

def orthogonalFrame (R : Plane ≃ₗᵢ[ℝ] Plane) : Coordinates ≃L[ℝ] Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.trans R.toContinuousLinearEquiv

lemma orthogonal_closedBall_square (R : Plane ≃ₗᵢ[ℝ] Plane) (b : Coordinates)
    {a : ℝ} (ha : 0 < a) :
    IsSquareTile (orthogonalFrame R '' closedBall b a) := by
  let M := orthogonalFrame R
  refine ⟨M b,R,2*a,by positivity,?_⟩
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    let q : Coordinates := fun i => (x i-b i)/(2*a)
    refine ⟨WithLp.toLp 2 q, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg ha.le] at hx
      intro i
      change |(x i-b i)/(2*a)| ≤ 1/2
      rw [abs_div, abs_of_pos (by positivity : 0 < 2*a)]
      apply (div_le_iff₀ (by positivity : 0 < 2*a)).mpr
      have hi := hx i
      change |x i-b i| ≤ a at hi
      linarith
    · change M b+(2*a) • M q = M x
      rw [← map_smul, ← map_add]
      congr 1
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,q]
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) ha.ne')]
      ring
  · rintro ⟨x,hx,rfl⟩
    refine ⟨b+(2*a) • WithLp.ofLp x, ?_, ?_⟩
    · rw [coordinates_closedBall b ha.le]
      intro i _
      change b i-a ≤ b i+(2*a)*x i ∧ b i+(2*a)*x i ≤ b i+a
      have hi := abs_le.mp (hx i)
      constructor <;> nlinarith [hi.1,hi.2]
    · change M (b+(2*a) • WithLp.ofLp x) = M b + (2*a) • R x
      simp [M,orthogonalFrame]

def squareProjected (h : ℝ) (C : Cylinder) : Prop :=
  ∃ T : Set Plane, ∃ g : Plane, IsSquareTile T ∧ C = projectedCylinder h g T

end RuledApproximation

end

end OAI
