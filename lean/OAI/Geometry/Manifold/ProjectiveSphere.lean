import Mathlib

namespace OAI

 

noncomputable section

open scoped Manifold ContDiff BigOperators ENNReal
open Bundle

namespace EinsteinFour

abbrev FourSpace := EuclideanSpace ℝ (Fin 4)
abbrev I4 := 𝓘(ℝ, FourSpace)

 
def coordinateVector (i : Fin 4) : FourSpace := EuclideanSpace.single i 1

 
abbrev RoundSphere4 := {x : EuclideanSpace ℝ (Fin 5) // ‖x‖ = 1}

 
abbrev ComplexProjective2 := Projectivization ℂ (EuclideanSpace ℂ (Fin 3))

 
abbrev RealProjective4 := Projectivization ℝ (EuclideanSpace ℝ (Fin 5))

 
def roundDistance (p q : RoundSphere4) : ℝ :=
  Real.arccos (inner ℝ p.val q.val)

 

def fubiniStudyDistance (p q : ComplexProjective2) : ℝ :=
  Real.arccos (‖inner ℂ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

 

def realProjectiveDistance (p q : RealProjective4) : ℝ :=
  Real.arccos (‖inner ℝ p.rep q.rep‖ / (‖p.rep‖ * ‖q.rep‖))

section Metric

variable (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

 
abbrev SmoothMetric :=
  ContMDiffRiemannianMetric I4 ∞ FourSpace (TangentSpace I4 : M → Type _)

variable {M}

 

def metricInChart (g : SmoothMetric M) (c : M) (z : FourSpace) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  let e := chartAt FourSpace c
  let d := mfderiv I4 I4 e.symm z
  fun i j => g.inner (e.symm z) (d (coordinateVector i)) (d (coordinateVector j))

 
def partialDeriv (f : FourSpace → ℝ) (i : Fin 4) (z : FourSpace) : ℝ :=
  fderiv ℝ f z (coordinateVector i)

 

def christoffel (g : SmoothMetric M) (c : M) (z : FourSpace)
    (k i j : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 4, (metricInChart g c z)⁻¹ k l *
    (partialDeriv (fun w => metricInChart g c w j l) i z +
     partialDeriv (fun w => metricInChart g c w i l) j z -
     partialDeriv (fun w => metricInChart g c w i j) l z)

 

def curvatureComponent (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) : ℝ :=
  partialDeriv (fun w => christoffel g c w l j k) i z -
  partialDeriv (fun w => christoffel g c w l i k) j z +
  ∑ p : Fin 4,
    (christoffel g c z l i p * christoffel g c z p j k -
     christoffel g c z l j p * christoffel g c z p i k)

 
def ricciInChart (g : SmoothMetric M) (c : M) (z : FourSpace)
    (i j : Fin 4) : ℝ :=
  ∑ k : Fin 4, curvatureComponent g c z k k i j

 

def sectionalNumerator (g : SmoothMetric M) (c : M) (z : FourSpace)
    (u v : FourSpace) : ℝ :=
  ∑ l : Fin 4, ∑ m : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4,
    metricInChart g c z l m * curvatureComponent g c z l i j k *
      u i * v j * v k * u m

 
def IsEinstein (g : SmoothMetric M) : Prop :=
  ∃ lam : ℝ, ∀ (c : M) (i j : Fin 4),
    ricciInChart g c (chartAt FourSpace c c) i j =
      lam * metricInChart g c (chartAt FourSpace c c) i j

 
def HasPositiveSectionalCurvature (g : SmoothMetric M) : Prop :=
  ∀ (c : M) (u v : FourSpace), LinearIndependent ℝ ![u, v] →
    0 < sectionalNumerator g c (chartAt FourSpace c c) u v

 

def scaledEDistance (g : SmoothMetric M) (a : ℝ) (x y : M) : ℝ≥0∞ :=
  letI : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  ENNReal.ofReal (Real.sqrt a) * Manifold.riemannianEDist I4 x y

 

def ScaledIsometricTo {N : Type*} (g : SmoothMetric M) (a : ℝ)
    (modelDistance : N → N → ℝ) : Prop :=
  ∃ f : M ≃ N, ∀ x y : M,
    ENNReal.ofReal (modelDistance (f x) (f y)) = scaledEDistance g a x y

end Metric

 

section SphereInvolution

variable {E : Type*} [NormedAddCommGroup E]

 
abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}

 
def antipode (x : UnitSphere E) : UnitSphere E :=
  ⟨-x.val, by simpa using x.property⟩

@[simp] theorem antipode_val (x : UnitSphere E) : (antipode x).val = -x.val := rfl

@[simp] theorem antipode_antipode (x : UnitSphere E) : antipode (antipode x) = x := by
  apply Subtype.ext
  simp

theorem unitSphere_ne_zero (x : UnitSphere E) : x.val ≠ 0 := by
  intro h
  have hx := x.property
  simp [h] at hx

variable [InnerProductSpace ℝ E]

theorem antipode_ne_self (x : UnitSphere E) : antipode x ≠ x := by
  intro h
  have h' : -x.val = x.val := congrArg Subtype.val h
  have hz : x.val = 0 := by
    have hh : (2 : ℝ) • x.val = 0 := by
      calc
        (2 : ℝ) • x.val = x.val + x.val := by module
        _ = -x.val + x.val := by rw [h']
        _ = 0 := neg_add_cancel x.val
    exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
  exact unitSphere_ne_zero x hz

 

theorem sphere_involution_antipodal
    (τ : UnitSphere E → UnitSphere E)
    (hτ : Function.Involutive τ)
    (hinner : ∀ x y, inner ℝ (τ x).val (τ y).val = inner ℝ x.val y.val)
    (hfree : ∀ x, τ x ≠ x) :
    ∀ x, τ x = antipode x := by
  intro x
  apply Subtype.ext
  change (τ x).val = -x.val
  by_contra hneg
  have hv : x.val + (τ x).val ≠ 0 := by
    intro hz
    exact hneg (eq_neg_of_add_eq_zero_right hz)
  let r : ℝ := ‖x.val + (τ x).val‖
  have hr : 0 < r := norm_pos_iff.mpr hv
  let z : UnitSphere E :=
    ⟨r⁻¹ • (x.val + (τ x).val), by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      exact inv_mul_cancel₀ (ne_of_gt hr)⟩
  have hzx := hinner z x
  have hzτx := hinner z (τ x)
  rw [hτ x] at hzτx
  have hzinner : inner ℝ (τ z).val z.val = inner ℝ z.val z.val := by
    change inner ℝ (τ z).val (r⁻¹ • (x.val + (τ x).val)) =
      inner ℝ z.val (r⁻¹ • (x.val + (τ x).val))
    simp only [inner_smul_right, inner_add_right]
    rw [hzx, hzτx, add_comm]
  have hzfixed : τ z = z := by
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have hzinner' : inner ℝ z.val (τ z).val = inner ℝ z.val z.val :=
      (real_inner_comm (τ z).val z.val).trans hzinner
    simp only [inner_sub_left, inner_sub_right, hinner z z, hzinner, hzinner',
      sub_self]
  exact hfree z hzfixed

end SphereInvolution

 

theorem round_distance_preserving_inner
    (τ : RoundSphere4 → RoundSphere4)
    (h : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y) :
    ∀ x y, inner ℝ (τ x).val (τ y).val = inner ℝ x.val y.val := by
  have bounds (x y : RoundSphere4) :
      -(1 : ℝ) ≤ inner ℝ x.val y.val ∧ inner ℝ x.val y.val ≤ 1 := by
    apply abs_le.mp
    simpa [x.property, y.property] using abs_real_inner_le_norm x.val y.val
  intro x y
  have heq := congrArg Real.cos (h x y)
  dsimp only [roundDistance] at heq
  rw [Real.cos_arccos (bounds (τ x) (τ y)).1 (bounds (τ x) (τ y)).2,
    Real.cos_arccos (bounds x y).1 (bounds x y).2] at heq
  exact heq

 

theorem free_round_involution_eq_antipode
    (τ : RoundSphere4 → RoundSphere4)
    (hτ : Function.Involutive τ)
    (hDistance : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y)
    (hfree : ∀ x, τ x ≠ x) : τ = antipode := by
  funext x
  exact sphere_involution_antipodal τ hτ
    (round_distance_preserving_inner τ hDistance) hfree x

section ProjectiveDistance

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

 

theorem normalized_inner_smul (x y : E) (a b : 𝕜) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖inner 𝕜 (a • x) (b • y)‖ / (‖a • x‖ * ‖b • y‖) =
      ‖inner 𝕜 x y‖ / (‖x‖ * ‖y‖) := by
  simp only [inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj, norm_smul]
  calc
    ‖b‖ * (‖a‖ * ‖inner 𝕜 x y‖) / (‖a‖ * ‖x‖ * (‖b‖ * ‖y‖)) =
        (‖a‖ * ‖b‖) * ‖inner 𝕜 x y‖ / ((‖a‖ * ‖b‖) * (‖x‖ * ‖y‖)) := by
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ (mul_ne_zero (norm_ne_zero_iff.mpr ha)
      (norm_ne_zero_iff.mpr hb))

 

theorem normalized_inner_mk_rep (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖inner 𝕜 (Projectivization.mk 𝕜 x hx).rep (Projectivization.mk 𝕜 y hy).rep‖ /
        (‖(Projectivization.mk 𝕜 x hx).rep‖ * ‖(Projectivization.mk 𝕜 y hy).rep‖) =
      ‖inner 𝕜 x y‖ / (‖x‖ * ‖y‖) := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep 𝕜 x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep 𝕜 y hy
  rw [← ha, ← hb]
  exact normalized_inner_smul x y (a : 𝕜) (b : 𝕜) a.ne_zero b.ne_zero

end ProjectiveDistance

theorem fubiniStudyDistance_mk (x y : EuclideanSpace ℂ (Fin 3))
    (hx : x ≠ 0) (hy : y ≠ 0) :
    fubiniStudyDistance (Projectivization.mk ℂ x hx) (Projectivization.mk ℂ y hy) =
      Real.arccos (‖inner ℂ x y‖ / (‖x‖ * ‖y‖)) := by
  rw [fubiniStudyDistance, normalized_inner_mk_rep]

theorem realProjectiveDistance_mk (x y : EuclideanSpace ℝ (Fin 5))
    (hx : x ≠ 0) (hy : y ≠ 0) :
    realProjectiveDistance (Projectivization.mk ℝ x hx) (Projectivization.mk ℝ y hy) =
      Real.arccos (‖inner ℝ x y‖ / (‖x‖ * ‖y‖)) := by
  rw [realProjectiveDistance, normalized_inner_mk_rep]

section AntipodalQuotient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 
def sphereToProjective (x : UnitSphere E) : Projectivization ℝ E :=
  Projectivization.mk ℝ x.val (unitSphere_ne_zero x)

 
theorem sphereToProjective_surjective :
    Function.Surjective (sphereToProjective : UnitSphere E → Projectivization ℝ E) := by
  intro p
  have hp : 0 < ‖p.rep‖ := norm_pos_iff.mpr p.rep_nonzero
  let x : UnitSphere E := ⟨‖p.rep‖⁻¹ • p.rep, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    exact inv_mul_cancel₀ (ne_of_gt hp)⟩
  refine ⟨x, ?_⟩
  change Projectivization.mk ℝ x.val (unitSphere_ne_zero x) = p
  conv_rhs => rw [← p.mk_rep]
  refine (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ⟨‖p.rep‖⁻¹, rfl⟩

 
theorem sphereToProjective_eq_iff (x y : UnitSphere E) :
    sphereToProjective x = sphereToProjective y ↔ x = y ∨ x = antipode y := by
  rw [sphereToProjective, sphereToProjective, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have habs := congrArg norm ha
    simp only [norm_smul, Real.norm_eq_abs, x.property, y.property, mul_one] at habs
    have ha' : a = 1 ∨ a = -1 := by
      rcases le_total 0 a with h | h
      · left
        rwa [abs_of_nonneg h] at habs
      · right
        rw [abs_of_nonpos h] at habs
        linarith
    rcases ha' with ha' | ha'
    · left
      apply Subtype.ext
      simpa [ha'] using ha.symm
    · right
      apply Subtype.ext
      simpa [ha'] using ha.symm
  · rintro (h | h)
    · exact ⟨1, by simpa using (congrArg Subtype.val h).symm⟩
    · exact ⟨-1, by simpa using (congrArg Subtype.val h).symm⟩

 
def antipodalSetoid (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Setoid (UnitSphere E) where
  r x y := x = y ∨ x = antipode y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun h => sphereToProjective_eq_iff _ _ |>.mp
      ((sphereToProjective_eq_iff _ _).mpr h).symm
    trans := fun h₁ h₂ => (sphereToProjective_eq_iff _ _).mp
      (((sphereToProjective_eq_iff _ _).mpr h₁).trans
        ((sphereToProjective_eq_iff _ _).mpr h₂)) }

 

def antipodalQuotientEquiv : Quotient (antipodalSetoid E) ≃ Projectivization ℝ E :=
  Equiv.ofBijective
    (Quotient.lift sphereToProjective fun x y h => (sphereToProjective_eq_iff x y).mpr h)
    (by
      constructor
      · intro x y h
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact Quotient.sound ((sphereToProjective_eq_iff x y).mp h)
      · intro p
        obtain ⟨x, hx⟩ := sphereToProjective_surjective (E := E) p
        exact ⟨Quotient.mk _ x, hx⟩)

@[simp] theorem antipodalQuotientEquiv_mk (x : UnitSphere E) :
    antipodalQuotientEquiv (Quotient.mk (antipodalSetoid E) x) = sphereToProjective x := rfl

end AntipodalQuotient

 
theorem realProjectiveDistance_sphere (x y : RoundSphere4) :
    realProjectiveDistance (sphereToProjective x) (sphereToProjective y) =
      Real.arccos |inner ℝ x.val y.val| := by
  rw [sphereToProjective, sphereToProjective, realProjectiveDistance_mk,
    x.property, y.property, mul_one, div_one, Real.norm_eq_abs]

 

theorem realProjectiveDistance_eq_min (x y : RoundSphere4) :
    realProjectiveDistance (sphereToProjective x) (sphereToProjective y) =
      min (roundDistance x y) (roundDistance x (antipode y)) := by
  rw [realProjectiveDistance_sphere]
  simp only [roundDistance, antipode_val, inner_neg_right]
  by_cases h : 0 ≤ inner ℝ x.val y.val
  · rw [abs_of_nonneg h, min_eq_left]
    exact Real.antitone_arccos (by linarith)
  · rw [abs_of_neg (lt_of_not_ge h), min_eq_right]
    exact Real.antitone_arccos (by linarith)

 

theorem free_round_involution_projective_fibers_and_distance
    (τ : RoundSphere4 → RoundSphere4)
    (hτ : Function.Involutive τ)
    (hDistance : ∀ x y, roundDistance (τ x) (τ y) = roundDistance x y)
    (hfree : ∀ x, τ x ≠ x) :
    (∀ x y, sphereToProjective x = sphereToProjective y ↔ x = y ∨ x = τ y) ∧
    (∀ x y, realProjectiveDistance (sphereToProjective x) (sphereToProjective y) =
      min (roundDistance x y) (roundDistance x (τ y))) := by
  rw [free_round_involution_eq_antipode τ hτ hDistance hfree]
  exact ⟨sphereToProjective_eq_iff, realProjectiveDistance_eq_min⟩

 

end EinsteinFour

end

end OAI
