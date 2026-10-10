import OAI.Analysis.KadisonKastler.Polar
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI

/-! # The quadratic step in boundary cocycle correction

Only the structural properties of the boundary mean occur here.  The mean
need not be normal.  Covariance cancellation and polar normalization give
the quadratic improvement used in the measurable iteration.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- A contractive, unital, star-preserving mean with both module identities.
The map `ι` includes fields independent of the averaged variable. -/
structure BimoduleMean (ι : B →⋆ₐ[ℂ] A) where
  toCLM : A →L[ℂ] B
  map_one : toCLM 1 = 1
  map_star : ∀ x, toCLM (star x) = star (toCLM x)
  norm_le : ∀ x, ‖toCLM x‖ ≤ ‖x‖
  map_left : ∀ b x, toCLM (ι b * x) = b * toCLM x
  map_right : ∀ x b, toCLM (x * ι b) = toCLM x * b

namespace BimoduleMean

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)

@[simp]
theorem fixed (b : B) : m.toCLM (ι b) = b := by
  simpa only [mul_one, m.map_one] using m.map_left b 1

/-- The linear terms cancel exactly in the centered product. -/
theorem covariance (x y : A) :
    m.toCLM (x * y) - m.toCLM x * m.toCLM y =
      m.toCLM ((x - ι (m.toCLM x)) * (y - ι (m.toCLM y))) := by
  simp only [sub_mul, mul_sub, map_sub, m.map_right, m.map_left, m.fixed]
  noncomm_ring

/-- Contractivity of the mean bounds the covariance by its two residuals. -/
theorem norm_covariance_le (x y : A) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤
      ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := by
  rw [m.covariance]
  exact (m.norm_le _).trans (norm_mul_le _ _)

/-- For a unitary the covariance identity is the exact unitarity defect. -/
theorem variance (x : unitary A) :
    1 - star (m.toCLM (x : A)) * m.toCLM (x : A) =
      m.toCLM (star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))) := by
  have hc := m.covariance (star (x : A)) (x : A)
  have hi : ι (m.toCLM (star (x : A))) = star (ι (m.toCLM (x : A))) := by
    rw [m.map_star]
    exact StarHomClass.map_star ι _
  rw [hi] at hc
  simpa only [Unitary.star_mul_self_of_mem x.property, m.map_one, m.map_star,
    star_sub] using hc

/-- Averaging preserves the error from a field independent of the mean variable. -/
theorem norm_sub_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖m.toCLM x - b‖ ≤ e := by
  rw [← m.fixed b, ← map_sub]
  exact (m.norm_le _).trans h

/-- The residual from the average is at most twice the original error. -/
theorem norm_residual_le (x : A) (b : B) {e : ℝ} (h : ‖x - ι b‖ ≤ e) :
    ‖x - ι (m.toCLM x)‖ ≤ 2 * e := by
  calc
    _ ≤ ‖x - ι b‖ + ‖ι b - ι (m.toCLM x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ e + e := add_le_add h (by
      rw [← map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le ι _).trans
        (by simpa only [norm_sub_rev] using m.norm_sub_le x b h))
    _ = _ := by ring

/-- Two residuals bounded by `2e` give the quadratic covariance bound. -/
theorem norm_covariance_le_four_mul_sq (x y : A) {e : ℝ} (he : 0 ≤ e)
    (hx : ‖x - ι (m.toCLM x)‖ ≤ 2 * e)
    (hy : ‖y - ι (m.toCLM y)‖ ≤ 2 * e) :
    ‖m.toCLM (x * y) - m.toCLM x * m.toCLM y‖ ≤ 4 * e ^ 2 := by
  calc
    _ ≤ ‖x - ι (m.toCLM x)‖ * ‖y - ι (m.toCLM y)‖ := m.norm_covariance_le x y
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The average of a unitary within `e` of the fixed algebra has unitarity
error at most `4e²`. -/
theorem norm_variance_le_four_mul_sq (x : unitary A) (b : B) {e : ℝ}
    (he : 0 ≤ e) (hx : ‖(x : A) - ι b‖ ≤ e) :
    ‖1 - star (m.toCLM (x : A)) * m.toCLM (x : A)‖ ≤ 4 * e ^ 2 := by
  have hr := m.norm_residual_le (x : A) b hx
  rw [m.variance]
  calc
    _ ≤ ‖star ((x : A) - ι (m.toCLM (x : A))) *
        ((x : A) - ι (m.toCLM (x : A)))‖ := m.norm_le _
    _ ≤ ‖(x : A) - ι (m.toCLM (x : A))‖ *
        ‖(x : A) - ι (m.toCLM (x : A))‖ := by
      simpa only [norm_star] using norm_mul_le
        (star ((x : A) - ι (m.toCLM (x : A))))
        ((x : A) - ι (m.toCLM (x : A)))
    _ ≤ (2 * e) * (2 * e) := mul_le_mul hr hr (norm_nonneg _) (by positivity)
    _ = _ := by ring

end BimoduleMean

private theorem boundary_sqrt_scalar_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hlarge : 1 ≤ (Real.sqrt t + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg t]
  calc
    _ ≤ (Real.sqrt t - 1) ^ 2 * (Real.sqrt t + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hlarge (sq_nonneg (Real.sqrt t - 1))]
    _ = _ := by rw [← mul_pow]; congr 1; nlinarith [Real.sq_sqrt ht]

section Ordered

variable [PartialOrder B] [StarOrderedRing B]

/-- The square root cannot increase the operator-norm error from one. -/
theorem norm_sqrt_sub_one_le (a : B) (ha : 0 ≤ a) :
    ‖CFC.sqrt a - 1‖ ≤ ‖a - 1‖ := by
  let b := CFC.sqrt a
  have hb : star b = b := (CFC.sqrt_nonneg a).isSelfAdjoint.star_eq
  have haStar : star a = a := ha.isSelfAdjoint.star_eq
  have hbCFC : b = cfc Real.sqrt a := by
    dsimp [b]
    rw [CFC.sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  have hleft : cfc (fun t : ℝ => (Real.sqrt t - 1) ^ 2) a =
      star (b - 1) * (b - 1) := by
    rw [cfc_pow (fun t : ℝ => Real.sqrt t - 1) 2 a,
      cfc_sub Real.sqrt (fun _ : ℝ => 1) a,
      cfc_const_one ℝ a, ← hbCFC, star_sub, hb, star_one, pow_two]
  have hright : cfc (fun t : ℝ => (t - 1) ^ 2) a =
      star (a - 1) * (a - 1) := by
    rw [cfc_pow (fun t : ℝ => t - 1) 2 a,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) a,
      cfc_id' ℝ a, cfc_const_one ℝ a, star_sub, haStar, star_one, pow_two]
  have horder : star (b - 1) * (b - 1) ≤ star (a - 1) * (a - 1) := by
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a).mpr
    intro t ht
    exact boundary_sqrt_scalar_sub_one_sq_le (spectrum_nonneg_of_nonneg ha ht)
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg horder (star_mul_self_nonneg _)
  rw [CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at hn
  change ‖b - 1‖ ≤ ‖a - 1‖
  nlinarith [norm_nonneg (b - 1), norm_nonneg (a - 1)]

/-- Polar normalization costs no more than the unitarity defect. -/
theorem exists_polar_unitary_close_of_near_unitary (x : B) (v : unitary B)
    (hx : ‖x - (v : B)‖ < 1) :
    ∃ u : unitary B, (u : B) * CFC.abs x = x ∧
      ‖(u : B) - x‖ ≤ ‖star x * x - 1‖ := by
  nontriviality B
  have hinv : ‖(((Unitary.toUnits v)⁻¹ : Bˣ) : B)‖ = 1 := by
    change ‖star (v : B)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  let t : Bˣ := Units.ofNearby (Unitary.toUnits v) x (by
    simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hx)
  have ht : (t : B) = x := rfl
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  rw [ht] at hu
  refine ⟨u, hu, ?_⟩
  have hid : (u : B) - x = (u : B) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [hid, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le (star x * x) (star_mul_self_nonneg x)

end Ordered

/-- A unitary is a contraction, including in the degenerate C-star algebra. -/
theorem norm_unitary_le_one (x : unitary A) : ‖(x : A)‖ ≤ 1 := by
  nontriviality A
  simp only [CStarRing.norm_coe_unitary, le_refl]

section Transport

variable {G : Type*} [Group G]

/-- The transport field used before averaging an approximate cocycle. -/
def boundaryTransport (α : G →* (B ≃⋆ₐ[ℂ] B)) (V : G → unitary B) (g t : G) : B :=
  (V t : B) * α g (star (V (g⁻¹ * t) : B))

/-- The transport fields are unitary before averaging. -/
theorem boundaryTransport_mem_unitary (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) (g t : G) : boundaryTransport α V g t ∈ unitary B := by
  exact mul_mem (V t).property
    (Unitary.map_mem (α g) (star (V (g⁻¹ * t))).property)

/-- The transport construction has an exact factorization even when `V`
is only an approximate cocycle. -/
theorem boundaryTransport_factor (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) (g h t : G) :
    boundaryTransport α V (g * h) t =
      boundaryTransport α V g t * α g (boundaryTransport α V h (g⁻¹ * t)) := by
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1 := by
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  simp only [boundaryTransport, map_mul, StarAlgEquiv.mul_apply, mul_inv_rev, mul_assoc]
  rw [← mul_assoc (α g (star (V (g⁻¹ * t) : B))), hcancel, one_mul]

/-- The pointwise distance from the transport field to the original
unitary is bounded by the original cocycle defect. -/
theorem norm_boundaryTransport_sub_le (α : G →* (B ≃⋆ₐ[ℂ] B))
    (V : G → unitary B) {e : ℝ}
    (hdefect : ∀ g h, ‖(V g : B) * α g (V h : B) - (V (g * h) : B)‖ ≤ e)
    (g t : G) : ‖boundaryTransport α V g t - (V g : B)‖ ≤ e := by
  let W : unitary B := Unitary.map (StarMonoidHom.ofClass (α g)) (V (g⁻¹ * t))
  have hcancel : α g (star (V (g⁻¹ * t) : B)) * (W : B) = 1 := by
    change α g (star (V (g⁻¹ * t) : B)) * α g (V (g⁻¹ * t) : B) = 1
    rw [← map_mul, Unitary.star_mul_self_of_mem (V (g⁻¹ * t)).property, map_one]
  have heq : (boundaryTransport α V g t - (V g : B)) * (W : B) =
      (V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B) := by
    rw [sub_mul, boundaryTransport, mul_assoc, hcancel, mul_one]
    rfl
  calc
    ‖boundaryTransport α V g t - (V g : B)‖ =
        ‖(boundaryTransport α V g t - (V g : B)) * (W : B)‖ :=
      (CStarRing.norm_mul_coe_unitary _ W).symm
    _ = ‖(V t : B) - (V g : B) * α g (V (g⁻¹ * t) : B)‖ := congrArg norm heq
    _ = ‖(V g : B) * α g (V (g⁻¹ * t) : B) - (V t : B)‖ := norm_sub_rev _ _
    _ ≤ e := by simpa only [mul_inv_cancel_left] using hdefect g (g⁻¹ * t)

end Transport

section Improvement

variable {ι : B →⋆ₐ[ℂ] A} (m : BimoduleMean ι)
variable [PartialOrder B] [StarOrderedRing B]

/-- One averaged unitary can be replaced by an actual unitary at quadratic
cost, while retaining its original first-order proximity. -/
theorem BimoduleMean.exists_improved_unitary (X : unitary A) (V : unitary B)
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hXV : ‖(X : A) - ι (V : B)‖ ≤ e) :
    ∃ W : unitary B,
      ‖(W : B) - m.toCLM (X : A)‖ ≤ 4 * e ^ 2 ∧
      ‖(W : B) - (V : B)‖ ≤ e + 4 * e ^ 2 := by
  have hmV := m.norm_sub_le (X : A) (V : B) hXV
  obtain ⟨W, -, hW⟩ := exists_polar_unitary_close_of_near_unitary
    (m.toCLM (X : A)) V (hmV.trans_lt he1)
  have hquad : ‖(W : B) - m.toCLM (X : A)‖ ≤ 4 * e ^ 2 :=
    hW.trans (by simpa only [norm_sub_rev] using m.norm_variance_le_four_mul_sq X V he hXV)
  refine ⟨W, hquad, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
    ((add_le_add hquad hmV).trans_eq (by ring))

omit [PartialOrder B] [StarOrderedRing B] in
/-- The operator-norm defect of the averaged family is quadratic. -/
theorem BimoduleMean.norm_averaged_defect_le_four_mul_sq
    {G : Type*} [Group G]
    (α : G → B ≃⋆ₐ[ℂ] B) (fieldAction : G → A ≃⋆ₐ[ℂ] A)
    (hequiv : ∀ g x, m.toCLM (fieldAction g x) = α g (m.toCLM x))
    (hι : ∀ g b, fieldAction g (ι b) = ι (α g b))
    (X : G → unitary A) (V : G → unitary B)
    (hfactor : ∀ g h, (X (g * h) : A) = (X g : A) * fieldAction g (X h : A))
    {e : ℝ} (he : 0 ≤ e) (hXV : ∀ g, ‖(X g : A) - ι (V g : B)‖ ≤ e)
    (g h : G) :
    ‖m.toCLM (X (g * h) : A) -
      m.toCLM (X g : A) * α g (m.toCLM (X h : A))‖ ≤ 4 * e ^ 2 := by
  rw [hfactor, ← hequiv]
  apply m.norm_covariance_le_four_mul_sq _ _ he
  · exact m.norm_residual_le _ _ (hXV g)
  · rw [hequiv, ← hι, ← map_sub, StarAlgEquiv.norm_map]
    exact m.norm_residual_le _ _ (hXV h)

/-- Quadratic polar correction for the entire family.  The cocycle
factorization and equivariance are exact structural identities; no correction
conclusion is assumed. -/
theorem BimoduleMean.exists_quadratic_improvement
    {G : Type*} [Group G]
    (α : G → B ≃⋆ₐ[ℂ] B) (fieldAction : G → A ≃⋆ₐ[ℂ] A)
    (hequiv : ∀ g x, m.toCLM (fieldAction g x) = α g (m.toCLM x))
    (hι : ∀ g b, fieldAction g (ι b) = ι (α g b))
    (X : G → unitary A) (V : G → unitary B)
    (hfactor : ∀ g h, (X (g * h) : A) = (X g : A) * fieldAction g (X h : A))
    {e : ℝ} (he : 0 ≤ e) (he1 : e < 1)
    (hXV : ∀ g, ‖(X g : A) - ι (V g : B)‖ ≤ e) :
    ∃ W : G → unitary B,
      (∀ g, ‖(W g : B) - (V g : B)‖ ≤ e + 4 * e ^ 2) ∧
      (∀ g h, ‖(W g : B) * α g (W h : B) - (W (g * h) : B)‖ ≤ 16 * e ^ 2) := by
  choose W hW hWV using fun g => m.exists_improved_unitary (X g) (V g) he he1 (hXV g)
  refine ⟨W, hWV, ?_⟩
  intro g h
  let a := m.toCLM (X g : A)
  let b := m.toCLM (X h : A)
  let c := m.toCLM (X (g * h) : A)
  have ha : ‖a‖ ≤ 1 := (m.norm_le _).trans (norm_unitary_le_one _)
  have hd := m.norm_averaged_defect_le_four_mul_sq α fieldAction hequiv hι X V hfactor he hXV g h
  have hsplit : (W g : B) * α g (W h : B) - (W (g * h) : B) =
      ((W g : B) - a) * α g (W h : B) +
        a * α g ((W h : B) - b) + (a * α g b - c) + (c - (W (g * h) : B)) := by
    rw [map_sub]
    noncomm_ring
  rw [hsplit]
  calc
    _ ≤ ‖((W g : B) - a) * α g (W h : B)‖ + ‖a * α g ((W h : B) - b)‖ +
        ‖a * α g b - c‖ + ‖c - (W (g * h) : B)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (4 * e ^ 2) * 1 + 1 * (4 * e ^ 2) + 4 * e ^ 2 + 4 * e ^ 2 := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact (norm_mul_le _ _).trans (mul_le_mul (hW g)
              (by rw [StarAlgEquiv.norm_map]; exact norm_unitary_le_one _)
              (norm_nonneg _) (by positivity))
          · exact (norm_mul_le _ _).trans (mul_le_mul ha
              (by rw [StarAlgEquiv.norm_map]; exact hW h)
              (norm_nonneg _) (by positivity))
        · simpa only [a, b, c, norm_sub_rev] using hd
      · simpa only [c, norm_sub_rev] using hW (g * h)
    _ = _ := by ring

end Improvement

end

end KadisonKastler

end OAI
