import Mathlib
import OAI.Analysis.Crouzeix.BoundaryForms
import OAI.Analysis.Crouzeix.SteinMetric

namespace OAI

/-! Endpoint. -/

noncomputable section

open Set Filter

open scoped Topology MatrixOrder Matrix.Norms.L2Operator

namespace CrouzeixHilbert.Endpoint

section Cone

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev Herm (A : Type*) [CStarAlgebra A] := selfAdjoint.submodule ℝ A

instance : PosSMulMono ℝ (Herm A) where
  smul_le_smul_of_nonneg_left {r} hr {x y} h := by
    change r • (x : A) ≤ r • (y : A)
    exact smul_le_smul_of_nonneg_left h hr

def unit : Herm A := ⟨1, IsSelfAdjoint.one A⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem unit_val : ((unit : Herm A) : A) = 1 := rfl

def strictCone : Set (Herm A) :=
  {H | ∃ ε : ℝ, 0 < ε ∧ ε • (unit : Herm A) ≤ H}

omit [StarOrderedRing A] in
theorem unit_mem_strictCone : (unit : Herm A) ∈ strictCone :=
  ⟨1, zero_lt_one, by simp⟩

theorem strictCone_nonneg {H : Herm A} (h : H ∈ strictCone) : 0 ≤ H := by
  obtain ⟨ε, hε, hH⟩ := h
  apply le_trans _ hH
  change 0 ≤ ε • (1 : A)
  exact smul_nonneg hε.le zero_le_one

theorem strictCone_add_nonneg {H P : Herm A} (hH : H ∈ strictCone)
    (hP : 0 ≤ P) : H + P ∈ strictCone := by
  obtain ⟨ε, hε, hH⟩ := hH
  exact ⟨ε, hε, hH.trans (le_add_of_nonneg_right hP)⟩

theorem strictCone_smul {H : Herm A} (hH : H ∈ strictCone) {r : ℝ}
    (hr : 0 < r) : r • H ∈ strictCone := by
  obtain ⟨ε, hε, hH⟩ := hH
  refine ⟨r * ε, mul_pos hr hε, ?_⟩
  rw [mul_smul]
  exact smul_le_smul_of_nonneg_left hH hr.le

theorem convex_strictCone : Convex ℝ (strictCone : Set (Herm A)) := by
  intro H hH J hJ a b ha hb hab
  obtain ⟨ε, hε, hH⟩ := hH
  obtain ⟨δ, hδ, hJ⟩ := hJ
  refine ⟨a * ε + b * δ, ?_, ?_⟩
  · have hs : 0 ≤ a * ε := mul_nonneg ha hε.le
    have ht : 0 ≤ b * δ := mul_nonneg hb hδ.le
    by_cases h : a = 0
    · have : b = 1 := by linarith
      simp [h, this, hδ]
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm h)) hε) ht
  · rw [add_smul, mul_smul, mul_smul]
    exact add_le_add (smul_le_smul_of_nonneg_left hH ha)
      (smul_le_smul_of_nonneg_left hJ hb)

theorem isOpen_strictCone : IsOpen (strictCone : Set (Herm A)) := by
  rw [Metric.isOpen_iff]
  intro H hH
  obtain ⟨ε, hε, hlower⟩ := hH
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro J hJ
  have hd : ‖(J - H : Herm A)‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hJ
  have hlo : -(‖(J - H : Herm A)‖) • (unit : Herm A) ≤ J - H := by
    change -(‖((J - H : Herm A) : A)‖) • (1 : A) ≤ ((J - H : Herm A) : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      (J - H).property.neg_algebraMap_norm_le_self
  refine ⟨ε / 2, half_pos hε, ?_⟩
  have hh := add_le_add hlower hlo
  rw [← add_smul, add_sub_cancel] at hh
  apply le_trans _ hh
  change (ε / 2) • (1 : A) ≤ (ε + -‖(J - H : Herm A)‖) • (1 : A)
  exact smul_le_smul_of_nonneg_right (by linarith) zero_le_one

theorem orderUnit_bounds (H : Herm A) :
    -(‖H‖) • (unit : Herm A) ≤ H ∧ H ≤ ‖H‖ • (unit : Herm A) := by
  constructor
  · change -(‖(H : A)‖) • (1 : A) ≤ (H : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_smul] using
      H.property.neg_algebraMap_norm_le_self
  · change (H : A) ≤ ‖(H : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using H.property.le_algebraMap_norm_self

theorem positive_mono (f : (Herm A) →L[ℝ] ℝ)
    (hf : ∀ H, 0 ≤ H → 0 ≤ f H) : Monotone f := by
  intro H J hHJ
  have h := hf (J - H) (sub_nonneg.mpr hHJ)
  rw [map_sub] at h
  linarith

theorem positive_eq_zero (f : (Herm A) →L[ℝ] ℝ)
    (hf : ∀ H, 0 ≤ H → 0 ≤ f H) (h1 : f unit = 0) : f = 0 := by
  ext H
  have hl := positive_mono f hf (orderUnit_bounds H).1
  have hu := positive_mono f hf (orderUnit_bounds H).2
  simp only [map_smul, smul_eq_mul, h1, mul_zero, zero_apply] at *
  exact le_antisymm hu hl

def congruence (T : A) : Herm A →ₗ[ℝ] Herm A where
  toFun H := ⟨star T * H * T, by
    change IsSelfAdjoint (star T * (H : A) * T)
    simpa only [star_star] using H.property.conjugate (star T)⟩
  map_add' H J := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, add_mul]
  map_smul' r H := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem congruence_val (T : A) (H : Herm A) :
    ((congruence T H : Herm A) : A) = star T * H * T := rfl

end Cone

lemma slope_nonpos {a b c : ℝ} (h : ∀ t : ℝ, 0 ≤ t → b + a * t ≤ c) : a ≤ 0 := by
  by_contra ha
  have ha : 0 < a := lt_of_not_ge ha
  have hb := h 0 le_rfl
  simp only [mul_zero, add_zero] at hb
  have ht : 0 ≤ (c - b + 1) / a := div_nonneg (by linarith) ha.le
  have hh := h ((c - b + 1) / a) ht
  rw [mul_div_cancel₀ _ ha.ne'] at hh
  linarith

lemma slope_zero {a b c : ℝ} (h : ∀ t : ℝ, c ≤ b + a * t) : a = 0 := by
  have hn : a ≤ 0 := slope_nonpos (b := -b) (c := -c) (fun t ht => by
    have := h (-t)
    linarith)
  have hp : -a ≤ 0 := slope_nonpos (b := -b) (c := -c) (fun t ht => by
    have := h t
    linarith)
  linarith

section Separation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

abbrev SlackSpace (A : Type*) [CStarAlgebra A] := ℝ × Herm A × Herm A × Herm A

def slacks (T : A) (s : ℝ) (H : Herm A) : SlackSpace A :=
  (s, H - unit, s • unit - H, H - congruence T H)

def lowerOpen (τ : ℝ) : Set (SlackSpace A) :=
  Iio τ ×ˢ strictCone ×ˢ strictCone ×ˢ strictCone

theorem convex_lowerOpen (τ : ℝ) : Convex ℝ (lowerOpen (A := A) τ) :=
  (convex_Iio τ).prod (convex_strictCone.prod (convex_strictCone.prod convex_strictCone))

theorem isOpen_lowerOpen (τ : ℝ) : IsOpen (lowerOpen (A := A) τ) :=
  isOpen_Iio.prod (isOpen_strictCone.prod (isOpen_strictCone.prod isOpen_strictCone))

omit [PartialOrder A] [StarOrderedRing A] in
theorem convex_slacks (T : A) : Convex ℝ {p : SlackSpace A | ∃ s H, p = slacks T s H} := by
  rintro x ⟨s, H, rfl⟩ y ⟨t, J, rfl⟩ a b ha hb hab
  refine ⟨a * s + b * t, a • H + b • J, ?_⟩
  dsimp only [slacks]
  ext1
  · rfl
  · ext1
    · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub]
      have he : a • (unit : Herm A) + b • unit = unit := by rw [← add_smul, hab, one_smul]
      calc
        a • H - a • unit + (b • J - b • unit) =
            a • H + b • J - (a • unit + b • unit) := by abel
        _ = _ := by rw [he]
    · ext1
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub, add_smul, mul_smul]
        module
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_sub, map_add, map_smul]
        module

def scalarPart (f : SlackSpace A →L[ℝ] ℝ) : ℝ := f (1, 0, 0, 0)

def firstPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    (ContinuousLinearMap.inl ℝ (Herm A) (Herm A × Herm A))))

def secondPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    ((ContinuousLinearMap.inr ℝ (Herm A) (Herm A × Herm A)).comp
      (ContinuousLinearMap.inl ℝ (Herm A) (Herm A)))))

def thirdPart (f : SlackSpace A →L[ℝ] ℝ) : Herm A →L[ℝ] ℝ :=
  -(f.comp ((ContinuousLinearMap.inr ℝ ℝ (Herm A × Herm A × Herm A)).comp
    ((ContinuousLinearMap.inr ℝ (Herm A) (Herm A × Herm A)).comp
      (ContinuousLinearMap.inr ℝ (Herm A) (Herm A)))))

omit [PartialOrder A] [StarOrderedRing A] in
theorem functional_decomposition (f : SlackSpace A →L[ℝ] ℝ)
    (s : ℝ) (U V W : Herm A) :
    f (s,U,V,W) = scalarPart f * s - firstPart f U - secondPart f V - thirdPart f W := by
  have he : (s,U,V,W) = s • ((1,0,0,0) : SlackSpace A) + (0,U,0,0) + (0,0,V,0) + (0,0,0,W) := by
    ext <;> simp
  rw [he, map_add, map_add, map_add, map_smul]
  simp [scalarPart, firstPart, secondPart, thirdPart, mul_comm]
  rfl

theorem lowerOpen_disjoint_slacks (T : A) {τ : ℝ}
    (hmin : ∀ s H, Metric.Feasible T s H → τ ≤ s) :
    Disjoint (lowerOpen (A := A) τ) {p : SlackSpace A | ∃ s H, p = slacks T s H} := by
  rw [Set.disjoint_left]
  rintro p hp ⟨s, H, rfl⟩
  obtain ⟨hs, hU, hV, hW⟩ := hp
  have hH : Metric.Feasible T s (H : A) := by
    constructor
    · exact sub_nonneg.mp (strictCone_nonneg hU)
    · have hv := strictCone_nonneg hV
      change 0 ≤ s • (1 : A) - (H : A) at hv
      simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mp hv
    · exact sub_nonneg.mp (strictCone_nonneg hW)
  exact hs.not_ge (hmin s H hH)

theorem separating_parts_nonneg (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ p ∈ lowerOpen τ, f p ≤ c) :
    0 ≤ scalarPart f ∧
      (∀ H, 0 ≤ H → 0 ≤ firstPart f H) ∧
      (∀ H, 0 ≤ H → 0 ≤ secondPart f H) ∧
      (∀ H, 0 ≤ H → 0 ≤ thirdPart f H) := by
  have h1 := unit_mem_strictCone (A := A)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := slope_nonpos (a := -scalarPart f)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1 - t, unit, unit, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 - t < τ; linarith, h1, h1, h1⟩
        have h := hf _ hp
        rw [functional_decomposition] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -firstPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit + t • H, unit, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, strictCone_add_nonneg h1 (smul_nonneg ht hH), h1, h1⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -secondPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit, unit + t • H, unit) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, h1, strictCone_add_nonneg h1 (smul_nonneg ht hH), h1⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith
  · intro H hH
    have h := slope_nonpos (a := -thirdPart f H)
      (b := scalarPart f * (τ - 1) - firstPart f unit - secondPart f unit - thirdPart f unit)
      (c := c) (fun t ht => by
        have hp : (τ - 1, unit, unit, unit + t • H) ∈ lowerOpen (A := A) τ :=
          ⟨by change τ - 1 < τ; linarith, h1, h1, strictCone_add_nonneg h1 (smul_nonneg ht hH)⟩
        have h := hf _ hp
        rw [functional_decomposition, map_add, map_smul] at h
        simp only [smul_eq_mul] at h
        linarith)
    linarith

theorem separating_value_lower (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ p ∈ lowerOpen τ, f p ≤ c) : scalarPart f * τ ≤ c := by
  let q : ℝ → ℝ := fun ε => scalarPart f * (τ - ε) - ε * firstPart f unit -
    ε * secondPart f unit - ε * thirdPart f unit
  have hcq : Continuous q := by dsimp [q]; fun_prop
  have ht : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (scalarPart f * τ)) := by
    simpa only [q, sub_zero, zero_mul] using hcq.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε : 0 < ε := hε
  have hp : (τ - ε, ε • unit, ε • unit, ε • unit) ∈ lowerOpen (A := A) τ := by
    have hs := strictCone_smul (unit_mem_strictCone (A := A)) hε
    exact ⟨by change τ - ε < τ; linarith, hs, hs, hs⟩
  have h := hf _ hp
  simpa only [q, functional_decomposition, map_smul, smul_eq_mul] using h

omit [PartialOrder A] [StarOrderedRing A] in
theorem separating_affine_balance (T : A) (c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (hf : ∀ s H, c ≤ f (slacks T s H)) :
    secondPart f unit = scalarPart f ∧
      (∀ H, secondPart f H - firstPart f H = thirdPart f H - thirdPart f (congruence T H)) ∧
      c ≤ firstPart f unit := by
  have he (s : ℝ) (H : Herm A) :
      f (slacks T s H) = firstPart f unit +
        (scalarPart f - secondPart f unit) * s +
          (secondPart f H - firstPart f H - thirdPart f H + thirdPart f (congruence T H)) := by
    simp only [slacks, functional_decomposition, map_sub, map_smul, smul_eq_mul]
    ring
  have hscalar := slope_zero (a := scalarPart f - secondPart f unit)
    (b := firstPart f unit) (c := c) (fun t => by
      have h := hf t 0
      simpa only [he, map_zero, sub_zero, add_zero, zero_sub] using h)
  have hscalar : secondPart f unit = scalarPart f := by linarith
  refine ⟨hscalar, ?_, ?_⟩
  · intro H
    have h := slope_zero
      (a := secondPart f H - firstPart f H - thirdPart f H + thirdPart f (congruence T H))
      (b := firstPart f unit) (c := c) (fun t => by
        have h := hf 0 (t • H)
        simp only [he, mul_zero, add_zero, map_smul, smul_eq_mul] at h
        linarith)
    linarith
  · have h := hf 0 0
    simpa only [he, mul_zero, add_zero, map_zero, sub_zero, zero_sub] using h

theorem exists_unit_slacks (T : A) (hT : spectralRadius ℂ T < 1) :
    ∃ (s : ℝ) (H : Herm A), unit ≤ H - unit ∧
      unit ≤ s • unit - H ∧ unit ≤ H - congruence T H := by
  let H₀ := Metric.steinSeries T
  have h₀ : (1 : A) ≤ H₀ := Metric.one_le_steinSeries T hT
  have h0 : 0 ≤ H₀ := Metric.steinSeries_nonneg T
  let H : Herm A := ⟨H₀ + H₀, IsSelfAdjoint.of_nonneg (add_nonneg h0 h0)⟩
  have hup : (H : A) ≤ algebraMap ℝ A ‖(H : A)‖ :=
    (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) (add_nonneg h0 h0)).mp le_rfl
  refine ⟨‖(H : A)‖ + 1, H, ?_, ?_, ?_⟩
  · change (1 : A) ≤ H₀ + H₀ - 1
    exact le_sub_iff_add_le.mpr (add_le_add h₀ h₀)
  · change (1 : A) ≤ (‖(H : A)‖ + 1) • (1 : A) - (H : A)
    rw [add_smul, one_smul]
    apply le_sub_iff_add_le.mpr
    simpa only [Algebra.algebraMap_eq_smul_one, add_comm] using add_le_add_right hup 1
  · change (1 : A) ≤ H₀ + H₀ - star T * (H₀ + H₀) * T
    rw [mul_add, add_mul, add_sub_add_comm, Metric.steinSeries_sub T hT]
    exact le_add_of_nonneg_right zero_le_one

theorem separating_scalar_pos (T : A) (hT : spectralRadius ℂ T < 1)
    (τ c : ℝ) (f : SlackSpace A →L[ℝ] ℝ)
    (ho : ∀ p ∈ lowerOpen τ, f p < c)
    (ha : ∀ s H, c ≤ f (slacks T s H)) : 0 < scalarPart f := by
  have ho' : ∀ p ∈ lowerOpen τ, f p ≤ c := fun p hp => (ho p hp).le
  obtain ⟨hlam, hY, hX, hZ⟩ := separating_parts_nonneg τ c f ho'
  have hc := separating_value_lower τ c f ho'
  by_contra hn
  have hlam0 : scalarPart f = 0 := le_antisymm (le_of_not_gt hn) hlam
  obtain ⟨s, H, hU, hV, hW⟩ := exists_unit_slacks T hT
  have hs := ha s H
  rw [slacks, functional_decomposition, hlam0, zero_mul] at hs
  rw [hlam0, zero_mul] at hc
  have he : (0 : Herm A) ≤ unit := (by change (0 : A) ≤ 1; exact zero_le_one)
  have hYe := hY unit he
  have hXe := hX unit he
  have hZe := hZ unit he
  have hYu := positive_mono (firstPart f) hY hU
  have hXv := positive_mono (secondPart f) hX hV
  have hZw := positive_mono (thirdPart f) hZ hW
  have hY0 : firstPart f = 0 := positive_eq_zero _ hY (by linarith)
  have hX0 : secondPart f = 0 := positive_eq_zero _ hX (by linarith)
  have hZ0 : thirdPart f = 0 := positive_eq_zero _ hZ (by linarith)
  have hf0 : f = 0 := by
    apply ContinuousLinearMap.ext
    rintro ⟨r,U,V,W⟩
    simp only [functional_decomposition, hlam0, hY0, hX0, hZ0, zero_apply,
      zero_mul, sub_zero]
  have h1 := unit_mem_strictCone (A := A)
  have hp : (τ - 1, unit, unit, unit) ∈ lowerOpen (A := A) τ :=
    ⟨by change τ - 1 < τ; linarith, h1, h1, h1⟩
  have hg := ho _ hp
  have ha0 := ha 0 0
  simp only [hf0, zero_apply] at hg ha0
  linarith

structure DualCertificate (T : A) (τ : ℝ) (H : Herm A) where
  X : Herm A →L[ℝ] ℝ
  Y : Herm A →L[ℝ] ℝ
  Z : Herm A →L[ℝ] ℝ
  X_positive : ∀ J, 0 ≤ J → 0 ≤ X J
  Y_positive : ∀ J, 0 ≤ J → 0 ≤ Y J
  Z_positive : ∀ J, 0 ≤ J → 0 ≤ Z J
  X_unit : X unit = 1
  Y_unit : Y unit = τ
  balance : ∀ J, X J - Y J = Z J - Z (congruence T J)
  Y_slack : Y (H - unit) = 0
  X_slack : X (τ • unit - H) = 0
  Z_slack : Z (H - congruence T H) = 0

theorem exists_dualCertificate (T : A) (hT : spectralRadius ℂ T < 1)
    {τ : ℝ} (H : Herm A) (hH : Metric.Feasible T τ (H : A))
    (hmin : ∀ s J, Metric.Feasible T s J → τ ≤ s) :
    Nonempty (DualCertificate T τ H) := by
  obtain ⟨f,c,ho,ha'⟩ := geometric_hahn_banach_open
    (convex_lowerOpen (A := A) τ) (isOpen_lowerOpen τ) (convex_slacks T)
    (lowerOpen_disjoint_slacks T hmin)
  have ha : ∀ s J, c ≤ f (slacks T s J) := fun s J => ha' _ ⟨s,J,rfl⟩
  have ho' : ∀ p ∈ lowerOpen τ, f p ≤ c := fun p hp => (ho p hp).le
  have hlam := separating_scalar_pos T hT τ c f ho ha
  obtain ⟨_, hY, hX, hZ⟩ := separating_parts_nonneg τ c f ho'
  obtain ⟨he, hbal, hval⟩ := separating_affine_balance T c f ha
  have hc := separating_value_lower τ c f ho'
  have hunit : (0 : Herm A) ≤ unit := (by change (0 : A) ≤ 1; exact zero_le_one)
  have hU : (0 : Herm A) ≤ H - unit := sub_nonneg.mpr hH.lower
  have hV : (0 : Herm A) ≤ τ • unit - H := by
    change 0 ≤ τ • (1 : A) - (H : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_nonneg.mpr hH.upper
  have hW : (0 : Herm A) ≤ H - congruence T H := sub_nonneg.mpr hH.stein
  have hab : f (slacks T τ H) = firstPart f unit := by
    simp only [slacks, functional_decomposition, map_sub, map_smul, smul_eq_mul]
    have hb := hbal H
    rw [he]
    linarith
  have hvalue : firstPart f unit = scalarPart f * τ - firstPart f (H - unit) -
      secondPart f (τ • unit - H) - thirdPart f (H - congruence T H) := by
    rw [← hab, slacks, functional_decomposition]
  have hYu := hY _ hU
  have hXv := hX _ hV
  have hZw := hZ _ hW
  have hYE : firstPart f unit = scalarPart f * τ := by linarith
  have hYS : firstPart f (H - unit) = 0 := by linarith
  have hXS : secondPart f (τ • unit - H) = 0 := by linarith
  have hZS : thirdPart f (H - congruence T H) = 0 := by linarith
  let r := (scalarPart f)⁻¹
  have hr : 0 ≤ r := (inv_pos.mpr hlam).le
  refine ⟨{
    X := r • secondPart f
    Y := r • firstPart f
    Z := r • thirdPart f
    X_positive := ?_
    Y_positive := ?_
    Z_positive := ?_
    X_unit := ?_
    Y_unit := ?_
    balance := ?_
    Y_slack := ?_
    X_slack := ?_
    Z_slack := ?_ }⟩
  · intro J hJ
    exact mul_nonneg hr (hX J hJ)
  · intro J hJ
    exact mul_nonneg hr (hY J hJ)
  · intro J hJ
    exact mul_nonneg hr (hZ J hJ)
  · simp only [smul_apply, smul_eq_mul, he, r, inv_mul_cancel₀ hlam.ne']
  · simp only [smul_apply, smul_eq_mul, hYE, r, ← mul_assoc,
      inv_mul_cancel₀ hlam.ne', one_mul]
  · intro J
    simpa only [smul_apply, smul_eq_mul, mul_sub] using congrArg (r * ·) (hbal J)
  · simp only [smul_apply, smul_eq_mul, hYS, mul_zero]
  · simp only [smul_apply, smul_eq_mul, hXS, mul_zero]
  · simp only [smul_apply, smul_eq_mul, hZS, mul_zero]

end Separation

section Riesz

open scoped InnerProductSpace ComplexOrder

open Boundary

def hermHS (n : ℕ) : Submodule ℝ (HS n) :=
  LinearMap.ker ((hsStar n).toLinearEquiv.toLinearMap - LinearMap.id)

@[simp] theorem mem_hermHS {n : ℕ} (u : HS n) :
    u ∈ hermHS n ↔ (ofHS u).IsHermitian := by
  simp only [hermHS, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv, sub_eq_zero,
    hsStar_apply, Matrix.IsHermitian]
  constructor
  · intro h
    exact congrArg ofHS h
  · intro h
    rw [h, toHS_ofHS]

def hermHSCoordinate (n : ℕ) : hermHS n →ₗ[ℝ] Herm (Matrix (Fin n) (Fin n) ℂ) where
  toFun u := ⟨ofHS u, (mem_hermHS u.val).mp u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_trace_representative {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X.IsHermitian ∧
      ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re := by
  let F := f.comp (hermHSCoordinate n).toContinuousLinearMap
  let u := (InnerProductSpace.toDual ℝ (hermHS n)).symm F
  refine ⟨ofHS u.val, (mem_hermHS _).mp u.property, ?_⟩
  intro J
  let v : hermHS n := ⟨toHS J.val, (mem_hermHS _).mpr J.property⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := v) (y := F)
  have he : hermHSCoordinate n v = J := by apply Subtype.ext; rfl
  change ⟪u, v⟫_ℝ = f (hermHSCoordinate n v) at h
  rw [he] at h
  rw [← h]
  change ⟪u.val, toHS J.val⟫_ℝ = _
  nth_rw 1 [← toHS_ofHS u.val]
  rw [real_inner_toHS, ((mem_hermHS _).mp u.property).eq]

theorem trace_representative_posSemidef {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ)
    (hf : ∀ J, 0 ≤ J → 0 ≤ f J)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (hrep : ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re) :
    X.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hX
  intro x
  let J : Herm (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨Matrix.vecMulVec x (star x), (Matrix.posSemidef_vecMulVec_self_star x).isHermitian⟩
  have hJ : (0 : Herm (Matrix (Fin n) (Fin n) ℂ)) ≤ J :=
    (Matrix.posSemidef_vecMulVec_self_star x).nonneg
  have h := hf J hJ
  rw [hrep] at h
  change 0 ≤ (X * Matrix.vecMulVec x (star x)).trace.re at h
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm] at h
  exact Complex.nonneg_iff.mpr ⟨h, (hX.im_star_dotProduct_mulVec_self x).symm⟩

theorem exists_positive_trace_representative {n : ℕ}
    (f : Herm (Matrix (Fin n) (Fin n) ℂ) →L[ℝ] ℝ)
    (hf : ∀ J, 0 ≤ J → 0 ≤ f J) :
    ∃ X : Matrix (Fin n) (Fin n) ℂ, X.PosSemidef ∧
      ∀ J : Herm (Matrix (Fin n) (Fin n) ℂ), f J = (X * J.val).trace.re := by
  obtain ⟨X,hX,hrep⟩ := exists_trace_representative f
  exact ⟨X, trace_representative_posSemidef f hf X hX hrep, hrep⟩

end Riesz

end CrouzeixHilbert.Endpoint

end

end OAI
