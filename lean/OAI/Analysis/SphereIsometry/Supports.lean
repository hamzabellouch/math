import OAI.Analysis.SphereIsometry.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace OAI

/-!
# Supporting functionals

Supports are continuous real linear functionals of norm at most one which attain
the norm at the specified vector. Hahn–Banach supplies supports and extends them
from any subspace. Restriction and extension relate assertions about every ambient
support to assertions about every support on a finite span.

The results here hold in arbitrary real normed spaces, including the zero space.
-/

namespace Tingley

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A norm-bounded real functional attaining the norm at a vector. -/
def SupportAt (φ : X →L[ℝ] ℝ) (a : X) : Prop :=
  ‖φ‖ ≤ 1 ∧ φ a = ‖a‖

/-- The norm-at-most-one formulation also supplies a support at zero. -/
theorem exists_support (a : X) : ∃ φ : X →L[ℝ] ℝ, SupportAt φ a :=
  exists_dual_vector'' ℝ a

theorem abs_apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    |φ x| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs, one_mul] using φ.le_of_opNorm_le hφ x

theorem apply_le_norm {φ : X →L[ℝ] ℝ} (hφ : ‖φ‖ ≤ 1) (x : X) :
    φ x ≤ ‖x‖ :=
  (le_abs_self (φ x)).trans (abs_apply_le_norm hφ x)

@[simp] theorem supportAt_zero_iff (φ : X →L[ℝ] ℝ) :
    SupportAt φ (0 : X) ↔ ‖φ‖ ≤ 1 := by
  simp [SupportAt]

theorem SupportAt.smul_nonneg {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) {c : ℝ} (hc : 0 ≤ c) : SupportAt φ (c • a) := by
  refine ⟨h.1, ?_⟩
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, h.2]

theorem supportAt_pos_smul_iff (φ : X →L[ℝ] ℝ) (a : X)
    {c : ℝ} (hc : 0 < c) : SupportAt φ (c • a) ↔ SupportAt φ a := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have heq := h.2
    rw [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at heq
    exact mul_left_cancel₀ (ne_of_gt hc) heq
  · intro h
    exact h.smul_nonneg hc.le

@[simp] theorem supportAt_neg_iff (φ : X →L[ℝ] ℝ) (a : X) :
    SupportAt (-φ) (-a) ↔ SupportAt φ a := by
  simp [SupportAt]

theorem SupportAt.neg {φ : X →L[ℝ] ℝ} {a : X} (h : SupportAt φ a) :
    SupportAt (-φ) (-a) :=
  (supportAt_neg_iff φ a).2 h

theorem SupportAt.subgradient {φ : X →L[ℝ] ℝ} {a : X}
    (h : SupportAt φ a) (z : X) : φ (z - a) ≤ ‖z‖ - ‖a‖ := by
  rw [map_sub, h.2]
  exact sub_le_sub_right (apply_le_norm h.1 z) ‖a‖

/-- Hahn–Banach extends from any real subspace without changing the norm. -/
theorem extension_norm_eq (U : Submodule ℝ X) (φ : U →L[ℝ] ℝ) :
    ∃ Φ : X →L[ℝ] ℝ, (∀ u : U, Φ (u : X) = φ u) ∧ ‖Φ‖ = ‖φ‖ :=
  _root_.exists_extension_norm_eq U φ

theorem supportAt_extension (U : Submodule ℝ X) (a : U)
    (φ : U →L[ℝ] ℝ) (h : SupportAt φ a) :
    ∃ Φ : X →L[ℝ] ℝ,
      (∀ u : U, Φ (u : X) = φ u) ∧ SupportAt Φ (a : X) := by
  obtain ⟨Φ, hΦ, hnorm⟩ := extension_norm_eq U φ
  exact ⟨Φ, hΦ, ⟨hnorm.trans_le h.1, (hΦ a).trans h.2⟩⟩

theorem norm_restrict_le (U : Submodule ℝ X) (φ : X →L[ℝ] ℝ) :
    ‖φ.comp U.subtypeL‖ ≤ ‖φ‖ :=
  (φ.comp U.subtypeL).opNorm_le_bound (norm_nonneg φ) fun u => φ.le_opNorm (u : X)

theorem SupportAt.restrict (U : Submodule ℝ X)
    {φ : X →L[ℝ] ℝ} (a : U) (h : SupportAt φ (a : X)) :
    SupportAt (φ.comp U.subtypeL) a :=
  ⟨(norm_restrict_le U φ).trans h.1, h.2⟩

/-- Extending to an enlargement retains even the exact operator norm. -/
theorem exists_extension_norm_eq_of_le {U V : Submodule ℝ X}
    (hUV : U ≤ V) (φ : U →L[ℝ] ℝ) :
    ∃ ψ : V →L[ℝ] ℝ,
      (∀ u : U, ψ ⟨(u : X), hUV u.property⟩ = φ u) ∧ ‖ψ‖ = ‖φ‖ := by
  obtain ⟨Φ, hΦ, hnorm⟩ := extension_norm_eq U φ
  let ψ : V →L[ℝ] ℝ := Φ.comp V.subtypeL
  have hagree (u : U) : ψ ⟨(u : X), hUV u.property⟩ = φ u := hΦ u
  refine ⟨ψ, hagree, le_antisymm ?_ ?_⟩
  · exact (norm_restrict_le V Φ).trans_eq hnorm
  · apply φ.opNorm_le_bound (norm_nonneg ψ)
    intro u
    rw [← hagree u]
    exact ψ.le_opNorm ⟨(u : X), hUV u.property⟩

/-- In particular, a support extends to every specified finite enlargement.
The stronger statement does not need either subspace to be finite-dimensional. -/
theorem supportAt_finite_enlargement (U V : Submodule ℝ X) (hUV : U ≤ V)
    (a : U) (φ : U →L[ℝ] ℝ) (h : SupportAt φ a) :
    ∃ ψ : V →L[ℝ] ℝ,
      (∀ u : U, ψ ⟨(u : X), hUV u.property⟩ = φ u) ∧
      SupportAt ψ ⟨(a : X), hUV a.property⟩ := by
  obtain ⟨ψ, hψ, hnorm⟩ := exists_extension_norm_eq_of_le hUV φ
  exact ⟨ψ, hψ, ⟨hnorm.trans_le h.1, (hψ a).trans h.2⟩⟩

/-- Universal assertions about support evaluations can be made on any subspace
containing the two vectors. This permits using the dual of their finite span. -/
theorem forall_supportAt_apply_iff_submodule (U : Submodule ℝ X)
    (a b : U) (P : ℝ → Prop) :
    (∀ φ : X →L[ℝ] ℝ, SupportAt φ (a : X) → P (φ (b : X))) ↔
    (∀ ψ : U →L[ℝ] ℝ, SupportAt ψ a → P (ψ b)) := by
  constructor
  · intro h ψ hψ
    obtain ⟨Φ, hΦ, hsupport⟩ := supportAt_extension U a ψ hψ
    simpa only [hΦ b] using h Φ hsupport
  · intro h Φ hΦ
    exact h (Φ.comp U.subtypeL) (SupportAt.restrict U a hΦ)

/-- Triangle equality is equivalent to the existence of a common support. -/
theorem norm_add_eq_iff_exists_common_supportAt (x y : X) :
    ‖x + y‖ = ‖x‖ + ‖y‖ ↔
      ∃ φ : X →L[ℝ] ℝ, SupportAt φ x ∧ SupportAt φ y := by
  constructor
  · intro heq
    obtain ⟨φ, hφ⟩ := exists_support (x + y)
    have hx := apply_le_norm hφ.1 x
    have hy := apply_le_norm hφ.1 y
    have hsum : φ x + φ y = ‖x‖ + ‖y‖ := by
      calc
        φ x + φ y = φ (x + y) := (map_add φ x y).symm
        _ = ‖x + y‖ := hφ.2
        _ = ‖x‖ + ‖y‖ := heq
    refine ⟨φ, ⟨hφ.1, ?_⟩, ⟨hφ.1, ?_⟩⟩
    · linarith
    · linarith
  · rintro ⟨φ, hx, hy⟩
    apply le_antisymm (norm_add_le x y)
    have h := apply_le_norm hx.1 (x + y)
    rwa [map_add, hx.2, hy.2] at h

/-- Positive weighted triangle equality for unit vectors gives one functional
taking value one at both vectors. No strict convexity is required. -/
theorem common_support_of_norm_add_eq {v w : X}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (heq : ‖α • v + β • w‖ = α + β) :
    ∃ φ : X →L[ℝ] ℝ, ‖φ‖ ≤ 1 ∧ φ v = 1 ∧ φ w = 1 := by
  have hsum : ‖α • v + β • w‖ = ‖α • v‖ + ‖β • w‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hα, abs_of_pos hβ,
      hv, hw, mul_one] using heq
  obtain ⟨φ, hvφ, hwφ⟩ :=
    (norm_add_eq_iff_exists_common_supportAt (α • v) (β • w)).mp hsum
  have hv' := (supportAt_pos_smul_iff φ v hα).mp hvφ
  have hw' := (supportAt_pos_smul_iff φ w hβ).mp hwφ
  exact ⟨φ, hv'.1, hv'.2.trans hv, hw'.2.trans hw⟩

end Tingley

end OAI
