import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
import Mathlib.Tactic.Ring

namespace OAI

namespace RyserCoveringCounterexample.Incidence

open scoped Pointwise

variable {F : Type*} [Field F] [DecidableEq F]

private lemma scalar_cover_neg_mem_diff
    {B : Finset F} {x : F} (hx : x ∈ B - B) :
    -x ∈ B - B := by
  rcases Finset.mem_sub.mp hx with ⟨u, hu, v, hv, rfl⟩
  exact Finset.mem_sub.mpr ⟨v, hv, u, hu, by ring⟩

theorem scalar_cover_add_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a + b) • B ⊆ (T + U + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, k, hk, euk⟩
  change t + h = a * x at eth
  change u + k = b * x at euk
  rcases Finset.mem_add.mp (hH (Finset.add_mem_add hh hk)) with
    ⟨v, hv, d, hd, evd⟩
  refine Finset.mem_add.mpr
    ⟨t + u + v, Finset.add_mem_add (Finset.add_mem_add ht hu) hv,
      d, hd, ?_⟩
  change t + u + v + d = (a + b) * x
  calc
    t + u + v + d = t + u + (v + d) := by ring
    _ = t + u + (h + k) := by rw [evd]
    _ = (t + h) + (u + k) := by ring
    _ = (a + b) * x := by rw [eth, euk]; ring

theorem scalar_cover_sub_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a - b) • B ⊆ (T - U + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, k, hk, euk⟩
  change t + h = a * x at eth
  change u + k = b * x at euk
  rcases Finset.mem_add.mp
      (hH (Finset.add_mem_add hh (scalar_cover_neg_mem_diff hk))) with
    ⟨v, hv, d, hd, evd⟩
  refine Finset.mem_add.mpr
    ⟨t - u + v, Finset.add_mem_add (Finset.sub_mem_sub ht hu) hv,
      d, hd, ?_⟩
  change t - u + v + d = (a - b) * x
  calc
    t - u + v + d = t - u + (v + d) := by ring
    _ = t - u + (h + -k) := by rw [evd]
    _ = (t + h) - (u + k) := by ring
    _ = (a - b) * x := by rw [eth, euk]; ring

theorem scalar_cover_neg_subset
    {B T : Finset F} {a : F}
    (ha : a • B ⊆ T + (B - B)) :
    (-a) • B ⊆ (-T) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hx)) with
    ⟨t, ht, h, hh, eth⟩
  change t + h = a * x at eth
  refine Finset.mem_add.mpr
    ⟨-t, Finset.neg_mem_neg ht,
      -h, scalar_cover_neg_mem_diff hh, ?_⟩
  change -t + -h = (-a) * x
  calc
    -t + -h = -(t + h) := by ring
    _ = -(a * x) := by rw [eth]
    _ = (-a) * x := by ring

theorem scalar_cover_mul_subset
    {B T U V : Finset F} {a b : F}
    (ha : a • B ⊆ T + (B - B))
    (hb : b • B ⊆ U + (B - B))
    (hH : (B - B) + (B - B) ⊆ V + (B - B)) :
    (a * b) • B ⊆ (a • U + T - T + V) + (B - B) := by
  intro z hz
  rcases Finset.mem_smul_finset.mp hz with ⟨x, hx, rfl⟩
  rcases Finset.mem_add.mp (hb (Finset.smul_mem_smul_finset hx)) with
    ⟨u, hu, h, hh, euh⟩
  rcases Finset.mem_sub.mp hh with ⟨y, hy, w, hw, rfl⟩
  change u + (y - w) = b * x at euh
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hy)) with
    ⟨t₁, ht₁, h₁, hh₁, e₁⟩
  rcases Finset.mem_add.mp (ha (Finset.smul_mem_smul_finset hw)) with
    ⟨t₂, ht₂, h₂, hh₂, e₂⟩
  change t₁ + h₁ = a * y at e₁
  change t₂ + h₂ = a * w at e₂
  rcases Finset.mem_add.mp
      (hH (Finset.add_mem_add hh₁ (scalar_cover_neg_mem_diff hh₂))) with
    ⟨v, hv, d, hd, evd⟩
  have hau : a * u ∈ a • U :=
    Finset.mem_smul_finset.mpr ⟨u, hu, rfl⟩
  refine Finset.mem_add.mpr ⟨a * u + t₁ - t₂ + v, ?_, d, hd, ?_⟩
  · exact Finset.add_mem_add
      (Finset.sub_mem_sub (Finset.add_mem_add hau ht₁) ht₂) hv
  · change a * u + t₁ - t₂ + v + d = (a * b) * x
    calc
      a * u + t₁ - t₂ + v + d =
          a * u + (t₁ - t₂) + (v + d) := by ring
      _ = a * u + (t₁ - t₂) + (h₁ + -h₂) := by rw [evd]
      _ = a * u + ((t₁ + h₁) - (t₂ + h₂)) := by ring
      _ = a * u + (a * y - a * w) := by rw [e₁, e₂]
      _ = a * (u + (y - w)) := by ring
      _ = (a * b) * x := by rw [euh]; ring

theorem scalar_cover_inv_sub_identity
    (B : Finset F) {a : F} (ha : a ≠ 0) :
    (-a⁻¹) • (a • B - B) = a⁻¹ • B - B := by
  have hscalar (u v : F) :
      (-a⁻¹) • (a • u - v) = a⁻¹ • v - u := by
    change (-a⁻¹) * (a * u - v) = a⁻¹ * v - u
    calc
      (-a⁻¹) * (a * u - v) =
          a⁻¹ * v - (a⁻¹ * a) * u := by ring
      _ = a⁻¹ * v - u := by rw [inv_mul_cancel₀ ha, one_mul]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_smul_finset.mp hz with ⟨w, hw, rfl⟩
    rcases Finset.mem_sub.mp hw with ⟨u, hu, v, hv, rfl⟩
    rcases Finset.mem_smul_finset.mp hu with ⟨x, hx, rfl⟩
    exact Finset.mem_sub.mpr
      ⟨a⁻¹ • v, Finset.mem_smul_finset.mpr ⟨v, hv, rfl⟩,
        x, hx, (hscalar x v).symm⟩
  · intro hz
    rcases Finset.mem_sub.mp hz with ⟨u, hu, v, hv, rfl⟩
    rcases Finset.mem_smul_finset.mp hu with ⟨x, hx, rfl⟩
    refine Finset.mem_smul_finset.mpr
      ⟨a • v - x, ?_, hscalar v x⟩
    exact Finset.mem_sub.mpr
      ⟨a • v, Finset.mem_smul_finset.mpr ⟨v, hv, rfl⟩,
        x, hx, rfl⟩

end RyserCoveringCounterexample.Incidence

end OAI
