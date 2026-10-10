import OAI.MathematicalPhysics.RapidForcing.Support

namespace OAI

/-! An explicit reflected similarity places the compact rapid-forcing
construction in a single unit chart.  The first-coordinate observation is
preserved, and material trajectories are conjugated by the same map. -/

noncomputable section
open Set
open scoped ContDiff
namespace RapidForcing.CompactEmbedding

def reflection : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 3 =>
    if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem reflection_apply (x : Space) (i : Fin 3) :
    reflection x i = if i = 0 then -x i else x i := by
  by_cases hi : i = 0 <;> simp [reflection, LinearIsometryEquiv.piLpCongrRight_apply, hi]

@[simp] theorem reflection_reflection (x : Space) : reflection (reflection x) = x := by
  ext i
  by_cases hi : i = 0 <;> simp [hi]

def linear : Space →L[ℝ] Space :=
  (1 / 8 : ℝ) • reflection.toContinuousLinearMap

def inverseLinear : Space →L[ℝ] Space :=
  (8 : ℝ) • reflection.toContinuousLinearMap

def coordinateSign (i : Fin 3) : ℝ := if i = 0 then -1 else 1

theorem linear_apply (x : Space) (i : Fin 3) :
    linear x i = (coordinateSign i / 8) * x i := by
  by_cases hi : i = 0 <;> simp [linear, coordinateSign, hi, div_eq_mul_inv]

theorem inverseLinear_basis (i : Fin 3) :
    inverseLinear (basis i) = (8 * coordinateSign i) • basis i := by
  ext j
  by_cases hji : j = i
  · subst j
    by_cases hi : i = 0 <;> simp [inverseLinear, coordinateSign, basis, hi]
  · have hj0 : i = 0 → j ≠ 0 := by intro hi; simpa [hi] using hji
    by_cases hi : i = 0 <;> simp [inverseLinear, coordinateSign, basis, hji, hi, hj0]

@[simp] theorem inverseLinear_linear (x : Space) : inverseLinear (linear x) = x := by
  simp [inverseLinear, linear, map_smul, smul_smul]

@[simp] theorem linear_inverseLinear (x : Space) : linear (inverseLinear x) = x := by
  simp [inverseLinear, linear, map_smul, smul_smul]

theorem norm_linear (x : Space) : ‖linear x‖ = (1 / 8 : ℝ) * ‖x‖ := by
  simp [linear, norm_smul]

theorem norm_inverseLinear (x : Space) : ‖inverseLinear x‖ = 8 * ‖x‖ := by
  simp [inverseLinear, norm_smul]

def center : Space := vec (3 / 8) (1 / 2) (1 / 2)

def embed (x : Space) : Space := center + linear x

def unembed (x : Space) : Space := inverseLinear (x - center)

@[simp] theorem unembed_embed (x : Space) : unembed (embed x) = x := by
  simp [unembed, embed]

@[simp] theorem embed_unembed (x : Space) : embed (unembed x) = x := by
  simp [unembed, embed]

@[simp] theorem embed_zero : embed 0 = center := by simp [embed]

@[simp] theorem unembed_center : unembed center = 0 := by simp [unembed]

theorem embed_injective : Function.Injective embed :=
  Function.LeftInverse.injective unembed_embed

theorem unembed_injective : Function.Injective unembed :=
  Function.LeftInverse.injective embed_unembed

@[simp] theorem embed_first (x : Space) : embed x 0 = 3 / 8 - x 0 / 8 := by
  simp [embed, center, vec, linear, sub_eq_add_neg, div_eq_mul_inv, mul_comm]

@[simp] theorem embed_second (x : Space) : embed x 1 = 1 / 2 + x 1 / 8 := by
  simp [embed, center, vec, linear, div_eq_mul_inv, mul_comm]

@[simp] theorem embed_third (x : Space) : embed x 2 = 1 / 2 + x 2 / 8 := by
  simp [embed, center, vec, linear, div_eq_mul_inv, mul_comm]

theorem embed_observation (x : Space) : 1 / 2 < embed x 0 ↔ x 0 < -1 := by
  rw [embed_first]
  constructor <;> intro h <;> linarith

def chart : Set Space := {x | (∀ i, 1 / 4 ≤ x i) ∧ ∀ i, x i ≤ 3 / 4}

theorem embed_mem_chart {x : Space} (hx : x ∈ K) : embed x ∈ chart := by
  obtain ⟨hx0, hx0', hx1, hx1', hx2, hx2'⟩ := hx
  have h0 := embed_first x
  have h1 := embed_second x
  have h2 := embed_third x
  constructor <;> intro i <;> fin_cases i <;> dsimp <;> linarith

theorem chart_inside_unit {x : Space} (hx : x ∈ chart) :
    ∀ i, 0 < x i ∧ x i < 1 := by
  intro i
  have h0 := hx.1 i
  have h1 := hx.2 i
  constructor <;> linarith

def compactChart : Set Space := embed '' K

theorem compactChart_compact : IsCompact compactChart :=
  K_compact.image (continuous_const.add linear.continuous)

theorem compactChart_subset_chart : compactChart ⊆ chart := by
  rintro _ ⟨x, hx, rfl⟩
  exact embed_mem_chart hx

theorem embed_hasFDerivAt (x : Space) : HasFDerivAt embed linear x := by
  exact linear.hasFDerivAt.const_add center

theorem unembed_hasFDerivAt (x : Space) : HasFDerivAt unembed inverseLinear x := by
  have he : unembed = fun y => inverseLinear y - inverseLinear center := by
    funext y
    exact map_sub inverseLinear y center
  rw [he]
  exact inverseLinear.hasFDerivAt.sub_const _

theorem embed_contDiff : ContDiff ℝ ∞ embed :=
  contDiff_const.add linear.contDiff

theorem unembed_contDiff : ContDiff ℝ ∞ unembed :=
  inverseLinear.contDiff.comp (contDiff_id.sub contDiff_const)

def field (u : Field Space) : Field Space :=
  fun t x => linear (u t (unembed x))

@[simp] theorem field_embed (u : Field Space) (t : ℝ) (x : Space) :
    field u t (embed x) = linear (u t x) := by simp [field]

theorem field_zero (u : Field Space) {t : ℝ} (hu : ∀ x, u t x = 0) :
    ∀ x, field u t x = 0 := by intro x; simp [field, hu]

theorem field_supported {u : Field Space} (hu : Supported u) {t : ℝ} (ht : 0 ≤ t) :
    tsupport (field u t) ⊆ compactChart := by
  apply closure_minimal _ compactChart_compact.isClosed
  intro x hx
  have hmem : unembed x ∈ K := by
    by_contra h
    exact hx (by simp [field, hu.zero_off ht h])
  exact ⟨unembed x, hmem, embed_unembed x⟩

theorem field_smooth {u : Field Space} (hu : Smooth u) : Smooth (field u) := by
  exact linear.contDiff.comp_contDiffOn
    (hu.comp (contDiff_fst.prodMk (unembed_contDiff.comp contDiff_snd)).contDiffOn
      (fun y hy => ⟨hy.1, mem_univ _⟩))

theorem embed_curve_hasDerivWithinAt {γ : ℝ → Space} {v : Space}
    {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ v s t) :
    HasDerivWithinAt (fun r => embed (γ r)) (linear v) s t := by
  simpa only [Function.comp_def] using (embed_hasFDerivAt (γ t)).comp_hasDerivWithinAt t hγ

theorem unembed_curve_hasDerivWithinAt {γ : ℝ → Space} {v : Space}
    {s : Set ℝ} {t : ℝ} (hγ : HasDerivWithinAt γ v s t) :
    HasDerivWithinAt (fun r => unembed (γ r)) (inverseLinear v) s t := by
  simpa only [Function.comp_def] using
    (unembed_hasFDerivAt (γ t)).comp_hasDerivWithinAt t hγ

def flow (X : ℝ → Space → Space) : ℝ → Space → Space :=
  fun t x => embed (X t (unembed x))

@[simp] theorem flow_embed (X : ℝ → Space → Space) (t : ℝ) (x : Space) :
    flow X t (embed x) = embed (X t x) := by simp [flow]

theorem trajectory_unembed {u : Field Space} {a : Space} {T : ℝ} {γ : ℝ → Space}
    (hγ : TrajectoryOn (field u) a T γ) :
    TrajectoryOn u (unembed a) T (fun t => unembed (γ t)) := by
  refine ⟨by change unembed (γ 0) = unembed a; rw [hγ.1], ?_⟩
  intro t ht
  simpa only [field, inverseLinear_linear] using
    unembed_curve_hasDerivWithinAt (hγ.2 t ht)

theorem materialFlow {u : Field Space} {X : ℝ → Space → Space}
    (hX : MaterialFlow u X) : MaterialFlow (field u) (flow X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp [flow, hX.1]
  · intro a t ht
    simpa only [flow, field, unembed_embed] using
      embed_curve_hasDerivWithinAt (hX.2.1 (unembed a) t ht)
  · intro T hT a γ hγ t ht
    have he := hX.2.2 T hT (unembed a) (fun r => unembed (γ r))
      (trajectory_unembed hγ) t ht
    have he' := congrArg embed he
    simpa only [embed_unembed, flow] using he'

theorem flow_observation (X : ℝ → Space → Space) (t : ℝ) :
    1 / 2 < flow X t center 0 ↔ X t 0 0 < -1 := by
  simpa only [flow, unembed_center] using embed_observation (X t 0)

theorem reaches_iff (X : ℝ → Space → Space) :
    (∃ t : ℝ, 0 ≤ t ∧ 1 / 2 < flow X t center 0) ↔
      ∃ t : ℝ, 0 ≤ t ∧ X t 0 0 < -1 := by
  simp only [flow_observation]

end RapidForcing.CompactEmbedding

end

end OAI
