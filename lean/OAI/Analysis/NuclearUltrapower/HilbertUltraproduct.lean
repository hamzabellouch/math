import Mathlib

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

namespace NuclearUltrapower

/-- Bounded scalar families have a genuine ultralimit. No countable completeness
or separability hypothesis is used. -/
theorem hilbert_tendsto_ultralimit_of_bounded {ι : Type u} (ω : Ultrafilter ι)
    {F : Type v} [NormedAddCommGroup F] [ProperSpace F] (f : ι → F)
    (hf : ∃ C : ℝ, ∀ i, ‖f i‖ ≤ C) :
    Tendsto f (ω : Filter ι) (𝓝 (limUnder (ω : Filter ι) f)) := by
  obtain ⟨C, hC⟩ := hf
  apply tendsto_nhds_limUnder
  obtain ⟨x, _, hx⟩ := (isCompact_closedBall (0 : F) C).ultrafilter_le_nhds'
    (Ultrafilter.map f ω) (by
      change {i | f i ∈ Metric.closedBall 0 C} ∈ (ω : Filter ι)
      exact Filter.Eventually.of_forall (fun i => by simpa using hC i))
  exact ⟨x, hx⟩

/-- A type synonym for bounded Hilbert families, equipped below with the
ultralimit semi-inner-product (not with the supremum norm). -/
def UltraPreHilbert {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] (_ω : Ultrafilter ι) := lp E ∞

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι)

instance : AddCommGroup (UltraPreHilbert E ω) := inferInstanceAs (AddCommGroup (lp E ∞))
instance : Module ℂ (UltraPreHilbert E ω) := inferInstanceAs (Module ℂ (lp E ∞))

def family (x : UltraPreHilbert E ω) : lp E ∞ := x

omit [∀ i, InnerProductSpace ℂ (E i)] in
@[simp] theorem family_add (x y : UltraPreHilbert E ω) :
    family ω (x + y) = family ω x + family ω y := rfl
@[simp] theorem family_smul (r : ℂ) (x : UltraPreHilbert E ω) :
    family ω (r • x) = r • family ω x := rfl

theorem inner_tendsto (x y : UltraPreHilbert E ω) :
    Tendsto (fun i => inner ℂ (family ω x i) (family ω y i)) (ω : Filter ι)
      (𝓝 (limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i)))) := by
  apply hilbert_tendsto_ultralimit_of_bounded
  refine ⟨‖family ω x‖ * ‖family ω y‖, fun i => ?_⟩
  exact (norm_inner_le_norm _ _).trans (mul_le_mul
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))

@[instance_reducible] def core : PreInnerProductSpace.Core ℂ (UltraPreHilbert E ω) where
  inner x y := limUnder (ω : Filter ι) (fun i => inner ℂ (family ω x i) (family ω y i))
  conj_inner_symm x y := by
    exact tendsto_nhds_unique ((inner_tendsto ω y x).star.congr
      (fun i => inner_conj_symm (family ω x i) (family ω y i))) (inner_tendsto ω x y)
  re_inner_nonneg x := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x))
      (Filter.Eventually.of_forall (fun i => (inner_self_nonneg (𝕜 := ℂ) (x := family ω x i))))
  add_left x y z := by
    apply tendsto_nhds_unique (inner_tendsto ω (x + y) z)
    simpa only [family_add, lp.coeFn_add, Pi.add_apply, inner_add_left] using
      (inner_tendsto ω x z).add (inner_tendsto ω y z)
  smul_left x y r := by
    apply tendsto_nhds_unique (inner_tendsto ω (r • x) y)
    simpa only [family_smul, lp.coeFn_smul, Pi.smul_apply, inner_smul_left] using
      (inner_tendsto ω x y).const_mul (starRingEnd ℂ r)

instance : SeminormedAddCommGroup (UltraPreHilbert E ω) :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ (core ω)

instance : InnerProductSpace ℂ (UltraPreHilbert E ω) := InnerProductSpace.ofCore (core ω)

@[simp] theorem inner_def (x y : UltraPreHilbert E ω) :
    inner ℂ x y = limUnder (ω : Filter ι)
      (fun i => inner ℂ (family ω x i) (family ω y i)) := rfl

/-- The seminorm is exactly the ultralimit of pointwise norms. -/
theorem norm_tendsto (x : UltraPreHilbert E ω) :
    Tendsto (fun i => ‖family ω x i‖) (ω : Filter ι) (𝓝 ‖x‖) := by
  have h := ((Complex.continuous_re.tendsto _).comp (inner_tendsto ω x x)).sqrt
  convert h using 1
  · funext i
    exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

end UltraPreHilbert

/-- The Hilbert ultraproduct, implemented as the Hausdorff completion of bounded
families for the ultralimit seminorm. This is equivalent to the standard
norm-null quotient, but gives completeness without a separate lifting argument. -/
abbrev HilbertUltraproduct {ι : Type u} (E : ι → Type v)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] (ω : Ultrafilter ι) :=
  UniformSpace.Completion (UltraPreHilbert E ω)

namespace UltraPreHilbert
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- Uniformly bounded operator families act on bounded vector families. -/
def mapLinear (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →ₗ[ℂ] UltraPreHilbert F ω where
  toFun x := (⟨fun i => T i (family ω x i), memℓp_infty
    ⟨‖T‖ * ‖family ω x‖, by
      rintro _ ⟨i, rfl⟩
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)
        (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _) (norm_nonneg _) (norm_nonneg _))⟩⟩ : lp F ∞)
  map_add' x y := by apply Subtype.ext; funext i; exact map_add (T i) _ _
  map_smul' c x := by apply Subtype.ext; funext i; exact map_smul (T i) _ _

@[simp] theorem family_map (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) (i : ι) :
    family ω (mapLinear ω T x) i = T i (family ω x i) := rfl

/-- Eventual, rather than uniform, bounds suffice after passing to the ultralimit. -/
theorem mapLinear_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) (x : UltraPreHilbert E ω) :
    ‖mapLinear ω T x‖ ≤ C * ‖x‖ := by
  apply le_of_tendsto_of_tendsto (norm_tendsto ω (mapLinear ω T x))
    ((norm_tendsto ω x).const_mul C)
  exact hT.mono (fun i hi => (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _)))

def mapContinuous (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    UltraPreHilbert E ω →L[ℂ] UltraPreHilbert F ω :=
  (mapLinear ω T).mkContinuous ‖T‖ (mapLinear_norm_le ω T ‖T‖
    (Filter.Eventually.of_forall (fun i => lp.norm_apply_le_norm ENNReal.top_ne_zero T i)))

end UltraPreHilbert

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v} {F : ι → Type w}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (ω : Ultrafilter ι)

/-- The induced operator on the completed Hilbert ultraproduct. -/
def map (T : lp (fun i => E i →L[ℂ] F i) ∞) :
    HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct F ω :=
  (UltraPreHilbert.mapContinuous ω T).completion

@[simp] theorem map_coe (T : lp (fun i => E i →L[ℂ] F i) ∞)
    (x : UltraPreHilbert E ω) :
    map ω T (x : HilbertUltraproduct E ω) =
    (UltraPreHilbert.mapLinear ω T x : HilbertUltraproduct F ω) :=
  ContinuousLinearMap.completion_apply_coe _ _

theorem map_norm_le (T : lp (fun i => E i →L[ℂ] F i) ∞) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ᶠ i in (ω : Filter ι), ‖T i‖ ≤ C) : ‖map ω T‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    simpa only [map_coe, UniformSpace.Completion.norm_coe] using
      UltraPreHilbert.mapLinear_norm_le ω T C hT x

end HilbertUltraproduct

end NuclearUltrapower

namespace NuclearUltrapower
namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] (ω : Ultrafilter ι)

local instance (i : ι) : IsBoundedSMul ℂ (E i →L[ℂ] E i) :=
  NormedSpace.toIsBoundedSMul

omit [∀ i, CompleteSpace (E i)] in
theorem map_zero  : map (E := E) (F := E) ω (0 : lp (fun i => E i →L[ℂ] E i) ∞) = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    rw [map_coe]
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω 0 x = 0 := by
      apply Subtype.ext; funext i
      change (0 : E i →L[ℂ] E i) (UltraPreHilbert.family ω x i) = 0
      rfl
    rw [he, UniformSpace.Completion.coe_zero]
    rfl

omit [∀ i, CompleteSpace (E i)] in
theorem map_add (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T + U) = map (E := E) (F := E) ω T + map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    simp only [add_apply, map_coe, ← UniformSpace.Completion.coe_add]
    congr 1

theorem map_smul (c : ℂ) (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    map (E := E) (F := E) ω (SMul.smul c T) = c • map (E := E) (F := E) ω T := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (map (E := E) (F := E) ω (SMul.smul c T)).continuous
      (c • map (E := E) (F := E) ω T).continuous
  | ih x =>
    have he : UltraPreHilbert.mapLinear (E := E) (F := E) ω (SMul.smul c T) x =
        c • UltraPreHilbert.mapLinear (E := E) (F := E) ω T x := by
      apply Subtype.ext
      funext i
      rfl
    rw [map_coe, smul_apply, map_coe,
      ← UniformSpace.Completion.coe_smul, he]

theorem map_mul (T U : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (T * U) = map (E := E) (F := E) ω T * map (E := E) (F := E) ω U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    change map ω (T * U) (x : HilbertUltraproduct E ω) = map ω T (map ω U x)
    rw [map_coe, map_coe, map_coe]
    congr 1

theorem map_star (T : lp (fun i => E i →L[ℂ] E i) ∞) : map (E := E) (F := E) ω (star T) = star (map (E := E) (F := E) ω T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    simp only [map_coe, UniformSpace.Completion.inner_coe, UltraPreHilbert.inner_def]
    congr 1
    funext i
    simp only [UltraPreHilbert.family_map, lp.coeFn_star, Pi.star_apply]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Bounded operator products and adjoints descend to the Hilbert ultraproduct. -/
def operatorRep : lp (fun i => E i →L[ℂ] E i) ∞ →⋆ₙₐ[ℂ]
    (HilbertUltraproduct E ω →L[ℂ] HilbertUltraproduct E ω) where
  toFun := map (E := E) (F := E) ω
  map_zero' := map_zero ω
  map_add' := map_add ω
  map_smul' := map_smul ω
  map_mul' := map_mul ω
  map_star' := map_star ω

@[simp] theorem operatorRep_apply (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    operatorRep ω T = map (E := E) (F := E) ω T := rfl

omit [∀ i, CompleteSpace (E i)] in
/-- The operator norm on the Hilbert ultraproduct is precisely the ultralimit
of coordinate operator norms. In particular no norm information is lost. -/
theorem map_norm_tendsto (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    Tendsto (fun i => ‖T i‖) (ω : Filter ι) (𝓝 ‖map ω T‖) := by
  have ht := hilbert_tendsto_ultralimit_of_bounded ω (fun i => ‖T i‖)
    ⟨‖T‖, fun i => by simpa only [Real.norm_eq_abs, abs_norm] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero T i⟩
  let c := limUnder (ω : Filter ι) (fun i => ‖T i‖)
  have hc : 0 ≤ c := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall (fun i => norm_nonneg _))
  have hle : ‖map ω T‖ ≤ c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact map_norm_le ω T (c + ε) (by positivity)
      ((ht.eventually (gt_mem_nhds (show c < c + ε by linarith))).mono (fun _ h => h.le))
  have hge : c ≤ ‖map ω T‖ := by
    apply le_of_forall_pos_le_add
    intro ε hε
    choose x hx hTx using fun i => (T i).exists_lt_apply_of_lt_opNorm
      (show ‖T i‖ - ε < ‖T i‖ by linarith)
    let X : UltraPreHilbert E ω := (⟨x, memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩; exact (hx i).le⟩⟩ : lp E ∞)
    have hnX : ‖X‖ ≤ 1 := le_of_tendsto_of_tendsto (UltraPreHilbert.norm_tendsto ω X)
      tendsto_const_nhds (Filter.Eventually.of_forall (fun i => (hx i).le))
    have hb : c - ε ≤ ‖UltraPreHilbert.mapLinear ω T X‖ :=
      le_of_tendsto_of_tendsto (ht.sub_const ε)
        (UltraPreHilbert.norm_tendsto ω (UltraPreHilbert.mapLinear ω T X))
        (Filter.Eventually.of_forall (fun i => (hTx i).le))
    have ho : ‖UltraPreHilbert.mapLinear ω T X‖ ≤ ‖map ω T‖ := by
      have he := (map ω T).le_opNorm_of_le
        (show ‖(X : HilbertUltraproduct E ω)‖ ≤ 1 by simpa using hnX)
      simpa only [map_coe, UniformSpace.Completion.norm_coe, mul_one] using he
    linarith
  rwa [show ‖map ω T‖ = c from le_antisymm hle hge]

omit [∀ i, CompleteSpace (E i)] in
/-- Norm-null families, and only norm-null families, represent zero. -/
theorem map_eq_zero_iff (T : lp (fun i => E i →L[ℂ] E i) ∞) :
    map ω T = 0 ↔ Tendsto (fun i => ‖T i‖) (ω : Filter ι) (𝓝 0) := by
  constructor
  · intro h; simpa [h] using map_norm_tendsto ω T
  · intro h
    exact norm_eq_zero.mp (tendsto_nhds_unique (map_norm_tendsto ω T) h)

end HilbertUltraproduct
end NuclearUltrapower
end
end

end OAI
