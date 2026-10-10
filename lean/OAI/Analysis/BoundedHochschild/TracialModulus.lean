import Mathlib
import OAI.Analysis.BoundedHochschild.HarmonicSums

namespace OAI

/-! Bounded-ball continuity, tracial null spaces and quotient seminorms. -/

noncomputable section


namespace TracialUltrapower
noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

section Modulus
variable {A E : Type*} [SeminormedAddCommGroup A] [SeminormedAddCommGroup E]

 
def BallSequential (q : A → E) (R : A → A) : Prop :=
  ∀ x : ℕ → A, (∃ r : ℝ, ∀ j, ‖x j‖ ≤ r) →
    Tendsto (fun j => ‖q (x j)‖) atTop (𝓝 0) →
    Tendsto (fun j => ‖q (R (x j))‖) atTop (𝓝 0)

 
def BallModulus (q : A → E) (R : A → A) : Prop :=
  ∀ r : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x : A,
    ‖x‖ ≤ r → ‖q x‖ < δ → ‖q (R x)‖ < ε

theorem ballSequential_iff_modulus (q : A → E) (R : A → A) :
    BallSequential q R ↔ BallModulus q R := by
  constructor
  · intro hs r ε hε
    by_contra h
    push Not at h
    choose x hx hxq hRx using fun j : ℕ =>
      h (1 / ((j : ℝ) + 1)) (by positivity)
    have hlim : Tendsto (fun j => ‖q (x j)‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun j => (hxq j).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hout := (hs x ⟨r, hx⟩ hlim).eventually_lt_const hε
    obtain ⟨j, hj⟩ := hout.exists
    exact (not_lt_of_ge (hRx j)) hj
  · intro hm x hx hlim
    obtain ⟨r, hr⟩ := hx
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hm r ε hε
    filter_upwards [hlim.eventually_lt_const hδ] with j hj
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) (hr j) hj

 
theorem BallModulus.map_tendsto {q : A → E} {R : A → A} (h : BallModulus q R)
    {ι : Type*} {l : Filter ι} {x : ι → A} {r : ℝ}
    (hx : ∀ᶠ j in l, ‖x j‖ ≤ r)
    (hlim : Tendsto (fun j => ‖q (x j)‖) l (𝓝 0)) :
    Tendsto (fun j => ‖q (R (x j))‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := h r ε hε
  filter_upwards [hx, hlim.eventually_lt_const hδ] with j hj hjq
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_norm] using hmod (x j) hj hjq

end Modulus

section NullSubmodule
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →ₗ[ℂ] E) (ω : Filter ℕ)

 

def nullSubmodule : Submodule ℂ (ℕ →ᵇ A) where
  carrier := {x | Tendsto (fun j => q (x j)) ω (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds (x := (0 : E))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.add_apply, map_add, add_zero] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, BoundedContinuousFunction.smul_apply, map_smul, smul_zero] using hx.const_smul c

@[simp] theorem mem_nullSubmodule (x : ℕ →ᵇ A) :
    x ∈ nullSubmodule q ω ↔ Tendsto (fun j => ‖q (x j)‖) ω (𝓝 0) := by
  change Tendsto (fun j => q (x j)) ω (𝓝 0) ↔ _
  exact tendsto_zero_iff_norm_tendsto_zero

theorem nullSubmodule_map_invariant (R : A →L[ℂ] A) (hR : BallModulus q R) :
    nullSubmodule q ω ≤ (nullSubmodule q ω).comap
      (R.compLeftContinuousBounded ℕ).toLinearMap := by
  intro x hx
  rw [Submodule.mem_comap, mem_nullSubmodule]
  exact hR.map_tendsto (Eventually.of_forall x.norm_coe_le_norm)
    ((mem_nullSubmodule q ω x).mp hx)

 

def quotientMap (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) →ₗ[ℂ]
      ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) :=
  (nullSubmodule q ω).mapQ (nullSubmodule q ω)
    (R.compLeftContinuousBounded ℕ).toLinearMap (nullSubmodule_map_invariant q ω R hR)

@[simp] theorem quotientMap_mk (R : A →L[ℂ] A) (hR : BallModulus q R)
    (x : ℕ →ᵇ A) :
    quotientMap q ω R hR (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (R.compLeftContinuousBounded ℕ x) := rfl

theorem norm_quotientMap_le (R : A →L[ℂ] A) (hR : BallModulus q R)
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q ω) :
    ‖quotientMap q ω R hR X‖ ≤ ‖R‖ * ‖X‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : 0 < ‖R‖ + 1 := by positivity
  obtain ⟨x, rfl, hx⟩ := Submodule.Quotient.norm_mk_lt X (div_pos hε hc)
  rw [quotientMap_mk]
  have hcomp : ‖R.compLeftContinuousBounded ℕ x‖ ≤ ‖R‖ * ‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro j
    exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j)
      (norm_nonneg _))
  calc
    _ ≤ ‖R.compLeftContinuousBounded ℕ x‖ := Submodule.Quotient.norm_mk_le _ _
    _ ≤ ‖R‖ * ‖x‖ := hcomp
    _ ≤ ‖R‖ * (‖(Submodule.Quotient.mk x : (ℕ →ᵇ A) ⧸ nullSubmodule q ω)‖ +
        ε / (‖R‖ + 1)) := by gcongr
    _ ≤ _ := by
      have hδ : 0 ≤ ε / (‖R‖ + 1) := (div_pos hε hc).le
      have heq : (‖R‖ + 1) * (ε / (‖R‖ + 1)) = ε := by field_simp
      nlinarith

 
def quotientContinuousMap (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) →L[ℂ]
      ((ℕ →ᵇ A) ⧸ nullSubmodule q ω) :=
  (quotientMap q ω R hR).mkContinuous ‖R‖ (norm_quotientMap_le q ω R hR)

theorem norm_quotientContinuousMap_le (R : A →L[ℂ] A) (hR : BallModulus q R) :
    ‖quotientContinuousMap q ω R hR‖ ≤ ‖R‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

end NullSubmodule

section ClosedNullSpace
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]

 

theorem isClosed_nullSubmodule (q : A →L[ℂ] E) (ω : Filter ℕ) :
    IsClosed (nullSubmodule q.toLinearMap ω : Set (ℕ →ᵇ A)) := by
  apply isClosed_of_closure_subset
  intro x hx
  change x ∈ nullSubmodule q.toLinearMap ω
  rw [mem_nullSubmodule]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : 0 < ‖q‖ + 1 := by positivity
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2 / (‖q‖ + 1))
    (by positivity)
  have hsmall : ‖q‖ * ‖x - y‖ < ε / 2 := by
    have hd : ‖x - y‖ < ε / 2 / (‖q‖ + 1) := by
      simpa only [dist_eq_norm] using hxy
    calc
      _ ≤ (‖q‖ + 1) * ‖x - y‖ := by gcongr; linarith
      _ < (‖q‖ + 1) * (ε / 2 / (‖q‖ + 1)) := mul_lt_mul_of_pos_left hd hc
      _ = _ := by field_simp
  have hy' := ((mem_nullSubmodule q.toLinearMap ω y).mp hy).eventually_lt_const
    (half_pos hε)
  filter_upwards [hy'] with j hj
  have hdiff : ‖q (x j) - q (y j)‖ < ε / 2 := by
    calc
      _ = ‖q ((x - y) j)‖ := by simp
      _ ≤ ‖q‖ * ‖(x - y) j‖ := q.le_opNorm _
      _ ≤ ‖q‖ * ‖x - y‖ := by gcongr; exact (x - y).norm_coe_le_norm j
      _ < _ := hsmall
  have hn := norm_le_norm_sub_add (q (x j)) (q (y j))
  simp only [dist_zero_right, Real.norm_eq_abs, abs_norm]
  change ‖q (x j)‖ < ε
  change ‖q (y j)‖ < ε / 2 at hj
  linarith

end ClosedNullSpace

section UltraSeminorm
variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E]
variable (q : A →L[ℂ] E) (ω : Ultrafilter ℕ)

 
def sequenceTwoNorm (x : ℕ →ᵇ A) : ℝ :=
  (ω : Filter ℕ).limUnder (fun j => ‖q (x j)‖)

theorem tendsto_sequenceTwoNorm (x : ℕ →ᵇ A) :
    Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 (sequenceTwoNorm q ω x)) := by
  have hbound : ∀ j, ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖) := by
    intro j
    exact ⟨norm_nonneg _, (q.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm j) (norm_nonneg _))⟩
  obtain ⟨a, _, ha⟩ := (isCompact_Icc : IsCompact (Set.Icc 0 (‖q‖ * ‖x‖))).ultrafilter_le_nhds
    (ω.map (fun j => ‖q (x j)‖)) (by
      rw [Ultrafilter.coe_map, le_principal_iff]
      change ∀ᶠ j in (ω : Filter ℕ), ‖q (x j)‖ ∈ Set.Icc 0 (‖q‖ * ‖x‖)
      exact Eventually.of_forall hbound)
  have ht : Tendsto (fun j => ‖q (x j)‖) (ω : Filter ℕ) (𝓝 a) := ha
  simpa only [sequenceTwoNorm, ht.limUnder_eq] using ht

theorem sequenceTwoNorm_nonneg (x : ℕ →ᵇ A) : 0 ≤ sequenceTwoNorm q ω x :=
  ge_of_tendsto' (tendsto_sequenceTwoNorm q ω x) (fun _ => norm_nonneg _)

theorem sequenceTwoNorm_eq_of_sub_mem (x y : ℕ →ᵇ A)
    (h : x - y ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    sequenceTwoNorm q ω x = sequenceTwoNorm q ω y := by
  have hz : Tendsto (fun j => ‖q (x j)‖ - ‖q (y j)‖) (ω : Filter ℕ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun j => ?_) ((mem_nullSubmodule _ _ _).mp h)
    simpa only [Real.norm_eq_abs, BoundedContinuousFunction.sub_apply, map_sub,
      ContinuousLinearMap.coe_coe] using abs_norm_sub_norm_le (q (x j)) (q (y j))
  have hh := tendsto_nhds_unique
    ((tendsto_sequenceTwoNorm q ω x).sub (tendsto_sequenceTwoNorm q ω y)) hz
  exact sub_eq_zero.mp hh

 

def quotientTwoNorm : ((ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) → ℝ :=
  Quotient.lift (sequenceTwoNorm q ω) (fun x y h =>
    sequenceTwoNorm_eq_of_sub_mem q ω x y ((Submodule.quotientRel_def _).mp h))

@[simp] theorem quotientTwoNorm_mk (x : ℕ →ᵇ A) :
    quotientTwoNorm q ω (Submodule.Quotient.mk x) = sequenceTwoNorm q ω x := rfl

theorem quotientTwoNorm_nonneg
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    0 ≤ quotientTwoNorm q ω X := by
  induction X using Quotient.inductionOn with | h x => exact sequenceTwoNorm_nonneg q ω x

 

theorem quotientMap_ballModulus (R : A →L[ℂ] A) (hR : BallModulus q R) :
    BallModulus (quotientTwoNorm q ω)
      (quotientContinuousMap q.toLinearMap (ω : Filter ℕ) R hR) := by
  intro r ε hε
  obtain ⟨δ, hδ, hmod⟩ := hR (r + 1) (ε / 2) (half_pos hε)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro X hX hXtwo
  obtain ⟨x, rfl, hx⟩ := Submodule.Quotient.norm_mk_lt X zero_lt_one
  have hxtwo : sequenceTwoNorm q ω x < δ := by
    rw [quotientTwoNorm_mk, Real.norm_eq_abs,
      abs_of_nonneg (sequenceTwoNorm_nonneg q ω x)] at hXtwo
    linarith
  have hsmall := (tendsto_sequenceTwoNorm q ω x).eventually_lt_const hxtwo
  have hout : ∀ᶠ j in (ω : Filter ℕ), ‖q (R (x j))‖ ≤ ε / 2 := by
    filter_upwards [hsmall] with j hj
    exact (hmod (x j) ((x.norm_coe_le_norm j).trans (by linarith)) hj).le
  change ‖sequenceTwoNorm q ω (R.compLeftContinuousBounded ℕ x)‖ < ε
  rw [Real.norm_eq_abs, abs_of_nonneg (sequenceTwoNorm_nonneg q ω _)]
  exact lt_of_le_of_lt (le_of_tendsto (tendsto_sequenceTwoNorm q ω
    (R.compLeftContinuousBounded ℕ x)) hout) (by linarith)

theorem quotientTwoNorm_eq_zero_iff
    (X : (ℕ →ᵇ A) ⧸ nullSubmodule q.toLinearMap (ω : Filter ℕ)) :
    quotientTwoNorm q ω X = 0 ↔ X = 0 := by
  induction X using Quotient.inductionOn with
  | h x =>
    constructor
    · intro hx
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [mem_nullSubmodule]
      change sequenceTwoNorm q ω x = 0 at hx
      exact hx ▸ tendsto_sequenceTwoNorm q ω x
    · intro hx
      have hz : x ∈ nullSubmodule q.toLinearMap (ω : Filter ℕ) :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      exact tendsto_nhds_unique (tendsto_sequenceTwoNorm q ω x)
        ((mem_nullSubmodule _ _ _).mp hz)

end UltraSeminorm

section TraceIdeal
open scoped ComplexOrder
open HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)

 
def traceHilbertMap : A →L[ℂ] τ.PreGNS :=
  τ.toPreGNS.toLinearMap.mkContinuous 1 (fun a => by
    change ‖τ.toPreGNS a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact preGNS_norm_le τ h1 a)

@[simp] theorem traceHilbertMap_apply (a : A) :
    traceHilbertMap τ h1 a = τ.toPreGNS a := rfl

variable (ω : Filter ℕ)

theorem nullSubmodule_mul_left (x y : ℕ →ᵇ A)
    (hy : y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    x * y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hy ⊢
  change Tendsto (fun j => ‖τ.toPreGNS (x j * y j)‖) ω (𝓝 0)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun j => (preGNS_norm_mul_le τ _ _).trans
      (mul_le_mul_of_nonneg_right (x.norm_coe_le_norm j) (norm_nonneg _)))
  simpa only [mul_zero, ContinuousLinearMap.coe_coe, traceHilbertMap_apply] using hy.const_mul ‖x‖

theorem nullSubmodule_mul_right (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x y : ℕ →ᵇ A)
    (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    x * y ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  change Tendsto (fun j => ‖τ.toPreGNS (x j * y j)‖) ω (𝓝 0)
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun j => (preGNS_norm_mul_right_le τ htr _ _).trans
      (mul_le_mul_of_nonneg_right (y.norm_coe_le_norm j) (norm_nonneg _)))
  simpa only [mul_zero, ContinuousLinearMap.coe_coe, traceHilbertMap_apply] using hx.const_mul ‖y‖

theorem nullSubmodule_star (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (x : ℕ →ᵇ A) (hx : x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω) :
    star x ∈ nullSubmodule (traceHilbertMap τ h1).toLinearMap ω := by
  rw [mem_nullSubmodule] at hx ⊢
  simpa only [ContinuousLinearMap.coe_coe, traceHilbertMap_apply,
    BoundedContinuousFunction.star_apply, preGNS_norm_star τ htr] using hx

 
def nullIdeal (htr : ∀ a b : A, τ (a*b) = τ (b*a)) : TwoSidedIdeal (ℕ →ᵇ A) :=
  TwoSidedIdeal.mk' (nullSubmodule (traceHilbertMap τ h1).toLinearMap ω)
    (Submodule.zero_mem _) (fun hx hy => Submodule.add_mem _ hx hy)
    (fun hx => Submodule.neg_mem _ hx)
    (fun {_ _} hy => nullSubmodule_mul_left τ h1 ω _ _ hy)
    (fun {_ _} hx => nullSubmodule_mul_right τ h1 ω htr _ _ hx)

theorem isClosed_nullIdeal (htr : ∀ a b : A, τ (a*b) = τ (b*a)) :
    IsClosed (nullIdeal τ h1 ω htr : Set (ℕ →ᵇ A)) :=
  by simpa only [nullIdeal, TwoSidedIdeal.coe_mk'] using
    isClosed_nullSubmodule (traceHilbertMap τ h1) ω

end TraceIdeal
end
end TracialUltrapower
end

end OAI
