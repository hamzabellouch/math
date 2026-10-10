import Mathlib

namespace OAI

/-! Four-dimensional tempered-distribution improvement and conformal-current identities. -/

noncomputable section

open scoped SchwartzMap
open LineDeriv

namespace ScaleConformal

def exponentialCharacter (α : ℝ) : Multiplicative ℝ →* ℂ where
  toFun s := (Real.exp (α * s.toAdd) : ℂ)
  map_one' := by simp
  map_mul' s t := by simp [mul_add, Real.exp_add]

theorem exponentialCharacter_injective : Function.Injective exponentialCharacter := by
  intro α β h
  have hh := DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ℝ))
  change (↑(Real.exp (α * 1)) : ℂ) = ↑(Real.exp (β * 1)) at hh
  rw [mul_one, mul_one] at hh
  exact Real.exp_injective (Complex.ofReal_injective hh)

theorem exponentialWeights_independent :
    LinearIndependent ℂ (fun α : ℝ => fun s : ℝ => (Real.exp (α * s) : ℂ)) := by
  exact (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    exponentialCharacter exponentialCharacter_injective

theorem finite_exponential_coefficients {M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : Finset ℝ) (v : ℝ → M)
    (h : ∀ s : ℝ, ∑ α ∈ S, (Real.exp (α * s) : ℂ) • v α = 0) :
    ∀ α ∈ S, v α = 0 := by
  intro α hα
  apply (Module.forall_dual_apply_eq_zero_iff ℂ (v α)).mp
  intro l
  have hl : (∑ β ∈ S, l (v β) • (fun s : ℝ => (Real.exp (β * s) : ℂ))) = 0 := by
    funext s
    have hh := congrArg l (h s)
    simpa [Finset.sum_apply, mul_comm] using hh
  exact (linearIndependent_iff'.mp exponentialWeights_independent) S (fun β => l (v β)) hl α hα

theorem finite_weight_selection {M : Type*} [AddCommGroup M] [Module ℂ M]
    (S : Finset ℝ) (v : ℝ → M) (a : ℝ) (c : M) (ha : a ∈ S)
    (h : ∀ s : ℝ, ∑ α ∈ S, (Real.exp (α * s) : ℂ) • v α =
      (Real.exp (a * s) : ℂ) • c) :
    v a = c ∧ ∀ b ∈ S, b ≠ a → v b = 0 := by
  classical
  let w (b : ℝ) : M := v b - if b = a then c else 0
  have hw : ∀ s : ℝ, ∑ b ∈ S, (Real.exp (b * s) : ℂ) • w b = 0 := by
    intro s
    simp only [w, smul_sub, Finset.sum_sub_distrib, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' S a, ite_eq_left ha, h s, sub_self]
  have hv := finite_exponential_coefficients S w hw
  constructor
  · have hv' := hv a ha
    simpa [w, sub_eq_zero] using hv'
  · intro b hb hba
    simpa [w, hba] using hv b hb

theorem finsupp_weight_selection {M : Type*} [AddCommGroup M] [Module ℂ M]
    (v : ℝ →₀ M) (a : ℝ) (c : M)
    (h : ∀ s : ℝ, v.sum (fun α b => (Real.exp (α * s) : ℂ) • b) =
      (Real.exp (a * s) : ℂ) • c) :
    v = Finsupp.single a c := by
  classical
  let w := v - Finsupp.single a c
  have hw : ∀ s : ℝ, ∑ α ∈ w.support, (Real.exp (α * s) : ℂ) • w α = 0 := by
    intro s
    change w.sum (fun α b => (Real.exp (α * s) : ℂ) • b) = 0
    dsimp only [w]
    rw [Finsupp.sum_sub_index (fun _ _ _ => smul_sub _ _ _)]
    rw [Finsupp.sum_single_index (h := fun α b => (Real.exp (α * s) : ℂ) • b)
      (smul_zero _), h s, sub_self]
  have hw0 : w = 0 := by
    ext α
    by_cases hα : α ∈ w.support
    · exact finite_exponential_coefficients w.support w hw α hα
    · exact Finsupp.notMem_support_iff.mp hα
  exact sub_eq_zero.mp hw0

section CommutingDerivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartz_derivatives_commute (f : 𝓢(E, ℂ)) (v w : E) :
    ∂_{v} (∂_{w} f) = ∂_{w} (∂_{v} f) := by
  ext x
  have hf : IsSymmSndFDerivAt ℝ (f : E → ℂ) x :=
    (f.smooth 2).contDiffAt.isSymmSndFDerivAt (by simp)
  have h := IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hf) (v := v) (w := w)
  simpa only [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    iteratedLineDerivOp_succ_left, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.tail,
    iteratedLineDerivOp_fin_zero] using h

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]

theorem distribution_derivatives_commute (u : 𝓢'(E, F)) (v w : E) :
    ∂_{v} (∂_{w} u) = ∂_{w} (∂_{v} u) := by
  ext f
  simp only [TemperedDistribution.lineDerivOp_apply_apply, lineDerivOp_neg, neg_neg]
  rw [schwartz_derivatives_commute]

def functionDerivative (v : E) (f : E → ℂ) : E → ℂ :=
  fun x => fderiv ℝ f x v

theorem fderiv_temperate {f : E → ℂ} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by simpa only [norm_iteratedFDeriv_fderiv] using h x⟩

theorem functionDerivative_temperate {f : E → ℂ} (hf : f.HasTemperateGrowth) (v : E) :
    (functionDerivative v f).HasTemperateGrowth := by
  exact (ContinuousLinearMap.apply ℝ ℂ v).hasTemperateGrowth.comp (fderiv_temperate hf)

theorem schwartz_multiplier_derivative {f : E → ℂ} (hf : f.HasTemperateGrowth)
    (v : E) (φ : 𝓢(E, ℂ)) :
    ∂_{v} (SchwartzMap.smulLeftCLM ℂ f φ) =
      SchwartzMap.smulLeftCLM ℂ (functionDerivative v f) φ +
        SchwartzMap.smulLeftCLM ℂ f (∂_{v} φ) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.smulLeftCLM_apply hf,
    add_apply,
    SchwartzMap.smulLeftCLM_apply_apply (functionDerivative_temperate hf v),
    SchwartzMap.smulLeftCLM_apply_apply hf, smul_eq_mul]
  rw [fderiv_fun_mul (hf.1.differentiable (by simp) x) φ.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul,
    functionDerivative]
  ring

theorem distribution_multiplier_derivative {f : E → ℂ} (hf : f.HasTemperateGrowth)
    (v : E) (u : 𝓢'(E, F)) :
    ∂_{v} (TemperedDistribution.smulLeftCLM F f u) =
      TemperedDistribution.smulLeftCLM F (functionDerivative v f) u +
        TemperedDistribution.smulLeftCLM F f (∂_{v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply]
  rw [schwartz_multiplier_derivative hf]
  simp only [map_neg, map_add]
  abel

end CommutingDerivatives

abbrev Spacetime := Fin 4 → ℝ

def coordinateVector (μ : Fin 4) : Spacetime := Pi.single μ 1

def metricSign (μ : Fin 4) : ℂ := if μ = 0 then 1 else -1

def metric (μ ν : Fin 4) : ℂ := if μ = ν then metricSign μ else 0

@[simp] theorem metric_diagonal (μ : Fin 4) : metric μ μ = metricSign μ := by
  simp [metric]

@[simp] theorem metric_sign_sq (μ : Fin 4) : metricSign μ * metricSign μ = 1 := by
  simp only [metricSign]
  split_ifs <;> norm_num

theorem metric_symmetric (μ ν : Fin 4) : metric μ ν = metric ν μ := by
  by_cases h : μ = ν
  · subst ν; rfl
  · simp [metric, h, Ne.symm h]

variable {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousConstSMul ℂ F]

abbrev Distribution (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :=
  𝓢'(Spacetime, F)

abbrev Tensor (F : Type*) [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] :=
  Fin 4 → Fin 4 → Distribution F

def pd (μ : Fin 4) (u : Distribution F) : Distribution F := ∂_{coordinateVector μ} u

@[simp] theorem partial_add (μ : Fin 4) (u v : Distribution F) :
    pd μ (u + v) = pd μ u + pd μ v := lineDerivOp_add _ _ _

@[simp] theorem partial_sub (μ : Fin 4) (u v : Distribution F) :
    pd μ (u - v) = pd μ u - pd μ v :=
  map_sub (lineDerivOpCLM ℂ (Distribution F) (coordinateVector μ)) _ _

@[simp] theorem partial_smul (μ : Fin 4) (a : ℂ) (u : Distribution F) :
    pd μ (a • u) = a • pd μ u := lineDerivOp_smul _ _ _

@[simp] theorem partial_zero (μ : Fin 4) : pd μ (0 : Distribution F) = 0 :=
  lineDerivOp_zero _

@[simp] theorem partial_sum {ι : Type*} (μ : Fin 4) (s : Finset ι)
    (u : ι → Distribution F) : pd μ (∑ i ∈ s, u i) = ∑ i ∈ s, pd μ (u i) := by
  exact map_sum (lineDerivOpCLM ℂ (Distribution F) (coordinateVector μ)) _ _

theorem partial_commute (μ ν : Fin 4) (u : Distribution F) :
    pd μ (pd ν u) = pd ν (pd μ u) :=
  distribution_derivatives_commute u _ _

def wave (u : Distribution F) : Distribution F :=
  ∑ μ, metricSign μ • pd μ (pd μ u)

def trace (T : Tensor F) : Distribution F :=
  ∑ μ, metricSign μ • T μ μ

def divergence (T : Tensor F) (ν : Fin 4) : Distribution F :=
  ∑ μ, metricSign μ • pd μ (T μ ν)

def correction (L : Distribution F) : Tensor F := fun μ ν =>
  (1 / 3 : ℂ) • (pd μ (pd ν L) - metric μ ν • wave L)

def improved (T : Tensor F) (L : Distribution F) : Tensor F := fun μ ν =>
  T μ ν + correction L μ ν

def SymmetricTensor (T : Tensor F) : Prop := ∀ μ ν, T μ ν = T ν μ

def ConservedTensor (T : Tensor F) : Prop := ∀ ν, divergence T ν = 0

theorem correction_symmetric (L : Distribution F) : SymmetricTensor (correction L) := by
  intro μ ν
  simp only [correction, partial_commute μ ν, metric_symmetric μ ν]

theorem partial_wave (μ : Fin 4) (u : Distribution F) :
    pd μ (wave u) = wave (pd μ u) := by
  simp only [wave, partial_sum, partial_smul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [partial_commute μ ν, partial_commute μ ν]

theorem metric_contract (ν : Fin 4) (u : Fin 4 → Distribution F) :
    (∑ μ, metricSign μ • metric μ ν • u μ) = u ν := by
  simp only [metric, ite_smul, zero_smul, smul_ite, smul_zero]
  simp [smul_smul]

theorem correction_conserved (L : Distribution F) : ConservedTensor (correction L) := by
  intro ν
  simp only [divergence, correction, partial_smul, partial_sub]
  simp_rw [smul_comm (metricSign _) (1 / 3 : ℂ)]
  rw [← Finset.smul_sum]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← smul_sub]
  change (1 / 3 : ℂ) • (wave (pd ν L) -
    ∑ μ, metricSign μ • metric μ ν • pd μ (wave L)) = 0
  rw [metric_contract, partial_wave, sub_self, smul_zero]

theorem correction_trace (L : Distribution F) : trace (correction L) = -wave L := by
  simp only [trace, correction, metric_diagonal]
  simp_rw [smul_comm (metricSign _) (1 / 3 : ℂ)]
  rw [← Finset.smul_sum]
  simp only [smul_sub, smul_smul, metric_sign_sq, one_smul, Finset.sum_sub_distrib]
  rw [← smul_sub]
  change (1 / 3 : ℂ) • (wave L - ∑ _ : Fin 4, wave L) = -wave L
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

theorem improvement_identities (T : Tensor F) (L : Distribution F)
    (hsymm : SymmetricTensor T) (hcons : ConservedTensor T)
    (htrace : trace T = wave L) :
    SymmetricTensor (improved T L) ∧ ConservedTensor (improved T L) ∧
      trace (improved T L) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro μ ν
    simp only [improved, hsymm μ ν, correction_symmetric L μ ν]
  · intro ν
    simp only [divergence, improved, partial_add, smul_add, Finset.sum_add_distrib]
    change divergence T ν + divergence (correction L) ν = 0
    rw [hcons ν, correction_conserved L ν, add_zero]
  · simp only [trace, improved, smul_add, Finset.sum_add_distrib]
    change trace T + trace (correction L) = 0
    rw [htrace, correction_trace, add_neg_cancel]

def multiply (f : Spacetime → ℂ) (u : Distribution F) : Distribution F :=
  TemperedDistribution.smulLeftCLM F f u

@[simp] theorem multiply_zero (f : Spacetime → ℂ) : multiply f (0 : Distribution F) = 0 :=
  map_zero _

@[simp] theorem multiply_add (f : Spacetime → ℂ) (u v : Distribution F) :
    multiply f (u + v) = multiply f u + multiply f v := map_add _ _ _

@[simp] theorem multiply_sub (f : Spacetime → ℂ) (u v : Distribution F) :
    multiply f (u - v) = multiply f u - multiply f v := map_sub _ _ _

@[simp] theorem multiply_smul (f : Spacetime → ℂ) (a : ℂ) (u : Distribution F) :
    multiply f (a • u) = a • multiply f u := map_smul _ _ _

@[simp] theorem multiply_sum {ι : Type*} (f : Spacetime → ℂ) (s : Finset ι)
    (u : ι → Distribution F) : multiply f (∑ i ∈ s, u i) = ∑ i ∈ s, multiply f (u i) :=
  map_sum _ _ _

theorem multiply_add_function {f g : Spacetime → ℂ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) (u : Distribution F) :
    multiply (f + g) u = multiply f u + multiply g u := by
  simp [multiply, TemperedDistribution.smulLeftCLM_add hf hg]

theorem multiply_smul_function {f : Spacetime → ℂ}
    (hf : f.HasTemperateGrowth) (a : ℂ) (u : Distribution F) :
    multiply (a • f) u = a • multiply f u := by
  simp [multiply, TemperedDistribution.smulLeftCLM_smul hf]

abbrev CovectorField := Fin 4 → Spacetime → ℂ

abbrev fpd (μ : Fin 4) (f : Spacetime → ℂ) : Spacetime → ℂ :=
  functionDerivative (coordinateVector μ) f

def vectorDivergence (X : CovectorField) : Spacetime → ℂ :=
  ∑ μ, metricSign μ • fpd μ (X μ)

def TemperateVectorField (X : CovectorField) : Prop :=
  ∀ μ, (X μ).HasTemperateGrowth

def ConformalKilling (X : CovectorField) : Prop := ∀ μ ν,
  fpd μ (X ν) + fpd ν (X μ) = (1 / 2 : ℂ) • metric μ ν • vectorDivergence X

theorem vectorDivergence_temperate {X : CovectorField} (hX : TemperateVectorField X) :
    (vectorDivergence X).HasTemperateGrowth := by
  have h (μ : Fin 4) (_ : μ ∈ (Finset.univ : Finset (Fin 4))) :
      (metricSign μ • fpd μ (X μ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).smul
      (functionDerivative_temperate (hX μ) _)
  simpa only [vectorDivergence, ← Finset.sum_apply] using
    (Function.HasTemperateGrowth.sum h)

def current (X : CovectorField) (T : Tensor F) (μ : Fin 4) : Distribution F :=
  ∑ ν, metricSign ν • multiply (X ν) (T μ ν)

def currentDivergence (J : Fin 4 → Distribution F) : Distribution F :=
  ∑ μ, metricSign μ • pd μ (J μ)

def derivativeContraction (X : CovectorField) (T : Tensor F) : Distribution F :=
  ∑ μ, ∑ ν, metricSign μ • metricSign ν • multiply (fpd μ (X ν)) (T μ ν)

theorem current_divergence_product_rule {X : CovectorField}
    (hX : TemperateVectorField X) (T : Tensor F) :
    currentDivergence (current X T) = derivativeContraction X T +
      ∑ ν, metricSign ν • multiply (X ν) (divergence T ν) := by
  have hprod (μ ν : Fin 4) (u : Distribution F) :
      pd μ (multiply (X ν) u) =
        multiply (fpd μ (X ν)) u + multiply (X ν) (pd μ u) :=
    distribution_multiplier_derivative (hX ν) _ _
  simp only [currentDivergence, current, partial_sum, partial_smul, hprod,
    smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  simp only [divergence, multiply_sum, multiply_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro μ _
  exact smul_comm _ _ _

theorem derivativeContraction_swap (X : CovectorField) {T : Tensor F}
    (hT : SymmetricTensor T) :
    (∑ μ, ∑ ν, metricSign μ • metricSign ν • multiply (fpd ν (X μ)) (T μ ν)) =
      derivativeContraction X T := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  rw [hT ν μ, smul_comm]

theorem conformal_killing_contraction {X : CovectorField}
    (hX : TemperateVectorField X) (hCK : ConformalKilling X)
    {T : Tensor F} (hT : SymmetricTensor T) :
    derivativeContraction X T =
      (1 / 4 : ℂ) • multiply (vectorDivergence X) (trace T) := by
  change ∀ μ ν, fpd μ (X ν) + fpd ν (X μ) =
    (1 / 2 : ℂ) • metric μ ν • vectorDivergence X at hCK
  have hsum : derivativeContraction X T + derivativeContraction X T =
      (1 / 2 : ℂ) • multiply (vectorDivergence X) (trace T) := by
    conv_lhs => rhs; rw [← derivativeContraction_swap X hT]
    simp only [derivativeContraction, ← Finset.sum_add_distrib, ← smul_add]
    simp_rw [← multiply_add_function
      (functionDerivative_temperate (hX _) _)
      (functionDerivative_temperate (hX _) _), hCK]
    have hmult (μ ν : Fin 4) :
        multiply ((1 / 2 : ℂ) • metric μ ν • vectorDivergence X) (T μ ν) =
          (1 / 2 : ℂ) • metric μ ν • multiply (vectorDivergence X) (T μ ν) := by
      have hg : (metric μ ν • vectorDivergence X).HasTemperateGrowth :=
        (Function.HasTemperateGrowth.const _).smul (vectorDivergence_temperate hX)
      rw [multiply_smul_function hg,
        multiply_smul_function (vectorDivergence_temperate hX)]
    simp only [hmult]
    simp only [metric, ite_smul, zero_smul, smul_ite, smul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp only [smul_smul, metric_sign_sq, mul_left_comm]
    simp only [trace, multiply_sum, multiply_smul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro μ _
    rw [smul_smul]
    congr 1
    ring
  calc
    derivativeContraction X T =
        (1 / 2 : ℂ) • (derivativeContraction X T + derivativeContraction X T) := by module
    _ = (1 / 2 : ℂ) • ((1 / 2 : ℂ) • multiply (vectorDivergence X) (trace T)) := by rw [hsum]
    _ = _ := by module

theorem conformal_current_divergence {X : CovectorField}
    (hX : TemperateVectorField X) (hCK : ConformalKilling X)
    {T : Tensor F} (hT : SymmetricTensor T) :
    currentDivergence (current X T) =
      (1 / 4 : ℂ) • multiply (vectorDivergence X) (trace T) +
        ∑ ν, metricSign ν • multiply (X ν) (divergence T ν) := by
  rw [current_divergence_product_rule hX T, conformal_killing_contraction hX hCK hT]

theorem conformal_current_conserved {X : CovectorField}
    (hX : TemperateVectorField X) (hCK : ConformalKilling X)
    {T : Tensor F} (hT : SymmetricTensor T) (hcons : ConservedTensor T)
    (htrace : trace T = 0) :
    currentDivergence (current X T) = 0 := by
  rw [conformal_current_divergence hX hCK hT, htrace]
  have hc (ν : Fin 4) : divergence T ν = 0 := hcons ν
  simp [hc]

structure AffineKillingVector where
  offset : Fin 4 → ℂ
  linear : Fin 4 → Spacetime →L[ℝ] ℂ
  skew : ∀ μ ν, linear μ (coordinateVector ν) + linear ν (coordinateVector μ) = 0

def AffineKillingVector.field (X : AffineKillingVector) : CovectorField :=
  fun μ x => X.offset μ + X.linear μ x

theorem AffineKillingVector.derivative (X : AffineKillingVector) (μ ν : Fin 4) :
    fpd μ (X.field ν) = fun _ => X.linear ν (coordinateVector μ) := by
  funext x
  change (fderiv ℝ (fun y : Spacetime => X.offset ν + X.linear ν y) x)
    (coordinateVector μ) = X.linear ν (coordinateVector μ)
  simp [fderiv_const_add]

@[simp] theorem AffineKillingVector.diagonal (X : AffineKillingVector) (μ : Fin 4) :
    X.linear μ (coordinateVector μ) = 0 := by
  have h := X.skew μ μ
  linear_combination (1 / 2 : ℂ) * h

theorem AffineKillingVector.temperate (X : AffineKillingVector) :
    TemperateVectorField X.field := fun μ =>
  (Function.HasTemperateGrowth.const _).add (X.linear μ).hasTemperateGrowth

@[simp] theorem AffineKillingVector.divergence (X : AffineKillingVector) :
    vectorDivergence X.field = 0 := by
  ext x
  simp [vectorDivergence, X.derivative]

theorem AffineKillingVector.conformalKilling (X : AffineKillingVector) :
    ConformalKilling X.field := by
  intro μ ν
  ext x
  simp only [X.derivative, Pi.add_apply, X.divergence, smul_zero, Pi.zero_apply]
  exact X.skew ν μ

def affineSuperpotential (X : AffineKillingVector) (L : Distribution F) : Tensor F :=
  fun lam μ => (1 / 3 : ℂ) •
    (multiply (X.field lam) (pd μ L) - multiply (X.field μ) (pd lam L) +
      X.linear μ (coordinateVector lam) • L)

theorem affineSuperpotential_antisymmetric (X : AffineKillingVector) (L : Distribution F)
    (μ ν : Fin 4) : affineSuperpotential X L μ ν = -affineSuperpotential X L ν μ := by
  have h : X.linear ν (coordinateVector μ) = -X.linear μ (coordinateVector ν) :=
    eq_neg_of_add_eq_zero_left (X.skew ν μ)
  simp only [affineSuperpotential, h, neg_smul]
  module

theorem correction_current (X : CovectorField) (L : Distribution F) (μ : Fin 4) :
    current X (correction L) μ = (1 / 3 : ℂ) •
      ((∑ ν, metricSign ν • multiply (X ν) (pd μ (pd ν L))) -
        multiply (X μ) (wave L)) := by
  simp only [current, correction, multiply_smul, multiply_sub]
  simp_rw [smul_comm (metricSign _) (1 / 3 : ℂ)]
  rw [← Finset.smul_sum]
  congr 1
  simp only [smul_sub, Finset.sum_sub_distrib]
  congr 1
  simp_rw [metric_symmetric μ]
  exact metric_contract μ _

theorem affine_superpotential_identity (X : AffineKillingVector) (L : Distribution F)
    (μ : Fin 4) :
    current X.field (correction L) μ = divergence (affineSuperpotential X L) μ := by
  have hprod (i j : Fin 4) (u : Distribution F) :
      pd i (multiply (X.field j) u) =
        X.linear j (coordinateVector i) • u + multiply (X.field j) (pd i u) := by
    have h := distribution_multiplier_derivative (X.temperate j) (coordinateVector i) u
    change pd i (multiply (X.field j) u) =
      multiply (fpd i (X.field j)) u + multiply (X.field j) (pd i u) at h
    simpa only [X.derivative, multiply, TemperedDistribution.smulLeftCLM_const] using h
  rw [correction_current]
  simp only [divergence, affineSuperpotential, partial_smul, partial_add, partial_sub, hprod,
    X.diagonal, zero_smul, zero_add]
  have hcancel (i : Fin 4) :
      multiply (X.field i) (pd i (pd μ L)) -
        (X.linear μ (coordinateVector i) • pd i L + multiply (X.field μ) (pd i (pd i L))) +
          X.linear μ (coordinateVector i) • pd i L =
      multiply (X.field i) (pd μ (pd i L)) - multiply (X.field μ) (pd i (pd i L)) := by
    rw [partial_commute i μ]
    abel
  simp_rw [hcancel, smul_comm (metricSign _) (1 / 3 : ℂ)]
  rw [← Finset.smul_sum]
  simp only [smul_sub, Finset.sum_sub_distrib]
  simp only [wave, multiply_sum, multiply_smul]

end ScaleConformal

end

end OAI
