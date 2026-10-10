import Mathlib
import OAI.NumberTheory.PrimePackets.NormalClosure

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
namespace PrimeDegreePackets.HeckeMellin

 
def unitIntegralIdeal (K : Type*) [Field K] [NumberField K] : integralFractionalIdeals K :=
  ⟨1, le_rfl⟩

lemma integralFractionalIdeals_absNorm_eq_one_iff {K : Type*} [Field K] [NumberField K]
    (J : integralFractionalIdeals K) :
    (FractionalIdeal.absNorm J.1.val : ℝ) = 1 ↔ J = unitIntegralIdeal K := by
  obtain ⟨I,hI⟩ := (integralFractionalIdealsEquiv K).surjective J
  subst J
  change (FractionalIdeal.absNorm (I.1 : FractionalIdeal (𝓞 K)⁰ K) : ℝ) = 1 ↔ _
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
  constructor
  · intro H
    have HI : I.1 = ⊤ := Ideal.absNorm_eq_one_iff.mp (by exact_mod_cast H)
    apply Subtype.ext
    apply Units.ext
    change (I.1 : FractionalIdeal (𝓞 K)⁰ K) = 1
    simp only [HI, FractionalIdeal.coeIdeal_top]
  · intro H
    have HI := congrArg (fun J : integralFractionalIdeals K => J.1.val) H
    change (I.1 : FractionalIdeal (𝓞 K)⁰ K) = 1 at HI
    have HI' : I.1 = ⊤ := FractionalIdeal.coeIdeal_injective (K := K) (by simpa using HI)
    simp [HI']

 

theorem idealClassDirichlet_tendsto_atTop {K : Type*} [Field K] [NumberField K]
    (w : ClassGroup (𝓞 K) → ℂ) :
    Tendsto (fun s : ℝ => idealClassDirichlet K w s) atTop (𝓝 (w 1)) := by
  classical
  let M := ∑ c : ClassGroup (𝓞 K), ‖w c‖
  let g := fun J : integralFractionalIdeals K =>
    if J = unitIntegralIdeal K then w 1 else 0
  have hg : (∑' J, g J) = w 1 := by
    simp [g]
  rw [← hg]
  apply tendsto_tsum_of_dominated_convergence
    ((integralFractionalIdeals_norm_summable (K := K) (s := 2) (by norm_num)).mul_left M)
  · intro J
    by_cases hJ : J = unitIntegralIdeal K
    · subst J
      rw [show g (unitIntegralIdeal K) = w 1 from ite_eq_left rfl]
      simp [unitIntegralIdeal]
    · have H : 1 < (FractionalIdeal.absNorm J.1.val : ℝ) :=
        lt_of_le_of_ne (integralFractionalIdeals_absNorm_ge_one J)
          (Ne.symm ((integralFractionalIdeals_absNorm_eq_one_iff J).not.mpr hJ))
      have HR := (tendsto_rpow_atBot_of_base_gt_one
        (FractionalIdeal.absNorm J.1.val : ℝ) H).comp tendsto_neg_atTop_atBot
      have HC := (Complex.continuous_ofReal.tendsto 0).comp HR
      have HC' := tendsto_const_nhds.mul HC (a := w (ClassGroup.mk K J.1))
      simpa only [Function.comp_apply, g, ite_eq_right hJ, Complex.ofReal_zero, mul_zero,
        Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le, Complex.ofReal_neg] using HC'
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs J
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (fractionalIdeal_absNorm_pos _),
      Complex.neg_re, Complex.ofReal_re]
    apply mul_le_mul
    · exact Finset.single_le_sum (fun c _ => norm_nonneg (w c)) (Finset.mem_univ _)
    · exact Real.rpow_le_rpow_of_exponent_le (integralFractionalIdeals_absNorm_ge_one J) (neg_le_neg hs)
    · exact Real.rpow_nonneg (fractionalIdeal_absNorm_pos _).le _
    · exact Finset.sum_nonneg (fun c _ => norm_nonneg (w c))

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

lemma idealClassDirichlet_eventually_ne_zero {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) :
    ∀ᶠ s : ℝ in atTop, idealClassDirichlet K χ s ≠ 0 := by
  apply (idealClassDirichlet_tendsto_atTop χ).eventually_ne
  simp

 

lemma entireIdealClassL_ne_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) :
    entireIdealClassL σ hn χ ≠ 0 := by
  obtain ⟨s,hs,hL⟩ := ((eventually_gt_atTop (1 : ℝ)).and
    (idealClassDirichlet_eventually_ne_zero χ)).exists
  have H : entireIdealClassL σ hn χ (s : ℂ) ≠ 0 := by
    rw [entireIdealClassL_eq σ hn χ (finite_group_character_sum_eq_zero χ hχ) hs]
    apply mul_ne_zero
    · apply mul_ne_zero (completionExponential_ne_zero _ _ _)
      apply pow_ne_zero
      exact Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by simpa using (lt_trans zero_lt_one hs)))
    · exact hL
  intro hf
  exact H (congrFun hf s)

 

theorem nonprincipalHeckeL_finite_nonnegative_order {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (entireIdealClassL σ hn χ) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (entireIdealClassL σ hn χ) z :=
    fun z => (entireIdealClassL_entire σ hn χ).analyticAt z
  have hfin : analyticOrderAt (entireIdealClassL σ hn χ) β ≠ ⊤ := by
    intro H
    exact entireIdealClassL_ne_zero σ hn χ hχ
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.HeckeMellin

 

def idealClassLFunction {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  (completionExponential (d+1) |(NumberField.discr K : ℝ)| s)⁻¹ *
    (Complex.Gamma (s/2))⁻¹ ^ (d+1) * entireIdealClassL σ hn χ s

lemma idealClassLFunction_entire {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) :
    Differentiable ℂ (idealClassLFunction σ hn χ) := by
  apply Differentiable.mul _ (entireIdealClassL_entire σ hn χ)
  apply Differentiable.mul
  · have HE : Differentiable ℂ (completionExponential (d+1)
        |(NumberField.discr K : ℝ)|) :=
      fun s => (completionExponential_hasDerivAt _ _ s).differentiableAt
    exact HE.inv (fun s => completionExponential_ne_zero _ _ s)
  · exact (Complex.differentiable_one_div_Gamma.comp (differentiable_id.div_const 2)).pow _

 

theorem idealClassLFunction_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    idealClassLFunction σ hn χ s = idealClassDirichlet K χ s := by
  unfold idealClassLFunction
  rw [entireIdealClassL_eq σ hn χ (finite_group_character_sum_eq_zero χ hχ) hs]
  have hE := completionExponential_ne_zero (d+1) |(NumberField.discr K : ℝ)| s
  have hG := Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith : 0 < s.re))
  rw [inv_pow]
  field_simp

 
lemma idealClassLFunction_tendsto_atTop {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) :
    Tendsto (fun s : ℝ => idealClassLFunction σ hn χ s) atTop (𝓝 1) := by
  have H := idealClassDirichlet_tendsto_atTop χ
  simp only [map_one] at H
  apply H.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  exact (idealClassLFunction_eq σ hn χ hχ hs).symm

lemma idealClassLFunction_ne_zero {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) :
    idealClassLFunction σ hn χ ≠ 0 := by
  obtain ⟨s,hs⟩ := ((idealClassLFunction_tendsto_atTop σ hn χ hχ).eventually_ne
    (one_ne_zero : (1 : ℂ) ≠ 0)).exists
  exact fun H => hs (congrFun H s)

 

theorem idealClassLFunction_finite_nonnegative_order {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (idealClassLFunction σ hn χ) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (idealClassLFunction σ hn χ) z :=
    fun z => (idealClassLFunction_entire σ hn χ).analyticAt z
  have hfin : analyticOrderAt (idealClassLFunction σ hn χ) β ≠ ⊤ := by
    intro H
    exact idealClassLFunction_ne_zero σ hn χ hχ
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end PrimeDegreePackets.HeckeMellin

open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
namespace PrimeDegreePackets.HeckeMellin

 
def conjugateClassCharacter {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) : ClassGroup (𝓞 K) →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp χ

@[simp] lemma conjugateClassCharacter_apply {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) (c : ClassGroup (𝓞 K)) :
    conjugateClassCharacter χ c = conj (χ c) := rfl

@[simp] lemma conjugateClassCharacter_conjugate {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) :
    conjugateClassCharacter (conjugateClassCharacter χ) = χ := by
  ext c
  simp

lemma conjugateClassCharacter_ne_one {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) : conjugateClassCharacter χ ≠ 1 := by
  intro H
  apply hχ
  ext c
  have Hc := congrArg (fun f : ClassGroup (𝓞 K) →* ℂ => conj (f c)) H
  simpa using Hc

lemma idealClassDirichlet_conj_real {K : Type*} [Field K] [NumberField K]
    (χ : ClassGroup (𝓞 K) →* ℂ) (r : ℝ) :
    conj (idealClassDirichlet K χ r) =
      idealClassDirichlet K (conjugateClassCharacter χ) r := by
  unfold idealClassDirichlet
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro J
  rw [map_mul, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (fractionalIdeal_absNorm_pos _).le,
    Complex.conj_ofReal]
  rfl

 

theorem idealClassLFunction_conjugation {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) (s : ℂ) :
    idealClassLFunction σ hn (conjugateClassCharacter χ) (conj s) =
      conj (idealClassLFunction σ hn χ s) := by
  have H : Differentiable ℂ (conj ∘ idealClassLFunction σ hn χ ∘ conj) := by
    intro z
    apply differentiableAt_conj_conj_iff.mpr
    exact idealClassLFunction_entire σ hn χ _
  have HE := entire_eq_of_real_eq H
    (idealClassLFunction_entire σ hn (conjugateClassCharacter χ)) (fun r hr => by
      simp only [Function.comp_apply, Complex.conj_ofReal]
      rw [idealClassLFunction_eq σ hn χ hχ hr,
        idealClassLFunction_eq σ hn _ (conjugateClassCharacter_ne_one χ hχ) hr,
        idealClassDirichlet_conj_real])
  have Hs := congrFun HE (conj s)
  simpa using Hs.symm

 
lemma idealClassLFunction_real_zero_conjugate {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (χ : ClassGroup (𝓞 K) →* ℂ) (hχ : χ ≠ 1) (β : ℝ)
    (hβ : idealClassLFunction σ hn χ β = 0) :
    idealClassLFunction σ hn (conjugateClassCharacter χ) β = 0 := by
  simpa only [Complex.conj_ofReal, hβ, _root_.map_zero] using
    idealClassLFunction_conjugation σ hn χ hχ (β : ℂ)

end PrimeDegreePackets.HeckeMellin

open Module
namespace PrimeDegreePackets

variable {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]

 
def cosetFixedVector (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) : G ⧸ H → W :=
  Quotient.lift (fun g : G => ρ g v) (by
    intro a b hab
    have hv : ρ (a⁻¹*b) v = v := v.property ⟨a⁻¹*b,
      (QuotientGroup.leftRel_apply).mp hab⟩
    calc
      ρ a v = ρ a (ρ (a⁻¹*b) v) := congrArg (ρ a) hv.symm
      _ = ρ b v := by rw [← Module.End.mul_apply, ← map_mul]; simp)

@[simp] lemma cosetFixedVector_mk (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) (g : G) :
    cosetFixedVector H ρ v (QuotientGroup.mk g) = ρ g v := rfl

lemma cosetFixedVector_smul (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) (g : G) (q : G ⧸ H) :
    cosetFixedVector H ρ v (g • q) = ρ g (cosetFixedVector H ρ v q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change ρ (g*a) v = ρ g (ρ a v)
    rw [map_mul, Module.End.mul_apply]

 

def cosetFixedIntertwiner (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) :
    Representation.IntertwiningMap (Representation.ofMulAction ℂ G (G ⧸ H)) ρ where
  toLinearMap := (Finsupp.linearCombination ℂ (cosetFixedVector H ρ v)).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  isIntertwining' g := by
    apply MonoidAlgebra.lhom_ext'
    intro q
    apply LinearMap.ext
    intro r
    simp [cosetFixedVector_smul]

@[simp] lemma cosetFixedIntertwiner_single (H : Subgroup G) (ρ : Representation ℂ G W)
    (v : Representation.invariants (ρ.comp H.subtype)) (q : G ⧸ H) (r : ℂ) :
    cosetFixedIntertwiner H ρ v (MonoidAlgebra.single q r) =
      r • cosetFixedVector H ρ v q := by
  simp [cosetFixedIntertwiner]

 

def cosetIntertwinerEvaluation (H : Subgroup G) (ρ : Representation ℂ G W) :
    Representation.IntertwiningMap (Representation.ofMulAction ℂ G (G ⧸ H)) ρ
      →ₗ[ℂ] Representation.invariants (ρ.comp H.subtype) where
  toFun f := ⟨f (MonoidAlgebra.single (QuotientGroup.mk (1:G)) 1), by
    intro h
    have he : (h : G) • (QuotientGroup.mk (1:G) : G ⧸ H) = QuotientGroup.mk (1:G) := by
      change QuotientGroup.mk ((h:G)*1) = QuotientGroup.mk (1:G)
      apply QuotientGroup.eq.mpr
      simp
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, ← f.isIntertwining,
      Representation.ofMulAction_single, he]⟩
  map_add' f g := by ext; rfl
  map_smul' r f := by ext; rfl

 
def cosetIntertwinerEquivInvariants (H : Subgroup G) (ρ : Representation ℂ G W) :
    Representation.IntertwiningMap (Representation.ofMulAction ℂ G (G ⧸ H)) ρ
      ≃ₗ[ℂ] Representation.invariants (ρ.comp H.subtype) :=
  { cosetIntertwinerEvaluation H ρ with
    invFun := cosetFixedIntertwiner H ρ
    left_inv f := by
      apply Representation.IntertwiningMap.ext
      apply MonoidAlgebra.lhom_ext'
      intro q
      induction q using Quotient.inductionOn with
      | h g =>
        apply LinearMap.ext
        intro r
        simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply,
          Representation.IntertwiningMap.toLinearMap_apply,
          cosetFixedIntertwiner_single, cosetFixedVector_mk]
        change r • ρ g (f (MonoidAlgebra.single (QuotientGroup.mk (1:G)) 1)) = _
        rw [← f.isIntertwining, Representation.ofMulAction_single]
        change r • f (MonoidAlgebra.single (QuotientGroup.mk (g*1)) 1) = _
        rw [mul_one, ← map_smul]
        congr 1
        simp
    right_inv v := by
      apply Subtype.ext
      change cosetFixedIntertwiner H ρ v (MonoidAlgebra.single
        (QuotientGroup.mk (1:G)) 1) = v
      simp }

 

theorem coset_character_multiplicity [Fintype G] [FiniteDimensional ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ G W) :
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g *
      (Representation.ofMulAction ℂ G (G ⧸ H)).character g⁻¹ =
        (finrank ℂ (Representation.invariants (ρ.comp H.subtype)) : ℂ) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G).ne')
  rw [Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
    (cosetIntertwinerEquivInvariants H ρ).finrank_eq]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

lemma virtual_characterPair_cosets {G I : Type*} [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) (c : I → ℤ) (H : Subgroup G) :
    characterPair (fun g => ∑ i, (c i : ℂ) * (V i).character g)
      (Representation.ofMulAction ℂ G (G ⧸ H)).character =
      (∑ i, c i * (finrank ℂ (Representation.invariants
        ((V i).ρ.comp H.subtype)) : ℤ) : ℤ) := by
  rw [characterPair_sum_left]
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro i _
  rw [characterPair_mul_left]
  exact congrArg (fun z : ℂ => (c i : ℂ) * z)
    (coset_character_multiplicity H ((V i).ρ))

 

theorem heilbronn_principal_of_coset_pairing {G I : Type*}
    [Group G] [Fintype G] [Fintype I]
    (V : I → FDRep ℂ G) [∀ i, Simple (V i)]
    (hV : ∀ i j, i ≠ j → ¬ Nonempty (V i ≅ V j)) (c : I → ℤ)
    (H : Subgroup G) (hodd : Odd H.index)
    (hdeg : ∑ i, (c i : ℂ) * (V i).character 1 = 1)
    (hcyclic : ∀ g : G,
      (∑ i, (c i : ℂ) * (V i).character g) *
        (∑ i, (c i : ℂ) * (V i).character g⁻¹) = 1)
    (hreal : ∀ g, (∑ i, (c i : ℂ) * (V i).character g).im = 0)
    (hperm : characterPair (fun g => ∑ i, (c i : ℂ) * (V i).character g)
      (Representation.ofMulAction ℂ G (G ⧸ H)).character = 1) :
    ∀ g, (∑ i, (c i : ℂ) * (V i).character g) = 1 := by
  apply heilbronn_principal_of_odd_index V hV c H hodd hdeg hcyclic hreal
  rw [virtual_characterPair_cosets] at hperm
  exact_mod_cast hperm

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

 
def cosetLatticeTheta (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) : ℂ :=
  ∑' z : d → ℤ, Complex.exp (-(b:ℂ) *
    ‖B (toLp 2 x + euclideanInteger z)‖^2)

lemma cosetLatticeTheta_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun z : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (toLp 2 x + euclideanInteger z)‖^2)) := by
  have H := ContinuousMap.summable_of_locally_summable_norm
    (coordinateGaussian_locallyNormal (coordinateBasis B) b hb)
  have H' := (ContinuousMap.evalCLM ℂ (x := x)).summable H
  simpa [translate, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add] using H'

lemma cosetPhase_norm (m : d → ℤ) (x : d → ℝ) :
    ‖UnitAddTorus.mFourier m (torusProjection x)‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
    fourier_apply, Circle.norm_coe, Finset.prod_const_one]

lemma twistedDualGaussian_summable
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    Summable (fun m : d → ℤ => Complex.exp (-(b:ℂ) *
      ‖B (euclideanInteger m)‖^2) * UnitAddTorus.mFourier m (torusProjection x)) := by
  apply Summable.of_norm_bounded (latticeTheta_summable B b hb).norm
  intro m
  simp [cosetPhase_norm]

 

theorem cosetLatticeTheta_poisson
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : d → ℝ) (b : ℝ) (hb : 0 < b) :
    cosetLatticeTheta B x b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          UnitAddTorus.mFourier m (torusProjection x) := by
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hsum : Summable (fun m : d → ℤ =>
      ∫ y, fourierCharacter m y * coordinateGaussian (coordinateBasis B) b y) := by
    simp_rw [coordinateGaussian_fourier B b hb]
    exact (latticeTheta_summable (adjointEquiv B.symm) _ hb').mul_left _
  have H := multivariate_poisson (coordinateGaussian (coordinateBasis B) b)
    (coordinateGaussian_locallyNormal _ b hb) (coordinateGaussian_integrable B b hb) hsum x
  simp only [coordinateGaussian_fourier B b hb, mul_assoc, tsum_mul_left] at H
  simpa [cosetLatticeTheta, coordinateGaussian, coordinateBasis, euclideanInteger, toLp_add,
    mul_assoc] using H

 

def congruenceTheta {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) : ℂ :=
  ∑ i, w i * cosetLatticeTheta B (x i) b

 
def congruenceThetaFourierWeight {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) (m : d → ℤ) : ℂ :=
  ∑ i, w i * UnitAddTorus.mFourier m (torusProjection (x i))

@[simp] lemma congruenceThetaFourierWeight_zero {I : Type*} [Fintype I]
    (x : I → d → ℝ) (w : I → ℂ) :
    congruenceThetaFourierWeight x w 0 = ∑ i, w i := by
  simp [congruenceThetaFourierWeight, UnitAddTorus.mFourier]

 

theorem congruenceTheta_poisson {I : Type*} [Fintype I]
    (B : EuclideanSpace ℝ d ≃L[ℝ] EuclideanSpace ℝ d)
    (x : I → d → ℝ) (w : I → ℂ) (b : ℝ) (hb : 0 < b) :
    congruenceTheta B x w b = ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
      (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2) *
        ∑' m : d → ℤ, Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
          ‖adjointEquiv B.symm (euclideanInteger m)‖^2) *
          congruenceThetaFourierWeight x w m := by
  classical
  let A : ℂ := ((|(LinearMap.det B.toLinearMap)⁻¹|:ℝ):ℂ) *
    (Real.pi / (b:ℂ)) ^ ((Fintype.card d:ℂ)/2)
  let F (m : d → ℤ) := Complex.exp (-((Real.pi^2/b:ℝ):ℂ) *
    ‖adjointEquiv B.symm (euclideanInteger m)‖^2)
  have hb' : 0 < Real.pi^2/b := div_pos (sq_pos_of_pos Real.pi_pos) hb
  have hs (i : I) : Summable (fun m : d → ℤ =>
      w i * (F m * UnitAddTorus.mFourier m (torusProjection (x i)))) :=
    (twistedDualGaussian_summable (adjointEquiv B.symm) (x i) _ hb').mul_left _
  unfold congruenceTheta
  simp_rw [cosetLatticeTheta_poisson B _ b hb]
  change (∑ i, w i * (A * ∑' m, F m *
    UnitAddTorus.mFourier m (torusProjection (x i)))) = _
  calc
    _ = A * ∑ i, ∑' m, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [tsum_mul_left]
      ring
    _ = A * ∑' m, ∑ i, w i * (F m *
        UnitAddTorus.mFourier m (torusProjection (x i))) := by
      rw [Summable.tsum_finsetSum (fun i _ => hs i)]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      simp only [congruenceThetaFourierWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
