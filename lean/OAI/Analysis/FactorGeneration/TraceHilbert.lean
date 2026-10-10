import Mathlib.Analysis.InnerProductSpace.Completion
import OAI.Analysis.FactorGeneration.CyclicPredual
import OAI.Analysis.FactorGeneration.NormalTrace

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Algebraic type copy indexed by the original factor hypotheses. -/
def TraceFreePreHilbert
(_hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
(_hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
(_hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
(_hunit : (1 : M.toStarSubalgebra) ≠ 0)
    : Type _ := M.toStarSubalgebra

local instance traceHilbertCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

instance traceFreePreHilbertRing : Ring E := inferInstanceAs (Ring M.toStarSubalgebra)
instance traceFreePreHilbertAlgebra : Algebra ℂ E :=
  inferInstanceAs (Algebra ℂ M.toStarSubalgebra)
instance traceFreePreHilbertStarRing : StarRing E :=
  inferInstanceAs (StarRing M.toStarSubalgebra)
instance traceFreePreHilbertStarModule : StarModule ℂ E :=
  inferInstanceAs (StarModule ℂ M.toStarSubalgebra)

/-- Algebraic identification only: it does not identify the two norms. -/
def traceFreeCopy : M.toStarSubalgebra ≃⋆ₐ[ℂ] E :=
  _root_.StarAlgEquiv.refl ℂ M.toStarSubalgebra

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

@[instance_reducible] def traceFreeInnerCore : InnerProductSpace.Core ℂ E where
  inner x y := τ₀ (star ((copy).symm x) * (copy).symm y)
  conj_inner_symm x y := by
    change star (τ₀ (star ((copy).symm y) * (copy).symm x)) = _
    rw [← (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.1]
    simp only [star_mul, star_star]
  re_inner_nonneg x :=
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _ (star_mul_self_nonneg _)
  add_left x y z := by simp only [map_add, star_add, add_mul]
  smul_left x y c := by
    simp only [map_smul, star_smul, smul_mul_assoc]
    rfl
  definite x hx := by
    have hz := (traceFreeTrace_faithful hfactor hdiff hfinite hunit _
      (star_mul_self_nonneg ((copy).symm x))).mp hx
    have hx' : (copy).symm x = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    exact (copy).symm.injective (hx'.trans (map_zero (copy).symm).symm)

instance traceFreePreHilbertNormedAddCommGroup : NormedAddCommGroup E :=
  (traceFreeInnerCore hfactor hdiff hfinite hunit).toNormedAddCommGroup
instance traceFreePreHilbertInnerProductSpace : InnerProductSpace ℂ E :=
  .ofCore { traceFreeInnerCore hfactor hdiff hfinite hunit with }

@[simp] theorem traceFreeCopy_inner (x y : M.toStarSubalgebra) :
    inner ℂ (copy x) (copy y) = τ₀ (star x*y) := rfl

theorem traceFreeCopy_norm_sq (x : M.toStarSubalgebra) :
    ‖copy x‖^2 = (τ₀ (star x*x)).re := by
  rw [← traceFreeCopy_inner hfactor hdiff hfinite hunit]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (copy x)).symm

/-- The actual Hilbert completion; no representation is supplied. -/
abbrev TraceFreeHilbert := UniformSpace.Completion E

def traceFreeInclusion : E →ₗᵢ[ℂ] TraceFreeHilbert hfactor hdiff hfinite hunit :=
  UniformSpace.Completion.toComplₗᵢ

@[simp] theorem traceFreeInclusion_inner (x y : M.toStarSubalgebra) :
    inner ℂ (traceFreeInclusion hfactor hdiff hfinite hunit (copy x))
      (traceFreeInclusion hfactor hdiff hfinite hunit (copy y)) = τ₀ (star x*y) :=
  UniformSpace.Completion.inner_coe (𝕜 := ℂ) (copy x) (copy y)

theorem traceFreeInclusion_denseRange :
    DenseRange (traceFreeInclusion hfactor hdiff hfinite hunit) :=
  UniformSpace.Completion.denseRange_coe

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertBoundCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertBoundOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertBoundPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceHilbertBoundLE : LE M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance traceHilbertBoundStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

theorem traceFreeTrace_mul_square_le (a x : M.toStarSubalgebra) :
    (τ₀ (star (a*x)*(a*x))).re ≤ ‖a‖^2 * (τ₀ (star x*x)).re := by
  have hp : 0 ≤ algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq a)
  have h := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _
    (star_left_conjugate_nonneg hp x)
  have he : star x*(algebraMap ℝ M.toStarSubalgebra (‖a‖^2)-star a*a)*x =
      (‖a‖^2) • (star x*x)-star (a*x)*(a*x) := by
    simp only [Algebra.algebraMap_eq_smul_one,mul_sub,sub_mul,mul_smul_comm,
      smul_mul_assoc,mul_one,star_mul,mul_assoc]
  rw [he,map_sub, ContinuousLinearMap.map_smul_of_tower, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  exact sub_nonneg.mp h

theorem traceFreeCopy_mul_norm_le (a x : M.toStarSubalgebra) :
    ‖copy (a*x)‖ ≤ ‖a‖ * ‖copy x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, traceFreeCopy_norm_sq, traceFreeCopy_norm_sq]
  exact traceFreeTrace_mul_square_le hfactor hdiff hfinite hunit a x

theorem traceFreeInclusion_mul_norm_le (a x : M.toStarSubalgebra) :
    ‖traceFreeInclusion hfactor hdiff hfinite hunit (copy (a*x))‖ ≤
      ‖a‖ * ‖traceFreeInclusion hfactor hdiff hfinite hunit (copy x)‖ := by
  simpa only [LinearIsometry.norm_map] using
    traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x

end

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertActionCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertActionOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

def traceFreeLeftOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulLeft ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x)

@[simp] theorem traceFreeLeftOnPreHilbert_apply (a : M.toStarSubalgebra) (x : E) :
    traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a x = copy a*x := rfl

def traceFreeLeftAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "L" => traceFreeLeftAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeLeftAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    L a (ι x) = ι (copy a*x) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeLeftOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeLeftAction_coe (a : M.toStarSubalgebra) (x : E) :
    L a (x : K) = ((copy a*x : E) : K) :=
  traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a x

theorem traceFreeLeftAction_norm_le (a : M.toStarSubalgebra) : ‖L a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  apply isClosed_property (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    (isClosed_le (by fun_prop) (by fun_prop))
  intro x
  obtain ⟨x,rfl⟩ := (copy).surjective x
  rw [traceFreeLeftAction_inclusion,LinearIsometry.norm_map,LinearIsometry.norm_map]
  exact traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit a x

@[simp] theorem traceFreeLeftAction_one : L 1 = 1 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_one,one_mul,one_apply_eq_self]

@[simp] theorem traceFreeLeftAction_mul (a b : M.toStarSubalgebra) :
    L (a*b) = L a*L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [mul_apply_eq_comp,traceFreeLeftAction_coe,map_mul,mul_assoc]

@[simp] theorem traceFreeLeftAction_add (a b : M.toStarSubalgebra) :
    L (a+b) = L a+L b := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [add_apply,traceFreeLeftAction_coe,map_add,add_mul,UniformSpace.Completion.coe_add]

@[simp] theorem traceFreeLeftAction_smul (c : ℂ) (a : M.toStarSubalgebra) :
    L (c • a) = c • L a := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (L (c • a)).continuous ((c • L a : K →L[ℂ] K)).continuous) ?_
  intro b
  change L (c • a) (ι b) = c • L a (ι b)
  rw [traceFreeLeftAction_inclusion,traceFreeLeftAction_inclusion,map_smul,smul_mul_assoc]
  exact (ι).map_smul c _

@[simp] theorem traceFreeLeftAction_zero : L 0 = 0 := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [traceFreeLeftAction_coe,map_zero,zero_mul,zero_apply,UniformSpace.Completion.coe_zero]

@[simp] theorem traceFreeLeftAction_star (a : M.toStarSubalgebra) : L (star a) = star (L a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b c
  obtain ⟨b,rfl⟩ := (copy).surjective b
  obtain ⟨c,rfl⟩ := (copy).surjective c
  rw [traceFreeLeftAction_coe,traceFreeLeftAction_coe]
  rw [UniformSpace.Completion.inner_coe,UniformSpace.Completion.inner_coe]
  change τ₀ (star (star a*b)*c) = τ₀ (star b*(a*c))
  simp only [star_mul,star_star,mul_assoc]

def traceFreeHilbertAction : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K) where
  toFun := L
  map_one' := traceFreeLeftAction_one hfactor hdiff hfinite hunit
  map_mul' := traceFreeLeftAction_mul hfactor hdiff hfinite hunit
  map_zero' := traceFreeLeftAction_zero hfactor hdiff hfinite hunit
  map_add' := traceFreeLeftAction_add hfactor hdiff hfinite hunit
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,traceFreeLeftAction_smul,traceFreeLeftAction_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := traceFreeLeftAction_star hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_inclusion (a x : M.toStarSubalgebra) :
    π a (ι (copy x)) = ι (copy (a*x)) := by
  exact (traceFreeLeftAction_inclusion hfactor hdiff hfinite hunit a (copy x)).trans
    (congrArg ι ((copy).map_mul a x).symm)

def traceFreeHilbertVector : K := ι (copy 1)

local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

@[simp] theorem traceFreeHilbertAction_vector (a : M.toStarSubalgebra) :
    π a Ω = ι (copy a) := by
  change π a (ι (copy 1)) = _
  rw [traceFreeHilbertAction_inclusion,mul_one]

theorem traceFreeHilbertVector_norm : ‖Ω‖ = 1 := by
  have h := traceFreeCopy_norm_sq hfactor hdiff hfinite hunit 1
  rw [star_one,one_mul,(traceFreeTrace_spec hfactor hdiff hfinite hunit).2.1] at h
  change ‖ι (copy 1)‖ = 1
  rw [LinearIsometry.norm_map]
  have hn := norm_nonneg (copy 1)
  change ‖copy 1‖^2 = 1 at h
  nlinarith

theorem traceFreeHilbertAction_injective : Function.Injective π := by
  intro a b hab
  have hv := congrArg (fun T : K →L[ℂ] K => T Ω) hab
  simp only [traceFreeHilbertAction_vector] at hv
  exact (copy).injective ((ι).injective hv)

theorem traceFreeHilbertAction_norm (a : M.toStarSubalgebra) : ‖π a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map π (traceFreeHilbertAction_injective hfactor hdiff hfinite hunit) a

theorem traceFreeHilbertAction_trace (a : M.toStarSubalgebra) : inner ℂ Ω (π a Ω) = τ₀ a := by
  rw [traceFreeHilbertAction_vector]
  change inner ℂ (ι (copy 1)) (ι (copy a)) = _
  rw [traceFreeInclusion_inner,star_one,one_mul]

theorem traceFreeHilbertAction_cyclic : DenseRange (fun a : M.toStarSubalgebra => π a Ω) := by
  have hc : Function.Surjective (fun a : M.toStarSubalgebra => copy a) :=
    fun b => ⟨(copy).symm b,(copy).apply_symm_apply b⟩
  have h := (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit).comp
    hc.denseRange (ι).continuous
  simpa only [traceFreeHilbertAction_vector,Function.comp_def] using h

theorem exists_traceFreeHilbert_representation :
    ∃ (ρ : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K),
      ‖v‖ = 1 ∧ Function.Injective ρ ∧ (∀ a, ‖ρ a‖ = ‖a‖) ∧
      (∀ a, inner ℂ v (ρ a v) = τ₀ a) ∧ Dense (Set.range (fun a => ρ a v)) :=
  ⟨π,Ω,traceFreeHilbertVector_norm hfactor hdiff hfinite hunit,
    traceFreeHilbertAction_injective hfactor hdiff hfinite hunit,
    traceFreeHilbertAction_norm hfactor hdiff hfinite hunit,
    traceFreeHilbertAction_trace hfactor hdiff hfinite hunit,
    traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit⟩

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertRightCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertRightOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertRightStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertRightOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

theorem traceFreeCopy_star_norm (x : M.toStarSubalgebra) : ‖copy (star x)‖ = ‖copy x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [traceFreeCopy_norm_sq,traceFreeCopy_norm_sq,star_star,
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2]

theorem traceFreeCopy_mul_norm_le_right (a x : M.toStarSubalgebra) :
    ‖copy (x*a)‖ ≤ ‖a‖ * ‖copy x‖ := by
  rw [← traceFreeCopy_star_norm hfactor hdiff hfinite hunit (x*a),star_mul]
  simpa only [norm_star,traceFreeCopy_star_norm] using
    traceFreeCopy_mul_norm_le hfactor hdiff hfinite hunit (star a) (star x)

def traceFreeRightOnPreHilbert (a : M.toStarSubalgebra) : E →L[ℂ] E :=
  LinearMap.mkContinuous (LinearMap.mulRight ℂ (copy a)) ‖a‖ (by
    intro x
    obtain ⟨x,rfl⟩ := (copy).surjective x
    exact traceFreeCopy_mul_norm_le_right hfactor hdiff hfinite hunit a x)

def traceFreeRightAction (a : M.toStarSubalgebra) : K →L[ℂ] K :=
  ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a)).extend
    (ι).toContinuousLinearMap

local notation "R" => traceFreeRightAction hfactor hdiff hfinite hunit

@[simp] theorem traceFreeRightAction_inclusion (a : M.toStarSubalgebra) (x : E) :
    R a (ι x) = ι (x*copy a) := by
  exact ContinuousLinearMap.extend_eq
    ((ι).toContinuousLinearMap.comp (traceFreeRightOnPreHilbert hfactor hdiff hfinite hunit a))
    (e := (ι).toContinuousLinearMap) (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit)
    ((ι).isometry.isUniformInducing) x

@[simp] theorem traceFreeRightAction_coe (a : M.toStarSubalgebra) (x : E) :
    R a (x : K) = ((x*copy a : E) : K) :=
  traceFreeRightAction_inclusion hfactor hdiff hfinite hunit a x

theorem traceFreeLeftRight_commute (a b : M.toStarSubalgebra) : π a*R b = R b*π a := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  change traceFreeLeftAction hfactor hdiff hfinite hunit a (R b (c : K)) =
    R b (traceFreeLeftAction hfactor hdiff hfinite hunit a (c : K))
  simp only [traceFreeLeftAction_coe,traceFreeRightAction_coe,mul_assoc]

@[simp] theorem traceFreeRightAction_vector (a : M.toStarSubalgebra) : R a Ω = ι (copy a) := by
  change R a (ι (copy 1)) = _
  rw [traceFreeRightAction_inclusion,map_one,one_mul]

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/
section
open Filter
open scoped ComplexConjugate CStarAlgebra Pointwise Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertClosureCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertClosureOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertClosureStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertClosureOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

/-- The bicommutant is a von Neumann algebra; no image-closedness is assumed. -/
def traceFreeHilbertClosure : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))) =
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    simp only [Set.centralizer_centralizer_centralizer]

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

theorem traceFreeHilbertClosure_mem_iff (T : K →L[ℂ] K) :
    T ∈ N ↔ T ∈ Set.centralizer (Set.centralizer ((π).range : Set (K →L[ℂ] K))) := by
  change T ∈ (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) ↔ _
  simp only [← SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

theorem traceFreeHilbertAction_mem_closure (a : M.toStarSubalgebra) : π a ∈ N := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit _).mpr
  intro T hT
  exact (hT (π a) ⟨a,rfl⟩).symm

def traceFreeHilbertIntoClosure : M.toStarSubalgebra →⋆ₐ[ℂ] (N).toStarSubalgebra :=
  (π).codRestrict (N).toStarSubalgebra (traceFreeHilbertAction_mem_closure hfactor hdiff hfinite hunit)

local notation "ρ" => traceFreeHilbertIntoClosure hfactor hdiff hfinite hunit

theorem traceFreeHilbertClosure_strong_net (T : (N).toStarSubalgebra) :
    ∃ a : Finset K × ℕ → M.toStarSubalgebra, ∀ x : K,
      Tendsto (fun d => π (a d) x) atTop (𝓝 (T.val x)) := by
  obtain ⟨b,hb⟩ := bicommutant_exists_strong_net (π).range T.val
    ((traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property)
  have hex (d : Finset K × ℕ) : ∃ a : M.toStarSubalgebra, π a = (b d).val := (b d).property
  choose a ha using hex
  exact ⟨a,fun x => by simpa only [ha] using hb x⟩

theorem traceFreeHilbertClosure_right_commute (T : (N).toStarSubalgebra) (a : M.toStarSubalgebra) :
    traceFreeRightAction hfactor hdiff hfinite hunit a*T.val =
      T.val*traceFreeRightAction hfactor hdiff hfinite hunit a := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property
  rintro B ⟨b,rfl⟩
  exact traceFreeLeftRight_commute hfactor hdiff hfinite hunit b a

theorem traceFreeHilbertClosure_separating (T : (N).toStarSubalgebra) (hT : T.val Ω = 0) : T = 0 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  change ∀ x : K, T.val x = (0 : K)
  apply isClosed_property (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit)
    (isClosed_eq T.val.continuous continuous_const)
  intro a
  rw [traceFreeHilbertAction_vector,← traceFreeRightAction_vector hfactor hdiff hfinite hunit a]
  have he := congrArg (fun B : K →L[ℂ] K => B Ω)
    (traceFreeHilbertClosure_right_commute hfactor hdiff hfinite hunit T a)
  simpa only [mul_apply_eq_comp,hT,map_zero] using he.symm

theorem traceFreeHilbertClosure_trace_commute_copy (T : (N).toStarSubalgebra) (b : M.toStarSubalgebra) :
    inner ℂ Ω (T.val (π b Ω)) = inner ℂ Ω (π b (T.val Ω)) := by
  classical
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_strong_net hfactor hdiff hfinite hunit T
  have he (d : Finset K × ℕ) : inner ℂ Ω (π (a d) (π b Ω)) =
      inner ℂ Ω (π b (π (a d) Ω)) := by
    change inner ℂ Ω ((π (a d)*π b) Ω) = inner ℂ Ω ((π b*π (a d)) Ω)
    rw [← map_mul,← map_mul,traceFreeHilbertAction_trace,traceFreeHilbertAction_trace]
    exact (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2 _ _
  have hl := (innerSL ℂ Ω).continuous.continuousAt.tendsto.comp (ha (π b Ω))
  have hr := ((innerSL ℂ Ω).comp (π b)).continuous.continuousAt.tendsto.comp (ha Ω)
  exact tendsto_nhds_unique hl (hr.congr (fun d => (he d).symm))

theorem traceFreeHilbertClosure_trace_commute (S T : (N).toStarSubalgebra) :
    inner ℂ Ω (S.val (T.val Ω)) = inner ℂ Ω (T.val (S.val Ω)) := by
  classical
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_strong_net hfactor hdiff hfinite hunit S
  have hl := (innerSL ℂ Ω).continuous.continuousAt.tendsto.comp (ha (T.val Ω))
  have hr := ((innerSL ℂ Ω).comp T.val).continuous.continuousAt.tendsto.comp (ha Ω)
  exact tendsto_nhds_unique hl (hr.congr (fun d =>
    traceFreeHilbertClosure_trace_commute_copy hfactor hdiff hfinite hunit T (a d)))

/-- Output tracial representation on the actual bicommutant. Its fields are
proved above; no TracialRepresentation is an input to this construction. -/
def traceFreeHilbertClosureTrace : UltrapowerBridge.TracialRepresentation N where
  vector := Ω
  norm_vector := traceFreeHilbertVector_norm hfactor hdiff hfinite hunit
  cyclic := traceFreeHilbertClosure_trace_commute hfactor hdiff hfinite hunit
  separating := traceFreeHilbertClosure_separating hfactor hdiff hfinite hunit

theorem traceFreeHilbertClosureTrace_copy (a : M.toStarSubalgebra) :
    (traceFreeHilbertClosureTrace hfactor hdiff hfinite hunit).trace (ρ a) = τ₀ a :=
  traceFreeHilbertAction_trace hfactor hdiff hfinite hunit a

theorem traceFreeHilbertClosureTrace_cyclic :
    DenseRange (fun a : (N).toStarSubalgebra => a.val Ω) := by
  apply (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit).mono
  rintro x ⟨a,rfl⟩
  exact ⟨ρ a,rfl⟩

end

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertWOTCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertWOTOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertWOTStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit
local instance traceHilbertWOTOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

def traceFreeHilbertActionCLM : M.toStarSubalgebra →L[ℂ] (K →L[ℂ] K) :=
  (π).toLinearMap.mkContinuous 1 (by
    intro a
    rw [one_mul]
    exact (traceFreeHilbertAction_norm hfactor hdiff hfinite hunit a).le)

def traceFreeHilbertCoefficient (x y : K) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ K x).comp
    (traceFreeHilbertActionCLM hfactor hdiff hfinite hunit))

@[simp] theorem traceFreeHilbertCoefficient_apply (x y : K) (a : M.toStarSubalgebra) :
    traceFreeHilbertCoefficient hfactor hdiff hfinite hunit x y a = inner ℂ y (π a x) := rfl

theorem traceFreeHilbertCoefficient_continuous : Continuous
    (fun p : K × K => traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2) :=
  ((innerSL ℂ).continuous.comp continuous_snd).clm_comp
    (((ContinuousLinearMap.apply ℂ K).continuous.comp continuous_fst).clm_comp continuous_const)

theorem traceFreeHilbertCoefficient_copy_ball_continuous (C : ℝ) (a b : M.toStarSubalgebra) :
    Continuous (fun T : weakOperatorBall M C =>
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩) := by
  obtain ⟨n,ξ,η,ht⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have he (T : weakOperatorBall M C) :
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩ = ∑ i, inner ℂ (b.val (η i)) (T.val (a.val (ξ i))) := by
    rw [traceFreeHilbertCoefficient_apply,traceFreeHilbertAction_inclusion,traceFreeInclusion_inner,ht]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (η i) ((star b.val) (T.val (a.val (ξ i)))) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (a.val (ξ i)) (b.val (η i)))

theorem traceFreeHilbertCoefficient_ball_continuous (C : ℝ) (x y : K) :
    Continuous (fun T : weakOperatorBall M C =>
      inner ℂ y (π ⟨T.val.toCLM,T.property.1⟩ x)) := by
  have hd : DenseRange (fun a : M.toStarSubalgebra => ι (copy a)) := by
    simpa only [traceFreeHilbertAction_vector] using
      traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit
  have hc := (ballContinuousFunctionals_isClosed M C).preimage
    (traceFreeHilbertCoefficient_continuous hfactor hdiff hfinite hunit)
  have hm : ∀ p : K × K,
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2 ∈ ballContinuousFunctionals M C := by
    apply isClosed_property (hd.prodMap hd) hc
    intro p
    exact traceFreeHilbertCoefficient_copy_ball_continuous hfactor hdiff hfinite hunit C p.1 p.2
  exact hm (x,y)

def traceFreeHilbertBallMap (C : ℝ) (T : weakOperatorBall M C) : K →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (π ⟨T.val.toCLM,T.property.1⟩)

theorem traceFreeHilbertBallMap_continuous (C : ℝ) :
    Continuous (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) :=
  ContinuousLinearMapWOT.continuous_iff.mpr
    (traceFreeHilbertCoefficient_ball_continuous hfactor hdiff hfinite hunit C)

theorem traceFreeHilbertBallMap_injective (C : ℝ) :
    Function.Injective (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) := by
  intro a b hab
  have he := traceFreeHilbertAction_injective hfactor hdiff hfinite hunit
    (congrArg ContinuousLinearMapWOT.toCLM hab)
  apply Subtype.ext
  exact congrArg (fun x : M.toStarSubalgebra => ContinuousLinearMapWOT.ofCLM x.val) he

theorem traceFreeHilbertBallMap_isClosedEmbedding (C : ℝ) :
    Topology.IsClosedEmbedding (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  exact (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C).isClosedEmbedding
    (traceFreeHilbertBallMap_injective hfactor hdiff hfinite hunit C)

def traceFreeHilbertWeakBall (C : ℝ) : Set (K →WOT[ℂ] K) :=
  {T | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ C ∧ ContinuousLinearMapWOT.ofCLM (π a) = T}

theorem traceFreeHilbertWeakBall_eq_range (C : ℝ) :
    traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C =
      Set.range (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) := by
  ext T
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩

theorem traceFreeHilbertWeakBall_isCompact (C : ℝ) :
    IsCompact (traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  rw [traceFreeHilbertWeakBall_eq_range]
  exact isCompact_range (traceFreeHilbertBallMap_continuous hfactor hdiff hfinite hunit C)

theorem traceFreeHilbertWeakBall_isClosed (C : ℝ) :
    IsClosed (traceFreeHilbertWeakBall hfactor hdiff hfinite hunit C) :=
  (traceFreeHilbertWeakBall_isCompact hfactor hdiff hfinite hunit C).isClosed

end Generator.Tracial

end

end OAI
