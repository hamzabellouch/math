import OAI.Analysis.CharacterCriterion.BalancedChannels

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.Traces
open scoped CStarAlgebra ComplexOrder InnerProductSpace Matrix
open Filter Topology
structure State (A : Type*) [CStarAlgebra A] where
  functional : A →L[ℂ] ℂ
  norm_le : ‖functional‖≤1
  one : functional 1=1
  trace : ∀ a b, functional (a*b)=functional (b*a)
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
lemma bound (τ : State A) (a : A) : ‖τ.functional a‖≤‖a‖ :=
  (τ.functional.le_opNorm a).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right τ.norm_le (norm_nonneg a))
def pullback (τ : State B) (φ : A →⋆ₐ[ℂ] B) : State A where
  functional := τ.functional.comp (φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by simpa using NonUnitalStarAlgHom.norm_apply_le φ a))
  norm_le := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun a => by
    change ‖τ.functional (φ a)‖≤1*‖a‖
    rw [one_mul]
    exact (bound τ _).trans (NonUnitalStarAlgHom.norm_apply_le φ a))
  one := by change τ.functional (φ 1)=1; rw [map_one,τ.one]
  trace a b := by change τ.functional (φ (a*b))=τ.functional (φ (b*a)); rw [map_mul φ, map_mul φ,τ.trace]
def positive [Nontrivial A] [PartialOrder A] [StarOrderedRing A] (τ : State A) : A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ τ.functional.toLinearMap (States.eval_nonneg τ.functional τ.norm_le τ.one)
lemma positive_apply [Nontrivial A] [PartialOrder A] [StarOrderedRing A] (τ : State A) (a : A) : positive τ a=τ.functional a := rfl
lemma conjugation (τ : State A) (u : unitary A) (a : A) :
    τ.functional (Unitary.conjStarAlgAut ℂ A u a)=τ.functional a := by
  change τ.functional ((u:A)*a*star (u:A))=τ.functional a
  rw [τ.trace,←mul_assoc (star (u:A)),u.property.1,one_mul]

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [instNonemptyι : Nonempty ι]
def matrixLinear : CStarMatrix ι ι ℂ →ₗ[ℂ] ℂ :=
  (Fintype.card ι:ℂ)⁻¹ • (Matrix.traceLinearMap ι ℂ ℂ).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearMap
omit instNonemptyι in
lemma matrixLinear_apply.{contextLevel1}
    (ι : Type contextLevel1)
    [Fintype ι]
    [DecidableEq ι]
    [Nonempty ι]
    (a : CStarMatrix ι ι ℂ) :
    matrixLinear ι a=(Fintype.card ι:ℂ)⁻¹*(∑ i, a i i) := rfl
lemma matrixLinear_bound (a : CStarMatrix ι ι ℂ) : ‖matrixLinear ι a‖≤‖a‖ := by
  rw [matrixLinear_apply,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    (Fintype.card ι:ℝ)⁻¹*‖∑ i, a i i‖ ≤ (Fintype.card ι:ℝ)⁻¹*∑ i, ‖a i i‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card ι:ℝ)⁻¹*∑ _i : ι, ‖a‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => CStarMatrix.norm_entry_le_norm)) (by positivity)
    _ = ‖a‖ := by simp [Fintype.card_ne_zero]
def matrixState : State (CStarMatrix ι ι ℂ) where
  functional := (matrixLinear ι).mkContinuous 1 (fun a => by simpa using matrixLinear_bound ι a)
  norm_le := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun a => by simpa using matrixLinear_bound ι a)
  one := by change matrixLinear ι 1=1; simp [matrixLinear_apply,Fintype.card_ne_zero]
  trace a b := by
    change (Fintype.card ι:ℂ)⁻¹*Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm (a*b))=
      (Fintype.card ι:ℂ)⁻¹*Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm (b*a))
    rw [map_mul CStarMatrix.ofMatrixStarAlgEquiv.symm, map_mul CStarMatrix.ofMatrixStarAlgEquiv.symm, Matrix.trace_mul_comm]
end KirchbergRordam.Traces
namespace KirchbergRordam.Traces
section
open Filter Topology
variable {D E : Type*} [CStarAlgebra D] [CStarAlgebra E]
lemma exists_extension (τ : State D) (φ : D →⋆ₐ[ℂ] E) (hφ : Isometry φ) :
    ∃ f : E →L[ℂ] ℂ, ‖f‖≤1 ∧ f 1=1 ∧ ∀ a, f (φ a)=τ.functional a := by
  let l : D →ₗᵢ[ℂ] E := φ.toAlgHom.toLinearMap.toLinearIsometry hφ
  let e := l.equivRange
  let f := τ.functional.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hf : ‖f‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖τ.functional (e.symm x)‖≤1*‖x‖
    rw [one_mul]
    exact (bound τ _).trans (e.symm.norm_map x).le
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq l.toLinearMap.range f
  have he (a : D) : g (φ a)=τ.functional a := by
    have hh := hg (e a)
    change g (φ a)=τ.functional (e.symm (e a)) at hh
    simpa only [e.symm_apply_apply] using hh
  refine ⟨g,hgn.trans_le hf,?_,he⟩
  simpa only [map_one,τ.one] using he 1

variable (S : CStarInductiveLimit.System)


theorem exists_inductive_trace (τ : ∀ n, State (S.obj n)) :
    Nonempty (State (CStarInductiveLimit.Algebra S)) := by
  classical
  let L := CStarInductiveLimit.Algebra S
  obtain ⟨f,hf⟩ : ∃ f : ℕ → (L →L[ℂ] ℂ), ∀ n,
      ‖f n‖≤1 ∧ f n 1=1 ∧ ∀ a, f n (CStarInductiveLimit.of S n a)=(τ n).functional a := by
    choose f hf using fun n => exists_extension (τ n) (CStarInductiveLimit.of S n)
      (CStarInductiveLimit.of_isometry S n)
    exact ⟨f,hf⟩
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  let g : ℕ → WeakDual ℂ L := fun n => StrongDual.toWeakDual (f n)
  have hm : PureStates.normStates L ∈ ω.map g := by
    change {n | g n ∈ PureStates.normStates L}∈(ω:Filter ℕ)
    exact Filter.Eventually.of_forall (fun n => ⟨(hf n).1,(hf n).2.1⟩)
  obtain ⟨ψ,hψ,ht⟩ := (PureStates.normStates_compact L).ultrafilter_le_nhds' (ω.map g) hm
  have hconv (a : L) : Tendsto (fun n => f n a) (ω:Filter ℕ) (𝓝 (ψ a)) :=
    ((WeakDual.eval_continuous a).tendsto ψ).comp ht
  have hstage (i j : ℕ) (a : S.obj i) (b : S.obj j) :
      ψ (CStarInductiveLimit.of S i a*CStarInductiveLimit.of S j b)=
      ψ (CStarInductiveLimit.of S j b*CStarInductiveLimit.of S i a) := by
    have hev : (fun n => f n (CStarInductiveLimit.of S i a*CStarInductiveLimit.of S j b))=ᶠ[atTop]
        (fun n => f n (CStarInductiveLimit.of S j b*CStarInductiveLimit.of S i a)) := by
      filter_upwards [eventually_ge_atTop (max i j)] with n hn
      have hi := (le_max_left i j).trans hn
      have hj := (le_max_right i j).trans hn
      rw [←CStarInductiveLimit.of_map S i n hi a,←CStarInductiveLimit.of_map S j n hj b,
        ←map_mul (CStarInductiveLimit.of S n),←map_mul (CStarInductiveLimit.of S n),
        (hf n).2.2,(hf n).2.2,(τ n).trace]
    exact tendsto_nhds_unique (hconv _) ((hconv _).congr' (hev.filter_mono (Ultrafilter.of_le _)).symm)
  refine ⟨⟨ψ.toStrongDual,hψ.1,hψ.2,?_⟩⟩
  intro a b
  apply CStarInductiveLimit.induction_on S a
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro i x
    apply CStarInductiveLimit.induction_on S b
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro j y
      exact hstage i j x y
end
open scoped TensorProduct InnerProductSpace ComplexOrder
open Filter Topology
open UniformSpace
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {R S : Type*} [CStarAlgebra R] [CStarAlgebra S]
def tensorRepresentation (π : R →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : S →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    MaxTensor.Algebra R S →⋆ₐ[ℂ] (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K) :=
  MaxTensor.lift (A:=R) (B:=S) (C:= (Spatial.Hilbert H K →L[ℂ] Spatial.Hilbert H K))
    ((Spatial.left (H:=H) (K:=K)).comp π) ((Spatial.right (H:=H) (K:=K)).comp ρ)
    (fun a b => Spatial.left_right_commute (H:=H) (K:=K) (π a) (ρ b))
lemma tensorRepresentation_tmul (π : R →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : S →⋆ₐ[ℂ] (K →L[ℂ] K))
    (a : R) (b : S) : tensorRepresentation π ρ (MaxTensor.of (a ⊗ₜ[ℂ] b))=Spatial.map (π a) (ρ b) := by
  unfold tensorRepresentation
  erw [MaxTensor.lift_of_tmul]
  change Spatial.map _ 1*Spatial.map 1 _=_
  rw [←Spatial.map_mul,mul_one,one_mul]
  rfl
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B] [PartialOrder A] [StarOrderedRing A]
  [PartialOrder B] [StarOrderedRing B]
variable (τ : State A) (σ : State B)
abbrev productHilbert := Spatial.Hilbert (positive τ).GNS (positive σ).GNS
def productRep : MaxTensor.Algebra A B →⋆ₐ[ℂ] (productHilbert τ σ →L[ℂ] productHilbert τ σ) :=
  tensorRepresentation (positive τ).gnsStarAlgHom (positive σ).gnsStarAlgHom
def productVector : productHilbert τ σ :=
  (((Representations.gnsVector (positive τ) 1) ⊗ₜ[ℂ] (Representations.gnsVector (positive σ) 1) :
    (positive τ).GNS ⊗[ℂ] (positive σ).GNS) : Spatial.Hilbert _ _)
lemma unitVector_norm (ρ : State A) : ‖Representations.gnsVector (positive ρ) 1‖=1 := by
  have hsq : ‖Representations.gnsVector (positive ρ) 1‖^2=1 := by
    have he := (inner_self_eq_norm_sq (𝕜:=ℂ) (Representations.gnsVector (positive ρ) 1)).symm
    simpa only [Representations.gnsVector_inner,star_one,one_mul,positive_apply,ρ.one,RCLike.one_re] using he
  nlinarith [norm_nonneg (Representations.gnsVector (positive ρ) 1)]
lemma productVector_norm : ‖productVector τ σ‖=1 := by
  rw [productVector,Completion.norm_coe,TensorProduct.norm_tmul,unitVector_norm,unitVector_norm,one_mul]
def productFunctional : MaxTensor.Algebra A B →L[ℂ] ℂ := by
  letI : PartialOrder (MaxTensor.Algebra A B) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (MaxTensor.Algebra A B) := CStarAlgebra.spectralOrderedRing _
  exact Representations.coefficient (productRep τ σ) (productVector τ σ) 1
lemma productFunctional_apply (x : MaxTensor.Algebra A B) :
    productFunctional τ σ x = ⟪productVector τ σ,productRep τ σ x (productVector τ σ)⟫_ℂ := rfl
lemma productFunctional_tmul (a : A) (b : B) :
    productFunctional τ σ (MaxTensor.of (a ⊗ₜ[ℂ] b))=τ.functional a*σ.functional b := by
  rw [productFunctional_apply]
  have he : productRep τ σ (MaxTensor.of (a ⊗ₜ[ℂ] b)) =
      Spatial.map ((positive τ).gnsStarAlgHom a) ((positive σ).gnsStarAlgHom b) := by
    exact tensorRepresentation_tmul _ _ _ _
  rw [he]
  change ⟪(productVector τ σ : Spatial.Hilbert _ _), _⟫_ℂ=_
  simp only [productVector,Spatial.map_coe,TensorProduct.mapL_tmul,
    Representations.gnsVector_apply,mul_one,Completion.inner_coe,TensorProduct.inner_tmul,
    Representations.gnsVector_inner,star_one,one_mul,positive_apply]
lemma productFunctional_bound (x : MaxTensor.Algebra A B) : ‖productFunctional τ σ x‖≤‖x‖ := by
  rw [productFunctional_apply]
  calc
    _ ≤ ‖productVector τ σ‖*‖productRep τ σ x (productVector τ σ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖productVector τ σ‖*(‖x‖*‖productVector τ σ‖) :=
      mul_le_mul_of_nonneg_left
        (((productRep τ σ x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le (productRep τ σ) x) (norm_nonneg _)))
        (norm_nonneg _)
    _ = _ := by rw [productVector_norm,one_mul,mul_one]
lemma productFunctional_one : productFunctional τ σ 1=1 := by
  have he := productFunctional_tmul τ σ 1 1
  change productFunctional τ σ
    (MaxTensor.of (MaxTensor.rawEquiv ((1 : A) ⊗ₜ[ℂ] (1 : B)))) =
      τ.functional 1 * σ.functional 1 at he
  rw [←_root_.Algebra.TensorProduct.one_def,map_one,τ.one,σ.one,one_mul] at he
  rw [map_one] at he
  exact he
lemma productFunctional_trace (x y : MaxTensor.Algebra A B) :
    productFunctional τ σ (x*y)=productFunctional τ σ (y*x) := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
    suffices ∀ tensor : A ⊗[ℂ] B,
        productFunctional τ σ (MaxTensor.of (MaxTensor.rawEquiv tensor) * y) =
          productFunctional τ σ (y * MaxTensor.of (MaxTensor.rawEquiv tensor))
      from this (MaxTensor.rawEquiv.symm x)
    intro tensor
    induction tensor using TensorProduct.inductionOn with
    | add x z hx hz => simp only [map_add,add_mul,mul_add,hx,hz]
    | tmul a b =>
      induction y using Completion.induction_on with
      | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
      | ih y =>
        suffices ∀ tensor : A ⊗[ℂ] B,
            productFunctional τ σ
              (MaxTensor.of (MaxTensor.rawEquiv (a ⊗ₜ[ℂ] b)) *
                MaxTensor.of (MaxTensor.rawEquiv tensor)) =
              productFunctional τ σ
                (MaxTensor.of (MaxTensor.rawEquiv tensor) *
                  MaxTensor.of (MaxTensor.rawEquiv (a ⊗ₜ[ℂ] b)))
          from this (MaxTensor.rawEquiv.symm y)
        intro tensor
        induction tensor using TensorProduct.inductionOn with
        | add y z hy hz => simp only [map_add,add_mul,mul_add,hy,hz]
        | tmul c d =>
          rw [←map_mul MaxTensor.of,←map_mul MaxTensor.of,
            ←map_mul MaxTensor.rawEquiv,←map_mul MaxTensor.rawEquiv,
            _root_.Algebra.TensorProduct.tmul_mul_tmul,_root_.Algebra.TensorProduct.tmul_mul_tmul]
          change productFunctional τ σ (MaxTensor.of ((a * c) ⊗ₜ[ℂ] (b * d))) =
            productFunctional τ σ (MaxTensor.of ((c * a) ⊗ₜ[ℂ] (d * b)))
          rw [productFunctional_tmul,productFunctional_tmul,τ.trace a c,σ.trace b d]
def product : State (MaxTensor.Algebra A B) where
  functional := productFunctional τ σ
  norm_le := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa using productFunctional_bound τ σ x)
  one := productFunctional_one τ σ
  trace := productFunctional_trace τ σ
lemma product_left (a : A) : (product τ σ).functional (MaxTensor.includeLeft a)=τ.functional a := by
  change productFunctional τ σ (MaxTensor.of (a ⊗ₜ[ℂ] (1:B)))=τ.functional a
  rw [productFunctional_tmul,σ.one,mul_one]
lemma product_right (b : B) : (product τ σ).functional (MaxTensor.includeRight b)=σ.functional b := by
  change productFunctional τ σ (MaxTensor.of ((1:A) ⊗ₜ[ℂ] b))=σ.functional b
  rw [productFunctional_tmul,τ.one,one_mul]
end KirchbergRordam.Traces
namespace KirchbergRordam.Traces
open Filter Topology
@[ext] lemma State.ext {A : Type*} [CStarAlgebra A] {τ σ : State A}
    (h : τ.functional=σ.functional) : τ=σ := by
  cases τ
  cases σ
  cases h
  rfl
variable {D : Type*} [CStarAlgebra D] [Nontrivial D]

theorem unique_of_halfFlip (h : TensorHalfFlip.HalfFlip D) (τ σ : State D) : τ=σ := by
  let : PartialOrder D := CStarAlgebra.spectralOrder _
  let : StarOrderedRing D := CStarAlgebra.spectralOrderedRing _
  obtain ⟨u,hu⟩ := h
  apply State.ext
  ext a
  have ht := ((product τ σ).functional.continuous.tendsto _).comp (hu a)
  have he (n : ℕ) : (product τ σ).functional (TensorHalfFlip.conj (u n) (MaxTensor.includeLeft a))=
      τ.functional a := by
    rw [conjugation,product_left]
  simp only [Function.comp_def,he,product_right] at ht
  exact tendsto_nhds_unique tendsto_const_nhds ht
end KirchbergRordam.Traces
namespace KirchbergRordam.BalancedDropLimit
open Traces
open scoped CStarAlgebra ComplexOrder


def stageTrace (n : ℕ) : Traces.State (Stage n) :=
  Traces.pullback (Traces.matrixState (Fin (BalancedDropMultiplicity.stage n) × Fin (BalancedDropMultiplicity.stage n+1)))
    (PrimeDimensionDrop.evaluation (BalancedDropMultiplicity.stage n) (BalancedDropMultiplicity.stage n+1) 0)
theorem trace_exists : Nonempty (Traces.State Algebra) :=
  Traces.exists_inductive_trace system stageTrace
theorem trace_unique (τ σ : Traces.State Algebra) : τ=σ :=
  Traces.unique_of_halfFlip BalancedDropHalfFlip.exists_half_flip τ σ


@[instance_reducible] def uniqueTrace : Unique (Traces.State Algebra) where
  default := Classical.choice trace_exists
  uniq τ := trace_unique τ (Classical.choice trace_exists)
end KirchbergRordam.BalancedDropLimit
end

end OAI
