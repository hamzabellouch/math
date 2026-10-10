import Mathlib

namespace OAI

section
universe u v w

noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End

namespace NuclearUltrapower

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The conjugate Hilbert space realized as the strong dual. Its norm is the
existing dual norm, not a new norm on the same space. -/
instance strongDualInner : InnerProductSpace ℂ (StrongDual ℂ K) where
  inner f g := ⟪(InnerProductSpace.toDual ℂ K).symm g,
    (InnerProductSpace.toDual ℂ K).symm f⟫_ℂ
  norm_sq_eq_re_inner f := by
    rw [← norm_sq_eq_re_inner, (InnerProductSpace.toDual ℂ K).symm.norm_map]
  conj_inner_symm f g := inner_conj_symm _ _
  add_left f g h := by simp only [map_add, inner_add_right]
  smul_left f g r := by simp only [map_smulₛₗ, inner_smul_right]

@[simp] theorem dual_inner_toDual (x : K) (f : StrongDual ℂ K) :
    ⟪InnerProductSpace.toDual ℂ K x, f⟫_ℂ = f x := by
  change ⟪(InnerProductSpace.toDual ℂ K).symm f,
    (InnerProductSpace.toDual ℂ K).symm (InnerProductSpace.toDual ℂ K x)⟫_ℂ = f x
  simp

/-- Algebraic finite-rank operators represented by Hilbert tensors. -/
def tensorOperator : K ⊗[ℂ] StrongDual ℂ K →ₗ[ℂ] (K →L[ℂ] K) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => f.smulRight x
          map_add' := by intro f g; ext v; simp [add_smul]
          map_smul' := by intro c f; ext v; simp [mul_smul] }
      map_add' := by intro x y; ext f v; simp [smul_add]
      map_smul' := by intro c x; ext f v; simp [smul_smul, mul_comm] }

omit [CompleteSpace K] in
@[simp] theorem tensorOperator_tmul (x : K) (f : StrongDual ℂ K) (v : K) :
    tensorOperator (x ⊗ₜ[ℂ] f) v = f v • x := rfl

/-- Matrix coefficient identity, valid without any countability restriction. -/
theorem tensorOperator_inner (z : K ⊗[ℂ] StrongDual ℂ K) (v y : K) :
    ⟪y, tensorOperator z v⟫_ℂ = ⟪y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v, z⟫_ℂ := by
  induction z using TensorProduct.inductionOn with
  | tmul x f => simp [mul_comm]
  | add z w hz hw =>
      simp only [map_add, add_apply, inner_add_right, hz, hw]
      simp [TensorProduct.inner_def]

/-- The operator norm is bounded by the Hilbert tensor (Hilbert--Schmidt) norm. -/
theorem tensorOperator_norm_le (z : K ⊗[ℂ] StrongDual ℂ K) :
    ‖tensorOperator z‖ ≤ ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have h := norm_inner_le_norm (𝕜 := ℂ)
    (tensorOperator z v ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v) z
  rw [← tensorOperator_inner, inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm,
    TensorProduct.norm_tmul, LinearIsometryEquiv.norm_map] at h
  by_cases hn : ‖tensorOperator z v‖ = 0
  · rw [hn]; positivity
  · have hp : 0 < ‖tensorOperator z v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    apply (mul_le_mul_iff_right₀ hp).mp
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using h

-- A shortcut for instance synthesis through the tensor's core norm.
instance tensorBoundedSMul : IsBoundedSMul ℂ (K ⊗[ℂ] StrongDual ℂ K) :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)

/-- Hilbert--Schmidt vectors, with the actual tensor Hilbert norm. -/
abbrev HilbertSchmidt (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] := UniformSpace.Completion (K ⊗[ℂ] StrongDual ℂ K)

def tensorOperatorL : K ⊗[ℂ] StrongDual ℂ K →L[ℂ] (K →L[ℂ] K) := by
  refine LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := K ⊗[ℂ] StrongDual ℂ K) (F := K →L[ℂ] K)
    (tensorOperator (K := K)) 1 ?_
  intro z
  change ‖tensorOperator z‖ ≤ 1 * ‖z‖
  rw [one_mul]
  exact tensorOperator_norm_le (K := K) z

/-- Faithful operator realization of the Hilbert--Schmidt completion. -/
def hsOperator : HilbertSchmidt K →L[ℂ] (K →L[ℂ] K) :=
  (tensorOperatorL (K := K)).extend UniformSpace.Completion.toComplL

@[simp] theorem hsOperator_coe (z : K ⊗[ℂ] StrongDual ℂ K) :
    hsOperator (z : HilbertSchmidt K) = tensorOperator z := by
  exact ContinuousLinearMap.extend_eq (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := K ⊗[ℂ] StrongDual ℂ K) (Eₗ := HilbertSchmidt K) (F := K →L[ℂ] K)
    (tensorOperatorL (K := K))
    (e := UniformSpace.Completion.toComplL) UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) z

@[simp] theorem hsOperator_tmul (x v : K) (f : StrongDual ℂ K) :
    hsOperator ((x ⊗ₜ[ℂ] f : K ⊗[ℂ] StrongDual ℂ K) : HilbertSchmidt K) v = f v • x := by
  rw [hsOperator_coe, tensorOperator_tmul]

/-- All Hilbert--Schmidt operators are compact, without a separability assumption. -/
theorem hsOperator_compact (z : HilbertSchmidt K) : IsCompactOperator (hsOperator z) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_setOfPred_isCompactOperator.preimage hsOperator.continuous
  | ih z =>
      rw [hsOperator_coe]
      induction z using TensorProduct.inductionOn with
      | tmul x f =>
          change IsCompactOperator (f.smulRight x)
          exact (isCompactOperator_of_locallyCompactSpace_dom f).clm_comp
            (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) x)
      | add z w hz hw =>
          rw [map_add]
          change IsCompactOperator (fun x => tensorOperator z x + tensorOperator w x)
          exact hz.add hw

/-- Matrix coefficients of the completed operator realization. -/
theorem hsOperator_inner (z : HilbertSchmidt K) (v y : K) :
    ⟪y, hsOperator z v⟫_ℂ =
      ⟪((y ⊗ₜ[ℂ] InnerProductSpace.toDual ℂ K v : K ⊗[ℂ] StrongDual ℂ K) :
        HilbertSchmidt K), z⟫_ℂ := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact continuous_const.inner (𝕜 := ℂ) ((hsOperator (K := K)).continuous.clm_apply continuous_const)
      · exact continuous_const.inner (𝕜 := ℂ) (g := fun z : HilbertSchmidt K => z) continuous_id
  | ih z =>
      rw [hsOperator_coe, UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)]
      exact tensorOperator_inner z v y

/-- The operator realization loses no Hilbert--Schmidt vector. -/
theorem hsOperator_injective : Function.Injective (hsOperator (K := K)) := by
  apply (hsOperator (K := K)).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change hsOperator z = 0 at hz
  have hp (x : K) (f : StrongDual ℂ K) :
      ⟪((x ⊗ₜ[ℂ] f : K ⊗[ℂ] StrongDual ℂ K) : HilbertSchmidt K), z⟫_ℂ = 0 := by
    obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ K).surjective f
    rw [← hsOperator_inner, hz, zero_apply, inner_zero_right]
  have ha (w : K ⊗[ℂ] StrongDual ℂ K) :
      ⟪(w : HilbertSchmidt K), z⟫_ℂ = 0 := by
    induction w using TensorProduct.inductionOn with
    | tmul x f => exact hp x f
    | add x y hx hy =>
        rw [UniformSpace.Completion.coe_add, inner_add_left (𝕜 := ℂ) (E := HilbertSchmidt K), hx, hy, add_zero]
  have hall (w : HilbertSchmidt K) : ⟪w, z⟫_ℂ = 0 := by
    induction w using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (continuous_id.inner (𝕜 := ℂ) (E := HilbertSchmidt K)
        (g := fun _ : HilbertSchmidt K => z) continuous_const) continuous_const
    | ih w => exact ha w
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hall z)

/-- The conjugate (contragredient) unitary on the strong dual. -/
def dualUnitary (u : K ≃ₗᵢ[ℂ] K) : StrongDual ℂ K ≃ₗᵢ[ℂ] StrongDual ℂ K :=
  ((InnerProductSpace.toDual ℂ K).symm.trans u).trans (InnerProductSpace.toDual ℂ K)

@[simp] theorem dualUnitary_toDual (u : K ≃ₗᵢ[ℂ] K) (v : K) :
    dualUnitary u (InnerProductSpace.toDual ℂ K v) = InnerProductSpace.toDual ℂ K (u v) := by
  simp [dualUnitary]

@[simp] theorem dualUnitary_apply (u : K ≃ₗᵢ[ℂ] K) (f : StrongDual ℂ K) (v : K) :
    dualUnitary u f v = f (u.symm v) := by
  obtain ⟨x, rfl⟩ := (InnerProductSpace.toDual ℂ K).surjective f
  rw [dualUnitary_toDual]
  change ⟪u x, v⟫_ℂ = ⟪x, u.symm v⟫_ℂ
  exact u.inner_map_eq_flip x v

/-- Extension of a linear isometry equivalence to metric completions. -/
def completionUnitary {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : E ≃ₗᵢ[ℂ] F) :
    UniformSpace.Completion E ≃ₗᵢ[ℂ] UniformSpace.Completion F :=
  u.toLinearEquiv.extendOfIsometry
    UniformSpace.Completion.toComplₗᵢ.toLinearMap UniformSpace.Completion.toComplₗᵢ.toLinearMap
    UniformSpace.Completion.denseRange_coe UniformSpace.Completion.denseRange_coe
    (fun x => by simp)

@[simp] theorem completionUnitary_coe {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (u : E ≃ₗᵢ[ℂ] F) (x : E) :
    completionUnitary u (x : UniformSpace.Completion E) = (u x : UniformSpace.Completion F) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- Conjugation is unitary for the Hilbert--Schmidt norm. -/
def hsConjugation (u : K ≃ₗᵢ[ℂ] K) : HilbertSchmidt K ≃ₗᵢ[ℂ] HilbertSchmidt K :=
  completionUnitary (E := K ⊗[ℂ] StrongDual ℂ K) (F := K ⊗[ℂ] StrongDual ℂ K)
    (TensorProduct.congrIsometry u (dualUnitary u))

@[simp] theorem hsConjugation_coe (u : K ≃ₗᵢ[ℂ] K) (z : K ⊗[ℂ] StrongDual ℂ K) :
    hsConjugation u (z : HilbertSchmidt K) =
      ((TensorProduct.congrIsometry u (dualUnitary u) z : K ⊗[ℂ] StrongDual ℂ K) :
        HilbertSchmidt K) := completionUnitary_coe _ z

/-- The tensor unitary acts by actual operator conjugation. -/
theorem hsOperator_conjugation (u : K ≃ₗᵢ[ℂ] K) (z : HilbertSchmidt K) :
    hsOperator (hsConjugation u z) =
      (u : K →L[ℂ] K) * hsOperator z * (u.symm : K →L[ℂ] K) := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (hsOperator (K := K)).continuous.comp (hsConjugation u).continuous
      · exact (continuous_const.mul (hsOperator (K := K)).continuous).mul continuous_const
  | ih z =>
      rw [hsConjugation_coe, hsOperator_coe, hsOperator_coe]
      induction z using TensorProduct.inductionOn with
      | tmul x f => ext v; simp
      | add x y hx hy => simp only [map_add, hx, hy, mul_add, add_mul]

variable {Γ : Type*} [Group Γ]

/-- The absence of nonzero finite-dimensional subrepresentations, without separability. -/
def HasNoFiniteDimensionalSubrep (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) : Prop :=
  ∀ W : Submodule ℂ K, W ≠ ⊥ →
    (∀ g : Γ, ∀ ξ ∈ W, σ g ξ ∈ W) → ¬ FiniteDimensional ℂ W

/-- The compact-operator obstruction used in the tensor-norm formulation.
This is the selfadjoint case; no dimension bound and no separability are used. -/
theorem compact_selfadjoint_commuting_eq_zero
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (T : K →L[ℂ] K) (hT : IsCompactOperator T) (hsym : T.IsSymmetric)
    (hcomm : ∀ g x, T (σ g x) = σ g (T x)) : T = 0 := by
  apply (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hT hsym).mp
  intro μ hμ
  by_contra hμ0
  have hfd := ContinuousLinearMap.finite_dimensional_eigenspace hT μ hμ0
  apply hσ (eigenspace T.toLinearMap μ) hμ ?_ hfd
  intro g x hx
  rw [mem_eigenspace_iff] at hx ⊢
  change T (σ g x) = μ • σ g x
  rw [hcomm, show T x = μ • x from hx, map_smul]

/-- Every compact operator in the commutant vanishes, not just selfadjoint ones.
This discharges the compact-operator part of lem:weak-mixing-bound. -/
theorem compact_commuting_eq_zero
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (T : K →L[ℂ] K) (hT : IsCompactOperator T)
    (hcomm : ∀ g x, T (σ g x) = σ g (T x)) : T = 0 := by
  have hc (g : Γ) : Commute T (σ g : K →L[ℂ] K) := by
    ext x
    exact hcomm g x
  have hcs (g : Γ) : Commute (star T) (σ g : K →L[ℂ] K) := by
    have h := (hc g⁻¹).star_star
    have he : (σ g⁻¹ : K →L[ℂ] K) = star (σ g : K →L[ℂ] K) := by
      simp only [map_inv, LinearIsometryEquiv.star_eq_symm, LinearIsometryEquiv.inv_def]
    simpa only [he, star_star] using h
  have hz : star T * T = 0 := by
    apply compact_selfadjoint_commuting_eq_zero σ hσ (star T * T)
      (hT.clm_comp (star T)) (IsSelfAdjoint.star_mul_self T).isSymmetric
    intro g x
    exact congrArg (fun f : K →L[ℂ] K => f x) ((hcs g).mul_left (hc g)).eq
  apply norm_eq_zero.mp
  have hn : ‖T‖ * ‖T‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, hz, norm_zero]
  exact mul_self_eq_zero.mp hn

@[simp] theorem hsConjugation_one : hsConjugation (1 : K ≃ₗᵢ[ℂ] K) = 1 := by
  ext z
  apply hsOperator_injective
  rw [hsOperator_conjugation]
  change (1 : K →L[ℂ] K) * hsOperator z * 1 = hsOperator z
  simp

@[simp] theorem hsConjugation_mul (u v : K ≃ₗᵢ[ℂ] K) :
    hsConjugation (u * v) = hsConjugation u * hsConjugation v := by
  ext z
  apply hsOperator_injective
  simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hsOperator_conjugation]
  change (u : K →L[ℂ] K) * (v : K →L[ℂ] K) * hsOperator z *
      ((v.symm : K →L[ℂ] K) * (u.symm : K →L[ℂ] K)) = _
  simp only [mul_assoc]

/-- The conjugation representation on all Hilbert--Schmidt operators. -/
def hsRepresentation (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) :
    Γ →* (HilbertSchmidt K ≃ₗᵢ[ℂ] HilbertSchmidt K) where
  toFun g := hsConjugation (σ g)
  map_one' := by rw [map_one, hsConjugation_one]
  map_mul' g h := by rw [map_mul, hsConjugation_mul]

/-- Weak mixing excludes every invariant Hilbert--Schmidt vector, with no
separability assumption. This is the invariant-vector step of the source bound. -/
theorem hsRepresentation_no_invariants (σ : Γ →* (K ≃ₗᵢ[ℂ] K))
    (hσ : HasNoFiniteDimensionalSubrep σ) (z : HilbertSchmidt K)
    (hz : ∀ g, hsRepresentation σ g z = z) : z = 0 := by
  apply hsOperator_injective
  rw [map_zero]
  apply compact_commuting_eq_zero σ hσ _ (hsOperator_compact z)
  intro g x
  have hc := congrArg (fun z : HilbertSchmidt K => hsOperator z (σ g x)) (hz g)
  change hsOperator (hsConjugation (σ g) z) (σ g x) = hsOperator z (σ g x) at hc
  rw [hsOperator_conjugation] at hc
  simpa using hc.symm

end NuclearUltrapower

noncomputable section
open scoped CStarAlgebra

namespace NuclearUltrapower

variable {A : Type*} [CStarAlgebra A] [PartialOrder A]

/-- A finite positive trace. This definition is used only for the finite-rank
part of the Powers--Størmer argument; no trace is assumed in the main theorem. -/
structure PositiveTrace (A : Type*) [CStarAlgebra A] [PartialOrder A] where
  toLinearMap : A →ₗ[ℝ] ℝ
  nonneg : ∀ a : A, 0 ≤ a → 0 ≤ toLinearMap a
  cyclic : ∀ a b : A, toLinearMap (a * b) = toLinearMap (b * a)

namespace PositiveTrace

instance : CoeFun (PositiveTrace A) (fun _ => A → ℝ) := ⟨fun τ => τ.toLinearMap⟩

@[simp] theorem map_add (τ : PositiveTrace A) (a b : A) :
    τ (a + b) = τ a + τ b := τ.toLinearMap.map_add a b
@[simp] theorem map_sub (τ : PositiveTrace A) (a b : A) :
    τ (a - b) = τ a - τ b := τ.toLinearMap.map_sub a b
@[simp] theorem map_zero (τ : PositiveTrace A) : τ 0 = 0 := τ.toLinearMap.map_zero

variable [StarOrderedRing A]

/-- Positivity of the trace pairing does not require the factors to commute. -/
theorem mul_nonneg (τ : PositiveTrace A) {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ τ (a * b) := by
  have hs : IsSelfAdjoint (CFC.sqrt a) := (CFC.sqrt_nonneg a).isSelfAdjoint
  have hp : 0 ≤ CFC.sqrt a * b * CFC.sqrt a := by
    exact hs.conjugate_nonneg hb
  have he : τ (a * b) = τ (CFC.sqrt a * b * CFC.sqrt a) := by
    calc
      τ (a * b) = τ ((CFC.sqrt a * CFC.sqrt a) * b) := by
        rw [CFC.sqrt_mul_sqrt_self a ha]
      _ = τ (CFC.sqrt a * (CFC.sqrt a * b)) := by rw [mul_assoc]
      _ = τ ((CFC.sqrt a * b) * CFC.sqrt a) := τ.cyclic _ _
  rw [he]
  exact τ.nonneg _ hp

/-- Pairing a selfadjoint contraction with an element is bounded by its trace
absolute value. This is the elementary dual trace-norm estimate needed below. -/
theorem contraction_pair_le_abs (τ : PositiveTrace A) {j d : A}
    (hjlo : -1 ≤ j) (hjhi : j ≤ 1) (hd : IsSelfAdjoint d) :
    τ (j * d) ≤ τ (CFC.abs d) := by
  have h₁ := τ.mul_nonneg (sub_nonneg.mpr hjhi) (CFC.posPart_nonneg d)
  have h₂ := τ.mul_nonneg (neg_le_iff_add_nonneg.mp hjlo) (CFC.negPart_nonneg d)
  rw [sub_mul, one_mul, map_sub] at h₁
  rw [add_mul, one_mul, map_add] at h₂
  calc
    τ (j * d) = τ (j * (posPart d - negPart d)) := by
      rw [CFC.posPart_sub_negPart d hd]
    _ = τ (j * posPart d) - τ (j * negPart d) := by rw [mul_sub, map_sub]
    _ ≤ τ (posPart d) + τ (negPart d) := by linarith
    _ = τ (CFC.abs d) := by rw [← map_add, CFC.posPart_add_negPart d hd]

/-- The lower estimate in the Powers--Størmer argument. -/
theorem square_sub_le_abs_pair (τ : PositiveTrace A) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    τ ((x - y) * (x - y)) ≤ τ (CFC.abs (x - y) * (x + y)) := by
  let f := x - y
  have hf : IsSelfAdjoint f := hx.isSelfAdjoint.sub hy.isSelfAdjoint
  have h₁ := τ.mul_nonneg (CFC.posPart_nonneg f)
    (show 0 ≤ x + y - f by dsimp [f]; convert add_nonneg hy hy using 1; abel)
  have h₂ := τ.mul_nonneg (CFC.negPart_nonneg f)
    (show 0 ≤ x + y + f by dsimp [f]; convert add_nonneg hx hx using 1; abel)
  rw [mul_sub, map_sub] at h₁
  rw [mul_add, map_add] at h₂
  calc
    τ (f * f) = τ ((posPart f - negPart f) * f) := by
      rw [CFC.posPart_sub_negPart f hf]
    _ = τ (posPart f * f) - τ (negPart f * f) := by rw [sub_mul, map_sub]
    _ ≤ τ (posPart f * (x + y)) + τ (negPart f * (x + y)) := by linarith
    _ = τ (CFC.abs f * (x + y)) := by
      rw [← map_add, ← add_mul, CFC.posPart_add_negPart f hf]

/-- The finite-spectrum sign of a selfadjoint element. -/
theorem exists_sign_of_finite_spectrum {f : A} (hf : IsSelfAdjoint f)
    (hs : (spectrum ℝ f).Finite) :
    ∃ j : A, -1 ≤ j ∧ j ≤ 1 ∧ j * f = CFC.abs f ∧ f * j = CFC.abs f ∧ ‖j‖ ≤ 1 := by
  have hc : ContinuousOn Real.sign (spectrum ℝ f) := hs.continuousOn _
  refine ⟨cfc Real.sign f, ?_, ?_, ?_, ?_, ?_⟩
  · have h : cfc (fun _ : ℝ => -1) f ≤ cfc Real.sign f := by
      apply (cfc_le_iff _ _ _ continuous_const.continuousOn hc hf).mpr
      intro r hr
      rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num
    simpa [cfc_const _ _ hf] using h
  · have h : cfc Real.sign f ≤ cfc (fun _ : ℝ => 1) f := by
      apply (cfc_le_iff _ _ _ hc continuous_const.continuousOn hf).mpr
      intro r hr
      rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num
    simpa [cfc_const _ _ hf] using h
  · conv_lhs => arg 2; rw [← cfc_id ℝ f hf]
    rw [← cfc_mul Real.sign id f hc continuous_id.continuousOn,
      CFC.abs_eq_cfc_norm f hf]
    apply cfc_congr
    intro r hr
    obtain hn | rfl | hp := lt_trichotomy r 0
    · simp [Real.sign_of_neg hn, Real.norm_eq_abs, abs_of_neg hn]
    · simp
    · simp [Real.sign_of_pos hp, Real.norm_eq_abs, abs_of_pos hp]
  · conv_lhs => arg 1; rw [← cfc_id ℝ f hf]
    rw [← cfc_mul id Real.sign f continuous_id.continuousOn hc,
      CFC.abs_eq_cfc_norm f hf]
    apply cfc_congr
    intro r hr
    obtain hn | rfl | hp := lt_trichotomy r 0
    · simp [Real.sign_of_neg hn, Real.norm_eq_abs, abs_of_neg hn]
    · simp
    · simp [Real.sign_of_pos hp, Real.norm_eq_abs, abs_of_pos hp]

  · apply norm_cfc_le zero_le_one
    intro r hr
    rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

/-- Powers--Størmer for a finite positive trace and a finite-spectrum difference.
This is the finite-rank analytic core, not yet the Hilbert--Schmidt theorem. -/
theorem powers_stormer_finite_spectrum (τ : PositiveTrace A) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hfinite : (spectrum ℝ (x - y)).Finite) :
    τ ((x - y) * (x - y)) ≤ τ (CFC.abs (x * x - y * y)) := by
  have hf : IsSelfAdjoint (x - y) := hx.isSelfAdjoint.sub hy.isSelfAdjoint
  obtain ⟨j, hjlo, hjhi, hjf, hfj, _hnj⟩ := exists_sign_of_finite_spectrum hf hfinite
  have hd : IsSelfAdjoint (x * x - y * y) := by
    change star (x * x - y * y) = x * x - y * y
    simp only [star_sub, star_mul, hx.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq]
  have he : τ (j * (x * x - y * y)) = τ (CFC.abs (x - y) * (x + y)) := by
    have hd' : x * x - y * y = (x - y) * x + y * (x - y) := by noncomm_ring
    rw [hd', mul_add, map_add]
    have hcy : τ (j * (y * (x - y))) = τ (CFC.abs (x - y) * y) := by
      rw [← mul_assoc, τ.cyclic (j * y) (x - y), ← mul_assoc, hfj]
    rw [hcy, ← mul_assoc j (x - y) x, hjf, ← map_add, ← mul_add]
  exact (τ.square_sub_le_abs_pair hx hy).trans
    (he ▸ τ.contraction_pair_le_abs hjlo hjhi hd)

end PositiveTrace
end NuclearUltrapower

namespace NuclearUltrapower
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

/-- The ordinary (unnormalized) matrix trace, restricted to its real part. -/
def matrixPositiveTrace (n : Type*) [Fintype n] [DecidableEq n] :
    PositiveTrace (Matrix n n ℂ) where
  toLinearMap := Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)
  nonneg _a ha := (Complex.nonneg_iff.mp (Matrix.nonneg_iff_posSemidef.mp ha).trace_nonneg).1
  cyclic a b := congrArg Complex.re (Matrix.trace_mul_comm a b)

/-- Matrix form of the square-root trace inequality, in every size. -/
theorem matrix_powers_stormer {n : Type*} [Fintype n] [DecidableEq n]
    {x y : Matrix n n ℂ} (hx : x.PosSemidef) (hy : y.PosSemidef) :
    (Matrix.trace ((x - y) * (x - y))).re ≤
      (Matrix.trace (CFC.abs (x * x - y * y))).re :=
  (matrixPositiveTrace n).powers_stormer_finite_spectrum hx.nonneg hy.nonneg
    Matrix.finite_real_spectrum

end NuclearUltrapower

namespace NuclearUltrapower
open scoped TensorProduct InnerProductSpace ComplexOrder
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The finite-dimensional Hilbert tensor representing an operator. -/
def finiteOperatorTensor [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    K ⊗[ℂ] StrongDual ℂ K :=
  ∑ i, T (stdOrthonormalBasis ℂ K i) ⊗ₜ[ℂ]
    InnerProductSpace.toDual ℂ K (stdOrthonormalBasis ℂ K i)

@[simp] theorem tensorOperator_finiteOperatorTensor [FiniteDimensional ℂ K]
    (T : K →L[ℂ] K) : tensorOperator (finiteOperatorTensor T) = T := by
  classical
  ext x
  simp only [finiteOperatorTensor, map_sum, sum_apply, tensorOperator_tmul,
    InnerProductSpace.toDual_apply_apply]
  simpa only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] using
    congrArg T ((stdOrthonormalBasis ℂ K).sum_repr x)

/-- The Hilbert--Schmidt inner product equals the unnormalized operator trace. -/
theorem finiteOperatorTensor_inner [FiniteDimensional ℂ K]
    (T U : K →L[ℂ] K) :
    ⟪finiteOperatorTensor T, finiteOperatorTensor U⟫_ℂ =
      LinearMap.trace ℂ K ((star T * U).toLinearMap) := by
  classical
  rw [finiteOperatorTensor, sum_inner (𝕜 := ℂ) (E := K ⊗[ℂ] StrongDual ℂ K)]
  simp_rw [← tensorOperator_inner, tensorOperator_finiteOperatorTensor]
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ K)]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ContinuousLinearMap.adjoint_inner_right T _ _).symm

/-- All finite-dimensional operators have their actual Hilbert--Schmidt norm. -/
theorem finiteOperatorTensor_norm_sq [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    ‖finiteOperatorTensor T‖ ^ 2 =
      (LinearMap.trace ℂ K ((star T * T).toLinearMap)).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (finiteOperatorTensor T), finiteOperatorTensor_inner]
  rfl

/-- The real part of the ordinary trace on finite-dimensional operators. -/
def operatorPositiveTrace [FiniteDimensional ℂ K] : PositiveTrace (K →L[ℂ] K) where
  toLinearMap :=
    { toFun T := (LinearMap.trace ℂ K T.toLinearMap).re
      map_add' := by intro T U; simp
      map_smul' := by intro r T; simp }
  nonneg T hT := (Complex.nonneg_iff.mp
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hT).toLinearMap.trace_nonneg).1
  cyclic T U := congrArg Complex.re (LinearMap.trace_mul_comm ℂ T.toLinearMap U.toLinearMap)

omit [CompleteSpace K] in
/-- Finite-dimensional operator spectra are finite also as real spectra. -/
theorem operator_finite_real_spectrum [FiniteDimensional ℂ K] (T : K →L[ℂ] K) :
    (spectrum ℝ T).Finite := by
  let e : (K →ₗ[ℂ] K) ≃ₐ[ℂ] (K →L[ℂ] K) :=
    { LinearMap.toContinuousLinearMap with
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  rw [← spectrum.preimage_algebraMap ℂ, ← AlgEquiv.spectrum_eq e.symm T]
  exact (Module.End.finite_spectrum T.toLinearMap).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Functorial conjugate Hilbert-space embedding. -/
def dualIsometry (f : F →ₗᵢ[ℂ] K) : StrongDual ℂ F →ₗᵢ[ℂ] StrongDual ℂ K :=
  (InnerProductSpace.toDual ℂ K).toLinearIsometry.comp
    (f.comp (InnerProductSpace.toDual ℂ F).symm.toLinearIsometry)

@[simp] theorem dualIsometry_toDual (f : F →ₗᵢ[ℂ] K) (x : F) :
    dualIsometry f (InnerProductSpace.toDual ℂ F x) = InnerProductSpace.toDual ℂ K (f x) := by
  simp [dualIsometry]
  rfl

/-- Tensorial inclusion of finite-rank operators along a Hilbert-space isometry. -/
def liftOperatorTensor (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F] (T : F →L[ℂ] F) :
    K ⊗[ℂ] StrongDual ℂ K :=
  TensorProduct.mapIsometry f (dualIsometry f) (finiteOperatorTensor T)

@[simp] theorem liftOperatorTensor_norm (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F]
    (T : F →L[ℂ] F) : ‖liftOperatorTensor f T‖ = ‖finiteOperatorTensor T‖ :=
  (TensorProduct.mapIsometry f (dualIsometry f)).norm_map _

/-- This inclusion is the usual compression along an isometric embedding. -/
theorem tensorOperator_liftOperatorTensor (f : F →ₗᵢ[ℂ] K) [FiniteDimensional ℂ F]
    (T : F →L[ℂ] F) :
    tensorOperator (liftOperatorTensor f T) =
      f.toContinuousLinearMap ∘L T ∘L f.toContinuousLinearMap.adjoint := by
  classical
  ext x
  simp only [liftOperatorTensor, finiteOperatorTensor, map_sum,
    TensorProduct.mapIsometry_apply, TensorProduct.map_tmul,
    sum_apply, tensorOperator_tmul]
  change (∑ i, dualIsometry f (InnerProductSpace.toDual ℂ F (stdOrthonormalBasis ℂ F i)) x •
    f (T (stdOrthonormalBasis ℂ F i))) = f (T (f.toContinuousLinearMap.adjoint x))
  simp only [dualIsometry_toDual, InnerProductSpace.toDual_apply_apply]
  have he (v : F) : ⟪f v, x⟫_ℂ = ⟪v, f.toContinuousLinearMap.adjoint x⟫_ℂ :=
    (ContinuousLinearMap.adjoint_inner_right f.toContinuousLinearMap v x).symm
  simp_rw [he]
  change (∑ i, ⟪stdOrthonormalBasis ℂ F i, f.toContinuousLinearMap.adjoint x⟫_ℂ •
    f (T (stdOrthonormalBasis ℂ F i))) = f (T (f.toContinuousLinearMap.adjoint x))
  simpa only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply] using
    congrArg (fun y => f (T y)) ((stdOrthonormalBasis ℂ F).sum_repr
      (f.toContinuousLinearMap.adjoint x))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The rectangular operator associated with an algebraic Hilbert tensor. -/
def crossOperator : E ⊗[ℂ] K →ₗ[ℂ] (StrongDual ℂ E →L[ℂ] K) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => (NormedSpace.inclusionInDoubleDual ℂ E x).smulRight y
          map_add' := by intro y z; ext f; simp [smul_add]
          map_smul' := by intro c y; ext f; simp [smul_smul, mul_comm] }
      map_add' := by intro x y; ext z f; simp [add_smul]
      map_smul' := by intro c x; ext y f; simp [mul_smul] }

omit [CompleteSpace E] [CompleteSpace K] in
@[simp] theorem crossOperator_tmul (x : E) (y : K) (f : StrongDual ℂ E) :
    crossOperator (x ⊗ₜ[ℂ] y) f = f x • y := rfl

omit [CompleteSpace K] in
@[simp] theorem crossOperator_tmul_rankOne (x : E) (y : K) :
    crossOperator (x ⊗ₜ[ℂ] y) =
      InnerProductSpace.rankOne ℂ y (InnerProductSpace.toDual ℂ E x) := by
  ext f
  simp

/-- The finite-rank reduced density; independent of any chosen tensor expansion. -/
def reducedDensity (z : E ⊗[ℂ] K) : K →L[ℂ] K :=
  crossOperator z ∘L (crossOperator z).adjoint

theorem reducedDensity_nonneg (z : E ⊗[ℂ] K) : 0 ≤ reducedDensity z :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (ContinuousLinearMap.isPositive_self_comp_adjoint _)

/-- The polarized partial-trace formula, before completion. -/
theorem trace_crossOperator [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) (C : K →L[ℂ] K) :
    LinearMap.trace ℂ K ((C ∘L crossOperator z ∘L (crossOperator w).adjoint).toLinearMap) =
      ⟪w, TensorProduct.mapL (ContinuousLinearMap.id ℂ E) C z⟫_ℂ := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      induction w using TensorProduct.inductionOn with
      | tmul v t =>
          simp only [crossOperator_tmul_rankOne, InnerProductSpace.adjoint_rankOne,
            InnerProductSpace.comp_rankOne,
            InnerProductSpace.trace_rankOne, TensorProduct.mapL_tmul,
            ContinuousLinearMap.id_apply, TensorProduct.inner_tmul]
          simp only [InnerProductSpace.rankOne_apply, dual_inner_toDual,
            InnerProductSpace.toDual_apply_apply, map_smul, inner_smul_right]
      | add w₁ w₂ h₁ h₂ =>
          simp only [map_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.toLinearMap_add,
            inner_add_left, h₁, h₂]
  | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp,
        ContinuousLinearMap.toLinearMap_add, inner_add_right, h₁, h₂]

/-- The reduced-density characterization by its trace. -/
theorem trace_reducedDensity [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) (C : K →L[ℂ] K) :
    LinearMap.trace ℂ K ((C * reducedDensity z).toLinearMap) =
      ⟪z, TensorProduct.mapL (ContinuousLinearMap.id ℂ E) C z⟫_ℂ :=
  trace_crossOperator z z C

/-- Conjugation/compression by an isometric Hilbert-space embedding. -/
def operatorLift (f : F →ₗᵢ[ℂ] K) (T : F →L[ℂ] F) : K →L[ℂ] K :=
  f.toContinuousLinearMap ∘L T ∘L f.toContinuousLinearMap.adjoint

@[simp] theorem operatorLift_mul (f : F →ₗᵢ[ℂ] K) (T U : F →L[ℂ] F) :
    operatorLift f (T * U) = operatorLift f T * operatorLift f U := by
  have hf (x : F) : f.toContinuousLinearMap.adjoint (f x) = x :=
    congrArg (fun T : F →L[ℂ] F => T x) f.adjoint_comp_self
  ext x
  change f (T (U (f.toContinuousLinearMap.adjoint x))) =
    f (T (f.toContinuousLinearMap.adjoint (f (U (f.toContinuousLinearMap.adjoint x)))))
  rw [hf]

theorem operatorLift_nonneg (f : F →ₗᵢ[ℂ] K) {T : F →L[ℂ] F} (hT : 0 ≤ T) :
    0 ≤ operatorLift f T :=
  ContinuousLinearMap.nonneg_iff_isPositive.mpr
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hT).conj_adjoint f.toContinuousLinearMap)

@[simp] theorem operatorLift_sqrt (f : F →ₗᵢ[ℂ] K) {T : F →L[ℂ] F} (hT : 0 ≤ T) :
    operatorLift f (CFC.sqrt T) = CFC.sqrt (operatorLift f T) := by
  symm
  apply (CFC.sqrt_eq_iff _ _ (operatorLift_nonneg f hT)
    (operatorLift_nonneg f (CFC.sqrt_nonneg T))).mpr
  rw [← operatorLift_mul, CFC.sqrt_mul_sqrt_self T hT]

variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']

omit [CompleteSpace K] [CompleteSpace F] in
/-- Naturality of the rectangular operator under arbitrary isometric embeddings. -/
theorem crossOperator_mapIsometry (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    crossOperator (TensorProduct.mapIsometry g f z) =
      f.toContinuousLinearMap ∘L crossOperator z ∘L (dualIsometry g).toContinuousLinearMap.adjoint := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
      simp only [TensorProduct.mapIsometry_apply, TensorProduct.map_tmul]
      change crossOperator (g x ⊗ₜ[ℂ] f y) = _
      rw [crossOperator_tmul_rankOne, crossOperator_tmul_rankOne,
        InnerProductSpace.rankOne_comp, ContinuousLinearMap.adjoint_adjoint,
        InnerProductSpace.comp_rankOne]
      change InnerProductSpace.rankOne ℂ (f y) (InnerProductSpace.toDual ℂ E' (g x)) =
        InnerProductSpace.rankOne ℂ (f y) (dualIsometry g (InnerProductSpace.toDual ℂ E x))
      rw [dualIsometry_toDual]
  | add z w hz hw =>
      simp only [map_add, hz, hw, ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]

/-- Partial trace discards an isometry on the first tensor factor. -/
theorem reducedDensity_mapIsometry (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    reducedDensity (TensorProduct.mapIsometry g f z) = operatorLift f (reducedDensity z) := by
  simp only [reducedDensity, crossOperator_mapIsometry, operatorLift,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hg (y : StrongDual ℂ E) :
      (dualIsometry g).toContinuousLinearMap.adjoint (dualIsometry g y) = y :=
    congrArg (fun T : StrongDual ℂ E →L[ℂ] StrongDual ℂ E => T y)
      (dualIsometry g).adjoint_comp_self
  ext x
  change f (crossOperator z ((dualIsometry g).toContinuousLinearMap.adjoint
      (dualIsometry g ((crossOperator z).adjoint (f.toContinuousLinearMap.adjoint x))))) =
    f (crossOperator z ((crossOperator z).adjoint (f.toContinuousLinearMap.adjoint x)))
  rw [hg]

/-- Finite-dimensional density trace equals the vector's squared norm. -/
theorem trace_reducedDensity_self [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) :
    (LinearMap.trace ℂ K (reducedDensity z).toLinearMap).re = ‖z‖ ^ 2 := by
  have h := trace_reducedDensity z (ContinuousLinearMap.id ℂ K)
  rw [show (ContinuousLinearMap.id ℂ K) * reducedDensity z = reducedDensity z from one_mul _,
    TensorProduct.mapL_id_id, ContinuousLinearMap.id_apply] at h
  rw [h]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) z

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Elementary vector-state estimate, valid without separability or completeness. -/
theorem vectorState_difference_le (A : H →L[ℂ] H) (hA : ‖A‖ ≤ 1) (x y : H) :
    (⟪x, A x⟫_ℂ - ⟪y, A y⟫_ℂ).re ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have he : ⟪x, A x⟫_ℂ - ⟪y, A y⟫_ℂ =
      ⟪x - y, A x⟫_ℂ + ⟪y, A (x - y)⟫_ℂ := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hx : ‖A x‖ ≤ ‖x‖ := by
    exact (A.le_opNorm x).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  have hy : ‖A (x - y)‖ ≤ ‖x - y‖ := by
    exact (A.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)
  rw [he, Complex.add_re]
  calc
    (⟪x - y, A x⟫_ℂ).re + (⟪y, A (x - y)⟫_ℂ).re ≤
        ‖⟪x - y, A x⟫_ℂ‖ + ‖⟪y, A (x - y)⟫_ℂ‖ :=
      add_le_add (Complex.re_le_norm _) (Complex.re_le_norm _)
    _ ≤ ‖x - y‖ * ‖A x‖ + ‖y‖ * ‖A (x - y)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
    _ = (‖x‖ + ‖y‖) * ‖x - y‖ := by ring

@[simp] theorem finiteOperatorTensor_sub [FiniteDimensional ℂ K] (T U : K →L[ℂ] K) :
    finiteOperatorTensor (T - U) = finiteOperatorTensor T - finiteOperatorTensor U := by
  classical
  simp only [finiteOperatorTensor, sub_apply, TensorProduct.sub_tmul,
    Finset.sum_sub_distrib]

/-- The trace-norm estimate for reduced density matrices. -/
theorem trace_abs_reducedDensity_sub_le [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) :
    (LinearMap.trace ℂ K (CFC.abs (reducedDensity z - reducedDensity w)).toLinearMap).re ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨j, _hlo, _hhi, hj, _hj', hnj⟩ := PositiveTrace.exists_sign_of_finite_spectrum
    ((reducedDensity_nonneg z).isSelfAdjoint.sub (reducedDensity_nonneg w).isSelfAdjoint)
    (operator_finite_real_spectrum _)
  rw [← hj, mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub,
    trace_reducedDensity, trace_reducedDensity]
  apply vectorState_difference_le
  calc
    ‖TensorProduct.mapL (ContinuousLinearMap.id ℂ E) j‖ ≤
        ‖ContinuousLinearMap.id ℂ E‖ * ‖j‖ := TensorProduct.norm_mapL_le _ _
    _ ≤ 1 * 1 := mul_le_mul ContinuousLinearMap.norm_id_le hnj (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

/-- Finite-dimensional Powers--Størmer in the Hilbert tensor norm. -/
theorem finite_density_root_difference [FiniteDimensional ℂ K] (z w : E ⊗[ℂ] K) :
    ‖finiteOperatorTensor (CFC.sqrt (reducedDensity z)) -
      finiteOperatorTensor (CFC.sqrt (reducedDensity w))‖ ^ 2 ≤
      (‖z‖ + ‖w‖) * ‖z - w‖ := by
  rw [← finiteOperatorTensor_sub, finiteOperatorTensor_norm_sq]
  have hs : star (CFC.sqrt (reducedDensity z) - CFC.sqrt (reducedDensity w)) =
      CFC.sqrt (reducedDensity z) - CFC.sqrt (reducedDensity w) :=
    ((CFC.sqrt_nonneg _).isSelfAdjoint.sub (CFC.sqrt_nonneg _).isSelfAdjoint).star_eq
  rw [hs]
  have h := (operatorPositiveTrace (K := K)).powers_stormer_finite_spectrum
    (CFC.sqrt_nonneg (reducedDensity z)) (CFC.sqrt_nonneg (reducedDensity w))
    (operator_finite_real_spectrum _)
  rw [CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg z),
    CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg w)] at h
  exact h.trans (trace_abs_reducedDensity_sub_le z w)

/-- The root of a finite-rank density has squared Hilbert--Schmidt norm equal
exactly to the vector's squared Hilbert norm. -/
theorem finite_density_root_norm_sq [FiniteDimensional ℂ K] (z : E ⊗[ℂ] K) :
    ‖finiteOperatorTensor (CFC.sqrt (reducedDensity z))‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [finiteOperatorTensor_norm_sq, (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self _ (reducedDensity_nonneg z), trace_reducedDensity_self]

/-- Every algebraic tensor has a genuine Hilbert--Schmidt reduced-density root,
without any dimension or separability assumption on the ambient spaces. -/
theorem exists_density_root (z : E ⊗[ℂ] K) :
    ∃ a : HilbertSchmidt K, hsOperator a = CFC.sqrt (reducedDensity z) ∧ ‖a‖ = ‖z‖ := by
  obtain ⟨F, hF, hFz⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z} : Set (E ⊗[ℂ] K)) (Set.finite_singleton z)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨w, hw⟩ := hFz (Set.mem_singleton z)
  have hm : TensorProduct.mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ w = z := hw
  have hd := reducedDensity_mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ w
  rw [hm] at hd
  let t := liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))
  refine ⟨(t : HilbertSchmidt K), ?_, ?_⟩
  · rw [hsOperator_coe]
    change tensorOperator (liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))) = _
    rw [tensorOperator_liftOperatorTensor]
    change operatorLift F.subtypeₗᵢ (CFC.sqrt (reducedDensity w)) = _
    rw [operatorLift_sqrt F.subtypeₗᵢ (reducedDensity_nonneg w), ← hd]
  · rw [UniformSpace.Completion.norm_coe]
    change ‖liftOperatorTensor F.subtypeₗᵢ (CFC.sqrt (reducedDensity w))‖ = ‖z‖
    rw [liftOperatorTensor_norm]
    have hn : ‖w‖ = ‖z‖ := by
      rw [← hm, (TensorProduct.mapIsometry ((LinearIsometry.id : E →ₗᵢ[ℂ] E)) F.subtypeₗᵢ).norm_map]
    have hs := finite_density_root_norm_sq w
    rw [hn] at hs
    nlinarith [norm_nonneg (finiteOperatorTensor (CFC.sqrt (reducedDensity w))), norm_nonneg z]

/-- The unique Hilbert--Schmidt vector realizing the positive density root. -/
def densityRoot (z : E ⊗[ℂ] K) : HilbertSchmidt K := (exists_density_root z).choose

@[simp] theorem hsOperator_densityRoot (z : E ⊗[ℂ] K) :
    hsOperator (densityRoot z) = CFC.sqrt (reducedDensity z) :=
  (exists_density_root z).choose_spec.1

@[simp] theorem densityRoot_norm (z : E ⊗[ℂ] K) : ‖densityRoot z‖ = ‖z‖ :=
  (exists_density_root z).choose_spec.2

/-- Uniqueness makes the finite-support construction independent of all choices. -/
theorem densityRoot_mapIsometry [FiniteDimensional ℂ F]
    (g : E →ₗᵢ[ℂ] E') (f : F →ₗᵢ[ℂ] K) (z : E ⊗[ℂ] F) :
    densityRoot (TensorProduct.mapIsometry g f z) =
      (liftOperatorTensor f (CFC.sqrt (reducedDensity z)) : HilbertSchmidt K) := by
  apply hsOperator_injective
  rw [hsOperator_densityRoot, hsOperator_coe, tensorOperator_liftOperatorTensor,
    reducedDensity_mapIsometry]
  exact (operatorLift_sqrt f (reducedDensity_nonneg z)).symm

@[simp] theorem liftOperatorTensor_sub [FiniteDimensional ℂ F]
    (f : F →ₗᵢ[ℂ] K) (T U : F →L[ℂ] F) :
    liftOperatorTensor f (T - U) = liftOperatorTensor f T - liftOperatorTensor f U := by
  simp only [liftOperatorTensor, finiteOperatorTensor_sub, map_sub]

/-- The reduced-root estimate holds in arbitrary ambient Hilbert spaces.
Both vectors are compared inside one finite-dimensional support, not separately. -/
theorem densityRoot_difference (z w : E ⊗[ℂ] K) :
    ‖densityRoot z - densityRoot w‖ ^ 2 ≤ (‖z‖ + ‖w‖) * ‖z - w‖ := by
  obtain ⟨F, hF, hFzw⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({z, w} : Set (E ⊗[ℂ] K)) (Set.toFinite _)
  let : FiniteDimensional ℂ F := hF
  obtain ⟨z', hz⟩ := hFzw (by simp : z ∈ ({z, w} : Set (E ⊗[ℂ] K)))
  obtain ⟨w', hw⟩ := hFzw (by simp : w ∈ ({z, w} : Set (E ⊗[ℂ] K)))
  let f := TensorProduct.mapIsometry (LinearIsometry.id : E →ₗᵢ[ℂ] E) F.subtypeₗᵢ
  have hz' : f z' = z := hz
  have hw' : f w' = w := hw
  rw [← hz', ← hw', densityRoot_mapIsometry, densityRoot_mapIsometry,
    ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe,
    ← liftOperatorTensor_sub, liftOperatorTensor_norm, finiteOperatorTensor_sub,
    ← map_sub, f.norm_map, f.norm_map, f.norm_map]
  exact finite_density_root_difference z' w'

/-- Unitary covariance of reduced densities, realized in actual HS space. -/
theorem densityRoot_unitary (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) (z : E ⊗[ℂ] K) :
    densityRoot (TensorProduct.congrIsometry u v z) = hsConjugation v (densityRoot z) := by
  apply hsOperator_injective
  rw [hsOperator_densityRoot, hsOperator_conjugation, hsOperator_densityRoot]
  change CFC.sqrt (reducedDensity (TensorProduct.mapIsometry u.toLinearIsometry
    v.toLinearIsometry z)) = _
  rw [reducedDensity_mapIsometry, ← operatorLift_sqrt _ (reducedDensity_nonneg z)]
  change ((v : K →L[ℂ] K) ∘L CFC.sqrt (reducedDensity z)) ∘L
    (v : K →L[ℂ] K).adjoint = _
  rw [v.adjoint_eq_symm]
  rfl

/-- The exact factor two in the Powers--Størmer inequality. -/
theorem densityRoot_unitary_difference (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K)
    (z : E ⊗[ℂ] K) :
    ‖hsConjugation v (densityRoot z) - densityRoot z‖ ^ 2 ≤
      (2 * ‖z‖) * ‖TensorProduct.congrIsometry u v z - z‖ := by
  rw [← densityRoot_unitary u v z]
  simpa only [(TensorProduct.congrIsometry u v).norm_map, ← two_mul] using
    densityRoot_difference (TensorProduct.congrIsometry u v z) z

/-- Exact standing Kazhdan-gap convention in the tensor-norm formulation. -/
def HasKazhdanGap {Γ : Type u} [Group Γ] (S : Finset Γ) (κ : ℝ) : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)),
    (∀ ξ : H, (∀ g : Γ, ρ g ξ = ξ) → ξ = 0) →
    ∀ ξ : H, κ * ‖ξ‖ ^ 2 ≤ ∑ s ∈ S, ‖ρ s ξ - ξ‖ ^ 2

/-- The full weak-mixing estimate on the dense algebraic tensor product. -/
theorem weak_mixing_bound_algebraic {Γ : Type u} [Group Γ]
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ : 0 < κ)
    (hgap : HasKazhdanGap.{u, v} S κ)
    {K : Type v} {E : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (U : Γ → (E ≃ₗᵢ[ℂ] E)) (z : E ⊗[ℂ] K) :
    κ ^ 2 / (4 * (S.card : ℝ)) * ‖z‖ ^ 2 ≤
      ∑ s ∈ S, ‖TensorProduct.congrIsometry (U s) (σ s) z - z‖ ^ 2 := by
  classical
  let δ : Γ → ℝ := fun s => ‖TensorProduct.congrIsometry (U s) (σ s) z - z‖
  have hδ s : 0 ≤ δ s := norm_nonneg _
  have hs : 0 < (S.card : ℝ) := Nat.cast_pos.mpr hS.card_pos
  have hh := hgap (HilbertSchmidt K) (hsRepresentation σ)
    (hsRepresentation_no_invariants σ hσ) (densityRoot z)
  rw [densityRoot_norm] at hh
  have he : κ * ‖z‖ ^ 2 ≤ (2 * ‖z‖) * ∑ s ∈ S, δ s := by
    refine hh.trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    exact densityRoot_unitary_difference (U s) (σ s) z
  by_cases hz : z = 0
  · subst z
    simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hκn : κ * ‖z‖ ≤ 2 * ∑ s ∈ S, δ s := by
    apply (mul_le_mul_iff_right₀ hn).mp
    nlinarith [he]
  have hsq : (κ * ‖z‖) ^ 2 ≤ (2 * ∑ s ∈ S, δ s) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hκ.le hn.le) hκn 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := δ)
  change κ ^ 2 / (4 * (S.card : ℝ)) * ‖z‖ ^ 2 ≤ ∑ s ∈ S, δ s ^ 2
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos (by norm_num) hs)).mpr
  nlinarith [hsq, hcs]

abbrev HilbertTensor (E K : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  UniformSpace.Completion (E ⊗[ℂ] K)

/-- Exact completed tensor action used in the source uniform spectral bound. -/
def tensorUnitaryAction {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) :
    HilbertTensor E K →L[ℂ] HilbertTensor E K :=
  (TensorProduct.mapL u.toContinuousLinearEquiv.toContinuousLinearMap
    v.toContinuousLinearEquiv.toContinuousLinearMap).completion

@[simp] theorem tensorUnitaryAction_coe {E K : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : E ≃ₗᵢ[ℂ] E) (v : K ≃ₗᵢ[ℂ] K) (z : E ⊗[ℂ] K) :
    tensorUnitaryAction u v (z : HilbertTensor E K) =
      (TensorProduct.congrIsometry u v z : HilbertTensor E K) := by
  rw [tensorUnitaryAction, ContinuousLinearMap.completion_apply_coe]
  simp only [TensorProduct.mapL_apply, TensorProduct.congrIsometry_apply]
  congr 1

/-- Source lem:weak-mixing-bound, for arbitrary (possibly nonseparable)
Hilbert spaces and arbitrary unitaries U_s with no relations imposed. -/
theorem weak_mixing_bound {Γ : Type u} [Group Γ]
    (S : Finset Γ) (κ : ℝ) (hS : S.Nonempty) (hκ : 0 < κ)
    (hgap : HasKazhdanGap.{u, v} S κ)
    {K : Type v} {E : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (σ : Γ →* (K ≃ₗᵢ[ℂ] K)) (hσ : HasNoFiniteDimensionalSubrep σ)
    (U : Γ → (E ≃ₗᵢ[ℂ] E)) (ξ : HilbertTensor E K) :
    κ ^ 2 / (4 * (S.card : ℝ)) * ‖ξ‖ ^ 2 ≤
      ∑ s ∈ S, ‖tensorUnitaryAction (U s) (σ s) ξ - ξ‖ ^ 2 := by
  induction ξ using UniformSpace.Completion.induction_on with
  | hp =>
      apply isClosed_le
      · exact continuous_const.mul (continuous_norm.pow 2)
      · exact continuous_finsetSum S (fun s _ =>
          (((tensorUnitaryAction (U s) (σ s)).continuous.sub continuous_id).norm.pow 2))
  | ih z =>
      simp only [tensorUnitaryAction_coe, ← UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.norm_coe]
      exact weak_mixing_bound_algebraic S κ hS hκ hgap σ hσ U z

end NuclearUltrapower

end
end
end

end OAI
