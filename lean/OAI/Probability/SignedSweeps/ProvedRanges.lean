import OAI.Probability.SignedSweeps.SpectralAngle
import OAI.Probability.SignedSweeps.SparseUniform

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators

lemma weightedMoment_le_one_of_level_zero {d : ℕ} (lam : Partition (2 ^ d))
    (hk : 2 ^ d - lam.1.rowLen 0 = 0) (r : ℕ) : weightedMoment lam r ≤ 1 := by
  have hdim : (spechtDimension lam : ℝ) ≤ 1 := by
    exact_mod_cast (by simpa [hk] using spechtDimension_le_pow_level lam)
  exact (weightedMoment_le_dimension_squared lam r).trans (by
    simpa using pow_le_pow_left₀ (Nat.cast_nonneg (spechtDimension lam)) hdim 2)

theorem sparse_signed_occurrence_moment_bound {δ η : ℝ} (hδ : 0 < δ)
    (hη : 0 ≤ η) (κ : ℝ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2 ^ d),
        ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) →
        ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam →
          logMoment (weightedMoment lam r) ≤
            ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨r₀, hr₀, hbound⟩ := uniform_sparse_moments hδ
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr d hd lam hk u v l h α β γ _occ
  exact moment_bound_of_le_one hd lam r (hbound r hr d lam hk) α β hη κ l

theorem signed_occurrence_moment_bound_proved_ranges (D : ℕ) {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 ≤ η) (κ : ℝ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d : ℕ, 1 ≤ d →
      ∀ lam : Partition (2 ^ d),
        (d ≤ D ∨
          ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) ≤ ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ∨
          2 ^ d - lam.1.rowLen 0 = 1 ∨
          2 ^ d / 2 < lam.1.colLen 0) →
        ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam →
          logMoment (weightedMoment lam r) ≤
            ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨r₀, hr₀, hsparse⟩ := uniform_sparse_moments hδ
  obtain ⟨R, _hR, hfinite⟩ := finite_base_moments D
  refine ⟨max r₀ R, hr₀.trans (le_max_left _ _), ?_⟩
  intro r hr d hd lam hcases u v l h α β γ _occ
  apply moment_bound_of_le_one hd lam r _ α β hη κ l
  have hrpos : 1 ≤ r := hr₀.trans ((le_max_left _ _).trans hr)
  rcases hcases with hsmall | hk | hkone | htall
  · exact hfinite r ((le_max_right _ _).trans hr) d hsmall lam
  · exact hsparse r ((le_max_left _ _).trans hr) d lam hk
  · rw [weightedMoment_eq_zero_of_level_one lam hkone hrpos]
    exact zero_le_one
  · rw [weightedMoment_eq_zero_of_long_column hd lam htall hrpos]
    exact zero_le_one

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

def finiteRegularRepresentation : Representation ℂ G (EuclideanSpace ℂ G) where
  toFun g := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)).toLinearEquiv.toLinearMap
  map_one' := by ext f h; change f (1⁻¹ * h) = f h; simp
  map_mul' := by
    intro g h; ext f k
    change f ((g * h)⁻¹ * k) = f (h⁻¹ * (g⁻¹ * k))
    simp [mul_assoc]

@[simp] lemma finiteRegularRepresentation_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    finiteRegularRepresentation g f h = f (g⁻¹ * h) := rfl

def coefficientAction (ρ : Representation ℂ G E) (f : G → ℂ) : E →ₗ[ℂ] E :=
  ∑ g, f g • ρ g

omit [FiniteDimensional ℂ E] in
@[simp] lemma coefficientAction_apply (ρ : Representation ℂ G E) (f : G → ℂ) (x : E) :
    coefficientAction ρ f x = ∑ g, f g • ρ g x := by
  simp [coefficientAction]

def conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  ∑ g, ρ g * T * ρ g⁻¹

omit [FiniteDimensional ℂ E] in
lemma conjugationSum_intertwines (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E)
    (h : G) (x : E) :
    conjugationSum ρ T (ρ h x) = ρ h (conjugationSum ρ T x) := by
  have he := Equiv.sum_comp (Equiv.mulLeft h) (fun g : G => (ρ g * T * ρ g⁻¹) (ρ h x))
  change (∑ g, (ρ (h * g) * T * ρ (h * g)⁻¹) (ρ h x)) = _ at he
  have hi : ρ h⁻¹ (ρ h x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [conjugationSum, LinearMap.sum_apply, ← he, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, hi]

omit [FiniteDimensional ℂ E] in
lemma trace_conjugationSum (ρ : Representation ℂ G E) (T : E →ₗ[ℂ] E) :
    LinearMap.trace ℂ E (conjugationSum ρ T) =
      (Fintype.card G : ℂ) * LinearMap.trace ℂ E T := by
  simp only [conjugationSum, map_sum]
  have h (g : G) : LinearMap.trace ℂ E (ρ g * T * ρ g⁻¹) = LinearMap.trace ℂ E T := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma conjugationSum_scalar (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (T : E →ₗ[ℂ] E) :
    conjugationSum ρ T =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ) * LinearMap.trace ℂ E T) • 1 := by
  let A : Representation.IntertwiningMap ρ ρ :=
    (conjugationSum ρ T).intertwiningMap_of_isIntertwiningMap ρ ρ
      (conjugationSum_intertwines ρ T)
  obtain ⟨z, hz⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective A
  have he : conjugationSum ρ T = z • (1 : E →ₗ[ℂ] E) := by
    ext x
    exact congrArg (fun a : Representation.IntertwiningMap ρ ρ => a x) hz.symm
  have hd : (finrank ℂ E : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℂ) (M := E)))
  have ht := congrArg (LinearMap.trace ℂ E) he
  rw [trace_conjugationSum, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  rw [he]
  congr 1
  field_simp
  linear_combination ht.symm

def matrixCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun x := WithLp.toLp 2 (fun g => inner ℂ v (ρ g⁻¹ x))
  map_add' := by intro x y; ext g; simp
  map_smul' := by intro z x; ext g; simp

omit [Fintype G] [FiniteDimensional ℂ E] in
@[simp] lemma matrixCoefficient_apply (ρ : Representation ℂ G E) (v x : E) (g : G) :
    matrixCoefficient ρ v x g = inner ℂ v (ρ g⁻¹ x) := rfl

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_intertwines (ρ : Representation ℂ G E) (v : E) (g : G) (x : E) :
    matrixCoefficient ρ v (ρ g x) = finiteRegularRepresentation g (matrixCoefficient ρ v x) := by
  ext h
  simp [← Module.End.mul_apply, ← map_mul]

omit [FiniteDimensional ℂ E] in
lemma matrixCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    matrixCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (matrixCoefficient ρ v x) := by
  simp only [coefficientAction_apply, map_sum, map_smul, matrixCoefficient_intertwines]

lemma matrixCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (matrixCoefficient ρ v x) (matrixCoefficient ρ w y) =
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) * inner ℂ w v * inner ℂ x y := by
  calc
    _ = inner ℂ x (conjugationSum ρ (InnerProductSpace.rankOne ℂ v w).toLinearMap y) := by
      rw [PiLp.inner_apply, conjugationSum, LinearMap.sum_apply, inner_sum]
      apply Finset.sum_congr rfl
      intro g _
      simp only [matrixCoefficient_apply, RCLike.inner_apply, Module.End.mul_apply,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      rw [map_smul, inner_smul_right, inner_conj_symm]
      congr 1
      simpa only [inv_inv] using representation_inner_inverse ρ hρ g⁻¹ x v
    _ = _ := by
      rw [conjugationSum_scalar, InnerProductSpace.trace_rankOne,
        LinearMap.smul_apply, Module.End.one_apply, inner_smul_right]

def normalizedCoefficient (ρ : Representation ℂ G E) (v : E) : E →ₗ[ℂ] EuclideanSpace ℂ G :=
  (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) • matrixCoefficient ρ v

lemma normalizedCoefficient_inner (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (v w x y : E) :
    inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ w y) =
      inner ℂ w v * inner ℂ x y := by
  have hd : (0 : ℝ) < finrank ℂ E := by exact_mod_cast Module.finrank_pos (R := ℂ) (M := E)
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hn : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ))) ^ 2 *
      ((Fintype.card G : ℝ) / (finrank ℂ E : ℝ)) = 1 := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  have hn' : (Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
      ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ)) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.ofReal_one]
      using congrArg (fun r : ℝ => (r : ℂ)) hn
  simp only [normalizedCoefficient, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal,
    matrixCoefficient_inner ρ hρ]
  calc
    _ = ((Real.sqrt ((finrank ℂ E : ℝ) / (Fintype.card G : ℝ)) : ℂ) ^ 2 *
        ((Fintype.card G : ℂ) / (finrank ℂ E : ℂ))) * (inner ℂ w v * inner ℂ x y) := by ring
    _ = _ := by rw [hn', one_mul]

omit [FiniteDimensional ℂ E] in
lemma normalizedCoefficient_action (ρ : Representation ℂ G E) (v : E) (f : G → ℂ) (x : E) :
    normalizedCoefficient ρ v (coefficientAction ρ f x) =
      coefficientAction finiteRegularRepresentation f (normalizedCoefficient ρ v x) := by
  simp only [normalizedCoefficient, LinearMap.smul_apply, matrixCoefficient_action, map_smul]

lemma normalizedCoefficient_orthonormal (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) :
    Orthonormal ℂ (fun i : Fin (finrank ℂ E) × Fin (finrank ℂ E) =>
      normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [normalizedCoefficient_inner ρ hρ]
  simp only [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal]
  by_cases h₁ : i.1 = j.1 <;> by_cases h₂ : i.2 = j.2 <;>
    simp [h₁, h₂, Eq.comm, Prod.ext_iff]

lemma positive_orthonormal_trace_le {I : Type*} [Fintype I] (T : E →ₗ[ℂ] E)
    (hT : T.IsPositive) (v : I → E) (hv : Orthonormal ℂ v) :
    ∑ i, (inner ℂ (v i) (T (v i))).re ≤ (LinearMap.trace ℂ E T).re := by
  simp_rw [quadratic_spectral T hT.isSymmetric]
  rw [Finset.sum_comm, trace_spectral T hT.isSymmetric]
  apply Finset.sum_le_sum
  intro j _
  rw [← Finset.mul_sum]
  have hb := hv.sum_inner_products_le (s := Finset.univ) (hT.isSymmetric.eigenvectorBasis rfl j)
  simp only [OrthonormalBasis.norm_eq_one, one_pow] at hb
  simp only [norm_inner_symm (x := v _) (y := hT.isSymmetric.eigenvectorBasis rfl j)] at hb
  exact (mul_le_mul_of_nonneg_left hb (hT.nonneg_eigenvalues rfl j)).trans_eq (mul_one _)

lemma coefficientAction_positive (ρ : Representation ℂ G E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction ρ f).IsPositive := by
  let i : Fin (finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℂ E i
  have hv : inner ℂ v v = 1 := by
    simpa only [v, ite_true] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal i i
  have hi (x y : E) :
      inner ℂ (normalizedCoefficient ρ v x) (normalizedCoefficient ρ v y) = inner ℂ x y := by
    rw [normalizedCoefficient_inner ρ hρ, hv, one_mul]
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← hi, ← hi x, normalizedCoefficient_action, normalizedCoefficient_action]
    exact hf.isSymmetric _ _
  · intro x
    rw [← hi, normalizedCoefficient_action]
    exact hf.re_inner_nonneg_left _

lemma irreducible_trace_le_regular (ρ : Representation ℂ G E) [ρ.IsIrreducible]
    [Nontrivial E] (hρ : ∀ g x, ‖ρ g x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (finrank ℂ E : ℝ) * (LinearMap.trace ℂ E (coefficientAction ρ f)).re ≤
      (LinearMap.trace ℂ (EuclideanSpace ℂ G) (coefficientAction finiteRegularRepresentation f)).re := by
  have hb := positive_orthonormal_trace_le _ hf _ (normalizedCoefficient_orthonormal ρ hρ)
  have he (i : Fin (finrank ℂ E) × Fin (finrank ℂ E)) :
      (inner ℂ (normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2))
        (coefficientAction finiteRegularRepresentation f
          (normalizedCoefficient ρ (stdOrthonormalBasis ℂ E i.1) (stdOrthonormalBasis ℂ E i.2)))).re =
      (inner ℂ (stdOrthonormalBasis ℂ E i.2) (coefficientAction ρ f (stdOrthonormalBasis ℂ E i.2))).re := by
    rw [← normalizedCoefficient_action, normalizedCoefficient_inner ρ hρ]
    simp only [orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal, ite_true, one_mul]
  simp only [he, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hb
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.re_sum]
  exact hb

lemma finiteRegular_trace (f : G → ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ G) (coefficientAction finiteRegularRepresentation f) =
      (Fintype.card G : ℂ) * f 1 := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  have h (i : G) : inner ℂ ((EuclideanSpace.basisFun G ℂ) i)
      (coefficientAction finiteRegularRepresentation f ((EuclideanSpace.basisFun G ℂ) i)) = f 1 := by
    simp [coefficientAction, PiLp.inner_apply, finiteRegularRepresentation_apply]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

def subgroupExtension (H : Subgroup G) :
    EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun f := WithLp.toLp 2 (fun g => if hg : g ∈ H then f ⟨g, hg⟩ else 0)
  map_add' := by intro x y; ext g; by_cases hg : g ∈ H <;> simp [hg]
  map_smul' := by intro z x; ext g; by_cases hg : g ∈ H <;> simp [hg]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply (H : Subgroup G) (f : EuclideanSpace ℂ H) (h : H) :
    subgroupExtension H f h = f h := by simp [subgroupExtension]

omit [Fintype G] in
@[simp] lemma subgroupExtension_apply_not_mem (H : Subgroup G) (f : EuclideanSpace ℂ H)
    (g : G) (hg : g ∉ H) : subgroupExtension H f g = 0 := by simp [subgroupExtension, hg]

lemma subgroup_sum_extension (H : Subgroup G) (f : H → ℂ) :
    ∑ g : G, (if hg : g ∈ H then f ⟨g, hg⟩ else 0) = ∑ h : H, f h := by
  classical
  symm
  apply Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective
  · intro g hg
    have hn : g ∉ H := by intro h; exact hg ⟨⟨g, h⟩, rfl⟩
    simp [hn]
  · intro h
    simp

lemma subgroupExtension_inner (H : Subgroup G) (x : EuclideanSpace ℂ H)
    (y : EuclideanSpace ℂ G) :
    inner ℂ (subgroupExtension H x) y = inner ℂ x (WithLp.toLp 2 (fun h : H => y h)) := by
  classical
  simp only [PiLp.inner_apply, subgroupExtension, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  split <;> simp_all

lemma coefficientAction_subgroup (H : Subgroup G) (f : G → ℂ)
    (x : EuclideanSpace ℂ H) (i : H) :
    coefficientAction finiteRegularRepresentation f (subgroupExtension H x) i =
      coefficientAction finiteRegularRepresentation (fun h : H => f h) x i := by
  classical
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul]
  rw [← subgroup_sum_extension]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ H
  · simp [hg, subgroupExtension, H.mul_mem (H.inv_mem hg) i.property]
    exact Or.inl rfl
  · have hgi : g⁻¹ * (i : G) ∉ H := by
      intro h
      apply hg
      have : g⁻¹ ∈ H := by simpa using H.mul_mem h (H.inv_mem i.property)
      simpa using H.inv_mem this
    simp [hg, subgroupExtension_apply_not_mem H x _ hgi]

lemma subgroup_coefficient_compression (H : Subgroup G) (f : G → ℂ)
    (x y : EuclideanSpace ℂ H) :
    inner ℂ (subgroupExtension H x)
      (coefficientAction finiteRegularRepresentation f (subgroupExtension H y)) =
    inner ℂ x (coefficientAction finiteRegularRepresentation (fun h : H => f h) y) := by
  rw [subgroupExtension_inner]
  congr 1
  ext i
  exact coefficientAction_subgroup H f y i

theorem subgroup_coefficient_positive (H : Subgroup G) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (fun h : H => f h)).IsPositive := by
  refine ⟨?_, ?_⟩
  · intro x y
    rw [← inner_conj_symm, ← subgroup_coefficient_compression,
      ← hf.isSymmetric, ← inner_conj_symm, starRingEnd_self_apply]
    exact subgroup_coefficient_compression H f x y
  · intro x
    rw [inner_re_symm, ← subgroup_coefficient_compression H f x x]
    exact (Complex.nonneg_iff.mp (hf.inner_nonneg_right _)).1

theorem subgroup_irreducible_trace_bound (H : Subgroup G)
    (ρ : Representation ℂ H E) [ρ.IsIrreducible] [Nontrivial E]
    (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) *
        (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) *
        (LinearMap.trace ℂ (EuclideanSpace ℂ G)
          (coefficientAction finiteRegularRepresentation f)).re := by
  have hpos := subgroup_coefficient_positive H f hf
  constructor
  · exact Complex.re_le_re (coefficientAction_positive ρ hρ _ hpos).trace_nonneg
  · have hb := irreducible_trace_le_regular ρ hρ _ hpos
    rw [finiteRegular_trace, Complex.mul_re] at hb
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero,
      OneMemClass.coe_one] at hb
    rw [finiteRegular_trace, Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    convert hb using 1
    field_simp

def bilateralRepresentation : Representation ℂ (G × G) (EuclideanSpace ℂ G) where
  toFun g := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.mulRight g.2⁻¹).trans (Equiv.mulLeft g.1))).toLinearEquiv.toLinearMap
  map_one' := by ext f h; change f (1⁻¹ * h * (1⁻¹)⁻¹) = f h; simp
  map_mul' := by
    intro g k; ext f h
    change f ((g.1 * k.1)⁻¹ * h * ((g.2 * k.2)⁻¹)⁻¹) =
      f (k.1⁻¹ * (g.1⁻¹ * h * (g.2⁻¹)⁻¹) * (k.2⁻¹)⁻¹)
    simp [mul_assoc]

@[simp] lemma bilateralRepresentation_apply (g : G × G) (f : EuclideanSpace ℂ G) (h : G) :
    bilateralRepresentation g f h = f (g.1⁻¹ * h * g.2) := by
  change f (g.1⁻¹ * h * (g.2⁻¹)⁻¹) = _
  rw [inv_inv]

lemma bilateralRepresentation_norm (g : G × G) (f : EuclideanSpace ℂ G) :
    ‖bilateralRepresentation g f‖ = ‖f‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.mulRight g.2⁻¹).trans (Equiv.mulLeft g.1))).norm_map f

@[simp] lemma bilateralRepresentation_left (g : G) :
    bilateralRepresentation (g, (1 : G)) = finiteRegularRepresentation g := by
  ext f h
  simp

lemma coefficientAction_right (f : G → ℂ) (g : G) (x : EuclideanSpace ℂ G) :
    coefficientAction finiteRegularRepresentation f (bilateralRepresentation (1, g) x) =
      bilateralRepresentation (1, g) (coefficientAction finiteRegularRepresentation f x) := by
  simp only [coefficientAction_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  ext i
  simp [mul_assoc]

def subgroupCoefficientCarrier (H : Subgroup G) (ρ : Representation ℂ H E) :
    Subrepresentation (bilateralRepresentation (G := G)) where
  toSubmodule := Submodule.span ℂ (Set.range (fun t : (G × G) × E × E =>
    bilateralRepresentation t.1 (subgroupExtension H (normalizedCoefficient ρ t.2.1 t.2.2))))
  apply_mem_toSubmodule g := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨k, v, w⟩, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨(g * k, v, w), by simp only [map_mul, Module.End.mul_apply]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

def subgroupCoefficientProjection (H : Subgroup G) (ρ : Representation ℂ H E) :
    EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G :=
  (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection.toLinearMap

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_intertwines (H : Subgroup G) (ρ : Representation ℂ H E)
    (g : G × G) (x : EuclideanSpace ℂ G) :
    subgroupCoefficientProjection H ρ (bilateralRepresentation g x) =
      bilateralRepresentation g (subgroupCoefficientProjection H ρ x) :=
  invariant_starProjection_intertwines _ bilateralRepresentation_norm (subgroupCoefficientCarrier H ρ) g x

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_commutes (H : Subgroup G) (ρ : Representation ℂ H E)
    (f : G → ℂ) :
    subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f =
      coefficientAction finiteRegularRepresentation f * subgroupCoefficientProjection H ρ := by
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, coefficientAction_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro g _
  rw [← bilateralRepresentation_left]
  congr 1
  exact subgroupCoefficientProjection_intertwines H ρ (g, 1) x

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_symmetric (H : Subgroup G) (ρ : Representation ℂ H E) :
    (subgroupCoefficientProjection H ρ).IsSymmetric := by
  intro x y
  exact (subgroupCoefficientCarrier H ρ).toSubmodule.inner_starProjection_left_eq_right x y

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_idempotent (H : Subgroup G) (ρ : Representation ℂ H E) :
    subgroupCoefficientProjection H ρ * subgroupCoefficientProjection H ρ =
      subgroupCoefficientProjection H ρ := by
  apply LinearMap.ext
  intro x
  exact (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_eq_self_iff.mpr
    ((subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_apply_mem x)

omit [FiniteDimensional ℂ E] in
lemma subgroupCoefficientProjection_fixes (H : Subgroup G) (ρ : Representation ℂ H E) (v x : E) :
    subgroupCoefficientProjection H ρ (subgroupExtension H (normalizedCoefficient ρ v x)) =
      subgroupExtension H (normalizedCoefficient ρ v x) := by
  apply (subgroupCoefficientCarrier H ρ).toSubmodule.starProjection_eq_self_iff.mpr
  apply Submodule.subset_span
  exact ⟨((1, 1), v, x), by simp only [show ((1, 1) : G × G) = 1 from rfl, map_one,
    Module.End.one_apply]⟩

lemma finiteRegular_coefficient_kernel (f : G → ℂ) (i j : G) :
    coefficientAction finiteRegularRepresentation f (EuclideanSpace.basisFun G ℂ j) i =
      f (i * j⁻¹) := by
  simp only [coefficientAction_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    finiteRegularRepresentation_apply, smul_eq_mul, EuclideanSpace.basisFun_apply]
  simp only [PiLp.single_apply, inv_mul_eq_iff_eq_mul, mul_ite, mul_one, mul_zero]
  have he (x : G) : i = x * j ↔ x = i * j⁻¹ := by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; rw [h, inv_mul_cancel_right]
  simp_rw [he]
  simp

end SignedSweeps
end

end OAI
