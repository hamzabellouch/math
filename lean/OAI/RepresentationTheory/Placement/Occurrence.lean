import Mathlib
import OAI.RepresentationTheory.Placement.Chart
import OAI.RepresentationTheory.Young.Classification
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Placement
variable {I U X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]

/- Dependence only on the listed coordinate values of a placement. -/
def DependsOn (coords : Y → I → U) (A : Finset I) (f : Y → ℂ) : Prop :=
  ∀ y y', (∀ i ∈ A, coords y i = coords y' i) → f y = f y'

/- Counting-measure top-level space. Equivalently the orthogonal complement
of the span of proper-coordinate cylinder functions (conjugation preserves that span). -/
def topSpace (coords : Y → I → U) : Submodule ℂ (Y → ℂ) where
  carrier := {v | ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
    DependsOn coords A f → ∑ y, f y*v y = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw A hA f hf
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hv A hA f hf, hw A hA f hf, zero_add]
  smul_mem' := by
    intro c v hv A hA f hf
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm (f _) c, mul_assoc]
    rw [← Finset.mul_sum, hv A hA f hf, mul_zero]

/- The source's s-normalized alternating kernel, over all coordinate subsets. -/
def alternatingKernel (s : ℝ) (p : Finset I → X → Y → ℝ) : Matrix X Y ℂ :=
  fun x y => (s⁻¹^(Fintype.card I) * ∑ A ∈ (Finset.univ : Finset I).powerset,
    (-1 : ℝ)^(Fintype.card I-A.card) * s^A.card * p A x y : ℝ)

/- All proper-subset marginal terms vanish on the top level. This is the
nontrivial algebraic bridge between Q and the actual transition operator. -/
omit [DecidableEq I] [Fintype X] in
theorem alternatingKernel_mulVec_top (coords : Y → I → U)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → X → Y → ℝ)
    (hp : ∀ A x, DependsOn coords A (fun y => (p A x y : ℂ)))
    {v : Y → ℂ} (hv : v ∈ topSpace coords) :
    (alternatingKernel s p).mulVec v = Matrix.mulVec (fun x y => (p Finset.univ x y : ℂ)) v := by
  funext x
  simp only [Matrix.mulVec, dotProduct, alternatingKernel, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_sum]
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single (Finset.univ : Finset I)]
  · simp only [Finset.card_univ, Nat.sub_self, pow_zero, one_mul]
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_pow, one_mul]
  · intro A hA hne
    have hzero := hv A hne (fun y => (p A x y : ℂ)) (hp A x)
    simp only [hzero, mul_zero]
  · simp

/- Counting HS norm always dominates the L2 operator norm, rectangular and
empty dimensions included. No entrywise max norm is used. -/
theorem matrix_l2_norm_le_hs (A : Matrix X Y ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ x, ∑ y, ‖A x y‖^2) := by
  let L : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ X :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  change ‖L‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) ?_
  intro v
  have hrow (x : X) : ‖(A.mulVec v) x‖^2 ≤
      (∑ y, ‖A x y‖^2)*(∑ y, ‖v y‖^2) := by
    have hnorm : ‖(A.mulVec v) x‖ ≤ ∑ y, ‖A x y‖*‖v y‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun y _ => le_of_eq (norm_mul _ _))
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖A x y‖) (fun y => ‖v y‖)
    exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => by positivity))).mpr hnorm).trans hc
  have hall : (∑ x, ‖(A.mulVec v) x‖^2) ≤
      (∑ x, ∑ y, ‖A x y‖^2)*(∑ y, ‖v y‖^2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun x _ => hrow x)
  change ‖Matrix.toEuclideanLin A v‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact hall

/- The actual full marginal has the alternating HS bound on the entire top
placement space. This is used before choosing an irreducible constituent. -/
omit [DecidableEq I] in
theorem fullKernel_top_norm_le (coords : Y → I → U)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → X → Y → ℝ)
    (hp : ∀ A x, DependsOn coords A (fun y => (p A x y : ℂ)))
    (v : EuclideanSpace ℂ Y) (hv : (fun y => v y) ∈ topSpace coords) :
    ‖(EuclideanSpace.equiv X ℂ).symm
      (Matrix.mulVec (fun x y => (p Finset.univ x y : ℂ)) v)‖ ≤
      Real.sqrt (∑ x, ∑ y, ‖alternatingKernel s p x y‖^2)*‖v‖ := by
  rw [← alternatingKernel_mulVec_top coords s hs p hp hv]
  exact ((alternatingKernel s p).l2_opNorm_mulVec v).trans
    (mul_le_mul_of_nonneg_right (matrix_l2_norm_le_hs _) (norm_nonneg _))
end CoordinateSweeps.Placement
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

theorem adjoint_intertwines {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ)
    (hB : ∀ g, B * P g = ρ.matrix g * B) (g : Γ) :
    P g * B.conjTranspose = B.conjTranspose * ρ.matrix g := by
  have hPinv : P g⁻¹ = (P g).conjTranspose := by
    calc
      P g⁻¹ = 1 * P g⁻¹ := (one_mul _).symm
      _ = ((P g).conjTranspose * P g) * P g⁻¹ := by rw [hP g]
      _ = (P g).conjTranspose := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h := congrArg Matrix.conjTranspose (hB g⁻¹)
  have hrinv : ρ.matrix g⁻¹ = (ρ.matrix g).conjTranspose := by
    calc
      ρ.matrix g⁻¹ = 1 * ρ.matrix g⁻¹ := (one_mul _).symm
      _ = ((ρ.matrix g).conjTranspose * ρ.matrix g) * ρ.matrix g⁻¹ := by rw [ρ.unitary g]
      _ = (ρ.matrix g).conjTranspose := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  simpa only [Matrix.conjTranspose_mul, hPinv, hrinv,
    Matrix.conjTranspose_conjTranspose] using h

/- Schur's lemma makes every nonzero intertwiner a scalar coisometry. -/
theorem intertwiner_gram_scalar {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ)
    (hB : ∀ g, B * P g = ρ.matrix g * B) :
    ∃ c : ℂ, B * B.conjTranspose = c • (1 : Matrix _ _ ℂ) := by
  apply ρ.commuting_scalar
  intro g
  rw [Matrix.mul_assoc, ← ρ.adjoint_intertwines P hP B hB g,
    ← Matrix.mul_assoc, hB g, Matrix.mul_assoc]

/- Exact norm transfer, with no extraneous dimension loss. Q need agree with
an averaged permutation operator only on the adjoint intertwiner range. -/
theorem norm_le_compression {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ) (hne : B ≠ 0)
    (hB : ∀ g, B * P g = ρ.matrix g * B)
    (K : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) (Q : Matrix X X ℂ)
    (hQ : Q * B.conjTranspose = B.conjTranspose * K) : ‖K‖ ≤ ‖Q‖ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨c, hc⟩ := ρ.intertwiner_gram_scalar P hP B hB
  have hn : ‖B‖ * ‖B‖ = ‖c‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self B.conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      hc, norm_smul, norm_one, mul_one] using h.symm
  have hcpos : 0 < ‖c‖ := by rw [← hn]; exact mul_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)
  have he : c • K = B * Q * B.conjTranspose := by
    rw [Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hc, Matrix.smul_mul, one_mul]
  have hbound : ‖c‖ * ‖K‖ ≤ ‖c‖ * ‖Q‖ := by
    rw [← norm_smul, he]
    calc
      ‖B * Q * B.conjTranspose‖ ≤ ‖B * Q‖ * ‖B.conjTranspose‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖B‖ * ‖Q‖) * ‖B.conjTranspose‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = (‖B‖ * ‖B‖) * ‖Q‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring
      _ = ‖c‖ * ‖Q‖ := by rw [hn]
  exact (mul_le_mul_iff_right₀ hcpos).mp hbound
end UnitaryIrrep
end CoordinateSweeps

noncomputable section
universe u v
open scoped ComplexConjugate

namespace CoordinateSweeps
/- The pointwise stabilizer of two sites, used in the sparse dimension bridge. -/
def fixTwo {Ω : Type*} (a b : Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {g | g a = a ∧ g b = b}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' hg hk := by simpa using And.intro (congrArg _ hk.1 |>.trans hg.1) (congrArg _ hk.2 |>.trans hg.2)
  inv_mem' := by
    intro g hg
    constructor
    · apply g.injective
      simpa using hg.1.symm
    · apply g.injective
      simpa using hg.2.symm

namespace SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- Generic Schur commutant lemma, with no classification assumptions. -/
theorem commuting_scalar {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (A : Module.End ℂ V) (hA : ∀ g, A * ρ g = ρ g * A) :
    ∃ c : ℂ, A = c • (1 : Module.End ℂ V) := by
  let F : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := A
      isIntertwining' := hA }
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.2 F
  refine ⟨c, ?_⟩
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  exact hh.symm

/- If all operators are scalar, irreducibility forces one dimension. -/
omit [FiniteDimensional ℂ V] in
theorem finrank_eq_one_of_scalars {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (hs : ∀ g, ∃ c : ℂ, ρ g = c • (1 : Module.End ℂ V)) :
    Module.finrank ℂ V = 1 := by
  have : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have he : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Subsingleton.elim _ _
    exact bot_ne_top he
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨c, hc⟩ := hs g
        rw [hc]
        exact Submodule.smul_mem _ c hx }
  have hne : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := Submodule.mem_span_singleton_self _
    rw [he] at hm
    exact hv hm
  have he : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hne
  have he' : (ℂ ∙ v : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule he
  rw [← finrank_top ℂ V, ← he']
  exact finrank_span_singleton hv

omit [FiniteDimensional ℂ V] in
@[simp] theorem subrep_bot_toSubmodule {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
omit [FiniteDimensional ℂ V] in
@[simp] theorem subrep_top_toSubmodule {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl

/- Flatten a subrepresentation of a subrepresentation without changing its dimension. -/
def nested {Γ : Type*} [Group Γ] {ρ : Representation ℂ Γ V}
    (S : Subrepresentation ρ) (T : Subrepresentation S.toRepresentation) : Subrepresentation ρ where
  toSubmodule := T.toSubmodule.map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨S.toRepresentation g w, T.apply_mem_toSubmodule g hw, rfl⟩

/- Existence of a least-dimensional constituent, proved rather than assumed. -/
theorem exists_minimal_constituent {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [Nontrivial V] :
    ∃ S : Subrepresentation ρ, 0 < Module.finrank ℂ S.toSubmodule ∧
      S.toRepresentation.IsIrreducible ∧
      ∀ T : Subrepresentation ρ, T ≠ ⊥ →
        Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
  classical
  have hp : ∃ n, ∃ S : Subrepresentation ρ,
      0 < Module.finrank ℂ S.toSubmodule ∧ Module.finrank ℂ S.toSubmodule = n :=
    ⟨Module.finrank ℂ V, ⊤, by simpa using (Module.finrank_pos (R := ℂ) (M := V)), by simp⟩
  obtain ⟨S, hSpos, hSdim⟩ := Nat.find_spec hp
  have hmin (T : Subrepresentation ρ) (hT : T ≠ ⊥) :
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    rw [hSdim]
    apply Nat.find_min' hp
    refine ⟨T, ?_, rfl⟩
    apply Module.finrank_pos_iff.mpr
    apply Submodule.nontrivial_iff_ne_bot.mpr
    exact fun ht => hT (Subrepresentation.toSubmodule_injective ht)
  refine ⟨S, hSpos, ?_, hmin⟩
  have : Nontrivial S.toSubmodule := Module.finrank_pos_iff.mp hSpos
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro T
    by_cases hT : T = ⊥
    · exact Or.inl hT
    right
    by_contra htop
    have hTp : 0 < Module.finrank ℂ T.toSubmodule := by
      apply Module.finrank_pos_iff.mpr
      apply Submodule.nontrivial_iff_ne_bot.mpr
      exact fun ht => hT (Subrepresentation.toSubmodule_injective ht)
    have hdim : Module.finrank ℂ (nested S T).toSubmodule = Module.finrank ℂ T.toSubmodule :=
      S.toSubmodule.finrank_map_subtype_eq T.toSubmodule
    have hnb : nested S T ≠ ⊥ := by
      intro he
      have hz : Module.finrank ℂ (nested S T).toSubmodule = 0 := by rw [he]; simp
      omega
    have hlow := hmin (nested S T) hnb
    rw [hdim] at hlow
    have hhigh : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ S.toSubmodule :=
      Submodule.finrank_lt (fun ht => htop (Subrepresentation.toSubmodule_injective ht))
    omega

/- Every reducible finite-group representation has a constituent of at most
half its dimension. This uses Maschke over ℂ, not an assumed decomposition. -/
theorem exists_constituent_le_half {Γ : Type*} [Group Γ] [Fintype Γ]
    (ρ : Representation ℂ Γ V) [Nontrivial V]
    (hn : ¬ρ.IsIrreducible) :
    ∃ S : Subrepresentation ρ, 0 < Module.finrank ℂ S.toSubmodule ∧
      S.toRepresentation.IsIrreducible ∧
      2 * Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨S, hpos, hirr, hmin⟩ := exists_minimal_constituent ρ
  have hnon : ∃ T : Subrepresentation ρ, T ≠ ⊥ ∧ T ≠ ⊤ := by
    by_contra h
    apply hn
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro he
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
    · intro T
      simpa only [not_exists, not_and_or, not_not] using (not_exists.mp h T)
  obtain ⟨T, hTbot, hTtop⟩ := hnon
  have hSt : S ≠ ⊤ := by
    intro he
    have hd := hmin T hTbot
    have ht : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ V :=
      Submodule.finrank_lt (fun ht => hTtop (Subrepresentation.toSubmodule_injective ht))
    rw [he] at hd
    simp only [subrep_top_toSubmodule, finrank_top] at hd
    omega
  let : NeZero (Nat.card Γ : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨U, hU⟩ := exists_isCompl S
  have hUb : U ≠ ⊥ := by
    intro he
    have h := hU.sup_eq_top
    rw [he, sup_bot_eq] at h
    exact hSt h
  have hle := hmin U hUb
  have hcompl : IsCompl S.toSubmodule U.toSubmodule := by
    apply IsCompl.of_eq
    · exact congrArg Subrepresentation.toSubmodule hU.inf_eq_bot
    · exact congrArg Subrepresentation.toSubmodule hU.sup_eq_top
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  exact ⟨S, hpos, hirr, by omega⟩

/- Restriction to permutations fixing two distinct sites is not irreducible,
unless the full irreducible is one-dimensional. This gives a factor-two
dimension descent every two removed cards, needed for sparse types. -/
theorem finrank_eq_one_of_fixTwo_irreducible
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (a b : Ω) (hab : a ≠ b)
    [hirr : Representation.IsIrreducible (ρ.comp (fixTwo a b).subtype)] :
    Module.finrank ℂ V = 1 := by
  have hc : ∀ g : fixTwo a b,
      ρ (Equiv.swap a b) * ρ g.val = ρ g.val * ρ (Equiv.swap a b) := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    rw [Equiv.mul_swap_eq_swap_mul, g.property.1, g.property.2]
  obtain ⟨c, hc⟩ := commuting_scalar (ρ.comp (fixTwo a b).subtype) (ρ (Equiv.swap a b)) hc
  have hswap (x y : Ω) (hxy : x ≠ y) : ρ (Equiv.swap x y) = c • (1 : Module.End ℂ V) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hxy)
    rw [← hg, map_mul, map_mul, hc]
    simp only [mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]
  apply finrank_eq_one_of_scalars ρ
  intro g
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, by simp⟩
  | swap_mul g x y hxy ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨c*d, ?_⟩
    rw [map_mul, hswap x y hxy, hd, smul_mul_smul_comm, one_mul]

/- Restriction along a surjective homomorphism preserves irreducibility. -/
omit [FiniteDimensional ℂ V] in
theorem irreducible_comp_surjective {Γ Δ : Type*} [Group Γ] [Group Δ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (f : Δ →* Γ) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) := by
  have he (S : Subrepresentation (ρ.comp f)) :
      S.toSubmodule = ⊥ ∨ S.toSubmodule = ⊤ := by
    let T : Subrepresentation ρ :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨x, rfl⟩ := hf g
          exact S.apply_mem_toSubmodule x hv }
    exact (eq_bot_or_eq_top T).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)
  have : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    apply bot_ne_top (α := Subrepresentation ρ)
    exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    exact (he S).imp (fun h => Subrepresentation.toSubmodule_injective h)
      (fun h => Subrepresentation.toSubmodule_injective h)

/- Permutations of the complementary sites, viewed in the two-point stabilizer. -/
def fixTwoHom (a b : Ω) : Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b} →* fixTwo a b where
  toFun g := ⟨Equiv.Perm.ofSubtype g,
    Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp),
    Equiv.Perm.ofSubtype_apply_of_not_mem g (by simp)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

omit [Fintype Ω] in
@[simp] theorem fixTwoHom_val (a b : Ω) (g : Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b}) :
    (fixTwoHom a b g).val = Equiv.Perm.ofSubtype g := rfl

omit [Fintype Ω] in
theorem fixTwoHom_surjective (a b : Ω) : Function.Surjective (fixTwoHom a b) := by
  intro g
  have hi (x : Ω) : ((g.val x ≠ a ∧ g.val x ≠ b) ↔ (x ≠ a ∧ x ≠ b)) := by
    have ha : g.val x = a ↔ x = a :=
      ⟨fun h => g.val.injective (h.trans g.property.1.symm), fun h => h ▸ g.property.1⟩
    have hb : g.val x = b ↔ x = b :=
      ⟨fun h => g.val.injective (h.trans g.property.2.symm), fun h => h ▸ g.property.2⟩
    simp only [ne_eq, ha, hb]
  refine ⟨g.val.subtypePerm hi, Subtype.ext ?_⟩
  apply Equiv.Perm.ofSubtype_subtypePerm hi
  intro x hx
  constructor
  · intro he; subst x; exact hx g.property.1
  · intro he; subst x; exact hx g.property.2

/- One factor-two dimension descent, with the remaining symmetric group
realized literally as permutations of the complement. -/
theorem exists_half_constituent_fixTwo
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] [Nontrivial V]
    (hd : Module.finrank ℂ V ≠ 1) (a b : Ω) (hab : a ≠ b) :
    ∃ S : Subrepresentation (ρ.comp (fixTwo a b).subtype),
      0 < Module.finrank ℂ S.toSubmodule ∧
      Representation.IsIrreducible (S.toRepresentation.comp (fixTwoHom a b)) ∧
      2 * Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ V := by
  classical
  have hn : ¬Representation.IsIrreducible (ρ.comp (fixTwo a b).subtype) := by
    intro hirr
    let := hirr
    exact hd (finrank_eq_one_of_fixTwo_irreducible ρ a b hab)
  obtain ⟨S, hpos, hirr, hdim⟩ := exists_constituent_le_half (ρ.comp (fixTwo a b).subtype) hn
  let := hirr
  exact ⟨S, hpos, irreducible_comp_surjective S.toRepresentation
    (fixTwoHom a b) (fixTwoHom_surjective a b), hdim⟩

/- Nonzero state space follows from irreducibility, including degenerate groups. -/
omit [FiniteDimensional ℂ V] in
theorem irreducible_nontrivial {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hn
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
  apply bot_ne_top (α := Subrepresentation ρ)
  exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)

/- A one-dimensional constituent is already visible after at most twice the
base-two logarithm of the dimension many fixed cards. The power formulation
avoids rounding conventions and is valid also for dimension one. -/
theorem sparse_line_by_dim (D : ℕ) :
    ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω]
      (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible],
      Module.finrank ℂ V = D →
      ∃ (t : ℕ) (A : Finset Ω) (W : Submodule ℂ V),
        Module.finrank ℂ W = 1 ∧ A.card ≤ 2*t ∧ 2^t ≤ D ∧
        ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) →
          ∀ w ∈ W, ρ g w ∈ W := by
  classical
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro Ω _ _ V _ _ _ ρ hirr hD
    have : Nontrivial V := irreducible_nontrivial ρ
    have hDpos : 0 < D := hD ▸ Module.finrank_pos
    by_cases hD1 : D = 1
    · refine ⟨0, ∅, ⊤, ?_, by simp, by simp [hD1], ?_⟩
      · simpa only [finrank_top] using hD.trans hD1
      · intro g hg w hw; trivial
    have hΩ : Nontrivial Ω := by
      by_contra hn
      have : Subsingleton Ω := not_nontrivial_iff_subsingleton.mp hn
      have hscalar : ∀ g : Equiv.Perm Ω, ∃ c : ℂ, ρ g = c • (1 : Module.End ℂ V) := by
        intro g
        have he : g = 1 := Subsingleton.elim _ _
        exact ⟨1, by rw [he, map_one, one_smul]⟩
      exact hD1 (hD.symm.trans (finrank_eq_one_of_scalars ρ hscalar))
    let := hΩ
    obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
    obtain ⟨S, hSpos, hSirr, hShalf⟩ := exists_half_constituent_fixTwo ρ
      (by simpa only [hD] using hD1) a b hab
    let ρ' : Representation ℂ (Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b}) S.toSubmodule :=
      S.toRepresentation.comp (fixTwoHom a b)
    let : ρ'.IsIrreducible := hSirr
    have hlt : Module.finrank ℂ S.toSubmodule < D := by rw [hD] at hShalf; omega
    obtain ⟨t, A, W, hWdim, hAcard, ht, hWstable⟩ :=
      ih (Module.finrank ℂ S.toSubmodule) hlt {x : Ω // x ≠ a ∧ x ≠ b}
        S.toSubmodule ρ' rfl
    let B : Finset Ω := insert a (insert b (A.image Subtype.val))
    refine ⟨t+1, B, W.map S.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
    · rw [Submodule.finrank_map_subtype_eq, hWdim]
    · have hc := Finset.card_image_le (s := A) (f := Subtype.val)
      have h1 := Finset.card_insert_le a (insert b (A.image Subtype.val))
      have h2 := Finset.card_insert_le b (A.image Subtype.val)
      dsimp [B]
      omega
    · rw [pow_succ]
      rw [hD] at hShalf
      omega
    · intro g hg w hw
      obtain ⟨w, hw, rfl⟩ := hw
      have hga : g a = a := hg a (by simp [B])
      have hgb : g b = b := hg b (by simp [B])
      obtain ⟨σ, hσ⟩ := fixTwoHom_surjective a b ⟨g, hga, hgb⟩
      have hsfix : ∀ x ∈ A, σ x = x := by
        intro x hx
        apply Subtype.ext
        calc
          (σ x).val = (fixTwoHom a b σ).val x.val :=
            (Equiv.Perm.ofSubtype_apply_coe σ x).symm
          _ = g x.val := congrArg (fun f : fixTwo a b => f.val x.val) hσ
          _ = x.val := hg x.val (by simp [B, Finset.mem_image_of_mem _ hx])
      refine ⟨ρ' σ w, hWstable σ hsfix w hw, ?_⟩
      change ρ ((fixTwoHom a b σ).val) w.val = ρ g w.val
      rw [hσ]

/- The rounded-free quantitative sparse dimension bridge for the actual
symmetric group, independent of a partition classification. -/
theorem exists_sparse_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (t : ℕ) (A : Finset Ω) (W : Submodule ℂ V),
      Module.finrank ℂ W = 1 ∧ A.card ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) →
        ∀ w ∈ W, ρ g w ∈ W :=
  sparse_line_by_dim _ Ω V ρ rfl

/- Ordinary permutation sign, embedded into the complex scalars. -/
def signScalar : Equiv.Perm Ω →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp Equiv.Perm.sign)

@[simp] theorem signScalar_apply (g : Equiv.Perm Ω) :
    signScalar g = ((Equiv.Perm.sign g : ℤ) : ℂ) := rfl

@[simp] theorem signScalar_swap (a b : Ω) (hab : a ≠ b) :
    signScalar (Equiv.swap a b) = -1 := by
  simp [signScalar_apply, Equiv.Perm.sign_swap hab]

/- Every one-dimensional representation of a finite symmetric group is
literally the trivial or sign representation. This also handles Ω of size 0,1. -/
theorem oneDimensional_trivial_or_sign
    (ρ : Representation ℂ (Equiv.Perm Ω) V) (hd : Module.finrank ℂ V = 1) :
    (∀ g, ρ g = 1) ∨ (∀ g, ρ g = signScalar g • (1 : Module.End ℂ V)) := by
  classical
  by_cases hΩ : Nontrivial Ω
  swap
  · have : Subsingleton Ω := not_nontrivial_iff_subsingleton.mp hΩ
    left
    intro g
    rw [Subsingleton.elim g 1, map_one]
  let := hΩ
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (ρ (Equiv.swap a b))
  change ρ (Equiv.swap a b) = c • (1 : Module.End ℂ V) at hc
  have hsame (x y : Ω) (hxy : x ≠ y) : ρ (Equiv.swap x y) = c • (1 : Module.End ℂ V) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hxy)
    rw [← hg, map_mul, map_mul, hc]
    simp only [mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]
  have hc2 : c*c = 1 := by
    apply (LinearEquiv.smul_id_of_finrank_eq_one hd).injective
    simp only [LinearEquiv.smul_id_of_finrank_eq_one_apply]
    change (c*c) • (1 : Module.End ℂ V) = 1 • (1 : Module.End ℂ V)
    rw [one_smul]
    calc
      (c*c) • (1 : Module.End ℂ V) = (c • (1 : Module.End ℂ V))*(c • 1) := by
        simp only [smul_mul_smul_comm, one_mul]
      _ = 1 := by rw [← hc, ← map_mul, Equiv.swap_mul_self, map_one]
  rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcn
  · left
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one => exact map_one _
    | swap_mul g x y hxy ih => rw [map_mul, hsame x y hxy, hc1, one_smul, ih, one_mul]
  · right
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul g x y hxy ih =>
      rw [map_mul, hsame x y hxy, hcn, ih, map_mul, signScalar_swap x y hxy,
        smul_mul_smul_comm, one_mul]

/- The cyclic span proof underlying the irreducible dimension lemma,
on an arbitrary finite-dimensional realization. -/
omit [FiniteDimensional ℂ V] in
theorem orbit_span_top {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible] (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g => ρ g v)) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k, rfl⟩ := hw
          rw [← Module.End.mul_apply, ← map_mul]
          exact Submodule.subset_span (Set.mem_range_self (g*k))
        | zero => simp
        | add x y hx hy hix hiy => simpa only [map_add] using Submodule.add_mem _ hix hiy
        | smul c x hx hi => simpa only [map_smul] using Submodule.smul_mem _ c hi }
  have hn : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := by
      change v ∈ Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply Submodule.subset_span
      exact ⟨1, by simp⟩
    rw [he] at hm
    exact hv hm
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top S).resolve_left hn)

/- The upper sparse dimension bound: a line invariant under the stabilizer
of k named sites gives at most n^k dimensions in its irreducible orbit. -/
theorem dimension_le_pow_of_stable_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (A : Finset Ω) (W : Submodule ℂ V) (hW : Module.finrank ℂ W = 1)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W) :
    Module.finrank ℂ V ≤ (Fintype.card Ω)^A.card := by
  classical
  have : Nontrivial W := (Module.finrank_pos_iff (R := ℂ) (M := W)).mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hv' : v.val ≠ 0 := by intro he; exact hv (Subtype.ext he)
  let restrict (g : Equiv.Perm Ω) : A → Ω := fun a => g a.val
  let chooseG (x : A → Ω) : Equiv.Perm Ω :=
    if hx : ∃ g, restrict g = x then Classical.choose hx else 1
  have hchoose (g : Equiv.Perm Ω) : restrict (chooseG (restrict g)) = restrict g := by
    dsimp [chooseG]
    rw [dite_eq_left (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)]
    exact Classical.choose_spec (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)
  let u (x : A → Ω) : V := ρ (chooseG x) v.val
  have hspan : Submodule.span ℂ (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← orbit_span_top ρ v.val hv']
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    let r := chooseG (restrict g)
    have hfix : ∀ a ∈ A, (r⁻¹*g) a = a := by
      intro a ha
      have he := congrFun (hchoose g) ⟨a, ha⟩
      change r a = g a at he
      simp only [Equiv.Perm.mul_apply]
      rw [← he]; simp
    have hw : ρ (r⁻¹*g) v.val ∈ W := hstable _ hfix _ v.property
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW hv
      (⟨ρ (r⁻¹*g) v.val, hw⟩ : W)
    have he : ρ g v.val = c • u (restrict g) := by
      have hh := congrArg (fun w : W => ρ r w.val) hc
      change ρ r (c • v.val) = ρ r (ρ (r⁻¹*g) v.val) at hh
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at hh
      exact hh.symm
    change ρ g v.val ∈ Submodule.span ℂ (Set.range u)
    rw [he]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self _))
  have hd := finrank_le_of_span_eq_top hspan
  simpa only [Fintype.card_fun, Fintype.card_coe] using hd

/- Pointwise stabilizer of a named finite set of sites. -/
def fixSet (A : Finset Ω) : Subgroup (Equiv.Perm Ω) where
  carrier := {g | ∀ a ∈ A, g a = a}
  one_mem' := by simp
  mul_mem' hg hh a ha := by simp only [Equiv.Perm.mul_apply, hh a ha, hg a ha]
  inv_mem' {g} hg a ha := by
    apply g.injective
    simpa using (hg a ha).symm

/- The complementary symmetric group onto the pointwise stabilizer. -/
def fixSetHom (A : Finset Ω) : Equiv.Perm {x : Ω // x ∉ A} →* fixSet A where
  toFun g := ⟨Equiv.Perm.ofSubtype g, fun _ ha =>
    Equiv.Perm.ofSubtype_apply_of_not_mem g (not_not.mpr ha)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g h)

omit [Fintype Ω] in
@[simp] theorem fixSetHom_val (A : Finset Ω) (g : Equiv.Perm {x : Ω // x ∉ A}) :
    (fixSetHom A g).val = Equiv.Perm.ofSubtype g := rfl

omit [Fintype Ω] in
theorem fixSetHom_surjective (A : Finset Ω) : Function.Surjective (fixSetHom A) := by
  intro g
  have hi (x : Ω) : (g.val x ∉ A) ↔ x ∉ A := by
    constructor
    · intro h hx
      apply h
      rwa [g.property x hx]
    · intro h hx
      have he := g.property (g.val x) hx
      have he' : g.val x = x := g.val.injective he
      exact h (he' ▸ hx)
  refine ⟨g.val.subtypePerm hi, Subtype.ext ?_⟩
  apply Equiv.Perm.ofSubtype_subtypePerm hi
  intro x hx
  by_contra hn
  exact hx (g.property x (by simpa using hn))

/- A stable line under a pointwise stabilizer is a literal trivial or sign
line. There is no hypothesis about a partition or a pre-existing embedding. -/
theorem stable_line_trivial_or_sign
    (ρ : Representation ℂ (Equiv.Perm Ω) V)
    (A : Finset Ω) (W : Submodule ℂ V) (hW : Module.finrank ℂ W = 1)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W) :
    ∃ u : V, u ≠ 0 ∧
      ((∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = u) ∨
       (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = signScalar g • u)) := by
  classical
  let S : Subrepresentation (ρ.comp (fixSet A).subtype) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun g w hw => hstable g.val g.property w hw }
  let ρ' := S.toRepresentation.comp (fixSetHom A)
  have : Nontrivial W := (Module.finrank_pos_iff (R := ℂ) (M := W)).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  refine ⟨u.val, fun he => hu (Subtype.ext he), ?_⟩
  rcases oneDimensional_trivial_or_sign ρ' hW with ht | hs
  · left
    intro g hg
    obtain ⟨σ, hσ⟩ := fixSetHom_surjective A ⟨g, hg⟩
    have he := congrArg (fun T : Module.End ℂ W => (T u).val) (ht σ)
    change ρ ((fixSetHom A σ).val) u.val = u.val at he
    simpa only [hσ] using he
  · right
    intro g hg
    obtain ⟨σ, hσ⟩ := fixSetHom_surjective A ⟨g, hg⟩
    have he := congrArg (fun T : Module.End ℂ W => (T u).val) (hs σ)
    change ρ ((fixSetHom A σ).val) u.val = signScalar σ • u.val at he
    simp only [signScalar_apply] at he ⊢
    rw [← Equiv.Perm.sign_ofSubtype σ] at he
    simpa only [← fixSetHom_val, hσ] using he

/- Minimal signed placement level with both dimension bounds. The last
clause rules out every earlier line, hence in particular every earlier fixed
vector of either the representation or its sign twist. -/
theorem exists_minimal_sparse_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (k t : ℕ) (A : Finset Ω) (u : V),
      A.card = k ∧ k ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      Module.finrank ℂ V ≤ (Fintype.card Ω)^k ∧ u ≠ 0 ∧
      ((∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = u) ∨
       (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = signScalar g • u)) ∧
      ∀ B : Finset Ω, B.card < k → ∀ (v : V),
        (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → ∃ c : ℂ, ρ g v = c • v) → v = 0 := by
  classical
  let P (k : ℕ) : Prop := ∃ (A : Finset Ω) (W : Submodule ℂ V), A.card = k ∧
    Module.finrank ℂ W = 1 ∧
    ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W
  obtain ⟨t, A₀, W₀, hW₀, hA₀, ht, hs₀⟩ := exists_sparse_line ρ
  have hex : ∃ k, P k := ⟨A₀.card, A₀, W₀, rfl, hW₀, hs₀⟩
  obtain ⟨A, W, hA, hW, hs⟩ := Nat.find_spec hex
  have hk : Nat.find hex ≤ A₀.card := Nat.find_min' hex ⟨A₀, W₀, rfl, hW₀, hs₀⟩
  obtain ⟨u, hu, hchar⟩ := stable_line_trivial_or_sign ρ A W hW hs
  refine ⟨Nat.find hex, t, A, u, hA, hk.trans hA₀, ht, ?_, hu, hchar, ?_⟩
  · rw [← hA]
    exact dimension_le_pow_of_stable_line ρ A W hW hs
  · intro B hB v hv
    by_contra hn
    have hp : P B.card := by
      refine ⟨B, ℂ ∙ v, rfl, finrank_span_singleton hn, ?_⟩
      intro g hg w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨r, hr⟩ := hv g hg
      rw [map_smul, hr, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact Nat.find_min hex hB hp
end SparseDimension
end CoordinateSweeps

noncomputable section
open scoped BigOperators

namespace CoordinateSweeps.PlacementOccurrence
variable {Γ X V : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]
    [AddCommGroup V] [Module ℂ V]

/- Sum of orbit vectors against placement coordinates. The repeated
stabilizer fibers are left in the sum, so no transversal choice is needed. -/
def orbitSynthesis (ρ : Representation ℂ Γ V) (u : V) (x₀ : X) : (X → ℂ) →ₗ[ℂ] V where
  toFun f := ∑ g, f (g • x₀) • ρ g u
  map_add' f h := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

/- Exact covariance, with the source's convention that gh applies h first. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_covariant (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (h : Γ) (f : X → ℂ) :
    orbitSynthesis ρ u x₀ (fun x => f (h⁻¹ • x)) = ρ h (orbitSynthesis ρ u x₀ f) := by
  change (∑ g, f (h⁻¹ • (g • x₀)) • ρ g u) = ρ h (∑ g, f (g • x₀) • ρ g u)
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun g => f (h⁻¹ • (g • x₀)) • ρ g u)]
  simp only [Equiv.coe_mulLeft, mul_smul, inv_smul_smul, map_sum, map_smul,
    map_mul, Module.End.mul_apply]

/- A vector fixed by the point stabilizer produces a nonzero synthesis map. -/
omit [Fintype X] in
theorem orbitSynthesis_delta_ne_zero (ρ : Representation ℂ Γ V) (u : V) (hu : u ≠ 0)
    (x₀ : X) (hfixed : ∀ g : Γ, g • x₀ = x₀ → ρ g u = u) :
    orbitSynthesis ρ u x₀ (fun x => if x = x₀ then 1 else 0) ≠ 0 := by
  classical
  have he : orbitSynthesis ρ u x₀ (fun x => if x = x₀ then 1 else 0) =
      ((Finset.univ.filter (fun g : Γ => g • x₀ = x₀)).card : ℂ) • u := by
    change (∑ g, (if g • x₀ = x₀ then (1 : ℂ) else 0) • ρ g u) = _
    simp only [ite_smul, one_smul, zero_smul]
    calc
      _ = ∑ g : Γ, if g • x₀ = x₀ then u else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        split_ifs with hg
        · exact hfixed g hg
        · rfl
      _ = _ := by rw [← Finset.sum_filter]; simp [Nat.cast_smul_eq_nsmul]
  rw [he]
  apply smul_ne_zero _ hu
  norm_cast
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨1, by simp⟩

/- Frobenius occurrence at the precise stabilizer level, proved by an
explicit intertwiner rather than postulated decomposition. -/
omit [Fintype X] in
theorem orbitSynthesis_surjective (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (u : V) (hu : u ≠ 0) (x₀ : X)
    (hfixed : ∀ g : Γ, g • x₀ = x₀ → ρ g u = u) :
    Function.Surjective (orbitSynthesis ρ u x₀) := by
  classical
  let S : Subrepresentation ρ :=
    { toSubmodule := (orbitSynthesis ρ u x₀).range
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨f, rfl⟩ := hv
        exact ⟨(fun x => f (g⁻¹ • x)), orbitSynthesis_covariant ρ u x₀ g f⟩ }
  have hne : S ≠ ⊥ := by
    intro he
    have hm : orbitSynthesis ρ u x₀ (fun x => if x = x₀ then 1 else 0) ∈ S :=
      ⟨_, rfl⟩
    rw [he] at hm
    exact orbitSynthesis_delta_ne_zero ρ u hu x₀ hfixed hm
  have he : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hne
  apply LinearMap.range_eq_top.mp
  exact congrArg Subrepresentation.toSubmodule he

/- The subgroup average is fixed under that subgroup, with no assumptions on
interrelations between different coordinate subgroups. -/
omit [Fintype Γ] in
theorem subgroup_sum_fixed (ρ : Representation ℂ Γ V) (K : Subgroup Γ) [Fintype K] (u : V)
    (k : K) : ρ k.val (∑ h : K, ρ h.val u) = ∑ h : K, ρ h.val u := by
  simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft k) (fun h : K => ρ h.val u)

/- Averaging a synthesis over a larger stabilizer acts only on the cyclic
vector whenever the coefficient function forgets those coordinates. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_subgroup_average (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (K : Subgroup Γ) [Fintype K] (f : X → ℂ)
    (hf : ∀ (g : Γ) (k : K), f ((g*k.val) • x₀) = f (g • x₀)) :
    orbitSynthesis ρ (∑ k : K, ρ k.val u) x₀ f =
      (Fintype.card K : ℂ) • orbitSynthesis ρ u x₀ f := by
  change (∑ g, f (g • x₀) • ρ g (∑ k : K, ρ k.val u)) = _
  simp only [map_sum, Finset.smul_sum, ← Module.End.mul_apply, ← map_mul]
  rw [Finset.sum_comm]
  have hk (k : K) : (∑ g : Γ, f (g • x₀) • ρ (g*k.val) u) = orbitSynthesis ρ u x₀ f := by
    calc
      _ = ∑ g : Γ, f ((g*k.val) • x₀) • ρ (g*k.val) u := by
        simp only [hf]
      _ = _ := Equiv.sum_comp (Equiv.mulRight k.val) (fun g => f (g • x₀) • ρ g u)
  simp only [hk, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/- Exact proper-coordinate annihilation used in source04:eq7: it is the
absence of fixed vectors one level earlier, not a partial cancellation claim. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_eq_zero_of_no_fixed (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (K : Subgroup Γ) [Fintype K]
    (hnof : ∀ v : V, (∀ k : K, ρ k.val v = v) → v = 0)
    (f : X → ℂ) (hf : ∀ (g : Γ) (k : K), f ((g*k.val) • x₀) = f (g • x₀)) :
    orbitSynthesis ρ u x₀ f = 0 := by
  have hzero : (∑ k : K, ρ k.val u) = 0 := hnof _ (subgroup_sum_fixed ρ K u)
  have h := orbitSynthesis_subgroup_average ρ u x₀ K f hf
  rw [hzero] at h
  have hz : orbitSynthesis ρ (0 : V) x₀ f = 0 := by simp [orbitSynthesis]
  rw [hz] at h
  apply (smul_eq_zero.mp h.symm).resolve_left
  exact_mod_cast Fintype.card_ne_zero
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V]

@[simp] theorem signScalar_mul_self (g : Equiv.Perm Ω) :
    signScalar g * signScalar g = (1 : ℂ) := by
  simp only [signScalar_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h <;> rw [h] <;> norm_num

/- Tensoring with the ordinary sign character, on exactly the same space. -/
def signTwist (ρ : Representation ℂ (Equiv.Perm Ω) V) :
    Representation ℂ (Equiv.Perm Ω) V where
  toFun g := signScalar g • ρ g
  map_one' := by simp
  map_mul' g h := by simp only [map_mul, smul_mul_smul_comm]

@[simp] theorem signTwist_apply (ρ : Representation ℂ (Equiv.Perm Ω) V)
    (g : Equiv.Perm Ω) (v : V) : signTwist ρ g v = signScalar g • ρ g v := rfl

/- The same invariant subspaces for ρ and its sign twist. -/
def untwistSubrep (ρ : Representation ℂ (Equiv.Perm Ω) V)
    (S : Subrepresentation (signTwist ρ)) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule := by
    intro g v hv
    have h := S.toSubmodule.smul_mem (signScalar g) (S.apply_mem_toSubmodule g hv)
    simpa only [signTwist_apply, smul_smul, signScalar_mul_self, one_smul] using h

instance signTwist_irreducible [FiniteDimensional ℂ V] (ρ : Representation ℂ (Equiv.Perm Ω) V)
    [ρ.IsIrreducible] : (signTwist ρ).IsIrreducible := by
  have : Nontrivial V := irreducible_nontrivial ρ
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro S
    rcases eq_bot_or_eq_top (untwistSubrep ρ S) with h | h
    · left
      have hh := congrArg Subrepresentation.toSubmodule h
      exact Subrepresentation.toSubmodule_injective hh
    · right
      have hh := congrArg Subrepresentation.toSubmodule h
      exact Subrepresentation.toSubmodule_injective hh

/- Either the original representation or its sign twist has a first placement
level k with both quantitative dimension bounds and no earlier fixed vector. -/
theorem exists_minimal_fixed_vector [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (ε : Bool) (k t : ℕ) (A : Finset Ω) (u : V),
      let τ := if ε then signTwist ρ else ρ
      A.card = k ∧ k ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      Module.finrank ℂ V ≤ (Fintype.card Ω)^k ∧ u ≠ 0 ∧
      (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → τ g u = u) ∧
      ∀ B : Finset Ω, B.card < k → ∀ v : V,
        (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → τ g v = v) → v = 0 := by
  obtain ⟨k,t,A,u,hA,hk,ht,hd,hu,hchar,hmin⟩ := exists_minimal_sparse_line ρ
  rcases hchar with htriv | hsign
  · refine ⟨false,k,t,A,u,hA,hk,ht,hd,hu,htriv, ?_⟩
    intro B hB v hv
    exact hmin B hB v (fun g hg => ⟨1, by simpa using hv g hg⟩)
  · refine ⟨true,k,t,A,u,hA,hk,ht,hd,hu, ?_, ?_⟩
    · intro g hg
      simp only [↓reduceIte, signTwist_apply, hsign g hg, smul_smul,
        signScalar_mul_self, one_smul]
    · intro B hB v hv
      apply hmin B hB v
      intro g hg
      refine ⟨signScalar g, ?_⟩
      have h := congrArg (fun w : V => signScalar g • w) (hv g hg)
      simpa only [Bool.true_eq, ↓reduceIte, signTwist_apply, smul_smul,
        signScalar_mul_self, one_smul] using h
end CoordinateSweeps.SparseDimension

namespace CoordinateSweeps.PlacementOccurrence
open SparseDimension
variable {Ω I V : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype I] [AddCommGroup V] [Module ℂ V]

/- Stabilizer of the small placement coordinates really is the pointwise
stabilizer of their image, so the exact earlier-level hypothesis applies. -/
theorem synthesis_kills_proper_coordinates
    (ρ : Representation ℂ (Equiv.Perm Ω) V) (u : V) (x₀ : I ↪ Ω)
    (hnof : ∀ B : Finset Ω, B.card < Fintype.card I → ∀ v : V,
      (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → ρ g v = v) → v = 0)
    (A : Finset I) (hA : A ≠ Finset.univ) (f : (I ↪ Ω) → ℂ)
    (hf : ∀ x y : I ↪ Ω, (∀ i ∈ A, x i = y i) → f x = f y) :
    orbitSynthesis ρ u x₀ f = 0 := by
  classical
  let B : Finset Ω := A.image x₀
  have hB : B.card < Fintype.card I := by
    dsimp [B]
    rw [Finset.card_image_of_injective _ x₀.injective]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  apply orbitSynthesis_eq_zero_of_no_fixed ρ u x₀ (fixSet B)
  · intro v hv
    exact hnof B hB v (fun g hg => hv ⟨g,hg⟩)
  · intro g k
    apply hf
    intro i hi
    change g (k.val (x₀ i)) = g (x₀ i)
    rw [k.property (x₀ i) (Finset.mem_image_of_mem _ hi)]
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.Placement
variable {I U X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
/- The adjoint of a synthesis map annihilating all cylinder functions lands
in the exact alternating-kernel top space. Complex conjugation is essential. -/
omit [DecidableEq I] in
theorem conjTranspose_mulVec_mem_top {D : Type*} [Fintype D]
    (coords : Y → I → U) (B : Matrix D Y ℂ)
    (hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
      DependsOn coords A f → B.mulVec f = 0) (w : D → ℂ) :
    B.conjTranspose.mulVec w ∈ topSpace coords := by
  intro A hA f hf
  have hfstar : DependsOn coords A (fun y => star (f y)) :=
    fun y y' h => congrArg star (hf y y' h)
  have hz := hB A hA (fun y => star (f y)) hfstar
  have hsum (d : D) : ∑ y, f y * star (B d y) = 0 := by
    have h := congrArg star (congrFun hz d)
    simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul,
      star_star, Pi.zero_apply, star_zero, mul_comm] using h
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hsum, zero_mul]
  exact Finset.sum_const_zero

/- Matrix form of top-level compression, ready for Schur norm transfer. -/
omit [DecidableEq I] [Fintype X] in
theorem alternatingKernel_mul_conjTranspose {D : Type*} [Fintype D]
    (coords : Y → I → U) (s : ℝ) (hs : s ≠ 0)
    (p : Finset I → X → Y → ℝ)
    (hp : ∀ A x, DependsOn coords A (fun y => (p A x y : ℂ)))
    (B : Matrix D Y ℂ)
    (hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
      DependsOn coords A f → B.mulVec f = 0) :
    alternatingKernel s p * B.conjTranspose =
      (show Matrix X Y ℂ from fun x y => (p Finset.univ x y : ℂ)) * B.conjTranspose := by
  apply Matrix.ext
  intro x d
  have hv : (fun y => B.conjTranspose y d) ∈ topSpace coords := by
    classical
    have h := conjTranspose_mulVec_mem_top coords B hB (Pi.single d 1)
    have he : B.conjTranspose.mulVec (Pi.single d 1) = (fun y => B.conjTranspose y d) := by
      ext y; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [he] at h
    exact h
  exact congrFun (alternatingKernel_mulVec_top coords s hs p hp hv) x
end CoordinateSweeps.Placement

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
variable {Γ X : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]

def actionMatrix : Γ →* Matrix X X ℂ :=
  Matrix.permMatrixHom.comp (MulAction.toPermHom Γ X)

omit [Fintype Γ] in
lemma actionMatrix_mulVec (g : Γ) (f : X → ℂ) :
    (actionMatrix g).mulVec f=fun x => f (g⁻¹ • x) := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ).mulVec f = _
  rw [Matrix.permMatrix_mulVec]
  rfl

omit [Fintype Γ] in
lemma actionMatrix_unitary (g : Γ) : (actionMatrix (X := X) g).conjTranspose*actionMatrix g=1 := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ).conjTranspose*
    ((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ=1
  rw [Matrix.conjTranspose_permMatrix,inv_inv,← Matrix.permMatrix_mul,inv_mul_cancel,Matrix.permMatrix_one]

def synthesisMatrix (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) :
    Matrix (Fin ρ.dimension) X ℂ := LinearMap.toMatrix' (orbitSynthesis ρ.asRepresentation u x₀)

lemma synthesisMatrix_mulVec (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) (f : X → ℂ) :
    (synthesisMatrix ρ u x₀).mulVec f=orbitSynthesis ρ.asRepresentation u x₀ f :=
  LinearMap.toMatrix'_mulVec _ _

lemma synthesisMatrix_covariant (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) (g : Γ) :
    synthesisMatrix ρ u x₀*actionMatrix g=ρ.matrix g*synthesisMatrix ρ u x₀ := by
  change (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (synthesisMatrix ρ u x₀) (actionMatrix g))=
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (ρ.matrix g) (synthesisMatrix ρ u x₀))
  apply Matrix.mulVec_injective
  funext f
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,actionMatrix_mulVec,
    synthesisMatrix_mulVec,synthesisMatrix_mulVec]
  exact orbitSynthesis_covariant ρ.asRepresentation u x₀ g f

lemma synthesisMatrix_ne_zero (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : X)
    (hfixed : ∀ g : Γ, g • x₀=x₀ → ρ.asRepresentation g u=u) : synthesisMatrix ρ u x₀ ≠ 0 := by
  intro h
  have hh := orbitSynthesis_delta_ne_zero ρ.asRepresentation u hu x₀ hfixed
  apply hh
  rw [← synthesisMatrix_mulVec,h,Matrix.zero_mulVec]

end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
open Placement
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

/- Source04:eq7 at its exact first placement level, with a constructed
nonzero synthesis intertwiner and Schur norm transfer. -/
omit [DecidableEq I] in
theorem first_level_norm_le (ρ : UnitaryIrrep (Equiv.Perm Ω))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : I ↪ Ω)
    (hfixed : ∀ g : Equiv.Perm Ω, (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset Ω, A.card < Fintype.card I → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → Equiv.Perm Ω)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → (I ↪ Ω) → (I ↪ Ω) → ℝ)
    (hp : ∀ A x, DependsOn (fun y : I ↪ Ω => y) A (fun y => (p A x y : ℂ)))
    (hfull : (show Matrix (I ↪ Ω) (I ↪ Ω) ℂ from fun x y => (p Finset.univ x y : ℂ))=
      ∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a)) :
    ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤
      ‖alternatingKernel s p‖ := by
  let B : Matrix (Fin ρ.dimension) (I ↪ Ω) ℂ := synthesisMatrix ρ u x₀
  have hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : (I ↪ Ω) → ℂ,
      DependsOn (fun y : I ↪ Ω => y) A f → B.mulVec f=0 := by
    intro A hA f hf
    rw [synthesisMatrix_mulVec]
    exact synthesis_kills_proper_coordinates ρ.asRepresentation u x₀ hnof A hA f hf
  have hne : B ≠ 0 := synthesisMatrix_ne_zero ρ u hu x₀ (by
    intro σ hσ
    exact hfixed σ (fun i => congrArg (fun x : I ↪ Ω => x i) hσ))
  have hnorm : ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤ ‖alternatingKernel s p‖ := by
    apply ρ.norm_le_compression (actionMatrix (X := I ↪ Ω)) actionMatrix_unitary B hne
      (synthesisMatrix_covariant ρ u x₀)
    rw [alternatingKernel_mul_conjTranspose (fun y : I ↪ Ω => y) s hs p hp B hB,hfull,
      Matrix.sum_mul,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    exact ρ.adjoint_intertwines _ actionMatrix_unitary B (synthesisMatrix_covariant ρ u x₀) (g a)
  exact hnorm

end CoordinateSweeps.PlacementOccurrence

open scoped Matrix.Norms.L2Operator

namespace CoordinateSweeps.PlacementOccurrence
variable {Γ X : Type*} [Group Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]
lemma actionMatrix_entry (g : Γ) (x y : X) : actionMatrix (X := X) g x y=if g⁻¹ • x=y then 1 else 0 := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ) x y=_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix]
end CoordinateSweeps.PlacementOccurrence

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
