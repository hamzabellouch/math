import OAI.GroupTheory.Kervaire.CurrentPullback

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
abbrev Mat (I : Type*) := Matrix I I ℂ
abbrev Alg (K R : Type*) := Mat K × Mat (K ⊕ R) × Mat R
abbrev Horizontal (K R : Type*) [Fintype K] [Fintype R] :=
  skewAdjoint.submodule ℝ (Mat K) × skewAdjoint.submodule ℝ (Mat R) × Matrix R K ℂ

/-- Diagonal corner inclusions, as continuous real linear maps. -/
def in11 : Mat K →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ fromBlocks A 0 0 0
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }
def in22 : Mat R →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B ↦ fromBlocks 0 0 0 B
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }

def diag (A : Mat K) (B : Mat R) : Mat (K ⊕ R) := fromBlocks A 0 0 B

def off (Z : Matrix R K ℂ) : Mat (K ⊕ R) := fromBlocks 0 (-Zᴴ) Z 0

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma off_skew (Z : Matrix R K ℂ) : star (off Z) = -off Z := by
  ext i j
  cases i <;> cases j <;> simp [off, Matrix.star_apply, Matrix.conjTranspose_apply]

lemma off_bracket (Z Y : Matrix R K ℂ) :
    off Z * off Y - off Y * off Z =
      diag (-Zᴴ*Y+Yᴴ*Z) (-Z*Yᴴ+Y*Zᴴ) := by
  simp only [off, diag, fromBlocks_multiply, mul_zero, zero_add, add_zero]
  ext i j
  cases i <;> cases j <;> simp [fromBlocks, sub_eq_add_neg]

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma diag_star (A : Mat K) (B : Mat R) : star (diag A B) = diag (star A) (star B) := by
  ext i j
  cases i <;> cases j <;> simp [diag, Matrix.star_apply]

omit [DecidableEq K] [DecidableEq R] in
lemma diag_mul (A C : Mat K) (B D : Mat R) : diag A B * diag C D = diag (A*C) (B*D) := by
  simp [diag, fromBlocks_multiply]

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma diag_sub (A C : Mat K) (B D : Mat R) : diag A B - diag C D = diag (A-C) (B-D) := by
  ext i j
  cases i <;> cases j <;> simp [diag, fromBlocks]

/-- The incidence map is polynomial in the redundant compact-group coordinates. -/
def incidence (f : ℝ × Mat K → Mat (K ⊕ R)) (p : ℝ × Alg K R) : Mat (K ⊕ R) :=
  f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1

omit [DecidableEq K] [DecidableEq R] in
lemma diag_eq_corner (A : Mat K) (B : Mat R) : diag A B = in11 A + in22 B := by
  ext i j
  cases i <;> cases j <;> simp [diag, in11, in22, fromBlocks]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

omit [Fintype K] [Fintype R] in
lemma diag_one : diag (1 : Mat K) (1 : Mat R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [diag, fromBlocks, one_apply]

lemma diag_unitary {A : Mat K} {B : Mat R} (hA : A ∈ unitary (Mat K))
    (hB : B ∈ unitary (Mat R)) : diag A B ∈ unitary (Mat (K ⊕ R)) := by
  rw [Unitary.mem_iff] at hA hB ⊢
  simp only [diag_star, diag_mul, hA.1, hA.2, hB.1, hB.2, diag_one, and_self]

lemma unitary_alg_parts (p : unitary (Alg K R)) :
    (p.val.1 ∈ unitary (Mat K)) ∧ (p.val.2.1 ∈ unitary (Mat (K ⊕ R))) ∧
      (p.val.2.2 ∈ unitary (Mat R)) := by
  have h := Unitary.mem_iff.mp p.property
  exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
    ⟨congrArg (Prod.fst ∘ Prod.snd) h.1, congrArg (Prod.fst ∘ Prod.snd) h.2⟩,
    ⟨congrArg (Prod.snd ∘ Prod.snd) h.1, congrArg (Prod.snd ∘ Prod.snd) h.2⟩⟩

lemma incidence_unitary {f : ℝ × Mat K → Mat (K ⊕ R)}
    (hf : ∀ t (X : unitary (Mat K)), f (t,(X : Mat K)) ∈ unitary (Mat (K ⊕ R)))
    (t : ℝ) (p : unitary (Alg K R)) : incidence f (t,(p : Alg K R)) ∈ unitary (Mat (K ⊕ R)) := by
  obtain ⟨hX,hQ,hT⟩ := unitary_alg_parts p
  exact (unitary _).mul_mem ((unitary _).mul_mem ((unitary _).mul_mem (hf t ⟨_,hX⟩) hQ)
    (diag_unitary ((unitary _).one_mem) (Unitary.star_mem hT))) (Unitary.star_mem hQ)

/-- A diagonal change of the frame is absorbed by a fiber-unitary direction. -/
lemma frame_diagonal_commutator (T : unitary (Mat R)) (U : Mat K) (V : Mat R) :
    diag U V * diag 1 (star (T : Mat R)) - diag 1 (star (T : Mat R)) * diag U V =
      in22 (V * star (T : Mat R) - star (T : Mat R) * V) := by
  rw [diag_mul, diag_mul, diag_sub]
  simp only [mul_one, one_mul, sub_self, diag, in22]
  rfl

def compensated (T : unitary (Mat R)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    skewAdjoint.submodule ℝ (Mat R) :=
  ⟨star (T : Mat R) * V * T - V, by
    change star (star (T : Mat R) * (V : Mat R) * T - V) = -_
    rw [star_sub, star_mul, star_mul, star_star, V.property]
    noncomm_ring⟩

lemma compensated_star_mul (T : unitary (Mat R)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    star ((T : Mat R) * (compensated T V : Mat R)) =
      (V : Mat R) * star (T : Mat R) - star (T : Mat R) * V := by
  change star ((T : Mat R) * (star (T : Mat R) * (V : Mat R) * T - V)) = _
  rw [mul_sub, ← mul_assoc, ← mul_assoc, (Unitary.mem_iff.mp T.property).2, one_mul,
    star_sub, star_mul, star_mul, V.property]
  noncomm_ring

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

/-- The positive invariant trace pairing on skew-Hermitian matrices. -/
def pairing : LinearMap.BilinForm ℝ S where
  toFun a :=
    { toFun := fun b ↦ -(Matrix.trace ((a : M) * (b : M))).re
      map_add' b c := by
        change -(trace ((a : M) * ((b : M) + (c : M)))).re =
          -(trace ((a : M)*(b : M))).re + -(trace ((a : M)*(c : M))).re
        rw [mul_add, trace_add, Complex.add_re]
        ring
      map_smul' := by intros; simp }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change -(trace (((a : M)+(b : M))*(c : M))).re =
      -(trace ((a : M)*(c : M))).re + -(trace ((b : M)*(c : M))).re
    rw [add_mul, trace_add, Complex.add_re]
    ring
  map_smul' r a := by ext c; simp

lemma pairing_apply (a b : S) : pairing a b = -(Matrix.trace ((a : M)*(b : M))).re := rfl

lemma pairing_symm : LinearMap.IsSymm (pairing (I := I)) := by
  constructor
  intro a b
  simp only [pairing_apply, trace_mul_comm (a : M) (b : M), RingHom.id_apply]

lemma pairing_self (a : S) : pairing a a = (Matrix.trace ((a : M)ᴴ*(a : M))).re := by
  have ha : (a : M)ᴴ = -(a : M) := a.property
  simp [ha, pairing_apply]

lemma pairing_self_eq_zero_iff (a : S) : pairing a a = 0 ↔ a = 0 := by
  rw [pairing_self]
  have hp := Complex.nonneg_iff.mp (posSemidef_conjTranspose_mul_self (a : M)).trace_nonneg
  constructor
  · intro h
    apply Subtype.ext
    apply trace_conjTranspose_mul_self_eq_zero_iff.mp
    apply Complex.ext h
    exact hp.2.symm
  · rintro rfl
    simp

def bracket (a b : S) : S :=
  ⟨(a : M)*(b : M)-(b : M)*(a : M), by
    change star ((a : M)*(b : M)-(b : M)*(a : M)) = -_
    rw [star_sub, star_mul, star_mul, a.property, b.property]
    simp only [neg_mul_neg]
    abel⟩

lemma bracket_pair_left (a b : S) : pairing (bracket a b) a = 0 := by
  change -(trace (((a : M)*(b : M)-(b : M)*(a : M))*(a : M))).re = 0
  rw [sub_mul, trace_sub, trace_mul_cycle (b : M) (a : M) (a : M)]
  simp

lemma bracket_pair_right (a b : S) : pairing (bracket a b) b = 0 := by
  change -(trace (((a : M)*(b : M)-(b : M)*(a : M))*(b : M))).re = 0
  rw [sub_mul, trace_sub, trace_mul_cycle (a : M) (b : M) (b : M)]
  simp

/-- Orthogonal bases exist without selecting an orientation or changing matrix norms. -/
lemma exists_orthogonal_basis : ∃ b : Basis (Fin (Module.finrank ℝ S)) ℝ S,
    (pairing (I := I)).IsOrthoᵢ b :=
  LinearMap.BilinForm.exists_orthogonal_basis pairing_symm

lemma pairing_eq_repr_mul {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (a : S) (i : J) :
    pairing a (b i) = b.repr a i * pairing (b i) (b i) := by
  classical
  conv_lhs => rw [← b.sum_repr a]
  simp only [LinearMap.map_sum₂, LinearMap.map_smul₂, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · intro j _ hji
    rw [hb hji, mul_zero]
  · simp

lemma bracket_repr_left {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (i j : J) :
    b.repr (bracket (b i) (b j)) i = 0 := by
  have h := bracket_pair_left (b i) (b j)
  rw [pairing_eq_repr_mul b hb] at h
  exact (mul_eq_zero.mp h).resolve_right (fun hz ↦ b.ne_zero i ((pairing_self_eq_zero_iff _).mp hz))

lemma bracket_repr_right {J : Type*} [Fintype J] (b : Basis J ℝ S)
    (hb : (pairing (I := I)).IsOrthoᵢ b) (i j : J) :
    b.repr (bracket (b i) (b j)) j = 0 := by
  have h := bracket_pair_right (b i) (b j)
  rw [pairing_eq_repr_mul b hb] at h
  exact (mul_eq_zero.mp h).resolve_right (fun hz ↦ b.ne_zero j ((pairing_self_eq_zero_iff _).mp hz))

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The redundant compact group has a canonically chosen horizontal frame. -/
def direction : Horizontal K R →ₗ[ℝ] skewAdjoint.submodule ℝ (Alg K R) where
  toFun h := ⟨((h.1 : Mat K),off h.2.2,(h.2.1 : Mat R)), by
    change (star (h.1 : Mat K),star (off h.2.2),star (h.2.1 : Mat R)) = -_
    rw [h.1.property, h.2.1.property, off_skew]
    rfl⟩
  map_add' h g := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    change off (h.2.2+g.2.2) = off h.2.2+off g.2.2
    simp only [off, conjTranspose_add, neg_add_rev, fromBlocks_add]
    congr 1 <;> first | simp only [zero_add] | exact add_comm _ _
  map_smul' c h := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    ext i j
    cases i <;> cases j <;> simp [off, fromBlocks, conjTranspose_smul]

/-- Lower block of the bracket of two off-diagonal skew matrices. -/
def rectBracket (Z Y : Matrix R K ℂ) : skewAdjoint.submodule ℝ (Mat R) :=
  ⟨-Z*Yᴴ+Y*Zᴴ, by
    change (-Z*Yᴴ+Y*Zᴴ)ᴴ = -(-Z*Yᴴ+Y*Zᴴ)
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_neg,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel⟩

omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_left (Y : Matrix R K ℂ) : rectBracket 0 Y = 0 := by
  apply Subtype.ext
  simp [rectBracket]
omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_right (Z : Matrix R K ℂ) : rectBracket Z 0 = 0 := by
  apply Subtype.ext
  simp [rectBracket]
@[simp] lemma compensated_zero (T : unitary (Mat R)) : compensated T 0 = 0 := by
  apply Subtype.ext
  simp [compensated]
@[simp] lemma skewBracket_zero_left (b : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket 0 b = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]
@[simp] lemma skewBracket_zero_right (a : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket a 0 = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]

/-- The defect of horizontal integrability is vertical and is absorbed by T. -/
def effectiveBracket (T : unitary (Mat R)) (h g : Horizontal K R) : Horizontal K R :=
  (KervaireSkewTrace.bracket h.1 g.1,
   KervaireSkewTrace.bracket h.2.1 g.2.1 + compensated T (rectBracket h.2.2 g.2.2),0)

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

def horizontalBasis : Basis (IK ⊕ IR ⊕ IZ) ℝ (Horizontal K R) := bK.prod (bR.prod bZ)

omit [Fintype IZ] in
lemma effectiveBracket_repr_left (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (T : unitary (Mat R)) (i j : IK ⊕ IR ⊕ IZ) :
    (horizontalBasis bK bR bZ).repr
      (effectiveBracket T (horizontalBasis bK bR bZ i) (horizontalBasis bK bR bZ j)) i = 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [horizontalBasis, Basis.prod_apply, effectiveBracket,
      KervaireSkewTrace.bracket_repr_left bK hbK, KervaireSkewTrace.bracket_repr_left bR hbR]

omit [Fintype IZ] in
lemma effectiveBracket_repr_right (hbK : (KervaireSkewTrace.pairing (I := K)).IsOrthoᵢ bK)
    (hbR : (KervaireSkewTrace.pairing (I := R)).IsOrthoᵢ bR)
    (T : unitary (Mat R)) (i j : IK ⊕ IR ⊕ IZ) :
    (horizontalBasis bK bR bZ).repr
      (effectiveBracket T (horizontalBasis bK bR bZ i) (horizontalBasis bK bR bZ j)) j = 0 := by
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [horizontalBasis, Basis.prod_apply, effectiveBracket,
      KervaireSkewTrace.bracket_repr_right bK hbK, KervaireSkewTrace.bracket_repr_right bR hbR]

end KervaireIncidenceCurrent

end

end OAI
