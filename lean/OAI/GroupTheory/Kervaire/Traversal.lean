import OAI.GroupTheory.Kervaire.FixedSpaces

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
open scoped ComplexOrder
open scoped ContDiff
open NormedSpace Complex
open scoped ContDiff Matrix.Norms.L2Operator
open MeasureTheory Set Filter
open scoped Topology ContDiff
open Matrix

namespace KervaireTraversal

section
open Matrix KervaireFixed KervaireSignPairing
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K]
abbrev Slots (I K : Type*) := (K ⊕ K) × I

def coordinates (s : I → ℤ) : ((K × I) ⊕ (K × I)) ≃ Slots I K where
  toFun p := match p with
    | .inl (k,i) => (if s i = 1 then Sum.inl k else Sum.inr k, i)
    | .inr (k,i) => (if s i = 1 then Sum.inr k else Sum.inl k, i)
  invFun p := match p with
    | (.inl k,i) => if s i = 1 then Sum.inl (k,i) else Sum.inr (k,i)
    | (.inr k,i) => if s i = 1 then Sum.inr (k,i) else Sum.inl (k,i)
  left_inv p := by rcases p with ⟨k,i⟩ | ⟨k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]
  right_inv p := by rcases p with ⟨k|k,i⟩ <;> by_cases h : s i = 1 <;> simp [h]

def mixer (X : Matrix K K ℂ) : Matrix (Slots I K) (Slots I K) ℂ :=
  blockDiagonal fun _ : I => fromBlocks 0 (star X) X 0

def exchange (P : Matrix (K × I) (K × I) ℂ) :
    Matrix ((K × I) ⊕ (K × I)) ((K × I) ⊕ (K × I)) ℂ := fromBlocks 0 (star P) P 0

omit [Fintype I] [Fintype K] in
lemma exchange_star (P : Matrix (K × I) (K × I) ℂ) : star (exchange P) = exchange P := by
  simp [exchange, star_eq_conjTranspose, fromBlocks_conjTranspose]

lemma exchange_sq (P : unitary (Matrix (K × I) (K × I) ℂ)) :
    exchange (P : Matrix (K × I) (K × I) ℂ) * exchange (P : Matrix (K × I) (K × I) ℂ) = 1 := by
  simp only [exchange, fromBlocks_multiply, zero_mul,mul_zero,add_zero,zero_add]
  rw [P.property.1,P.property.2]
  exact fromBlocks_one

lemma exchange_unitary (P : unitary (Matrix (K × I) (K × I) ℂ)) :
    exchange (P : Matrix (K × I) (K × I) ℂ) ∈ unitary _ := by
  rw [Unitary.mem_iff,exchange_star,exchange_sq]
  exact ⟨rfl,rfl⟩

omit [Fintype I] [Fintype K] in
lemma mixer_coordinates (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (X : Matrix K K ℂ) :
    Matrix.reindex (coordinates (K := K) s).symm (coordinates (K := K) s).symm (mixer X) =
      fromBlocks 0 (signedMatrix (fun i ↦ -s i) X) (star (signedMatrix (fun i ↦ -s i) X)) 0 := by
  ext (⟨k,i⟩ | ⟨k,i⟩) (⟨l,j⟩ | ⟨l,j⟩) <;>
    rcases hs i with hi | hi <;> rcases hs j with hj | hj <;>
    by_cases hij : i = j <;>
    simp_all [Matrix.reindex_apply,coordinates,mixer,signedMatrix,
      blockDiagonal_apply,fromBlocks,eq_comm,Matrix.star_apply]

lemma signedMatrix_unitary (s : I → ℤ) (X : unitary (Matrix K K ℂ)) :
    signedMatrix s (X : Matrix K K ℂ) ∈ unitary (Matrix (K × I) (K × I) ℂ) := by
  have hu (i : I) : (if s i = 1 then (X : Matrix K K ℂ) else star (X : Matrix K K ℂ)) ∈ unitary _ := by
    split
    · exact X.property
    · exact Unitary.star_mem X.property
  constructor <;>
    simp only [signedMatrix,star_eq_conjTranspose,blockDiagonal_conjTranspose, ← blockDiagonal_mul]
  · convert (blockDiagonal_one (m := K) (o := I) (α := ℂ)) using 1
    exact congrArg blockDiagonal (funext fun i ↦ (hu i).1)
  · convert (blockDiagonal_one (m := K) (o := I) (α := ℂ)) using 1
    exact congrArg blockDiagonal (funext fun i ↦ (hu i).2)

lemma exists_mixer_fixed [Nonempty K] (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (P : unitary (Matrix (K × I) (K × I) ℂ)) :
    ∃ X : unitary (Matrix K K ℂ),
      2 * Fintype.card K ≤ fixedDim (mixer (X : Matrix K K ℂ) *
        Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) := by
  have hn (i : I) : -s i = 1 ∨ -s i = -1 := by rcases hs i with h | h <;> simp [h]
  have hnsum : (∑ i, -s i) = 1 ∨ (∑ i, -s i) = -1 := by
    rw [Finset.sum_neg_distrib]
    rcases hsum with h | h <;> simp [h]
  obtain ⟨X,hX⟩ := exists_signed_fixed (fun i ↦ -s i) hn hnsum P
  let D : unitary (Matrix (K × I) (K × I) ℂ) :=
    ⟨signedMatrix (fun i ↦ -s i) (X : Matrix K K ℂ), signedMatrix_unitary _ X⟩
  have hD := two_mul_fixedDim_le D P
  refine ⟨X,?_⟩
  have hr := fixedDim_reindex (coordinates (K := K) s).symm
    (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ)))
  have hm : Matrix.reindex (coordinates (K := K) s).symm (coordinates s).symm
      (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) =
      Matrix.reindex (coordinates s).symm (coordinates s).symm (mixer (X : Matrix K K ℂ)) * exchange (P : Matrix (K × I) (K × I) ℂ) := by
    rw [show Matrix.reindex (coordinates s).symm (coordinates s).symm
      (mixer (X : Matrix K K ℂ) * Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) =
      Matrix.reindex (coordinates s).symm (coordinates s).symm (mixer (X : Matrix K K ℂ)) *
      Matrix.reindex (coordinates s).symm (coordinates s).symm (Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ))) from
      map_mul (Matrix.reindexAlgEquiv ℂ ℂ (coordinates s).symm) _ _]
    congr 1
    ext i j
    simp [Matrix.reindex_apply]
  rw [hm,mixer_coordinates s hs] at hr
  rw [← hr]
  exact (Nat.mul_le_mul_left 2 hX).trans hD
end

section
open Matrix KervaireFixed
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Every unitary selfadjoint exchange has a unitary off-diagonal block. -/
lemma offDiagonal_representation (N : Matrix (E ⊕ E) (E ⊕ E) ℂ)
    (hNs : star N = N) (hNu : N ∈ unitary (Matrix (E ⊕ E) (E ⊕ E) ℂ))
    (h₀ : ∀ i j, N (.inl i) (.inl j) = 0)
    (h₁ : ∀ i j, N (.inr i) (.inr j) = 0) :
    ∃ P : unitary (Matrix E E ℂ), N = fromBlocks 0 (star (P : Matrix E E ℂ)) P 0 := by
  let P : Matrix E E ℂ := fun i j ↦ N (.inr i) (.inl j)
  have he : N = fromBlocks 0 (star P) P 0 := by
    ext (i|i) (j|j)
    · exact h₀ i j
    · have h := congrFun (congrFun hNs (.inl i)) (.inr j)
      exact h.symm
    · rfl
    · exact h₁ i j
  have hp : P ∈ unitary (Matrix E E ℂ) := by
    have hs : N * N = 1 := by simpa only [hNs] using hNu.1
    rw [he,fromBlocks_multiply] at hs
    constructor
    · ext i j
      have h := congrFun (congrFun hs (.inl i)) (.inl j)
      simpa [Matrix.one_apply] using h
    · ext i j
      have h := congrFun (congrFun hs (.inr i)) (.inr j)
      simpa [Matrix.one_apply] using h
  exact ⟨⟨P,hp⟩,he⟩
end

open Matrix KervaireFixed
open scoped Classical
variable {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
local instance : DecidableEq (Slots I K) := Classical.decEq _

/-- The exact mixing step for an arbitrary scalar band involution exchanging
positive and negative traversal slots. No monomial restriction is imposed on X. -/
lemma exists_mixer_for_exchange (s : I → ℤ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hsum : (∑ i, s i) = 1 ∨ (∑ i, s i) = -1)
    (T : Matrix (Slots I K) (Slots I K) ℂ)
    (hTs : star T = T) (hTu : T ∈ unitary (Matrix (Slots I K) (Slots I K) ℂ))
    (h₀ : ∀ i j, T (coordinates s (.inl i)) (coordinates s (.inl j)) = 0)
    (h₁ : ∀ i j, T (coordinates s (.inr i)) (coordinates s (.inr j)) = 0) :
    ∃ X : unitary (Matrix K K ℂ), 2 * Fintype.card K ≤ fixedDim (mixer (X : Matrix K K ℂ) * T) := by
  let e := coordinates (K := K) s
  let N := Matrix.reindex e.symm e.symm T
  have hNs : star N = N := by
    dsimp only [N]
    rw [show star (Matrix.reindex e.symm e.symm T) = Matrix.reindex e.symm e.symm (star T) from
      Matrix.conjTranspose_reindex e.symm e.symm T,hTs]
  have hNu : N ∈ unitary (Matrix ((K × I) ⊕ (K × I)) ((K × I) ⊕ (K × I)) ℂ) :=
    (reindexUnitary e.symm ⟨T,hTu⟩).property
  obtain ⟨P,hP⟩ := offDiagonal_representation N hNs hNu h₀ h₁
  obtain ⟨X,hX⟩ := exists_mixer_fixed s hs hsum P
  refine ⟨X,?_⟩
  have he : Matrix.reindex (coordinates s) (coordinates s) (exchange (P : Matrix (K × I) (K × I) ℂ)) = T := by
    change Matrix.reindex e e (fromBlocks 0 (star (P : Matrix (K × I) (K × I) ℂ)) P 0) = T
    rw [← hP]
    ext i j
    simp [N,Matrix.reindex_apply]
  rwa [he] at hX
end KervaireTraversal

namespace KervaireMatrix
open Matrix KervaireRegular
open scoped Classical
variable {D : Type*} [Fintype D]

/-- The exact scalar weighted permutation attached to the oriented bands. -/
def monomial (θ : Equiv.Perm D) (u : D → ℂ) : Matrix D D ℂ :=
  fun i j ↦ if i = θ j then u j else 0

@[simp] lemma monomial_mul (θ τ : Equiv.Perm D) (u v : D → ℂ) :
    monomial θ u * monomial τ v = monomial (θ*τ) (fun j ↦ u (τ j)*v j) := by
  ext i j
  simp only [Matrix.mul_apply,monomial]
  rw [Finset.sum_eq_single (τ j)]
  · simp only
    change (if i = θ (τ j) then u (τ j) else 0) * v j =
      if i = θ (τ j) then u (τ j)*v j else 0
    split_ifs <;> simp
  · intro k _ hk
    simp [hk]
  · simp

omit [Fintype D] in
@[simp] lemma monomial_one [DecidableEq D] : monomial (Equiv.refl D) (fun _ ↦ 1) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [monomial,Matrix.one_apply,h]

omit [Fintype D] in
lemma monomial_star (θ : Equiv.Perm D) (u : D → ℂ) :
    star (monomial θ u) = monomial θ⁻¹ (fun j ↦ star (u (θ⁻¹ j))) := by
  ext i j
  simp only [Matrix.star_apply,monomial]
  by_cases h : j = θ i
  · subst j
    simp
  · have h' : i ≠ θ⁻¹ j := by
      intro he
      apply h
      simp [he]
    change i ≠ θ.symm j at h'
    simp [h,h']

lemma monomial_unitary [DecidableEq D] (θ : Equiv.Perm D) (u : D → ℂ)
    (hu : ∀ d, u d ∈ unitary ℂ) : monomial θ u ∈ unitary (Matrix D D ℂ) := by
  rw [Unitary.mem_iff,monomial_star,monomial_mul,monomial_mul]
  constructor
  · simp only [inv_mul_cancel]
    change monomial (Equiv.refl D) (fun j ↦ star (u (θ.symm (θ j))) * u j) = 1
    simpa only [Equiv.symm_apply_apply,funext (fun j ↦ (hu j).1)] using monomial_one (D := D)
  · simp only [mul_inv_cancel]
    change monomial (Equiv.refl D) (fun j ↦ u (θ.symm j) * star (u (θ.symm j))) = 1
    simpa only [funext (fun j ↦ (hu (θ.symm j)).2)] using monomial_one (D := D)

omit [Fintype D] in
lemma monomial_selfadjoint (θ : Equiv.Perm D) (hθ : ∀ d, θ (θ d) = d)
    (u : D → ℂ) (hu : ∀ d, u (θ d) = star (u d)) :
    star (monomial θ u) = monomial θ u := by
  have hi : θ⁻¹ = θ := by ext d; exact (θ.injective (by simp [hθ]))
  rw [monomial_star,hi]
  congr 1
  ext d
  simp [hu]

variable {A : Type*} [Group A]
lemma scalarTensor_monomial (θ : Equiv.Perm D) (u : D → ℂ) :
    scalarTensor (A := A) (monomial θ u) = weightedShift θ u (fun _ ↦ (1 : A)) := by
  ext f ⟨d,a⟩
  simp only [scalarTensor_apply,monomial]
  rw [Finset.sum_eq_single (θ⁻¹ d)]
  · simp [weightedShift,mul_apply_eq_comp]
  · intro j _ hj
    have h : d ≠ θ j := by intro he; apply hj; simp [he]
    simp [h]
  · simp
end KervaireMatrix

namespace KervaireMixing
open Matrix KervaireMatrix KervaireRegular KervaireFixed
open scoped Classical
variable {I K A : Type*} [Fintype I] [Fintype K] [Group A] [Nonempty I] [Nonempty K]
local instance : DecidableEq (Slot I K) := Classical.decEq _

lemma phase_upper_of_fixed (ρ : Equiv.Perm I) (a : I → A)
    (T : Matrix (Slot I K) (Slot I K) ℂ)
    (hT : T ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ)) (hTs : star T = T)
    (X : Matrix.unitaryGroup K ℂ)
    (hfix : 2 * Fintype.card K ≤ fixedDim (mixingMatrix (I := I) (X : Matrix K K ℂ) * T)) :
    let _ := isStarNormal_of_mem_unitary
      (mul_mem (S_unitary (K := K) ρ a) (scalarTensor_mem_unitary (A := A) hT))
    KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤
      3 / 2 * (Fintype.card I : ℝ) * Fintype.card K - Fintype.card K := by
  let Q := mixingMatrix (I := I) (X : Matrix K K ℂ)
  have hQ : Q ∈ unitary (Matrix (Slot I K) (Slot I K) ℂ) := by
    constructor
    · convert (mixingMatrix_unitary (I := I) X).1 using 1
      ext i j
      simp [Matrix.one_apply]
    · convert (mixingMatrix_unitary (I := I) X).2 using 1
      ext i j
      simp [Matrix.one_apply]
  have hQs : star Q = Q := mixingMatrix_star _
  have hconj : Q * (Q*T) * star Q = star (Q*T) := by
    have hsq : Q*Q = 1 := by simpa only [hQs] using hQ.1
    rw [← mul_assoc,hsq,one_mul,star_mul,hTs]
  have hb := phase_scalar_le_codim (A := A) (Q*T) Q (mul_mem hQ hT) hQ hconj
  let U : algebra (D := Slot I K) (A := A) :=
    ⟨S ρ a * J (I := I) (X : Matrix K K ℂ),
      (mem_algebra _).mpr ((S_commutant ρ a).mul (J_commutant _))⟩
  let V : algebra (D := Slot I K) (A := A) :=
    ⟨scalarTensor (A := A) (Q*T), (mem_algebra _).mpr (scalarTensor_mem_commutant _)⟩
  have hU : U ∈ unitary (algebra (D := Slot I K) (A := A)) :=
    (KervaireCentralizer.unitary_iff _ U).mpr (mul_mem (S_unitary ρ a) (J_unitary X))
  have hV : V ∈ unitary (algebra (D := Slot I K) (A := A)) :=
    (KervaireCentralizer.unitary_iff _ V).mpr (scalarTensor_mem_unitary (mul_mem hQ hT))
  have hUV : ((U*V : algebra (D := Slot I K) (A := A)) : Operator (Slot I K) A) =
      S ρ a * scalarTensor (A := A) T := by
    change (S ρ a * J (I := I) (X : Matrix K K ℂ)) * scalarTensor (Q*T) = _
    rw [scalarTensor_mul]
    change (S ρ a * J (I := I) (X : Matrix K K ℂ)) * (J (X : Matrix K K ℂ) * scalarTensor T) = _
    rw [← mul_assoc,mul_assoc (S ρ a),J_sq,mul_one]
  let _ := isStarNormal_of_mem_unitary (mul_mem (S_unitary (K := K) ρ a) (scalarTensor_mem_unitary (A := A) hT))
  let _ := isStarNormal_of_mem_unitary (mul_mem (S_unitary (K := K) ρ a) (J_unitary (I := I) X))
  let _ := isStarNormal_of_mem_unitary (scalarTensor_mem_unitary (A := A) (mul_mem hQ hT))
  have hsub := phase_mul_le U V hU hV
  change KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤ _
  have hsub' : KervaireMatrix.phase (S ρ a * scalarTensor (A := A) T) ≤
      KervaireMatrix.phase (S ρ a * J (I := I) (X : Matrix K K ℂ)) +
      KervaireMatrix.phase (scalarTensor (A := A) (Q*T)) := by
    simpa only [hUV] using hsub
  rw [phase_SJ] at hsub'
  have hc : (2 : ℝ) * Fintype.card K ≤ fixedDim (Q*T) := by exact_mod_cast hfix
  simp only [Slot,Fintype.card_prod,Fintype.card_sum,Nat.cast_mul,Nat.cast_add] at hb
  linarith
end KervaireMixing

end

end OAI
