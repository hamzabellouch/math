import Mathlib

namespace OAI

noncomputable section

namespace ZeroKey

section

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

universe v17_0

theorem exists_isometry_comp_of_norm_eq {V : Type v17_0} [inst17_0 : NormedAddCommGroup V]
    [inst17_1 : InnerProductSpace ℂ V] [inst17_2 : FiniteDimensional ℂ V]
    (f g : V →ₗ[ℂ] V)
    (h : ∀ x, ‖f x‖ = ‖g x‖) :
    ∃ U : V →ₗᵢ[ℂ] V, U.toLinearMap.comp g = f := by
  have hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := ⟨1, fun x => by simp [h x]⟩
  let L : LinearMap.range g →ₗᵢ[ℂ] V :=
    { toLinearMap := (f.compLeftInverse g).toLinearMap
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        simpa only [ContinuousLinearMap.coe_coe,
          LinearMap.compLeftInverse_apply_of_bdd f g hb x (g x) rfl,
          ← Submodule.norm_coe] using h x }
  refine ⟨L.extend, ?_⟩
  ext x
  change L.extend (g x) = f x
  rw [show L.extend (g x) = L ⟨g x, LinearMap.mem_range_self g x⟩ from
    L.extend_apply ⟨g x, LinearMap.mem_range_self g x⟩]
  exact LinearMap.compLeftInverse_apply_of_bdd f g hb x (g x) rfl

universe v43_0

lemma norm_eq_of_gram_eq {ι : Type v43_0} [inst43_0 : Fintype ι] [inst43_1 : DecidableEq ι]
    (A B : Matrix ι ι ℂ) (h : Aᴴ * A = Bᴴ * B)
    (x : EuclideanSpace ℂ ι) : ‖A.toEuclideanLin x‖ = ‖B.toEuclideanLin x‖ := by
  have hh := congrArg (fun M : Matrix ι ι ℂ =>
    inner ℂ x (M.toEuclideanLin x)) h
  simp only [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right] at hh
  change inner ℂ (A.toEuclideanLin x) (A.toEuclideanLin x) =
    inner ℂ (B.toEuclideanLin x) (B.toEuclideanLin x) at hh
  have hh' := congrArg (RCLike.re : ℂ → ℝ) hh
  simpa only [inner_self_eq_norm_sq, sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)] using hh'

theorem exists_unitary_mul_of_gram_eq {ι : Type v43_0} [inst43_0 : Fintype ι]
    [inst43_1 : DecidableEq ι]
    (A B : Matrix ι ι ℂ)
    (h : Aᴴ * A = Bᴴ * B) :
    ∃ U : Matrix.unitaryGroup ι ℂ, A = (U : Matrix ι ι ℂ) * B := by
  obtain ⟨U, hU⟩ := exists_isometry_comp_of_norm_eq A.toEuclideanLin B.toEuclideanLin
    (norm_eq_of_gram_eq A B h)
  let e := U.toLinearIsometryEquiv rfl
  let V : Matrix ι ι ℂ := Matrix.toEuclideanLin.symm U.toLinearMap
  have hV : V ∈ Matrix.unitaryGroup ι ℂ := by
    exact e.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun ι ℂ)
      (EuclideanSpace.basisFun ι ℂ)
  refine ⟨⟨V, hV⟩, ?_⟩
  apply Matrix.toEuclideanLin.injective
  simp only [Matrix.toLpLin_mul_same]
  have hVlin : V.toEuclideanLin = U.toLinearMap := by simp [V]
  change A.toEuclideanLin = V.toEuclideanLin.comp B.toEuclideanLin
  rw [hVlin, hU]

universe v84_0

def traceNorm {ι : Type v84_0} [inst84_0 : Fintype ι] [inst84_1 : DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ := (Matrix.trace (CFC.sqrt (Aᴴ * A))).re

universe v155_0 v155_1

def matrixVector {ι : Type v155_0} {κ : Type v155_1}
    (A : Matrix ι κ ℂ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun x => A x.1 x.2)

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

universe v217_0

def matrixUnit {ι : Type v217_0} [DecidableEq ι] (i j : ι) : Matrix ι ι ℂ :=
  fun a b => if a = i ∧ b = j then 1 else 0

def amplify {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (k : ℕ)
    (U : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ) :
    Matrix (Fin k × Fin b) (Fin k × Fin b) ℂ :=
  fun i j => L (fun x y => U (i.1, x) (j.1, y)) i.2 j.2

def CompletelyPositive {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) : Prop :=
  ∀ k U, U.PosSemidef → (amplify L k U).PosSemidef

def transposeLinear (a : ℕ) : Mat a →ₗ[ℂ] Mat a where
  toFun := Matrix.transpose
  map_add' := Matrix.transpose_add
  map_smul' _ _ := rfl

def PPTType {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) : Prop :=
  CompletelyPositive L ∧ CompletelyPositive (L.comp (transposeLinear a))

def tensorMap {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) :
    Matrix (Fin b × Fin d) (Fin b × Fin d) ℂ :=
  fun i j => ∑ x, ∑ y, ∑ z, ∑ w,
    U (x,z) (y,w) * L (matrixUnit x y) i.1 j.1 * M (matrixUnit z w) i.2 j.2

universe v243_0

def outer {ι : Type v243_0} (u v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => u i * star (v j)

universe v246_0

def Density {ι : Type v246_0} [Fintype ι] (R : Matrix ι ι ℂ) : Prop :=
  R.PosSemidef ∧ Matrix.trace R = 1

universe v264_0

def amplifyIndex {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) {κ : Type v264_0}
    (U : Matrix (κ × Fin a) (κ × Fin a) ℂ) :
    Matrix (κ × Fin b) (κ × Fin b) ℂ :=
  fun i j => L (fun x y => U (i.1,x) (j.1,y)) i.2 j.2

universe v269_0

lemma cp_amplifyIndex {a b : ℕ} {L : Mat a →ₗ[ℂ] Mat b} (hL : CompletelyPositive L)
    {κ : Type v269_0} [Fintype κ] (U : Matrix (κ × Fin a) (κ × Fin a) ℂ)
    (hU : U.PosSemidef) : (amplifyIndex L U).PosSemidef := by
  let e := Fintype.equivFin κ
  have h := hL (Fintype.card κ)
    (U.submatrix (fun i => (e.symm i.1, i.2)) (fun i => (e.symm i.1, i.2)))
    (hU.submatrix _)
  have h' := h.submatrix (fun i : κ × Fin b => (e i.1, i.2))
  convert h' using 1
  ext i j
  simp [amplifyIndex, amplify, Matrix.submatrix]

lemma matrix_sum_units {a : ℕ} (U : Mat a) :
    U = ∑ x, ∑ y, U x y • matrixUnit x y := by
  ext i j
  simp [matrixUnit, Matrix.sum_apply, Matrix.smul_apply, ite_and]

lemma linearMap_matrix_units {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (U : Mat a) :
    L U = ∑ x, ∑ y, U x y • L (matrixUnit x y) := by
  conv_lhs => rw [matrix_sum_units U]
  simp

lemma linearMap_matrix_units_apply {a b : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (U : Mat a)
    (i j : Fin b) : L U i j = ∑ x, ∑ y, U x y * L (matrixUnit x y) i j := by
  have h := congrArg (fun A : Mat b => A i j) (linearMap_matrix_units L U)
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h

lemma tensorMap_apply {a b c d : ℕ} (L : Mat a →ₗ[ℂ] Mat b) (M : Mat c →ₗ[ℂ] Mat d)
    (U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ) (i j : Fin b) (k l : Fin d) :
    tensorMap L M U (i,k) (j,l) =
      L (fun x y => M (fun z w => U (x,z) (y,w)) k l) i j := by
  calc
    _ = ∑ x, ∑ y, (∑ z, ∑ w, U (x,z) (y,w) * M (matrixUnit z w) k l) *
        L (matrixUnit x y) i j := by
      simp only [tensorMap, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = ∑ x, ∑ y, M (fun z w => U (x,z) (y,w)) k l * L (matrixUnit x y) i j := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      exact congrArg (fun t => t * L (matrixUnit x y) i j)
        (linearMap_matrix_units_apply M (fun z w => U (x,z) (y,w)) k l).symm
    _ = _ := (linearMap_matrix_units_apply L _ i j).symm

lemma tensorMap_positive {a b c d : ℕ} {L : Mat a →ₗ[ℂ] Mat b}
    {M : Mat c →ₗ[ℂ] Mat d} (hL : CompletelyPositive L) (hM : CompletelyPositive M)
    {U : Matrix (Fin a × Fin c) (Fin a × Fin c) ℂ} (hU : U.PosSemidef) :
    (tensorMap L M U).PosSemidef := by
  have h₁ := cp_amplifyIndex hM U hU
  have h₂ := cp_amplifyIndex hL _ (h₁.submatrix Prod.swap)
  have h₃ := h₂.submatrix Prod.swap
  convert h₃ using 1
  ext i j
  exact tensorMap_apply L M U i.1 j.1 i.2 j.2

universe v375_0

lemma outer_posSemidef {ι : Type v375_0} [Fintype ι] (u : ι → ℂ) : (outer u u).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star u

universe v1019_0

lemma cp_of_kraus_representation {a b : ℕ} {ν : Type v1019_0} [Fintype ν]
    (L : Mat a →ₗ[ℂ] Mat b) (K : ν → Matrix (Fin b) (Fin a) ℂ)
    (hK : ∀ U, L U = ∑ s, K s * U * (K s)ᴴ) : CompletelyPositive L := by
  intro r U hU
  have he : amplify L r U = ∑ s, ((1 : Mat r) ⊗ₖ K s) * U * ((1 : Mat r) ⊗ₖ K s)ᴴ := by
    ext ⟨i,x⟩ ⟨j,y⟩
    change L (fun v w => U (i,v) (j,w)) x y = _
    erw [hK]
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    change (K s * U.submatrix (fun v => (i,v)) (fun w => (j,w)) * (K s)ᴴ) x y = _
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix,
      Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

  rw [he]
  apply Matrix.posSemidef_sum
  intro s _
  exact hU.mul_mul_conjTranspose_same _

end

open Matrix

open scoped MatrixOrder ComplexOrder Kronecker

section

universe v1102_0 v1102_1

variable {σ : Type v1102_0} {ι : σ → Type v1102_1} [inst1102_0 : Fintype σ] [inst1102_1 : DecidableEq σ]
  [inst1102_2 : ∀ s, Fintype (ι s)] [inst1102_3 : ∀ s, DecidableEq (ι s)]

def tensorPi (A : ∀ s, Matrix (ι s) (ι s) ℂ) : Matrix (∀ s, ι s) (∀ s, ι s) ℂ :=
  fun i j => ∏ s, A s (i s) (j s)

omit inst1102_3 in
lemma tensorPi_mul [∀ s, DecidableEq (ι s)] (A B : ∀ s, Matrix (ι s) (ι s) ℂ) :
    tensorPi (fun s => A s * B s) = tensorPi A * tensorPi B := by
  ext i j
  simp only [tensorPi, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Finset.prod_mul_distrib

omit inst1102_1 inst1102_2 in
lemma tensorPi_one [DecidableEq σ] [∀ s, Fintype (ι s)] : tensorPi (fun s => (1 : Matrix (ι s) (ι s) ℂ)) = 1 := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [tensorPi]
  · obtain ⟨s,hs⟩ := Function.ne_iff.mp h
    simp only [tensorPi, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    simp [hs]

omit inst1102_1 inst1102_2 inst1102_3 in
lemma tensorPi_star [DecidableEq σ] [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)] (A : ∀ s, Matrix (ι s) (ι s) ℂ) :
    tensorPi (fun s => (A s)ᴴ) = (tensorPi A)ᴴ := by
  ext i j
  simp [tensorPi, Matrix.conjTranspose_apply]

lemma tensorPi_projection (A : ∀ s, Matrix (ι s) (ι s) ℂ)
    (hA : ∀ s, IsStarProjection (A s)) : IsStarProjection (tensorPi A) := by
  constructor
  · change tensorPi A * tensorPi A = tensorPi A
    rw [← tensorPi_mul]
    congr 1
    funext s
    exact (hA s).isIdempotentElem
  · change (tensorPi A)ᴴ = tensorPi A
    rw [← tensorPi_star]
    congr 1
    funext s
    exact (hA s).isSelfAdjoint

universe v1163_0

omit inst1102_2 inst1102_3 in
lemma tensorPi_sum [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)] {α : σ → Type v1163_0} [∀ s, Fintype (α s)]
    (A : ∀ s, α s → Matrix (ι s) (ι s) ℂ) :
    (∑ a : ∀ s, α s, tensorPi (fun s => A s (a s))) =
      tensorPi (fun s => ∑ a, A s a) := by
  ext i j
  simp only [Matrix.sum_apply, tensorPi]
  exact (Fintype.prod_sum (fun s a => A s a (i s) (j s))).symm

end

namespace Explicit

section

abbrev p : ℕ := 257

abbrev k : ℕ := 1028

@[irreducible] def b : ℕ := Nat.choose 1027 513

@[irreducible] def Q : ℕ := b^3

@[irreducible] def K : ℕ := k^3

def dimensionFunction (q : ℕ) : ℕ := 4^(Nat.choose q 8)

lemma dimensionFunction_eq (q : ℕ) : dimensionFunction q = 4^(Nat.choose q 8) := rfl

@[irreducible] def D : ℕ := dimensionFunction Q

lemma D_eq : D = 4^(Nat.choose Q 8) := by
  unfold D
  exact dimensionFunction_eq Q

def outputDimensionFunction (q d : ℕ) : ℕ := q*d

lemma outputDimensionFunction_eq (q d : ℕ) : outputDimensionFunction q d = q*d := rfl

@[irreducible] def m : ℕ := outputDimensionFunction Q D

lemma m_eq : m = Q*D := by
  unfold m
  exact outputDimensionFunction_eq Q D

def Base := {A : Finset (Fin k) // A.card = 514 ∧ (0 : Fin k) ∈ A}

instance : Finite Base := by unfold Base; infer_instance

instance : Fintype Base := Fintype.ofFinite _

instance : DecidableEq Base := Classical.decEq _

instance : LinearOrder Base := LinearOrder.lift' (fun A : Base => A.1.sort (· ≤ ·)) (by
  intro A B h
  apply Subtype.ext
  simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)

def Question := Lex (Fin 3 → Base)

instance : Finite Question := by unfold Question; infer_instance

instance : Fintype Question := Fintype.ofFinite _

instance : DecidableEq Question := Classical.decEq _

instance : LinearOrder Question := inferInstanceAs (LinearOrder (Lex (Fin 3 → Base)))

def baseVector (A : Base) (h : Fin k) : ℝ :=
  (if h ∈ A.1 then 1 else -1) / Real.sqrt k

def vector (q : Question) (h : Fin 3 → Fin k) : ℝ :=
  ∏ l, baseVector (ofLex q l) (h l)

def overlap (q r : Question) : ℝ := ∑ h, vector q h * vector r h

def EightSet := {S : Finset Question // S.card = 8}

instance : Finite EightSet := by unfold EightSet; infer_instance

instance : Fintype EightSet := Fintype.ofFinite _

instance : DecidableEq EightSet := Classical.decEq _

instance : LinearOrder EightSet := LinearOrder.lift'
  (fun S : EightSet => S.1.sort (· ≤ ·)) (by
    intro S T h
    apply Subtype.ext
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h)

def PairwiseOrthogonal (S : EightSet) : Prop :=
  ∀ q ∈ S.1, ∀ r ∈ S.1, q ≠ r → overlap q r = 0

abbrev Sign := Fin 2

def signValue (s : Sign) : ℂ := if s=0 then -1 else 1

abbrev Outcome := Lex (Sign × Sign)

abbrev LocalBasis := Lex (Fin 2 × Fin 2)

def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]

def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

def tensor₂ (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix LocalBasis LocalBasis ℂ :=
  (A ⊗ₖ B).submatrix ofLex ofLex

def observable : Fin 3 → Fin 3 → Matrix LocalBasis LocalBasis ℂ
  | 0,0 => tensor₂ pauliX 1
  | 0,1 => tensor₂ 1 pauliX
  | 0,2 => tensor₂ pauliX pauliX
  | 1,0 => tensor₂ 1 pauliZ
  | 1,1 => tensor₂ pauliZ 1
  | 1,2 => tensor₂ pauliZ pauliZ
  | 2,0 => tensor₂ pauliX pauliZ
  | 2,1 => tensor₂ pauliZ pauliX
  | 2,2 => tensor₂ pauliY pauliY

def contextObservable (t : Fin 6) (j : Fin 3) : Matrix LocalBasis LocalBasis ℂ :=
  if h : t.val < 3 then observable ⟨t.val,h⟩ j
  else observable j ⟨t.val-3, by omega⟩

def contextProjection (t : Fin 6) (a : Outcome) : Matrix LocalBasis LocalBasis ℂ :=
  (1/4 : ℂ) • ((1+signValue (ofLex a).1 • contextObservable t 0) *
    (1+signValue (ofLex a).2 • contextObservable t 1))

def trivialProjection (a : Outcome) : Matrix LocalBasis LocalBasis ℂ :=
  if ofLex a = (1,1) then 1 else 0

def localProjection (S : EightSet) (q : Question) (a : Outcome) :
    Matrix LocalBasis LocalBasis ℂ :=
  by
    classical
    exact
      if PairwiseOrthogonal S then
        if h : q ∈ S.1 then
          let rank := (S.1.orderIsoOfFin S.2).symm ⟨q,h⟩
          if hr : rank.val < 6 then contextProjection ⟨rank.val,hr⟩ a
          else trivialProjection a
        else trivialProjection a
      else trivialProjection a

def Basis := Lex (EightSet → LocalBasis)

instance : Finite Basis := by unfold Basis; infer_instance

instance : Fintype Basis := Fintype.ofFinite _

instance : DecidableEq Basis := Classical.decEq _

instance : LinearOrder Basis := inferInstanceAs (LinearOrder (Lex (EightSet → LocalBasis)))

def OutcomeString := Lex (EightSet → Outcome)

instance : Finite OutcomeString := by unfold OutcomeString; infer_instance

instance : Fintype OutcomeString := Fintype.ofFinite _

instance : DecidableEq OutcomeString := Classical.decEq _

instance : LinearOrder OutcomeString := inferInstanceAs (LinearOrder (Lex (EightSet → Outcome)))

def Label := Lex (Question × OutcomeString)

instance : Finite Label := by unfold Label; infer_instance

instance : Fintype Label := Fintype.ofFinite _

instance : DecidableEq Label := Classical.decEq _

instance : LinearOrder Label := inferInstanceAs (LinearOrder (Lex (Question × OutcomeString)))

def projection (i : Label) : Matrix Basis Basis ℂ := fun h l =>
  ∏ S, localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) (ofLex h S) (ofLex l S)

def block (i j : Label) : Matrix Basis Basis ℂ :=
  (overlap (ofLex i).1 (ofLex j).1 : ℂ) • (projection i * projection j)

universe v1312_0 v1312_1

def traceBlockMap {α : Type v1312_0} {β : Type v1312_1} [Fintype α] [DecidableEq α]
    (H : β → β → Matrix α α ℂ) : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ where
  toFun U i j := trace (H i j * U)
  map_add' U V := by
    ext i j
    change trace (H i j * (U+V)) = trace (H i j * U)+trace (H i j * V)
    rw [mul_add, Matrix.trace_add]
  map_smul' c U := by
    ext i j
    change trace (H i j * (c • U)) = c * trace (H i j * U)
    rw [Matrix.mul_smul, Matrix.trace_smul]
    rfl

def rawOutput : Matrix (Label × Label) (Label × Label) ℂ := fun i j =>
  ∑ h, ∑ l, block i.1 j.1 l h * block i.2 j.2 l h

def rho : Matrix (Label × Label) (Label × Label) ℂ :=
  ((Q^2*D : ℕ) : ℂ)⁻¹ • rawOutput

lemma tensor₂_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : LocalBasis) :
    tensor₂ A B i j = A (ofLex i).1 (ofLex j).1 * B (ofLex i).2 (ofLex j).2 := rfl

lemma sum_localBasis (f : LocalBasis → ℂ) : (∑ i, f i) =
    f (toLex (0,0)) + f (toLex (0,1)) + (f (toLex (1,0)) + f (toLex (1,1))) := by
  change (∑ i : Fin 2 × Fin 2, f (toLex i)) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]

lemma signValue_sq (a : Sign) : signValue a * signValue a = 1 := by
  fin_cases a <;> norm_num [signValue]

lemma signValue_conj (a : Sign) : star (signValue a) = signValue a := by
  fin_cases a <;> norm_num [signValue]

lemma localBasis_one_apply (i j : LocalBasis) :
    (1 : Matrix LocalBasis LocalBasis ℂ) i j = if ofLex i = ofLex j then 1 else 0 := by
  simp only [Matrix.one_apply, ofLex.injective.eq_iff]

lemma context_hermitian (t : Fin 6) (j : Fin 3) :
    (contextObservable t j).IsHermitian := by
  fin_cases t <;> fin_cases j <;> change (tensor₂ _ _).IsHermitian
  all_goals
    rw [Matrix.IsHermitian]
    ext i l
    rw [Matrix.conjTranspose_apply, tensor₂_apply, tensor₂_apply]
    generalize hi : ofLex i = ii
    generalize hl : ofLex l = ll
    rcases ii with ⟨i,h⟩
    rcases ll with ⟨l,k⟩
    fin_cases i <;> fin_cases h <;> fin_cases l <;> fin_cases k <;>
      norm_num [pauliX, pauliY, pauliZ, Matrix.one_apply]

lemma context_real (t : Fin 6) (j : Fin 3) (i l : LocalBasis) :
    star (contextObservable t j i l) = contextObservable t j i l := by
  fin_cases t <;> fin_cases j <;> change star (tensor₂ _ _ i l) = tensor₂ _ _ i l
  all_goals
    rw [tensor₂_apply]
    generalize hi : ofLex i = ii
    generalize hl : ofLex l = ll
    rcases ii with ⟨i,h⟩
    rcases ll with ⟨l,k⟩
    fin_cases i <;> fin_cases h <;> fin_cases l <;> fin_cases k <;>
      norm_num [pauliX, pauliY, pauliZ, Matrix.one_apply]

lemma context_involution (t : Fin 6) (j : Fin 3) :
    contextObservable t j * contextObservable t j = 1 := by
  fin_cases t <;> fin_cases j <;> change tensor₂ _ _ * tensor₂ _ _ = (1 : Matrix LocalBasis LocalBasis ℂ)
  all_goals
    ext i l
    rw [Matrix.mul_apply, sum_localBasis, localBasis_one_apply]
    simp only [tensor₂_apply, ofLex_toLex]
    generalize hi : ofLex i = ii
    generalize hl : ofLex l = ll
    rcases ii with ⟨i,h⟩
    rcases ll with ⟨l,k⟩
    fin_cases i <;> fin_cases h <;> fin_cases l <;> fin_cases k <;>
      norm_num [pauliX, pauliY, pauliZ, Matrix.one_apply]

lemma context_commute (t : Fin 6) :
    Commute (contextObservable t 0) (contextObservable t 1) := by
  change contextObservable t 0 * contextObservable t 1 = contextObservable t 1 * contextObservable t 0
  fin_cases t <;> change tensor₂ _ _ * tensor₂ _ _ = tensor₂ _ _ * tensor₂ _ _
  all_goals
    ext i l
    simp only [Matrix.mul_apply, sum_localBasis, tensor₂_apply, ofLex_toLex]
    generalize hi : ofLex i = ii
    generalize hl : ofLex l = ll
    rcases ii with ⟨i,h⟩
    rcases ll with ⟨l,k⟩
    fin_cases i <;> fin_cases h <;> fin_cases l <;> fin_cases k <;>
      norm_num [pauliX, pauliY, pauliZ, Matrix.one_apply]

def contextParity (t : Fin 6) : ℂ := if t=5 then -1 else 1

lemma context_third (t : Fin 6) : contextObservable t 2 =
    contextParity t • (contextObservable t 0 * contextObservable t 1) := by
  fin_cases t <;> change tensor₂ _ _ = _ • (tensor₂ _ _ * tensor₂ _ _)
  all_goals
    ext i l
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, sum_localBasis, tensor₂_apply, ofLex_toLex]
    generalize hi : ofLex i = ii
    generalize hl : ofLex l = ll
    rcases ii with ⟨i,h⟩
    rcases ll with ⟨l,k⟩
    fin_cases i <;> fin_cases h <;> fin_cases l <;> fin_cases k <;>
      norm_num [contextParity, pauliX, pauliY, pauliZ, Matrix.one_apply, Fin.ext_iff]

def spectralSign (O : Matrix LocalBasis LocalBasis ℂ) (a : Sign) :=
  (1/2 : ℂ) • (1 + signValue a • O)

lemma sign_eigen_aux (O : Matrix LocalBasis LocalBasis ℂ) (hO : O*O=1) (a : Sign) :
    O*(1+signValue a • O) = signValue a • (1+signValue a • O) := by
  simp only [mul_add, mul_one, mul_smul_comm, hO, smul_add, smul_smul,
    signValue_sq, one_smul]
  exact add_comm _ _

lemma spectralSign_projection (O : Matrix LocalBasis LocalBasis ℂ)
    (hO : O.IsHermitian) (hO2 : O*O=1) (a : Sign) :
    IsStarProjection (spectralSign O a) := by
  refine ⟨?_, ?_⟩
  · change spectralSign O a * spectralSign O a = spectralSign O a
    dsimp [spectralSign]
    rw [smul_mul_smul_comm, add_mul, one_mul, smul_mul_assoc, sign_eigen_aux O hO2]
    rw [smul_smul, signValue_sq, one_smul]
    module
  · change star (spectralSign O a) = spectralSign O a
    dsimp [spectralSign]
    simp only [star_smul, star_add, star_one, signValue_conj, hO.star_eq]
    norm_num

lemma spectralSign_commute (O T : Matrix LocalBasis LocalBasis ℂ)
    (h : Commute O T) (a b : Sign) : Commute (spectralSign O a) (spectralSign T b) := by
  unfold spectralSign
  exact ((Commute.one_left _).add_left ((Commute.one_right _).add_right
    (h.smul_left _ |>.smul_right _))).smul_left _ |>.smul_right _

lemma contextProjection_factor (t : Fin 6) (a : Outcome) : contextProjection t a =
    spectralSign (contextObservable t 0) (ofLex a).1 *
      spectralSign (contextObservable t 1) (ofLex a).2 := by
  simp only [contextProjection, spectralSign, smul_mul_smul_comm]
  norm_num

lemma contextProjection_projection (t : Fin 6) (a : Outcome) :
    IsStarProjection (contextProjection t a) := by
  rw [contextProjection_factor]
  exact (spectralSign_projection _ (context_hermitian t 0) (context_involution t 0) _).mul
    (spectralSign_projection _ (context_hermitian t 1) (context_involution t 1) _)
    (spectralSign_commute _ _ (context_commute t) _ _)

lemma contextProjection_real (t : Fin 6) (a : Outcome) (i j : LocalBasis) :
    star (contextProjection t a i j) = contextProjection t a i j := by
  simp only [contextProjection, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    star_mul, star_sum, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    star_add, context_real, signValue_conj]
  simp [Matrix.one_apply, mul_comm]

lemma contextParity_conj (t : Fin 6) : star (contextParity t) = contextParity t := by
  unfold contextParity
  split <;> norm_num

def contextEigenvalue (t : Fin 6) (a : Outcome) : Fin 3 → ℂ :=
  ![signValue (ofLex a).1, signValue (ofLex a).2,
    contextParity t * signValue (ofLex a).1 * signValue (ofLex a).2]

lemma context_eigen_first (t : Fin 6) (a : Outcome) :
    contextObservable t 0 * contextProjection t a =
      signValue (ofLex a).1 • contextProjection t a := by
  unfold contextProjection
  rw [mul_smul_comm, ← mul_assoc, sign_eigen_aux _ (context_involution t 0),
    smul_mul_assoc, smul_comm]

lemma context_eigen_second (t : Fin 6) (a : Outcome) :
    contextObservable t 1 * contextProjection t a =
      signValue (ofLex a).2 • contextProjection t a := by
  unfold contextProjection
  rw [mul_smul_comm]
  have hc : Commute (contextObservable t 1)
      (1+signValue (ofLex a).1 • contextObservable t 0) :=
    (Commute.one_right _).add_right ((context_commute t).symm.smul_right _)
  rw [← mul_assoc, hc, mul_assoc, sign_eigen_aux _ (context_involution t 1),
    mul_smul_comm, smul_comm]

lemma context_eigen (t : Fin 6) (a : Outcome) (j : Fin 3) :
    contextObservable t j * contextProjection t a =
      contextEigenvalue t a j • contextProjection t a := by
  fin_cases j
  · exact context_eigen_first t a
  · exact context_eigen_second t a
  · change contextObservable t 2 * contextProjection t a =
      (contextParity t * signValue (ofLex a).1 * signValue (ofLex a).2) • _
    rw [context_third, smul_mul_assoc, mul_assoc, context_eigen_second,
      mul_smul_comm, context_eigen_first]
    simp only [smul_smul]
    congr 1
    ring

lemma contextEigenvalue_conj (t : Fin 6) (a : Outcome) (j : Fin 3) :
    star (contextEigenvalue t a j) = contextEigenvalue t a j := by
  (fin_cases j <;> simp [contextEigenvalue, star_mul, signValue_conj, contextParity_conj]); ring

lemma context_eigen_right (t : Fin 6) (a : Outcome) (j : Fin 3) :
    contextProjection t a * contextObservable t j =
      contextEigenvalue t a j • contextProjection t a := by
  have h := congrArg star (context_eigen t a j)
  simpa only [star_mul, (contextProjection_projection t a).isSelfAdjoint.star_eq,
    (context_hermitian t j).star_eq, star_smul, contextEigenvalue_conj] using h

lemma spectralSign_sum (O : Matrix LocalBasis LocalBasis ℂ) :
    ∑ a, spectralSign O a = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [spectralSign, signValue]
  module

lemma contextProjection_sum (t : Fin 6) : ∑ a, contextProjection t a = 1 := by
  simp_rw [contextProjection_factor]
  change (∑ a : Sign × Sign, spectralSign (contextObservable t 0) a.1 *
    spectralSign (contextObservable t 1) a.2) = _
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, spectralSign_sum, one_mul]

universe v1552_0

lemma eigenvalues_agree {ι : Type v1552_0} [Fintype ι] (E F O : Matrix ι ι ℂ)
    (a b : ℂ) (hE : E*O=a • E) (hF : O*F=b • F) (hEF : E*F≠0) : a=b := by
  apply smul_left_injective ℂ hEF
  calc a • (E*F) = (E*O)*F := by rw [hE, smul_mul_assoc]
       _ = E*(O*F) := mul_assoc _ _ _
       _ = b • (E*F) := by rw [hF, mul_smul_comm]

lemma signValue_injective : Function.Injective signValue := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | rfl | norm_num [signValue] at hab

lemma contextProjection_orthogonal (t : Fin 6) (a b : Outcome) (hab : a≠b) :
    contextProjection t a * contextProjection t b = 0 := by
  by_contra h
  have he (j : Fin 3) := eigenvalues_agree _ _ _ _ _
    (context_eigen_right t a j) (context_eigen t b j) h
  apply hab
  apply ofLex.injective
  apply Prod.ext
  · exact signValue_injective (he 0)
  · exact signValue_injective (he 1)

lemma trivialProjection_projection (a : Outcome) : IsStarProjection (trivialProjection a) := by
  unfold trivialProjection
  split <;> simp only [IsStarProjection.one, IsStarProjection.zero]

lemma trivialProjection_sum : ∑ a, trivialProjection a = 1 := by
  classical
  have h : ∀ a, trivialProjection a = if a = toLex (1,1) then 1 else 0 := by
    intro a
    simp [trivialProjection, ← ofLex.injective.eq_iff]
  simp only [h]
  simp

lemma trivialProjection_orthogonal (a b : Outcome) (hab : a≠b) :
    trivialProjection a * trivialProjection b = 0 := by
  by_cases ha : ofLex a = (1,1)
  · have hb : ofLex b ≠ (1,1) := fun hb => hab (ofLex.injective (ha.trans hb.symm))
    simp [trivialProjection, hb]
  · simp [trivialProjection, ha]

lemma localProjection_type (S : EightSet) (q : Question) :
    (localProjection S q = trivialProjection) ∨
      (∃ t : Fin 6, localProjection S q = contextProjection t) := by
  classical
  unfold localProjection
  split
  · split
    · dsimp only
      split
      · exact Or.inr ⟨_,rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

lemma localProjection_projection (S : EightSet) (q : Question) (a : Outcome) :
    IsStarProjection (localProjection S q a) := by
  rcases localProjection_type S q with h | ⟨t,h⟩
  · rw [h]; exact trivialProjection_projection a
  · rw [h]; exact contextProjection_projection t a

lemma localProjection_real (S : EightSet) (q : Question) (a : Outcome) (i j : LocalBasis) :
    star (localProjection S q a i j) = localProjection S q a i j := by
  rcases localProjection_type S q with h | ⟨t,h⟩
  · rw [h]
    unfold trivialProjection
    split <;> simp [Matrix.one_apply]
  · rw [h]; exact contextProjection_real t a i j

lemma localProjection_sum (S : EightSet) (q : Question) :
    ∑ a, localProjection S q a = 1 := by
  rcases localProjection_type S q with h | ⟨t,h⟩
  · rw [h]; exact trivialProjection_sum
  · rw [h]; exact contextProjection_sum t

lemma localProjection_orthogonal (S : EightSet) (q : Question) (a b : Outcome) (hab : a≠b) :
    localProjection S q a * localProjection S q b = 0 := by
  rcases localProjection_type S q with h | ⟨t,h⟩
  · rw [h]; exact trivialProjection_orthogonal a b hab
  · rw [h]; exact contextProjection_orthogonal t a b hab

lemma projection_tensor (i : Label) : projection i =
    (tensorPi (fun S => localProjection S (ofLex i).1 (ofLex (ofLex i).2 S))).submatrix
      (show Basis ≃ (EightSet → LocalBasis) from Equiv.refl _) (show Basis ≃ (EightSet → LocalBasis) from Equiv.refl _) := rfl

lemma projection_projection (i : Label) : IsStarProjection (projection i) := by
  let e : Basis ≃ (EightSet → LocalBasis) := Equiv.refl _
  let A := tensorPi (fun S => localProjection S (ofLex i).1 (ofLex (ofLex i).2 S))
  have hA : IsStarProjection A := tensorPi_projection _ (fun S => localProjection_projection _ _ _)
  rw [projection_tensor]
  change IsStarProjection (A.submatrix e e)
  constructor
  · change A.submatrix e e * A.submatrix e e = A.submatrix e e
    rw [Matrix.submatrix_mul_equiv, hA.isIdempotentElem]
  · change (A.submatrix e e)ᴴ = A.submatrix e e
    rw [Matrix.conjTranspose_submatrix, show Aᴴ=A from hA.isSelfAdjoint]

lemma projection_real (i : Label) (h l : Basis) : star (projection i h l) = projection i h l := by
  change (starRingEnd ℂ) (∏ S, localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) (ofLex h S) (ofLex l S)) = _
  rw [map_prod]
  simp only [starRingEnd_apply, localProjection_real]
  rfl

lemma projection_sum (q : Question) : ∑ a : OutcomeString, projection (toLex (q,a)) = 1 := by
  ext h l
  simp only [Matrix.sum_apply, projection, ofLex_toLex]
  have he := congr_fun (congr_fun (tensorPi_sum (fun S a => localProjection S q a)) (ofLex h)) (ofLex l)
  have hr : tensorPi (fun S => ∑ a, localProjection S q a) = 1 := by
    simp only [localProjection_sum, tensorPi_one]
  rw [hr] at he
  calc
    _ = ∑ a : EightSet → Outcome, ∏ S, localProjection S q (a S) (ofLex h S) (ofLex l S) :=
      (Equiv.sum_comp (show (EightSet → Outcome) ≃ OutcomeString from Equiv.refl _)
        (fun a : OutcomeString => ∏ S, localProjection S q (ofLex a S) (ofLex h S) (ofLex l S))).symm
    _ = _ := by
      simpa only [tensorPi, Matrix.sum_apply, Matrix.one_apply,
        show (ofLex h = ofLex l) ↔ h=l from Iff.rfl] using he

lemma projection_mul_apply (i j : Label) (h l : Basis) :
    (projection i * projection j) h l = ∏ S,
      (localProjection S (ofLex i).1 (ofLex (ofLex i).2 S) *
        localProjection S (ofLex j).1 (ofLex (ofLex j).2 S)) (ofLex h S) (ofLex l S) := by
  let e : Basis ≃ (EightSet → LocalBasis) := Equiv.refl _
  let A := tensorPi (fun S => localProjection S (ofLex i).1 (ofLex (ofLex i).2 S))
  let B := tensorPi (fun S => localProjection S (ofLex j).1 (ofLex (ofLex j).2 S))
  change (A.submatrix e e * B.submatrix e e) h l = _
  rw [Matrix.submatrix_mul_equiv]
  exact congr_fun (congr_fun (tensorPi_mul _ _).symm (ofLex h)) (ofLex l)

lemma trivialProjection_commute (a : Outcome) (A : Matrix LocalBasis LocalBasis ℂ) :
    Commute (trivialProjection a) A := by
  unfold trivialProjection
  split <;> simp

lemma localProjection_self_commute (S : EightSet) (q : Question) (a b : Outcome) :
    Commute (localProjection S q a) (localProjection S q b) := by
  by_cases h : a=b
  · subst b; exact Commute.refl _
  · change _ * _ = _ * _
    rw [localProjection_orthogonal _ _ _ _ h,
      localProjection_orthogonal _ _ _ _ (Ne.symm h)]

lemma localProjection_trivial_of_not_orthogonal (S : EightSet) (q : Question)
    (h : ¬PairwiseOrthogonal S) : localProjection S q = trivialProjection := by
  funext a
  simp only [localProjection, ite_eq_right h]

lemma localProjection_trivial_of_not_mem (S : EightSet) (q : Question)
    (h : q∉S.1) : localProjection S q = trivialProjection := by
  funext a
  simp only [localProjection, dite_eq_right h, ite_self]

lemma localProjection_commute (S : EightSet) (q r : Question) (a b : Outcome)
    (hqr : overlap q r ≠ 0) : Commute (localProjection S q a) (localProjection S r b) := by
  by_cases he : q=r
  · subst r; exact localProjection_self_commute S q a b
  by_cases hS : PairwiseOrthogonal S
  · by_cases hq : q∈S.1
    · have hr : r∉S.1 := fun hr => hqr (hS q hq r hr he)
      rw [localProjection_trivial_of_not_mem S r hr]
      exact (trivialProjection_commute b _).symm
    · rw [localProjection_trivial_of_not_mem S q hq]
      exact trivialProjection_commute a _
  · rw [localProjection_trivial_of_not_orthogonal S q hS]
    exact trivialProjection_commute a _

lemma projection_commute (i j : Label) (hij : overlap (ofLex i).1 (ofLex j).1 ≠ 0) :
    Commute (projection i) (projection j) := by
  change _ * _ = _ * _
  ext h l
  rw [projection_mul_apply, projection_mul_apply]
  apply Finset.prod_congr rfl
  intro S _
  rw [(localProjection_commute S _ _ _ _ hij).eq]

universe v1965_0

lemma card_subsets_containing {α : Type v1965_0} [Fintype α] [DecidableEq α]
    (a : α) (r : ℕ) (hr : 1 ≤ r)
    [Fintype {A : Finset α // A.card=r ∧ a ∈ A}] :
    Fintype.card {A : Finset α // A.card=r ∧ a ∈ A} =
      Nat.choose (Fintype.card α - 1) (r-1) := by
  rw [Fintype.card_of_subtype
    (((Finset.univ : Finset α).powersetCard r).filter ({a} ⊆ ·)) (by
      intro A
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and, Finset.singleton_subset_iff])]
  rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
    (by simpa only [Finset.card_singleton] using hr)]
  simp only [Finset.card_univ, Finset.card_singleton]

lemma card_base : Fintype.card Base = b := by
  let : Fintype {A : Finset (Fin k) // A.card=514 ∧ (0 : Fin k) ∈ A} :=
    inferInstanceAs (Fintype Base)
  have h := card_subsets_containing (0 : Fin k) 514 (by decide)
  change Fintype.card Base = Nat.choose (Fintype.card (Fin k)-1) (514-1) at h
  rw [Fintype.card_fin] at h
  delta b
  exact h.trans (congrArg₂ Nat.choose (show k-1=1027 from rfl) (show 514-1=513 from rfl))

lemma card_question : Fintype.card Question = Q := by
  rw [Fintype.card_congr (show Question ≃ (Fin 3 → Base) from Equiv.refl _)]
  rw [Fintype.card_fun, Fintype.card_fin, card_base]
  delta Q
  rfl

universe v1995_0

lemma signed_overlap {α : Type v1995_0} [Fintype α] [DecidableEq α] (A B : Finset α) :
    (∑ h, (if h ∈ A then (1:ℝ) else -1) * (if h ∈ B then 1 else -1)) =
      Fintype.card α - 2*(A.card:ℝ) - 2*(B.card:ℝ) + 4*(A ∩ B).card := by
  have hp (h : α) :
      (if h ∈ A then (1:ℝ) else -1) * (if h ∈ B then 1 else -1) =
      1 - 2*(if h ∈ A then 1 else 0) - 2*(if h ∈ B then 1 else 0) +
        4*(if h ∈ A ∩ B then 1 else 0) := by
    by_cases ha : h ∈ A <;> by_cases hb : h ∈ B <;> simp [ha,hb] <;> norm_num
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  congr 1
  ext x
  simp

lemma base_inner (A B : Base) :
    (∑ h, baseVector A h * baseVector B h) = (A.1 ∩ B.1).card / (p:ℝ) - 1 := by
  simp only [baseVector, div_mul_div_comm, ← Finset.sum_div]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ k), signed_overlap]
  rw [A.2.1,B.2.1]
  simp only [Fintype.card_fin, k, p]
  push_cast
  ring

lemma base_unit (A : Base) : ∑ h, baseVector A h * baseVector A h = 1 := by
  rw [base_inner, Finset.inter_self, A.2.1]
  norm_num [p]

lemma vector_unit (q : Question) : overlap q q = 1 := by
  change Lex (Fin 3 → Base) at q
  unfold overlap vector
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l h => baseVector (ofLex q l) h * baseVector (ofLex q l) h)]
  simp only [base_unit, Finset.prod_const_one]

@[irreducible] def a₀ : ℕ := ∑ j ∈ Finset.range p, Nat.choose k j

open Finset

lemma choose_mono_small {n i j : ℕ} (hij : i ≤ j) (hj : j ≤ n/2) :
    Nat.choose n i ≤ Nat.choose n j := by
  induction hij with
  | refl => rfl
  | @step j hij ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

lemma a₀_upper : a₀ ≤ 257 * Nat.choose 1028 257 := by
  delta a₀
  calc
    (∑ j ∈ range 257, Nat.choose 1028 j) ≤ ∑ _j ∈ range 257, Nat.choose 1028 257 := by
      apply sum_le_sum
      intro j hj
      exact choose_mono_small (Nat.le_of_lt (mem_range.mp hj)) (by decide)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]

lemma binomial_term_le (n j x y : ℕ) (hj : j ≤ n) :
    x^j*y^(n-j)*Nat.choose n j ≤ (x+y)^n := by
  rw [add_pow]
  exact single_le_sum (f := fun m => x^m*y^(n-m)*Nat.choose n m)
    (fun _ _ => Nat.zero_le _) (show j ∈ range (n+1) from mem_range.mpr (by omega))

lemma choose_upper : Nat.choose 1028 257 < 12^257 := by
  have ht := binomial_term_le 1028 257 1 3 (by decide)
  simp only [one_pow, one_mul, show 1028-257=771 from rfl, show 1+3=4 from rfl] at ht
  have hn : (4:ℕ)^1028 < 3^771*12^257 := by
    have hh := pow_lt_pow_left₀ (by norm_num : (4:ℕ)^4 < 3^3*12) (by positivity) (by decide : 257 ≠ 0)
    have hl : ((4:ℕ)^4)^257 = 4^1028 := by rw [← pow_mul]
    have hr : ((3:ℕ)^3*12)^257 = 3^771*12^257 :=
      by rw [mul_pow, ← pow_mul]
    exact (congrArg₂ (fun x y : ℕ => x<y) hl hr).mp hh
  have hh : 3^771 * Nat.choose 1028 257 < 3^771 * 12^257 := lt_of_le_of_lt ht hn
  exact Nat.lt_of_mul_lt_mul_left hh

lemma double_b : Nat.choose 1028 514 = 2*b := by
  delta b
  have hs : Nat.choose 1027 514 = Nat.choose 1027 513 :=
    Nat.choose_symm_of_eq_add (show 1027=514+513 from rfl)
  calc
    Nat.choose 1028 514 = Nat.choose 1027 513 + Nat.choose 1027 514 :=
      (congrArg₂ Nat.choose (show 1028=Nat.succ 1027 from rfl)
        (show 514=Nat.succ 513 from rfl)).trans ((Nat.choose_succ_succ 1027 513).trans
        (congrArg (fun x => Nat.choose 1027 513 + x)
          (congrArg (Nat.choose 1027) (show Nat.succ 513=514 from rfl))))
    _ = 2 * Nat.choose 1027 513 := by rw [hs]; omega

lemma b_lower : 2^1028 ≤ 2058*b := by
  have h : (∑ j ∈ range (1028+1), Nat.choose 1028 j) ≤
      ∑ _j ∈ range (1028+1), Nat.choose 1028 514 :=
    sum_le_sum (fun j _ => Nat.choose_le_middle j 1028)
  rw [Nat.sum_range_choose, sum_const, card_range, nsmul_eq_mul, double_b] at h
  simpa only [Nat.cast_id, show 1028+1=1029 from rfl, ← Nat.mul_assoc, show 1029*2=2058 from rfl] using h

lemma strict_parameter_bound : 3*a₀*K < b := by
  have ha := a₀_upper
  have hc := choose_upper
  have hb := b_lower
  have ha' : a₀ < 257*12^257 := lt_of_le_of_lt ha (Nat.mul_lt_mul_of_pos_left hc (by decide))
  have hn : (2058:ℕ)*(3*(257*12^257)*1028^3) < 2^1028 := by
    calc
      (2058:ℕ)*(3*(257*12^257)*1028^3) < 16^257 := by
        rw [show 257=256+1 from rfl, pow_add, pow_add]
        norm_num
      _ = 2^1028 := by
        calc
          (16 : ℕ)^257 = ((2 : ℕ)^4)^257 := congrArg (fun value : ℕ => value^257) (show 16 = 2^4 from rfl)
          _ = 2^1028 := by rw [← pow_mul]
  delta K
  change 3*a₀*1028^3 < b
  apply Nat.lt_of_mul_lt_mul_left (a := 2058)
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 2058
    (Nat.mul_le_mul_right (1028^3) (Nat.mul_le_mul_left 3 (Nat.le_of_lt ha')))) (hn.trans_le hb)

lemma b_pos : 0 < b := lt_of_le_of_lt (Nat.zero_le _) strict_parameter_bound

end

universe v2431_0

lemma card_subsets {α : Type v2431_0} [Fintype α] [DecidableEq α] (r : ℕ)
    [Fintype {S : Finset α // S.card=r}] :
    Fintype.card {S : Finset α // S.card=r} = Nat.choose (Fintype.card α) r := by
  rw [Fintype.card_of_subtype ((Finset.univ : Finset α).powersetCard r) (by
    intro S
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])]
  rw [Finset.card_powersetCard, Finset.card_univ]

lemma card_eightSet : Fintype.card EightSet = Nat.choose Q 8 := by
  let : Fintype {S : Finset Question // S.card=8} := inferInstanceAs (Fintype EightSet)
  exact (card_subsets (α := Question) 8).trans (congrArg (fun n => Nat.choose n 8) card_question)

lemma card_basis_aux : Fintype.card Basis = Fintype.card LocalBasis ^ Fintype.card EightSet := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (show Basis ≃ (EightSet → LocalBasis) from Equiv.refl _)).trans Nat.card_fun

lemma card_localBasis : Fintype.card LocalBasis = 4 := by
  rw [Fintype.card_congr (show LocalBasis ≃ (Fin 2 × Fin 2) from Equiv.refl _),
    Fintype.card_prod, Fintype.card_fin]

lemma card_basis : Fintype.card Basis = D := by
  exact (card_basis_aux.trans (congrArg₂ (fun a b : ℕ => a^b) card_localBasis card_eightSet)).trans D_eq.symm

lemma card_outcomeString : Fintype.card OutcomeString = D :=
  (Fintype.card_congr (show OutcomeString ≃ Basis from Equiv.refl _)).trans card_basis

lemma card_label : Fintype.card Label = m := by
  rw [Fintype.card_congr (show Label ≃ (Question × OutcomeString) from Equiv.refl _)]
  rw [Fintype.card_prod, card_question, card_outcomeString]
  exact m_eq.symm

def basisOrder : Fin D ≃o Basis := Fintype.orderIsoFinOfCardEq Basis card_basis

def labelOrder : Fin m ≃o Label := Fintype.orderIsoFinOfCardEq Label (by
  have cardContaining {α : Type} [Fintype α] [DecidableEq α]
      (a : α) (r : ℕ) (hr : 1 ≤ r)
      [Fintype {A : Finset α // A.card = r ∧ a ∈ A}] :
      Fintype.card {A : Finset α // A.card = r ∧ a ∈ A} =
        Nat.choose (Fintype.card α - 1) (r - 1) := by
    as_aux_lemma =>
      rw [Fintype.card_of_subtype
        (((Finset.univ : Finset α).powersetCard r).filter ({a} ⊆ ·)) (by
          intro A
          simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
            true_and, Finset.singleton_subset_iff])]
      rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)
        (by simpa only [Finset.card_singleton] using hr)]
      simp only [Finset.card_univ, Finset.card_singleton]
  have hbase : Fintype.card Base = b := by
    as_aux_lemma =>
      let : Fintype {A : Finset (Fin k) // A.card = 514 ∧ (0 : Fin k) ∈ A} :=
        inferInstanceAs (Fintype Base)
      have h := cardContaining (0 : Fin k) 514 (by decide)
      change Fintype.card Base = Nat.choose (Fintype.card (Fin k) - 1) (514 - 1) at h
      rw [Fintype.card_fin] at h
      delta b
      exact h.trans (congrArg₂ Nat.choose (show k - 1 = 1027 from rfl)
        (show 514 - 1 = 513 from rfl))
  have hquestion : Fintype.card Question = Q := by
    calc
      Fintype.card Question = Fintype.card (Fin 3 → Base) :=
        Fintype.card_congr (show Question ≃ (Fin 3 → Base) from Equiv.refl _)
      _ = Fintype.card Base ^ Fintype.card (Fin 3) := Fintype.card_fun
      _ = b ^ 3 := congrArg₂ (fun x y : ℕ => x ^ y) hbase (Fintype.card_fin 3)
      _ = Q := Q.eq_def.symm

  have height : Fintype.card EightSet = Nat.choose Q 8 := by
    as_aux_lemma =>
      let : Fintype {S : Finset Question // S.card = 8} := inferInstanceAs (Fintype EightSet)
      change Fintype.card {S : Finset Question // S.card = 8} = _
      rw [Fintype.card_of_subtype ((Finset.univ : Finset Question).powersetCard 8) (by
        intro S
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])]
      rw [Finset.card_powersetCard, Finset.card_univ, hquestion]
  have hlocal : Fintype.card Outcome = 4 := by
    as_aux_lemma =>
      rw [Fintype.card_congr (show Outcome ≃ (Fin 2 × Fin 2) from Equiv.refl _),
        Fintype.card_prod, Fintype.card_fin]
  have houtcome : Fintype.card OutcomeString = D := by
    as_aux_lemma =>
      calc
        Fintype.card OutcomeString = Fintype.card Outcome ^ Fintype.card EightSet := by
          rw [Fintype.card_congr (show OutcomeString ≃ (EightSet → Outcome) from Equiv.refl _),
            Fintype.card_fun]
        _ = 4 ^ Nat.choose Q 8 := congrArg₂ (fun a b : ℕ => a ^ b) hlocal height
        _ = D := by
          have hd (q : ℕ) : dimensionFunction q = 4 ^ Nat.choose q 8 := rfl
          symm
          unfold D
          exact hd Q
  rw [Fintype.card_congr (show Label ≃ (Question × OutcomeString) from Equiv.refl _)]
  rw [Fintype.card_prod, hquestion, houtcome]
  have hm (q d : ℕ) : outputDimensionFunction q d = q * d := rfl
  symm
  unfold m
  exact hm Q D)

def rhoFin : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  rho.submatrix (Prod.map labelOrder labelOrder) (Prod.map labelOrder labelOrder)

lemma overlap_symm (q r : Question) : overlap q r = overlap r q := by
  unfold overlap
  exact Finset.sum_congr rfl (fun h _ => mul_comm _ _)

lemma projection_transpose (i : Label) : (projection i)ᵀ = projection i := by
  ext h l
  have hh := congrArg (fun A : Matrix Basis Basis ℂ => A h l)
    (show (projection i)ᴴ=projection i from (projection_projection i).isSelfAdjoint)
  exact (projection_real i l h).symm.trans hh

lemma block_swap (i j : Label) : block i j = block j i := by
  by_cases h : overlap (ofLex i).1 (ofLex j).1 = 0
  · simp only [block, ← overlap_symm (ofLex i).1 (ofLex j).1, h,
      Complex.ofReal_zero, zero_smul]
  · unfold block
    rw [overlap_symm, (projection_commute i j h).eq]

lemma block_transpose (i j : Label) : (block i j)ᵀ = block i j := by
  by_cases h : overlap (ofLex i).1 (ofLex j).1 = 0
  · simp only [block, h, Complex.ofReal_zero, zero_smul, Matrix.transpose_zero]
  · unfold block
    rw [Matrix.transpose_smul, Matrix.transpose_mul, projection_transpose, projection_transpose,
      (projection_commute i j h).eq]

lemma block_diag (i : Label) : block i i = projection i := by
  unfold block
  rw [vector_unit, Complex.ofReal_one, one_smul, (projection_projection i).isIdempotentElem]

lemma rawOutput_trace (i j : Label × Label) :
    rawOutput i j = trace (block i.1 j.1 * block i.2 j.2) := by
  rw [← block_transpose i.1 j.1]
  simp only [rawOutput, trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

lemma rawOutput_crossed_diagonal (i j : Label) :
    rawOutput (i,j) (i,j) = trace (projection i * projection j) := by
  rw [rawOutput_trace, block_diag, block_diag]

def makeLabel (q : Question) (a : OutcomeString) : Label := toLex (q,a)

lemma projection_sum_makeLabel (q : Question) : ∑ a, projection (makeLabel q a) = 1 := projection_sum q

universe v2545_0

lemma sum_label {M : Type v2545_0} [AddCommMonoid M] (f : Label → M) :
    ∑ i, f i = ∑ q : Question, ∑ a : OutcomeString, f (makeLabel q a) := by
  exact (Equiv.sum_comp (show (Question × OutcomeString) ≃ Label from Equiv.refl _) f).symm.trans
    (Fintype.sum_prod_type _)

lemma sum_projection_pair_trace (q r : Question) :
    (∑ a : OutcomeString, ∑ b : OutcomeString,
      trace (projection (makeLabel q a) * projection (makeLabel r b))) = (D : ℂ) := by
  have h : (∑ a : OutcomeString, ∑ b : OutcomeString,
      projection (makeLabel q a) * projection (makeLabel r b)) = 1 := by
    simp_rw [← Finset.mul_sum, projection_sum_makeLabel, mul_one]
    exact projection_sum_makeLabel q
  have hh := congrArg Matrix.trace h
  simpa only [trace_sum, trace_one, card_basis] using hh

lemma rawOutput_trace_total : trace rawOutput = (Q^2*D : ℕ) := by
  change (∑ i : Label × Label, rawOutput i i) = _
  rw [Fintype.sum_prod_type]
  simp_rw [rawOutput_crossed_diagonal, sum_label]
  conv_lhs =>
    arg 2; ext q
    rw [Finset.sum_comm]
  simp_rw [sum_projection_pair_trace]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_question,
    Nat.cast_mul, Nat.cast_pow]
  ring

end Explicit

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

universe v2604_0 v2604_1

def Separable {ι : Type v2604_0} {κ : Type v2604_1} [Fintype ι] [Fintype κ]
    (R : Matrix (ι × κ) (ι × κ) ℂ) : Prop :=
  ∃ (n : ℕ) (A : Fin n → Matrix ι ι ℂ) (B : Fin n → Matrix κ κ ℂ),
    (∀ s, (A s).PosSemidef) ∧ (∀ s, (B s).PosSemidef) ∧ R = ∑ s, A s ⊗ₖ B s

open Finset

namespace Explicit

lemma Q_pos : 0 < Q := by unfold Q; exact pow_pos b_pos 3

lemma D_pos : 0 < D := by rw [D_eq]; exact pow_pos (by decide) _

end Explicit

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

section

universe v2846_0 v2846_1 v2846_2

variable {α : Type v2846_0} {β : Type v2846_1} {γ : Type v2846_2} [inst2846_0 : Fintype α] [inst2846_1 : Fintype β] [inst2846_2 : Fintype γ]

def projectionKraus (u : β → γ → ℝ) (P : β → Matrix α α ℂ) :
    (γ × α) → Matrix β α ℂ := fun s i a => (u i s.1 : ℂ) * P i s.2 a

omit inst2846_1 in
lemma projectionKraus_coeff [Fintype β] (u : β → γ → ℝ) (P : β → Matrix α α ℂ)
    (hP : ∀ i, (P i).IsHermitian) (i j : β) (a b : α) :
    (∑ s, projectionKraus u P s i a * star (projectionKraus u P s j b)) =
      (∑ h, (u i h : ℂ) * (u j h : ℂ)) * (P j * P i) b a := by
  simp only [projectionKraus, Fintype.sum_prod_type, star_mul, Complex.star_def,
    Complex.conj_ofReal]
  have hp (l : α) : star (P j l b) = P j b l := congrArg (fun A : Matrix α α ℂ => A b l) (hP j).eq
  simp only [← Complex.star_def, hp, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma projectionKraus_formula (u : β → γ → ℝ) (P : β → Matrix α α ℂ)
    (hP : ∀ i, (P i).IsHermitian) (U : Matrix α α ℂ) (i j : β) :
    (∑ s, projectionKraus u P s * U * (projectionKraus u P s)ᴴ) i j =
      trace (((∑ h, (u i h : ℂ) * (u j h : ℂ)) • (P j * P i)) * U) := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp only [Finset.sum_mul]
  calc
    _ = ∑ b, ∑ a, (∑ s, projectionKraus u P s i a * star (projectionKraus u P s j b)) * U a b := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = _ := by
      simp only [projectionKraus_coeff u P hP, trace, Matrix.diag_apply,
        Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]

end

namespace Explicit

def questionFin (i : Fin m) : Question := (ofLex (labelOrder i)).1

def projectionFin (i : Fin m) : Mat D := (projection (labelOrder i)).submatrix basisOrder basisOrder

def blockFin (i j : Fin m) : Mat D := (block (labelOrder i) (labelOrder j)).submatrix basisOrder basisOrder

def constructionMapFin : Mat D →ₗ[ℂ] Mat m := traceBlockMap blockFin

lemma projectionFin_hermitian (i : Fin m) : (projectionFin i).IsHermitian :=
  (show (projection (labelOrder i)).IsHermitian from
    (projection_projection (labelOrder i)).isSelfAdjoint).submatrix _

lemma blockFin_swap (i j : Fin m) : blockFin i j = blockFin j i := by
  unfold blockFin
  rw [block_swap]

lemma blockFin_formula (i j : Fin m) : blockFin i j =
    (overlap (questionFin i) (questionFin j) : ℂ) •
      (projectionFin i * projectionFin j) := by
  unfold blockFin block projectionFin
  change _ = (overlap (questionFin i) (questionFin j) : ℂ) • _
  have hh := (Matrix.submatrix_mul_equiv (projection (labelOrder i)) (projection (labelOrder j))
    basisOrder basisOrder.toEquiv basisOrder).symm
  exact congrArg (fun A : Mat D => (overlap (questionFin i) (questionFin j) : ℂ) • A) hh

lemma constructionMapFin_kraus (U : Mat D) : constructionMapFin U =
    ∑ s, projectionKraus (fun i => vector (questionFin i)) projectionFin s * U *
      (projectionKraus (fun i => vector (questionFin i)) projectionFin s)ᴴ := by
  ext i j
  change trace (blockFin i j * U) = _
  rw [projectionKraus_formula _ _ projectionFin_hermitian]
  rw [blockFin_swap i j, blockFin_formula]
  have hc : (overlap (questionFin j) (questionFin i) : ℂ) =
      ∑ h, (vector (questionFin i) h : ℂ) * (vector (questionFin j) h : ℂ) := by
    rw [overlap_symm]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
    rfl
  rw [hc]

lemma constructionMapFin_cp : CompletelyPositive constructionMapFin :=
  cp_of_kraus_representation _ _ constructionMapFin_kraus

lemma constructionMapFin_unit (x y : Fin D) (i j : Fin m) :
    constructionMapFin (matrixUnit x y) i j = blockFin i j y x := by
  change trace (blockFin i j * matrixUnit x y) = _
  simp [trace, Matrix.diag_apply, Matrix.mul_apply, matrixUnit, ite_and]

def omegaVector : Fin D × Fin D → ℂ := fun i => if i.1=i.2 then 1 else 0

def rawOutputFin : Matrix (Fin m × Fin m) (Fin m × Fin m) ℂ :=
  rawOutput.submatrix (Prod.map labelOrder labelOrder) (Prod.map labelOrder labelOrder)

lemma rawOutputFin_tensor : rawOutputFin =
    tensorMap constructionMapFin constructionMapFin (outer omegaVector omegaVector) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change rawOutput (labelOrder i, labelOrder a) (labelOrder j, labelOrder b) = _
  simp only [tensorMap, outer, omegaVector, constructionMapFin_unit, apply_ite,
    star_one, star_zero, ite_mul, one_mul, zero_mul, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ h, ∑ l, block (labelOrder i) (labelOrder j) l h *
    block (labelOrder a) (labelOrder b) l h) =
    ∑ h : Fin D, ∑ l : Fin D, block (labelOrder i) (labelOrder j) (basisOrder l) (basisOrder h) *
    block (labelOrder a) (labelOrder b) (basisOrder l) (basisOrder h)
  rw [← Equiv.sum_comp basisOrder.toEquiv]
  apply Finset.sum_congr rfl
  intro h _
  exact (Equiv.sum_comp basisOrder.toEquiv _).symm

lemma rawOutputFin_psd : rawOutputFin.PosSemidef := by
  rw [rawOutputFin_tensor]
  exact tensorMap_positive constructionMapFin_cp constructionMapFin_cp (outer_posSemidef _)

lemma rawOutputFin_trace : trace rawOutputFin = ((Q^2*D : ℕ) : ℂ) := by
  rw [← rawOutput_trace_total]
  unfold trace
  exact Equiv.sum_comp (labelOrder.toEquiv.prodCongr labelOrder.toEquiv)
    (fun x : Label × Label => rawOutput x x)

lemma rhoFin_eq : rhoFin = ((Q^2*D : ℕ) : ℂ)⁻¹ • rawOutputFin := rfl

lemma symbolic_normalization_ne_zero (q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
    ((q^2*d : ℕ) : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (mul_pos (pow_pos hq 2) hd).ne'

lemma normalization_ne_zero : ((Q^2*D : ℕ) : ℂ) ≠ 0 :=
  symbolic_normalization_ne_zero Q D Q_pos D_pos

lemma rhoFin_density : Density rhoFin := by
  rw [rhoFin_eq]
  constructor
  · exact rawOutputFin_psd.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [trace_smul, rawOutputFin_trace, smul_eq_mul, inv_mul_cancel₀ normalization_ne_zero]

end Explicit

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder

universe v3096_0 v3096_1 v3096_2 v3096_3 v3096_4

variable {A : Type v3096_0} {B : Type v3096_1} {C : Type v3096_2} [inst3096_0 : AddCommGroup A] [inst3096_1 : Module ℂ A] [inst3096_2 : One A]
  [inst3096_3 : AddCommGroup B] [inst3096_4 : Module ℂ B] [inst3096_5 : One B]
  [inst3096_6 : AddCommGroup C] [inst3096_7 : Module ℂ C] [inst3096_8 : One C]
  {ι : Type v3096_3} {κ : Type v3096_4} [inst3096_9 : Fintype ι] [inst3096_10 : Fintype κ] [inst3096_11 : DecidableEq ι] [inst3096_12 : DecidableEq κ]

universe v3101_0 v3101_1

abbrev ReferenceFunctional (A : Type v3101_0) [AddCommGroup A] [Module ℂ A]
    (ι : Type v3101_1) := A →ₗ[ℂ] Matrix ι ι ℂ

def PositiveFunctional [LE A] (S : ReferenceFunctional A ι) : Prop :=
  ∀ x, 0 ≤ x → (S x).PosSemidef

universe v3140_0 v3140_1 v3140_2

structure ObservableInstrument (O : Type v3140_0) [MeasurableSpace O]
    (A : Type v3140_1) (B : Type v3140_2) [AddCommGroup A] [Module ℂ A] [One A] [LE A]
    [AddCommGroup B] [Module ℂ B] [One B] [LE B] where
  operation : Set O → B →ₗ[ℂ] A
  positive : ∀ E, MeasurableSet E → ∀ x, 0 ≤ x → 0 ≤ operation E x
  total_unit : operation Set.univ 1 = 1

universe v3147_0

variable {O : Type v3147_0} [inst3147_0 : MeasurableSpace O] [inst3147_1 : LE A] [inst3147_2 : LE B]
  (J : ObservableInstrument O A B) (S : ReferenceFunctional A ι)

structure InstrumentRun where
  law : Measure O
  probability : IsProbabilityMeasure law
  posterior : O → ReferenceFunctional B ι
  posterior_positive : ∀ o, PositiveFunctional (posterior o)
  posterior_trace : ∀ o, trace (posterior o 1) = 1
  integrable : ∀ x i j, Integrable (fun o => posterior o x i j) law
  update : ∀ E, MeasurableSet E → ∀ x i j,
    (∫ o in E, posterior o x i j ∂law) = S (J.operation E x) i j

namespace InstrumentRun

variable (r : InstrumentRun J S)

omit inst3096_11 in
theorem reference_mean [DecidableEq ι] (i j : ι) :
    (∫ o, r.posterior o 1 i j ∂r.law) = S 1 i j := by
  simpa only [Measure.restrict_univ, J.total_unit] using
    r.update Set.univ MeasurableSet.univ 1 i j

end InstrumentRun

end UnrestrictedQuantum

namespace ZeroKey

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

open scoped ENNReal

section

universe v3216_0 v3216_1

theorem sample_instrument_kernel {S : Type v3216_0} {O : Type v3216_1} [MeasurableSpace S]
    [MeasurableSpace O] [StandardBorelSpace O] [Nonempty O]
    (κ : Kernel S O) [IsMarkovKernel κ] :
    ∃ f : S → I → O, Measurable (uncurry f) ∧
      (∀ s, volume.map (f s) = κ s) ∧
      ∀ (μ : Measure S) [IsFiniteMeasure μ],
        (μ.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
  obtain ⟨f,hf,hfLaw⟩ := κ.exists_measurable_map_eq_unitInterval
  change Measurable (fun p : S × I => f p.1 p.2) at hf
  refine ⟨f,hf,hfLaw,?_⟩
  intro μ hμ
  ext B hB
  rw [Measure.map_apply (measurable_fst.prodMk hf) hB,
    Measure.prod_apply (hB.preimage (measurable_fst.prodMk hf)),
    Measure.compProd_apply hB]
  congr 1
  funext s
  rw [← hfLaw s, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hB)]
  rfl

abbrev UniformTape := ℕ → I

def uniformTapeLaw : Measure UniformTape :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure I))

instance : IsProbabilityMeasure uniformTapeLaw := by
  unfold uniformTapeLaw
  infer_instance

end

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal

section

universe v3447_0

variable {Ω : Type v3447_0} {mΩ : MeasurableSpace Ω} [inst3447_0 : StandardBorelSpace Ω]
  {μ : Measure Ω} [inst3447_1 : IsFiniteMeasure μ]

lemma indicator_one_mul (s : Set Ω) (f : Ω → ℝ) :
    s.indicator (fun _ => (1:ℝ)) * f = s.indicator f := by
  ext x
  by_cases hx : x∈s <;> simp [hx]

lemma indicator_inter_one (s t : Set Ω) :
    (s∩t).indicator (fun _ => (1:ℝ)) =
      s.indicator (t.indicator (fun _ => (1:ℝ))) := by
  ext x
  by_cases hs : x∈s <;> by_cases ht : x∈t <;> simp [hs,ht]

lemma condIndep_condExp_right {C A B : MeasurableSpace Ω}
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hCA : C ≤ A)
    (h : CondIndep C A B hC μ) {t : Set Ω} (ht : MeasurableSet[B] t) :
    μ[t.indicator (fun _ => (1:ℝ)) | A] =ᵐ[μ]
      μ[t.indicator (fun _ => (1:ℝ)) | C] := by
  let f := t.indicator (fun _ : Ω => (1:ℝ))
  have hf : Integrable f μ := (integrable_const (1:ℝ)).indicator (hB t ht)
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hA hf
  · intro s hs hμs
    exact integrable_condExp.integrableOn
  · intro s hs hμs
    have hs' : MeasurableSet[mΩ] s := hA s hs
    have hsi : Integrable (s.indicator (fun _ : Ω => (1:ℝ))) μ :=
      (integrable_const (1:ℝ)).indicator hs'
    have hprod : Integrable (s.indicator (fun _ : Ω => (1:ℝ)) * μ[f | C]) μ := by
      rw [indicator_one_mul]
      exact integrable_condExp.indicator hs'
    have hp := condExp_mul_of_stronglyMeasurable_right
      (stronglyMeasurable_condExp (μ := μ) (m := C) (f := f)) hprod hsi
    rw [indicator_one_mul] at hp
    have hh := ((condIndep_iff C A B hC hA hB μ).mp h) s t hs ht
    change μ[(s∩t).indicator (fun _ => (1:ℝ)) | C] =ᵐ[μ]
      μ[s.indicator (fun _ => (1:ℝ)) | C] * μ[f | C] at hh
    calc
      (∫ x in s, μ[f | C] x ∂μ) = ∫ x, s.indicator (μ[f | C]) x ∂μ :=
        (integral_indicator hs').symm
      _ = ∫ x, μ[s.indicator (μ[f | C]) | C] x ∂μ := (integral_condExp hC).symm
      _ = ∫ x, μ[(s∩t).indicator (fun _ => (1:ℝ)) | C] x ∂μ :=
        integral_congr_ae (hp.trans hh.symm)
      _ = ∫ x, (s∩t).indicator (fun _ => (1:ℝ)) x ∂μ := integral_condExp hC
      _ = ∫ x in s, f x ∂μ := by
        rw [indicator_inter_one, integral_indicator hs']
  · exact (stronglyMeasurable_condExp.mono hCA).aestronglyMeasurable

lemma condIndep_local_refinement {C N A B : MeasurableSpace Ω}
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hCA : C ≤ A) (hCN : C ≤ N) (hNA : N ≤ A)
    (h : CondIndep C A B hC μ) :
    CondIndep N A B (hNA.trans hA) μ := by
  have hN := hNA.trans hA
  rw [condIndep_iff N A B hN hA hB]
  intro s t hs ht
  let f := t.indicator (fun _ : Ω => (1:ℝ))
  have hf : Integrable f μ := (integrable_const (1:ℝ)).indicator (hB t ht)
  have hp : μ[f | A] =ᵐ[μ] μ[f | C] := condIndep_condExp_right hC hA hB hCA h ht
  have hcN : μ[μ[f | C] | N] = μ[f | C] :=
    condExp_of_stronglyMeasurable hN (stronglyMeasurable_condExp.mono hCN) integrable_condExp
  have htN : μ[f | N] =ᵐ[μ] μ[f | C] := by
    calc
      _ =ᵐ[μ] μ[μ[f | A] | N] := (condExp_condExp_of_le hNA hA).symm
      _ =ᵐ[μ] μ[μ[f | C] | N] := condExp_congr_ae hp
      _ =ᵐ[μ] μ[f | C] := by rw [hcN]
  have hsep : μ[s.indicator f | A] =ᵐ[μ] s.indicator (μ[f | C]) := by
    apply (condExp_indicator hf hs).trans
    filter_upwards [hp] with x hx
    by_cases hxs : x∈s <;> simp [hxs,hx]
  have hsi : Integrable (s.indicator (fun _ : Ω => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (hA s hs)
  have hprod : Integrable (s.indicator (fun _ : Ω => (1:ℝ)) * μ[f | C]) μ := by
    rw [indicator_one_mul]
    exact integrable_condExp.indicator (hA s hs)
  have hpull := condExp_mul_of_stronglyMeasurable_right
    (stronglyMeasurable_condExp.mono hCN) hprod hsi
  rw [indicator_one_mul] at hpull
  change μ[(s∩t).indicator (fun _ => (1:ℝ)) | N] =ᵐ[μ]
    μ[s.indicator (fun _ => (1:ℝ)) | N] * μ[f | N]
  rw [indicator_inter_one]
  calc
    _ =ᵐ[μ] μ[μ[s.indicator f | A] | N] := (condExp_condExp_of_le hNA hA).symm
    _ =ᵐ[μ] μ[s.indicator (μ[f | C]) | N] := condExp_congr_ae hsep
    _ =ᵐ[μ] μ[s.indicator (fun _ => (1:ℝ)) | N] * μ[f | C] := hpull
    _ =ᵐ[μ] _ := by
      filter_upwards [htN] with x hx
      simp only [Pi.mul_apply, hx]

def recordInterFamily (B C : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ b n, MeasurableSet[B] b ∧ MeasurableSet[C] n ∧ s = b∩n}

lemma recordInterFamily_pi (B C : MeasurableSpace Ω) : IsPiSystem (recordInterFamily B C) := by
  rintro s ⟨b,n,hb,hn,rfl⟩ t ⟨b',n',hb',hn',rfl⟩ _
  refine ⟨b∩b',n∩n',hb.inter hb',hn.inter hn',?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

lemma recordInterFamily_generate (B C : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (recordInterFamily B C) = B ⊔ C := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨b,n,hb,hn,rfl⟩
    exact ((show B ≤ B ⊔ C from le_sup_left) b hb).inter
      ((show C ≤ B ⊔ C from le_sup_right) n hn)
  · apply sup_le
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨s,Set.univ,hs,MeasurableSet.univ,(Set.inter_univ s).symm⟩
    · intro s hs
      apply MeasurableSpace.measurableSet_generateFrom
      exact ⟨Set.univ,s,MeasurableSet.univ,hs,(Set.univ_inter s).symm⟩

lemma condIndep_join_public_right {C A B : MeasurableSpace Ω}
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndep C A B hC μ) : CondIndep C A (B ⊔ C) hC μ := by
  let p : Set (Set Ω) := {s | MeasurableSet[A] s}
  have hp : IsPiSystem p := by
    intro s hs t ht _
    exact hs.inter ht
  have hpg : A = MeasurableSpace.generateFrom p :=
    (@MeasurableSpace.generateFrom_measurableSet Ω A).symm
  have hpM : ∀ s ∈ p, MeasurableSet[mΩ] s := hA
  have hrM : ∀ s ∈ recordInterFamily B C, MeasurableSet[mΩ] s := by
    rintro s ⟨b,n,hb,hn,rfl⟩
    exact (hB b hb).inter (hC n hn)
  apply CondIndepSets.condIndep hA (sup_le hB hC) hp (recordInterFamily_pi B C)
    hpg (recordInterFamily_generate B C).symm
  rw [condIndepSets_iff C hC p (recordInterFamily B C) hpM hrM μ]
  rintro s _ hs ⟨b,n,hb,hn,rfl⟩
  have hsb : Integrable ((s∩b).indicator (fun _ : Ω => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator ((hA s hs).inter (hB b hb))
  have hbI : Integrable (b.indicator (fun _ : Ω => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (hB b hb)
  have hleft := condExp_indicator hsb hn
  have hright := condExp_indicator hbI hn
  have he1 : (s∩(b∩n)).indicator (fun _ : Ω => (1:ℝ)) =
      n.indicator ((s∩b).indicator (fun _ : Ω => (1:ℝ))) := by
    ext x
    by_cases hx : x∈n <;> by_cases hsx : x∈s <;> by_cases hbx : x∈b <;> simp [hx,hsx,hbx]
  have he2 : (b∩n).indicator (fun _ : Ω => (1:ℝ)) =
      n.indicator (b.indicator (fun _ : Ω => (1:ℝ))) := by
    ext x
    by_cases hx : x∈n <;> by_cases hbx : x∈b <;> simp [hx,hbx]
  have hfactor := (condIndep_iff C A B hC hA hB μ).mp h s b hs hb
  change μ[(s∩(b∩n)).indicator (fun _ => (1:ℝ)) | C] =ᵐ[μ]
    μ[s.indicator (fun _ => (1:ℝ)) | C] * μ[(b∩n).indicator (fun _ => (1:ℝ)) | C]
  rw [he1,he2]
  filter_upwards [hleft,hright,hfactor] with x hx hy hz
  change μ[n.indicator ((s∩b).indicator (fun _ => (1:ℝ))) | C] x =
    μ[s.indicator (fun _ => (1:ℝ)) | C] x *
      μ[n.indicator (b.indicator (fun _ => (1:ℝ))) | C] x
  rw [hx,hy]
  by_cases hxn : x∈n <;> simp [hxn,Pi.mul_apply] at hz ⊢
  exact hz

lemma condIndep_local_message {C N A B : MeasurableSpace Ω}
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ) (hCN : C ≤ N)
    (hNA : N ≤ A ⊔ C) (h : CondIndep C A B hC μ) :
    CondIndep N A B (hNA.trans (sup_le hA hC)) μ := by
  have hjoin : CondIndep C (A ⊔ C) B hC μ :=
    (condIndep_join_public_right hC hB hA h.symm).symm
  have href := condIndep_local_refinement hC (sup_le hA hC) hB
    le_sup_right hCN hNA hjoin
  exact condIndep_of_condIndep_of_le_left href le_sup_left

end

universe v3643_0

lemma condFactor_full_transcript {Ω : Type v3643_0} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [inst3643_0 : IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (f g : Ω → ℝ)
    (h : ∀ n, μ[f*g | ℱ n] =ᵐ[μ] μ[f | ℱ n] * μ[g | ℱ n]) :
    μ[f*g | ⨆ n, ℱ n] =ᵐ[μ] μ[f | ⨆ n, ℱ n] * μ[g | ⨆ n, ℱ n] := by
  have he : ∀ᵐ x ∂μ, ∀ n, μ[f*g | ℱ n] x = μ[f | ℱ n] x * μ[g | ℱ n] x :=
    ae_all_iff.mpr h
  filter_upwards [he, tendsto_ae_condExp (ℱ := ℱ) (f*g),
    tendsto_ae_condExp (ℱ := ℱ) f, tendsto_ae_condExp (ℱ := ℱ) g] with x hx hfg hf hg
  exact tendsto_nhds_unique hfg ((hf.mul hg).congr (fun n => (hx n).symm))

lemma condIndep_full_transcript {Ω : Type v3643_0} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [inst3643_0 : IsFiniteMeasure μ]
    [StandardBorelSpace Ω]
    (ℱ : Filtration ℕ mΩ) (mA mB : MeasurableSpace Ω) (hA : mA ≤ mΩ) (hB : mB ≤ mΩ)
    (h : ∀ n, CondIndep (ℱ n) mA mB (ℱ.le n) μ) :
    CondIndep (⨆ n, ℱ n) mA mB (iSup_le fun n => ℱ.le n) μ := by
  rw [condIndep_iff _ _ _ _ hA hB]
  intro s t hs ht
  have hh (n : ℕ) := (condIndep_iff _ _ _ _ hA hB μ).mp (h n) s t hs ht
  have he : (s ∩ t).indicator (fun _ : Ω => (1:ℝ)) =
      s.indicator (fun _ : Ω => (1:ℝ)) * t.indicator (fun _ : Ω => (1:ℝ)) := by
    ext x
    by_cases hxs : x∈s <;> by_cases hxt : x∈t <;> simp [hxs,hxt]
  simpa only [he] using condFactor_full_transcript ℱ (s.indicator (fun _ => (1:ℝ)))
    (t.indicator (fun _ => (1:ℝ))) (by simpa only [he] using hh)

open MeasureTheory ProbabilityTheory Function Set

section

universe v3698_0

lemma indep_condIndep_bot {Ω : Type v3698_0} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {A B : MeasurableSpace Ω} (hA : A ≤ mΩ) (hB : B ≤ mΩ) (h : Indep A B P) :
    CondIndep ⊥ A B bot_le P := by
  rw [condIndep_iff _ _ _ _ hA hB]
  intro s t hs ht
  have hmul := (h.indepSet_of_measurableSet hs ht).measure_inter_eq_mul
  simp only [condExp_bot, integral_indicator (hA s hs), integral_indicator (hB t ht),
    integral_indicator ((hA s hs).inter (hB t ht)), integral_const,
    smul_eq_mul, mul_one]
  exact Filter.Eventually.of_forall fun _ => by
    simpa only [Measure.real, Measure.restrict_apply_univ, Pi.mul_apply, ENNReal.toReal_mul] using congrArg ENNReal.toReal hmul

universe v3715_0 v3715_1 v3715_2

structure LocalTapeProgram (U : Type v3715_0) (V : Type v3715_1) (M : Type v3715_2) [MeasurableSpace U]
    [MeasurableSpace V] [MeasurableSpace M] where
  alice : ℕ → Bool
  sendA : (n : ℕ) → U × (Fin n → M) → M
  sendB : (n : ℕ) → V × (Fin n → M) → M
  measA : ∀ n, Measurable (sendA n)
  measB : ∀ n, Measurable (sendB n)

namespace LocalTapeProgram

universe v3724_0 v3724_1 v3724_2

variable {U : Type v3724_0} {V : Type v3724_1} {M : Type v3724_2} [inst3724_0 : MeasurableSpace U] [inst3724_1 : MeasurableSpace V] [inst3724_2 : MeasurableSpace M]
  (p : LocalTapeProgram U V M)

def publicPrefix : (n : ℕ) → U × V → (Fin n → M)
  | 0, _ => Fin.elim0
  | n+1, ω => Fin.snoc (publicPrefix n ω)
      (if p.alice n then p.sendA n (ω.1,publicPrefix n ω) else p.sendB n (ω.2,publicPrefix n ω))

end LocalTapeProgram

end

open MeasureTheory ProbabilityTheory Function Set unitInterval

universe v3943_0 v3943_1

structure LocalOutcomeSampler (O : Type v3943_0) (M : Type v3943_1) [MeasurableSpace O] [MeasurableSpace M] where
  alice : ℕ → Bool
  sampleA : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × I → O
  sampleB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × I → O
  sendA : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M
  sendB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M
  sampleA_meas : ∀ n, Measurable (sampleA n)
  sampleB_meas : ∀ n, Measurable (sampleB n)
  sendA_meas : ∀ n, Measurable (sendA n)
  sendB_meas : ∀ n, Measurable (sendB n)

namespace LocalOutcomeSampler

universe v3955_0 v3955_1

variable {O : Type v3955_0} {M : Type v3955_1} [inst3955_0 : MeasurableSpace O] [inst3955_1 : MeasurableSpace M]
  (p : LocalOutcomeSampler O M)

def privatePrefix (a : Bool) : (n : ℕ) → UniformTape × (Fin n → M) → (Fin n → (O ⊕ Unit))
  | 0, _ => Fin.elim0
  | n+1, pair =>
    let old := privatePrefix a n (pair.1,fun i => pair.2 i.castSucc)
    let pubPast := fun i : Fin n => pair.2 i.castSucc
    Fin.snoc old (if p.alice n = a then Sum.inl
      (if a then p.sampleA n ((old,pubPast),pair.1 n)
       else p.sampleB n ((old,pubPast),pair.1 n)) else Sum.inr ())

def extractPrivate (a : Bool) (n : ℕ) (x : Fin n → O) : Fin n → (O ⊕ Unit) :=
  fun i => if p.alice i = a then Sum.inl (x i) else Sum.inr ()

def publicFrom : (n : ℕ) → (Fin n → O) → (Fin n → M)
  | 0, _ => Fin.elim0
  | n+1, x =>
    let old := fun i : Fin n => x i.castSucc
    let pubPast := publicFrom n old
    Fin.snoc pubPast (if p.alice n then
      p.sendA n ((p.extractPrivate true n old,pubPast),x (Fin.last n)) else
      p.sendB n ((p.extractPrivate false n old,pubPast),x (Fin.last n)))

end LocalOutcomeSampler

end

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

universe v4350_0 v4350_1

open scoped Matrix.Norms.L2Operator in
instance matrixMeasurableSpace {m : Type v4350_0} {n : Type v4350_1} [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) := borel _

universe v4353_0 v4353_1

open scoped Matrix.Norms.L2Operator in
instance matrixBorelSpace {m : Type v4353_0} {n : Type v4353_1} [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

universe v4357_0 v4357_1

variable {Ω : Type v4357_0} {ι : Type v4357_1} [inst4357_0 : MeasurableSpace Ω] [inst4357_1 : Fintype ι] [inst4357_2 : DecidableEq ι]

universe v4361_0 v4361_1

structure PositiveMatrixMeasure (Ω : Type v4361_0) (ι : Type v4361_1) [MeasurableSpace Ω] [Fintype ι] where
  entry : ι → ι → ComplexMeasure Ω
  positive : ∀ S, MeasurableSet S → Matrix.PosSemidef (fun i j => entry i j S)

namespace PositiveMatrixMeasure

def value (W : PositiveMatrixMeasure Ω ι) (S : Set Ω) : Matrix ι ι ℂ := fun i j => W.entry i j S

def density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) : Ω → Matrix ι ι ℂ :=
  fun t i j => (W.entry i j).rnDeriv μ t

omit inst4357_2 in
lemma measurable_density [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) :
    Measurable (W.density μ) := by
  have hh : Measurable (fun t i j => (W.entry i j).rnDeriv μ t) := by
    apply Measurable.of_eval; intro i
    apply Measurable.of_eval; intro j
    unfold ComplexMeasure.rnDeriv
    simp only [Complex.mk_eq_add_mul_I]
    apply Measurable.add
    · exact Complex.measurable_ofReal.comp ((W.entry i j).re.measurable_rnDeriv μ)
    · exact (Complex.measurable_ofReal.comp ((W.entry i j).im.measurable_rnDeriv μ)).mul_const Complex.I

  have hc : Continuous (Matrix.of : (ι → ι → ℂ) → Matrix ι ι ℂ) := by
    exact continuous_matrix (fun i j => continuous_apply_apply i j)
  exact hc.measurable.comp hh

omit inst4357_2 in
lemma integrable_entry [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) (i j : ι) :
    Integrable (fun t => W.density μ t i j) μ := (W.entry i j).integrable_rnDeriv μ

omit inst4357_2 in
lemma entry_absolutelyContinuous [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω)
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0) (i j : ι) :
    W.entry i j ≪ᵥ μ.toENNRealVectorMeasure := by
  intro S hS
  by_cases hs : MeasurableSet S
  · have hm : μ S = 0 := by simpa [Measure.toENNRealVectorMeasure_apply,hs] using hS
    exact congrArg (fun M : Matrix ι ι ℂ => M i j) (hAC S hs hm)
  · exact (W.entry i j).not_measurable hs

lemma integral_density_entry (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0)
    (S : Set Ω) (hS : MeasurableSet S) (i j : ι) :
    (∫ t in S, W.density μ t i j ∂μ) = W.value S i j := by
  have h := (ComplexMeasure.absolutelyContinuous_ennreal_iff _ _).mp
    (W.entry_absolutelyContinuous μ hAC i j)
  apply Complex.ext
  · have hh := congrArg (fun s : SignedMeasure Ω => s S)
      (SignedMeasure.withDensityᵥ_rnDeriv_eq (W.entry i j).re μ h.1)
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hS] at hh
    change RCLike.re (∫ t in S, W.density μ t i j ∂μ) = _
    rw [← integral_re ((W.integrable_entry μ i j).integrableOn)]
    exact hh
  · have hh := congrArg (fun s : SignedMeasure Ω => s S)
      (SignedMeasure.withDensityᵥ_rnDeriv_eq (W.entry i j).im μ h.2)
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hS] at hh
    change RCLike.im (∫ t in S, W.density μ t i j ∂μ) = _
    rw [← integral_im ((W.integrable_entry μ i j).integrableOn)]
    exact hh

end PositiveMatrixMeasure

lemma ae_complex_nonneg_of_integral_nonneg {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ)
    (h : ∀ S, MeasurableSet S → μ S < ⊤ → 0 ≤ ∫ t in S, f t ∂μ) :
    ∀ᵐ t ∂μ, 0 ≤ f t := by
  have hre : ∀ᵐ t ∂μ, 0 ≤ (f t).re := by
    apply ae_nonneg_of_forall_setIntegral_nonneg hf.re
    intro S hs hm
    rw [integral_re hf.integrableOn]
    exact (RCLike.nonneg_iff.mp (h S hs hm)).1
  have him : (fun t => (f t).im) =ᵐ[μ] fun _ => (0:ℝ) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hf.im (integrable_zero _ _ _)
    intro S hs hm
    rw [integral_im hf.integrableOn]
    simp only [Pi.zero_apply,integral_zero]
    exact (RCLike.nonneg_iff.mp (h S hs hm)).2
  filter_upwards [hre,him] with t ht hi
  exact RCLike.nonneg_iff.mpr ⟨ht,hi⟩

def quadraticValue (v : ι → ℂ) (M : Matrix ι ι ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * M i j * v j

omit inst4357_2 in
lemma quadraticValue_eq [DecidableEq ι] (v : ι → ℂ) (M : Matrix ι ι ℂ) :
    quadraticValue v M = star v ⬝ᵥ (M *ᵥ v) := by
  simp [quadraticValue,dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]

omit inst4357_2 in
lemma integrable_quadraticValue [DecidableEq ι] {μ : Measure Ω} {F : Ω → Matrix ι ι ℂ}
    (hF : ∀ i j, Integrable (fun t => F t i j) μ) (v : ι → ℂ) :
    Integrable (fun t => quadraticValue v (F t)) μ := by
  apply integrable_finsetSum; intro i _
  apply integrable_finsetSum; intro j _
  exact ((hF i j).const_mul _).mul_const _

omit inst4357_2 in
lemma integral_quadraticValue [DecidableEq ι] {μ : Measure Ω} {F : Ω → Matrix ι ι ℂ}
    (hF : ∀ i j, Integrable (fun t => F t i j) μ) (v : ι → ℂ) :
    (∫ t, quadraticValue v (F t) ∂μ) = quadraticValue v (fun i j => ∫ t, F t i j ∂μ) := by
  unfold quadraticValue
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => ((hF i j).const_mul _).mul_const _))]
  apply Finset.sum_congr rfl; intro i _
  rw [integral_finsetSum _ (fun j _ => ((hF i j).const_mul _).mul_const _)]
  apply Finset.sum_congr rfl; intro j _
  rw [integral_mul_const,integral_const_mul]

lemma density_posSemidef_ae (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S = 0 → W.value S = 0) :
    ∀ᵐ t ∂μ, (W.density μ t).PosSemidef := by
  have hherm : ∀ᵐ t ∂μ, (W.density μ t).IsHermitian := by
    have hij (i j : ι) : (fun t => star (W.density μ t j i)) =ᵐ[μ]
        (fun t => W.density μ t i j) := by
      apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
        ((Complex.conjCLE.integrable_comp_iff).mpr (W.integrable_entry μ j i)) (W.integrable_entry μ i j)
      intro S hs hm
      simp only [Complex.conjCLE_apply,integral_conj,W.integral_density_entry μ hAC S hs]
      exact congrArg (fun M : Matrix ι ι ℂ => M i j) (W.positive S hs).isHermitian.eq
    have hh : ∀ᵐ t ∂μ, ∀ i j, star (W.density μ t j i)=W.density μ t i j :=
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (hij i))
    filter_upwards [hh] with t ht
    exact Matrix.IsHermitian.ext ht
  have hq (v : ι → ℂ) : ∀ᵐ t ∂μ, 0 ≤ quadraticValue v (W.density μ t) := by
    apply ae_complex_nonneg_of_integral_nonneg
      (integrable_quadraticValue (W.integrable_entry μ) v)
    intro S hs hm
    rw [integral_quadraticValue (fun i j => (W.integrable_entry μ i j).integrableOn)]
    simp only [W.integral_density_entry μ hAC S hs]
    change 0 ≤ quadraticValue v (W.value S)
    rw [quadraticValue_eq]
    exact (W.positive S hs).dotProduct_mulVec_nonneg v
  obtain ⟨s,hs,hd⟩ := TopologicalSpace.exists_countable_dense (ι → ℂ)
  let : Countable s := hs.to_subtype
  have hqs : ∀ᵐ t ∂μ, ∀ v : s, 0 ≤ quadraticValue v (W.density μ t) :=
    ae_all_iff.mpr (fun v => hq v)
  filter_upwards [hherm,hqs] with t ht hqt
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨ht,fun v => ?_⟩
  rw [← quadraticValue_eq]
  refine hd.denseRange_val.induction_on (p := fun v => 0 ≤ quadraticValue v (W.density μ t)) v ?_ hqt
  · apply isClosed_le continuous_const
    unfold quadraticValue
    fun_prop

end

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ProbabilityTheory ENNReal NNReal Topology

universe v4526_0

lemma psd_entry_norm_le_trace {ι : Type v4526_0} [inst4526_0 : Fintype ι]
    [inst4526_1 : DecidableEq ι]
    {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (i j : ι) :
    ‖M i j‖ ≤ (trace M).re := by
  let S := CFC.sqrt M
  have hS : S.IsHermitian := (CFC.sqrt_nonneg M).isSelfAdjoint.isHermitian
  have hSS : S * Sᴴ = M := by rw [hS.eq]; exact CFC.sqrt_mul_sqrt_self M hM.nonneg
  let v (i : ι) : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun k => S i k)
  have he (i j : ι) : M i j = inner ℂ (v j) (v i) := by
    rw [← hSS]
    simp [v,Matrix.mul_apply,EuclideanSpace.inner_toLp_toLp,dotProduct]
  have hv (i : ι) : ‖v i‖ = Real.sqrt (M i i).re := by
    rw [he]; exact norm_eq_sqrt_re_inner (𝕜 := ℂ) (v i)
  have hdiag (i : ι) : (M i i).re ≤ (trace M).re := by
    change (M i i).re ≤ (∑ k, M k k).re
    rw [Complex.re_sum]
    exact Finset.single_le_sum (fun k _ => (RCLike.nonneg_iff.mp (hM.diag_nonneg (i:=k))).1) (Finset.mem_univ i)
  have ht : 0 ≤ (trace M).re := (RCLike.nonneg_iff.mp hM.trace_nonneg).1
  calc
    ‖M i j‖ ≤ ‖v j‖ * ‖v i‖ := by rw [he]; exact norm_inner_le_norm _ _
    _ ≤ Real.sqrt (trace M).re * Real.sqrt (trace M).re := by
      rw [hv,hv]
      exact mul_le_mul (Real.sqrt_le_sqrt (hdiag j)) (Real.sqrt_le_sqrt (hdiag i))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (trace M).re := Real.mul_self_sqrt ht

universe v4553_0

lemma uniformIntegrable_of_ae_norm_le_one {Ω : Type v4553_0} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [inst4553_0 : IsFiniteMeasure μ]
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hb : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ 1) :
    UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of le_rfl ENNReal.one_ne_top hf
  intro ε hε
  refine ⟨2, fun n => ?_⟩
  have hz : ({ω | (2:ℝ≥0) ≤ ‖f n ω‖₊}.indicator (f n)) =ᵐ[μ] 0 := by
    filter_upwards [hb n] with ω hω
    rw [Set.indicator_of_notMem]
    · rfl
    · simp only [Set.mem_ofPred_eq,not_le]
      have : ‖f n ω‖₊ ≤ (1:ℝ≥0) := hω
      exact lt_of_le_of_lt this (by norm_num)
  rw [eLpNorm_congr_ae hz,eLpNorm_zero]
  exact bot_le

lemma bounded_martingale_limit {Ω : Type v4553_0} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [inst4553_0 : IsFiniteMeasure μ] {F : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hf : Martingale f F μ)
    (hb : ∀ n, ∀ᵐ ω ∂μ, ‖f n ω‖ ≤ 1) :
    ∃ g : Ω → ℝ, Integrable g μ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) ∧
      (∀ n, f n =ᵐ[μ] μ[g | F n]) := by
  have hui := uniformIntegrable_of_ae_norm_le_one
    (fun n => ((hf.stronglyMeasurable n).mono (F.le n)).aestronglyMeasurable) hb
  refine ⟨F.limitProcess f μ, ?_, hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hui,
    hf.ae_eq_condExp_limitProcess hui⟩
  obtain ⟨R,hR⟩ := hui.2
  exact (hf.submartingale.memLp_limitProcess hR).integrable le_rfl

universe v4584_0 v4584_1

variable {Ω : Type v4584_0} {ι : Type v4584_1} [inst4584_0 : MeasurableSpace Ω] [inst4584_1 : Fintype ι] [inst4584_2 : DecidableEq ι]
  {μ : Measure Ω} {G : Ω → Matrix ι ι ℂ}

lemma integrable_matrix_of_entries (hG : ∀ i j, Integrable (fun ω => G ω i j) μ) :
    Integrable G μ := by
  have h : Integrable (fun ω i j => G ω i j) μ :=
    integrable_pi_iff.mpr (fun i => integrable_pi_iff.mpr (hG i))
  let L : (ι → ι → ℂ) →L[ℂ] Matrix ι ι ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℂ).toLinearMap
  exact L.integrable_comp h

lemma integral_matrix_entry (hG : Integrable G μ) (i j : ι) :
    (∫ ω, G ω ∂μ) i j = ∫ ω, G ω i j ∂μ := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  exact (L.integral_comp_comm hG).symm

def positiveMatrixMeasureOfDensity (hG : ∀ i j, Integrable (fun ω => G ω i j) μ)
    (hp : ∀ᵐ ω ∂μ, (G ω).PosSemidef) : PositiveMatrixMeasure Ω ι where
  entry i j := μ.withDensityᵥ (fun ω => G ω i j)
  positive S hS := by
    have he : (fun i j => μ.withDensityᵥ (fun ω => G ω i j) S) = ∫ ω in S, G ω ∂μ := by
      ext i j
      rw [withDensityᵥ_apply (hG i j) hS,
        integral_matrix_entry (integrable_matrix_of_entries hG).integrableOn]
    rw [he]
    exact (integral_nonneg_of_ae ((ae_restrict_of_ae hp).mono (fun _ h => h.nonneg))).posSemidef

lemma positiveMatrixMeasureOfDensity_value
    (hG : ∀ i j, Integrable (fun ω => G ω i j) μ)
    (hp : ∀ᵐ ω ∂μ, (G ω).PosSemidef) (S : Set Ω) (hS : MeasurableSet S) :
    (positiveMatrixMeasureOfDensity hG hp).value S = ∫ ω in S, G ω ∂μ := by
  ext i j
  change μ.withDensityᵥ (fun ω => G ω i j) S = _
  rw [withDensityᵥ_apply (hG i j) hS,
    integral_matrix_entry (integrable_matrix_of_entries hG).integrableOn]

end

section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

universe v4714_0 v4714_1 v4714_2

variable {ι : Type v4714_0} {κ : Type v4714_1} {η : Type v4714_2} [inst4714_0 : Fintype ι] [inst4714_1 : Fintype κ] [inst4714_2 : Fintype η]
  [inst4714_3 : DecidableEq ι] [inst4714_4 : DecidableEq κ] [inst4714_5 : DecidableEq η]

def keepReference (U : Matrix (ι × η) (ι × η) ℂ) : Matrix η η ℂ :=
  fun x y => ∑ i, U (i,x) (i,y)

def referenceFilter (K : Matrix κ η ℂ) (U : Matrix (ι × η) (ι × η) ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  ((1 : Matrix ι ι ℂ) ⊗ₖ K) * U * ((1 : Matrix ι ι ℂ) ⊗ₖ K)ᴴ

omit inst4714_1 inst4714_4 inst4714_5 in
lemma referenceFilter_apply [Fintype κ] [DecidableEq κ] [DecidableEq η] (K : Matrix κ η ℂ) (U : Matrix (ι × η) (ι × η) ℂ)
    (i j : ι) (x y : κ) :
    referenceFilter K U (i,x) (j,y) = ∑ s, ∑ t, K x s * U (i,s) (j,t) * star (K y t) := by
  simp only [referenceFilter,Matrix.conjTranspose_kronecker,Matrix.conjTranspose_one]
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,
    Matrix.conjTranspose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma keepReference_filter (K : Matrix κ η ℂ) (U : Matrix (ι × η) (ι × η) ℂ) :
    keepReference (referenceFilter K U) = K * keepReference U * Kᴴ := by
  ext x y
  simp only [keepReference,referenceFilter_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  rw [Finset.sum_comm]

def vectorize (S : Matrix ι η ℂ) : ι × η → ℂ := fun p => S p.1 p.2

omit inst4714_2 inst4714_3 inst4714_5 in
lemma keepReference_vectorize [Fintype η] [DecidableEq ι] [DecidableEq η] (S : Matrix ι η ℂ) :
    keepReference (outer (vectorize S) (vectorize S)) = (Sᴴ*S)ᵀ := by
  ext x y
  simp only [keepReference,outer,vectorize,Matrix.transpose_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl; intro i _; ring

lemma referenceFilter_vectorize (K : Matrix κ η ℂ) (S : Matrix ι η ℂ) :
    referenceFilter K (outer (vectorize S) (vectorize S)) =
      outer (vectorize (S*Kᵀ)) (vectorize (S*Kᵀ)) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  rw [referenceFilter_apply]
  simp only [outer,vectorize,Matrix.mul_apply,Matrix.transpose_apply,star_sum,star_mul]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro t _
  ring

def localProbe : ι × ι → ℂ :=
  vectorize (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℂ) • (1 : Matrix ι ι ℂ))

def canonicalPurification (R : Matrix ι ι ℂ) : ι × ι → ℂ := vectorize (CFC.sqrt R)

def preparationFilter (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Real.sqrt (Fintype.card ι : ℝ) : ℂ) • (CFC.sqrt R)ᵀ

lemma preparation_filter_identity [Nonempty ι] (R : Matrix ι ι ℂ) :
    referenceFilter (preparationFilter R) (outer (localProbe (ι := ι)) localProbe) =
      outer (canonicalPurification R) (canonicalPurification R) := by
  unfold localProbe canonicalPurification preparationFilter
  rw [referenceFilter_vectorize,Matrix.transpose_smul,Matrix.transpose_transpose,
    Matrix.smul_mul,Matrix.mul_smul,one_mul,smul_smul]
  have hc : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)).ne'
  rw [inv_mul_cancel₀ hc,one_smul]

lemma canonical_reference (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    keepReference (outer (canonicalPurification R) (canonicalPurification R)) = Rᵀ := by
  rw [canonicalPurification,keepReference_vectorize,
    (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq,CFC.sqrt_mul_sqrt_self R hR.nonneg]

end

namespace PositiveMatrixMeasure

section

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

universe v4860_0 v4860_1

variable {Ω : Type v4860_0} {ι : Type v4860_1} [inst4860_0 : MeasurableSpace Ω] [inst4860_1 : Fintype ι] [inst4860_2 : DecidableEq ι]

def traceSigned (W : PositiveMatrixMeasure Ω ι) : SignedMeasure Ω :=
  ∑ i, (W.entry i i).re

omit inst4860_2 in
lemma traceSigned_apply [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (S : Set Ω) :
    W.traceSigned S = (trace (W.value S)).re := by
  simp [traceSigned,trace,value,ComplexMeasure.re_apply]
  apply Finset.sum_congr rfl; intro i _; rfl

lemma traceSigned_nonneg (W : PositiveMatrixMeasure Ω ι) :
    (0 : SignedMeasure Ω) ≤[Set.univ] W.traceSigned := by
  simpa only [VectorMeasure.restrict_univ] using (show (0 : SignedMeasure Ω) ≤ W.traceSigned from by
    intro S hS
    change 0 ≤ W.traceSigned S
    rw [traceSigned_apply]
    have hh : (0:ℂ) ≤ trace (W.value S) := (W.positive S hS).trace_nonneg
    exact (RCLike.nonneg_iff.mp hh).1)

def traceMeasure (W : PositiveMatrixMeasure Ω ι) : Measure Ω :=
  W.traceSigned.toMeasureOfZeroLE Set.univ MeasurableSet.univ (by
    simpa only [VectorMeasure.restrict_univ] using
      (show (0 : SignedMeasure Ω) ≤ W.traceSigned from by
        intro S hS
        have htrace : W.traceSigned S = (trace (W.value S)).re := by
          simp [traceSigned, trace, value, ComplexMeasure.re_apply]
          apply Finset.sum_congr rfl
          intro i _
          rfl
        change 0 ≤ W.traceSigned S
        rw [htrace]
        exact (RCLike.nonneg_iff.mp (W.positive S hS).trace_nonneg).1))

instance traceMeasure_finite (W : PositiveMatrixMeasure Ω ι) : IsFiniteMeasure W.traceMeasure :=
  inferInstanceAs (IsFiniteMeasure (W.traceSigned.toMeasureOfZeroLE Set.univ
    MeasurableSet.univ W.traceSigned_nonneg))

lemma integrable_trace_density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) :
    Integrable (fun t => trace (W.density μ t)) μ := by
  exact integrable_finsetSum _ (fun i _ => W.integrable_entry μ i i)

lemma integral_trace_density (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S=0 → W.value S=0)
    (S : Set Ω) (hS : MeasurableSet S) :
    (∫ t in S, trace (W.density μ t) ∂μ) = trace (W.value S) := by
  unfold trace diag
  rw [integral_finsetSum _ (fun i _ => (W.integrable_entry μ i i).integrableOn)]
  apply Finset.sum_congr rfl; intro i _
  exact W.integral_density_entry μ hAC S hS i i

universe v4989_0

def filter {κ : Type v4989_0} [Fintype κ] (W : PositiveMatrixMeasure Ω ι) (K : Matrix κ ι ℂ) :
    PositiveMatrixMeasure Ω κ where
  entry x y := ∑ i, ∑ j, (K x i * star (K y j)) • W.entry i j
  positive S hS := by
    have he : (fun x y => (∑ i, ∑ j, (K x i * star (K y j)) • W.entry i j) S) =
        K * W.value S * Kᴴ := by
      ext x y
      simp only [_root_.sum_apply,_root_.smul_apply,Matrix.mul_apply,
        Matrix.conjTranspose_apply,smul_eq_mul,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      dsimp [value]
      ring
    rw [he]
    exact (W.positive S hS).mul_mul_conjTranspose_same K

universe v5006_0

omit inst4860_2 in
lemma filter_value [DecidableEq ι] {κ : Type v5006_0} [Fintype κ] (W : PositiveMatrixMeasure Ω ι)
    (K : Matrix κ ι ℂ) (S : Set Ω) : (W.filter K).value S = K * W.value S * Kᴴ := by
  ext x y
  simp only [filter,value,_root_.sum_apply,_root_.smul_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,smul_eq_mul,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

end

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

universe v5077_0 v5077_1 v5077_2

variable {O : Type v5077_0} {ι : Type v5077_1} {η : Type v5077_2} [inst5077_0 : MeasurableSpace O] [inst5077_1 : Fintype ι] [inst5077_2 : Fintype η]
  [inst5077_3 : DecidableEq ι] [inst5077_4 : DecidableEq η]

universe v5098_0

def pushforward {T : Type v5098_0} [MeasurableSpace T] (W : PositiveMatrixMeasure O η)
    (f : O → T) (hf : Measurable f) : PositiveMatrixMeasure T η where
  entry i j := (W.entry i j).map f
  positive S hS := by
    simpa only [VectorMeasure.map_apply _ hf hS] using W.positive (f ⁻¹' S) (hf hS)

universe v5104_0

omit inst5077_4 in
lemma pushforward_value [DecidableEq η] {T : Type v5104_0} [MeasurableSpace T] (W : PositiveMatrixMeasure O η)
    (f : O → T) (hf : Measurable f) (S : Set T) (hS : MeasurableSet S) :
    (W.pushforward f hf).value S = W.value (f ⁻¹' S) := by
  ext i j; exact VectorMeasure.map_apply _ hf hS

end PositiveMatrixMeasure

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v5273_0

variable {O : Type v5273_0} [inst5273_0 : MeasurableSpace O]

def historyPrefix (n : ℕ) (x : ℕ → O) : Fin n → O := fun i => x i

lemma measurable_historyPrefix (n : ℕ) : Measurable (historyPrefix (O := O) n) := by
  unfold historyPrefix
  fun_prop

def historyFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → O)) where
  seq n := MeasurableSpace.comap (historyPrefix n) inferInstance
  mono' := by
    intro n k hnk
    apply MeasurableSpace.comap_le_iff_le_map.mpr
    intro S hS
    change MeasurableSet[MeasurableSpace.comap (historyPrefix k) inferInstance]
      (historyPrefix n ⁻¹' S)
    refine ⟨(fun s : Fin k → O => fun i : Fin n => s (Fin.castLE hnk i)) ⁻¹' S,
      (show Measurable (fun s : Fin k → O => fun i : Fin n => s (Fin.castLE hnk i)) by fun_prop) hS,?_⟩
    rfl
  le' n := (show Measurable (historyPrefix (O := O) n) by unfold historyPrefix; fun_prop).comap_le

lemma historyPrefix_adapted (n : ℕ) :
    Measurable[(historyFiltration (O := O)) n] (historyPrefix (O := O) n) :=
  Measurable.of_comap_le le_rfl

lemma historyFiltration_generates :
    (inferInstance : MeasurableSpace (ℕ → O)) = ⨆ n, historyFiltration (O := O) n := by
  apply le_antisymm
  · change (⨆ k : ℕ, MeasurableSpace.comap (fun x : ℕ → O => x k) inferInstance) ≤ _
    apply iSup_le
    intro k
    apply le_iSup_of_le (k+1)
    have hk := (measurable_pi_apply (⟨k,Nat.lt_succ_self k⟩ : Fin (k+1))).comp
      (historyPrefix_adapted (O := O) (k+1))
    exact hk.comap_le
  · exact iSup_le (fun n => (historyFiltration (O := O)).le n)

universe v5311_0

variable {ι : Type v5311_0} [inst5311_0 : Fintype ι] [inst5311_1 : DecidableEq ι]

universe v5313_0

lemma density_entry_bound {Ω : Type v5313_0} [MeasurableSpace Ω]
    (U : Ω → Matrix ι ι ℂ) (hU : ∀ x, Density (U x)) (i j : ι) (x : Ω) :
    ‖U x i j‖ ≤ 1 := by
  have h := psd_entry_norm_le_trace (hU x).1 i j
  simpa only [(hU x).2,Complex.one_re] using h

universe v5319_0

lemma integrable_density_entry {Ω : Type v5319_0} [MeasurableSpace Ω]
    (U : Ω → Matrix ι ι ℂ) (hU : ∀ x, Density (U x)) (hm : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] (i j : ι) :
    Integrable (fun x => U x i j) μ := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  exact Integrable.of_bound (L.continuous.measurable.comp hm).aestronglyMeasurable 1
    (Filter.Eventually.of_forall (density_entry_bound U hU i j))

variable (P : Measure (ℕ → O)) [inst5327_0 : IsProbabilityMeasure P]
    (K : (n : ℕ) → Kernel (Fin n → O) O) [inst5327_1 : ∀ n, IsMarkovKernel (K n)]
    (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ K n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
    (U : (n : ℕ) → (Fin n → O) → Matrix ι ι ℂ)
    (hU : ∀ n s, Density (U n s)) (hm : ∀ n, Measurable (U n))
    (hmean : ∀ n s i j,
      (∫ o, U (n+1) (Fin.snoc (α := fun _ : Fin (n+1) => O) s o) i j ∂K n s) = U n s i j)

include hP hU hm hmean in
lemma reference_history_step_integral (n : ℕ) (S : Set (ℕ → O))
    (hS : MeasurableSet[historyFiltration n] S) (i j : ι) :
    (∫ x in S, U (n+1) (historyPrefix (n+1) x) i j ∂P) =
      ∫ x in S, U n (historyPrefix n x) i j ∂P := by
  classical
  obtain ⟨A,hA,rfl⟩ := hS
  let r : (Fin (n+1) → O) → (Fin n → O) := fun s i => s i.castSucc
  have hr : Measurable r := by fun_prop
  let snoc : (Fin n → O) × O → (Fin (n+1) → O) := fun s => Fin.snoc s.1 s.2
  have hs : Measurable snoc := by
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [snoc] using measurable_snd
    · simpa only [snoc, Fin.snoc_castSucc, Function.comp_def] using ((measurable_pi_apply j).comp measurable_fst)
  let f : (Fin (n+1) → O) → ℂ := (r ⁻¹' A).indicator (fun s => U (n+1) s i j)
  let g : (Fin n → O) → ℂ := A.indicator (fun s => U n s i j)
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  have hf : Measurable f := (L.continuous.measurable.comp (hm (n+1))).indicator (hr hA)
  have hg : Measurable g := (L.continuous.measurable.comp (hm n)).indicator hA
  have hfi : Integrable (fun s => f (snoc s)) ((P.map (historyPrefix n)) ⊗ₘ K n) := by
    apply Integrable.of_bound (hf.comp hs).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro s
    exact (norm_indicator_le_norm_self (s := r ⁻¹' A) (fun t => U (n+1) t i j) (snoc s)).trans (density_entry_bound (U (n+1)) (hU (n+1)) i j _)
  have he (s : Fin n → O) : (∫ o, f (snoc (s,o)) ∂K n s) = g s := by
    have hh (o : O) : f (snoc (s,o)) =
        if s ∈ A then U (n+1) (Fin.snoc s o) i j else 0 := by
      simp only [f,Set.indicator,Set.mem_preimage,r,snoc]
      have ht : (fun i : Fin n => Fin.snoc (α := fun _ : Fin (n+1) => O) s o i.castSucc) = s := by
        ext i; simp
      rw [ht]
    simp_rw [hh]
    by_cases h : s ∈ A
    · simp only [h,ite_true,g,Set.indicator_of_mem]
      exact hmean n s i j
    · simp [h,g]
  calc
    _ = ∫ x, f (historyPrefix (n+1) x) ∂P := by
      rw [← integral_indicator ((measurable_historyPrefix n) hA)]
      congr 1
    _ = ∫ s, f s ∂P.map (historyPrefix (n+1)) :=
      (integral_map (measurable_historyPrefix _).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ s, f s ∂(((P.map (historyPrefix n)) ⊗ₘ K n).map snoc) := by rw [hP n]
    _ = ∫ s, f (snoc s) ∂((P.map (historyPrefix n)) ⊗ₘ K n) :=
      integral_map hs.aemeasurable hf.aestronglyMeasurable
    _ = ∫ s, ∫ o, f (snoc (s,o)) ∂K n s ∂P.map (historyPrefix n) :=
      MeasureTheory.Measure.integral_compProd hfi
    _ = ∫ s, g s ∂P.map (historyPrefix n) := by simp_rw [he]
    _ = ∫ x, g (historyPrefix n x) ∂P :=
      integral_map (measurable_historyPrefix n).aemeasurable hg.aestronglyMeasurable
    _ = _ := by
      rw [← integral_indicator ((measurable_historyPrefix n) hA)]
      rfl

include hP hU hm hmean in
lemma reference_history_integral (n k : ℕ) (hnk : n ≤ k) (S : Set (ℕ → O))
    (hS : MeasurableSet[historyFiltration n] S) (i j : ι) :
    (∫ x in S, U k (historyPrefix k x) i j ∂P) =
      ∫ x in S, U n (historyPrefix n x) i j ∂P := by
  induction k, hnk using Nat.le_induction with
  | base => rfl
  | succ k hnk ih =>
    rw [reference_history_step_integral P K hP U hU hm hmean k S
      (((historyFiltration (O := O)).mono hnk) S hS) i j]
    exact ih

omit inst5311_1 in
lemma reference_history_measurable [DecidableEq ι] (n : ℕ) (i j : ι) (hm : ∀ n, Measurable (U n)) :
    Measurable[historyFiltration n] (fun x => U n (historyPrefix n x) i j) := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap
  exact L.continuous.measurable.comp ((hm n).comp (historyPrefix_adapted n))

lemma reference_history_integrable (n : ℕ) (i j : ι) (hU : ∀ n s, Density (U n s))
    (hm : ∀ n, Measurable (U n)) :
    Integrable (fun x => U n (historyPrefix n x) i j) P := by
  exact integrable_density_entry (fun x => U n (historyPrefix n x))
    (fun x => hU n _) ((hm n).comp (measurable_historyPrefix n)) P i j

include hP hU hm hmean in
lemma reference_history_martingale_re (i j : ι) :
    Martingale (fun n x => (U n (historyPrefix n x) i j).re) historyFiltration P := by
  refine ⟨fun n => ((reference_history_measurable U n i j hm).re).stronglyMeasurable, ?_⟩
  intro n k hnk
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (historyFiltration.le n)
    ((reference_history_integrable P U k i j hU hm).re)
  · intro S _ _
    exact (reference_history_integrable P U n i j hU hm).re.integrableOn
  · intro S hS _
    change (∫ x in S, RCLike.re (U n (historyPrefix n x) i j) ∂P) = _
    rw [integral_re (reference_history_integrable P U n i j hU hm).integrableOn,
      integral_re (reference_history_integrable P U k i j hU hm).integrableOn,
      reference_history_integral P K hP U hU hm hmean n k hnk S hS i j]
  · exact ((reference_history_measurable U n i j hm).re).stronglyMeasurable.aestronglyMeasurable

include hP hU hm hmean in
lemma reference_history_martingale_im (i j : ι) :
    Martingale (fun n x => (U n (historyPrefix n x) i j).im) historyFiltration P := by
  refine ⟨fun n => ((reference_history_measurable U n i j hm).im).stronglyMeasurable, ?_⟩
  intro n k hnk
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (historyFiltration.le n)
    ((reference_history_integrable P U k i j hU hm).im)
  · intro S _ _
    exact (reference_history_integrable P U n i j hU hm).im.integrableOn
  · intro S hS _
    change (∫ x in S, RCLike.im (U n (historyPrefix n x) i j) ∂P) = _
    rw [integral_im (reference_history_integrable P U n i j hU hm).integrableOn,
      integral_im (reference_history_integrable P U k i j hU hm).integrableOn,
      reference_history_integral P K hP U hU hm hmean n k hnk S hS i j]
  · exact ((reference_history_measurable U n i j hm).im).stronglyMeasurable.aestronglyMeasurable

end

open MeasureTheory ProbabilityTheory Matrix Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

universe v5486_0 v5486_1

variable {Ω : Type v5486_0} {ι : Type v5486_1} {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst5486_0 : Fintype ι] [inst5486_1 : DecidableEq ι] {μ : Measure Ω} [inst5486_2 : IsFiniteMeasure μ]
  {F : Filtration ℕ mΩ}

theorem local_reference_limit
    (W : ℕ → Ω → Matrix ι ι ℂ)
    (hW : ∀ n x, Density (W n x))
    (hlocal : ∀ n, Measurable[L] (W n))
    (hL : L ≤ mΩ)
    (hr : ∀ i j, Martingale (fun n x => (W n x i j).re) F μ)
    (hi : ∀ i j, Martingale (fun n x => (W n x i j).im) F μ) :
    ∃ G : Ω → Matrix ι ι ℂ,
      Measurable[L] G ∧ (∀ x, Density (G x)) ∧
      (∀ i j, Integrable (fun x => G x i j) μ) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => W n x) atTop (𝓝 (G x))) ∧
      (∀ n S, MeasurableSet[F n] S →
        (∫ x in S, G x ∂μ) = ∫ x in S, W n x ∂μ) := by
  classical
  have hbound (n : ℕ) (i j : ι) (x : Ω) : ‖W n x i j‖ ≤ 1 := by
    simpa only [(hW n x).2, Complex.one_re] using
      psd_entry_norm_le_trace (hW n x).1 i j
  have hbr (i j : ι) (n : ℕ) : ∀ᵐ x ∂μ, ‖(W n x i j).re‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun x =>
      (show ‖(W n x i j).re‖ ≤ ‖W n x i j‖ from by
        simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (W n x i j)).trans
      (hbound n i j x))
  have hbi (i j : ι) (n : ℕ) : ∀ᵐ x ∂μ, ‖(W n x i j).im‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun x =>
      (show ‖(W n x i j).im‖ ≤ ‖W n x i j‖ from by
        simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm (W n x i j)).trans
      (hbound n i j x))
  choose gr hgr htr hcr using (fun i j => bounded_martingale_limit (hr i j) (hbr i j))
  choose gi hgi hti hci using (fun i j => bounded_martingale_limit (hi i j) (hbi i j))
  let H : Ω → Matrix ι ι ℂ := fun x i j => (gr i j x : ℂ) + (gi i j x : ℂ)*Complex.I
  have hH (i j : ι) : Integrable (fun x => H x i j) μ :=
    ((hgr i j).ofReal).add (((hgi i j).ofReal).mul_const Complex.I)
  have hlimH : ∀ᵐ x ∂μ, Tendsto (fun n => W n x) atTop (𝓝 (H x)) := by
    have htr' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (htr i))
    have hti' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (hti i))
    filter_upwards [htr', hti'] with x hx hy
    have hc : Tendsto (fun n i j => W n x i j) atTop (𝓝 (fun i j => H x i j)) := by
      apply tendsto_pi_nhds.mpr; intro i
      apply tendsto_pi_nhds.mpr; intro j
      have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hx i j)).add
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hy i j)).mul_const Complex.I)
      simpa only [Function.comp_apply, Pi.add_apply, Complex.re_add_im] using hh
    have hcM : Continuous (Matrix.of : (ι → ι → ℂ) → Matrix ι ι ℂ) :=
      continuous_matrix (fun i j => continuous_apply_apply i j)
    exact hcM.continuousAt.tendsto.comp hc
  let raw : Ω → Matrix ι ι ℂ := fun x => limUnder atTop (fun n => W n x)
  have hraw : Measurable[L] raw :=
    (@StronglyMeasurable.limUnder ℕ Ω (Matrix ι ι ℂ) L _ _ atTop _ _ _ _
      (fun n => (hlocal n).stronglyMeasurable)).measurable
  have hgood : MeasurableSet[L] {x | 0 ≤ raw x ∧ trace (raw x) = 1} := by
    exact (measurableSet_le measurable_const hraw).inter
      (measurableSet_eq_fun ((Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.continuous.measurable.comp hraw) measurable_const)
  let G : Ω → Matrix ι ι ℂ := fun x =>
    if 0 ≤ raw x ∧ trace (raw x) = 1 then raw x else W 0 x
  have hGm : Measurable[L] G := hraw.ite hgood (hlocal 0)
  have hGp (x : Ω) : Density (G x) := by
    dsimp [G]
    split
    · rename_i h
      exact ⟨h.1.posSemidef, h.2⟩
    · exact hW 0 x
  have hGH : G =ᵐ[μ] H := by
    filter_upwards [hlimH] with x hx
    have hrx : raw x = H x := hx.limUnder_eq
    have hp : 0 ≤ H x :=
      isClosed_Ici.mem_of_tendsto hx (Eventually.of_forall (fun n => (hW n x).1.nonneg))
    have ht : trace (H x) = 1 := by
      have htend := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap.continuous.continuousAt.tendsto.comp hx
      have he : (fun n => trace (W n x)) = fun _ => (1 : ℂ) := funext (fun n => (hW n x).2)
      change Tendsto (fun n => trace (W n x)) atTop (𝓝 (trace (H x))) at htend
      rw [he] at htend
      exact tendsto_nhds_unique htend tendsto_const_nhds
    simp only [G, hrx, hp, ht, and_self, ↓reduceIte]
  have hGi (i j : ι) : Integrable (fun x => G x i j) μ :=
    (hH i j).congr (hGH.mono (fun x hx => congrArg (fun M => M i j) hx.symm))
  refine ⟨G,hGm,hGp,hGi,?_,?_⟩
  · filter_upwards [hlimH,hGH] with x hx he
    simpa only [he] using hx
  · intro n S hS
    have hc (i j : ι) : Integrable (fun x => W n x i j) μ :=
      Integrable.of_bound (((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).measurable.comp
        ((hlocal n).mono hL le_rfl)).aestronglyMeasurable 1
        (Eventually.of_forall (hbound n i j))
    ext i j
    rw [integral_matrix_entry (integrable_matrix_of_entries hGi).integrableOn,
      integral_matrix_entry (integrable_matrix_of_entries hc).integrableOn]
    calc
      _ = ∫ x in S, H x i j ∂μ := integral_congr_ae
        (ae_restrict_of_ae (hGH.mono (fun x hx => congrArg (fun M => M i j) hx)))
      _ = ∫ x in S, W n x i j ∂μ := by
        apply Complex.ext
        · change RCLike.re (∫ x in S, H x i j ∂μ) = RCLike.re (∫ x in S, W n x i j ∂μ)
          rw [← integral_re (hH i j).integrableOn, ← integral_re (hc i j).integrableOn]
          have heH : (fun x => RCLike.re (H x i j)) = gr i j := by
            funext x; simp [H]
          rw [heH, ← setIntegral_condExp (F.le n) (hgr i j) hS]
          exact integral_congr_ae (ae_restrict_of_ae (hcr i j n).symm)
        · change RCLike.im (∫ x in S, H x i j ∂μ) = RCLike.im (∫ x in S, W n x i j ∂μ)
          rw [← integral_im (hH i j).integrableOn, ← integral_im (hc i j).integrableOn]
          have heH : (fun x => RCLike.im (H x i j)) = gi i j := by
            funext x; simp [H]
          rw [heH, ← setIntegral_condExp (F.le n) (hgi i j) hS]
          exact integral_congr_ae (ae_restrict_of_ae (hci i j n).symm)

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v5616_0 v5616_1

abbrev LocalHistory (O : Type v5616_0) (M : Type v5616_1) (n : ℕ) :=
  (Fin n → (O ⊕ Unit)) × (Fin n → M)

universe v5619_0 v5619_1

def localActive {O : Type v5619_0} {M : Type v5619_1} {n : ℕ} (h : LocalHistory O M n) (o : O) (m : M) :
    LocalHistory O M (n+1) :=
  (Fin.snoc h.1 (Sum.inl o), Fin.snoc h.2 m)

universe v5623_0 v5623_1

def localPassive {O : Type v5623_0} {M : Type v5623_1} {n : ℕ} (h : LocalHistory O M n) (m : M) :
    LocalHistory O M (n+1) :=
  (Fin.snoc h.1 (Sum.inr ()), Fin.snoc h.2 m)

universe v5628_0 v5628_1 v5628_2 v5628_3

variable {O : Type v5628_0} {M : Type v5628_1} {ι : Type v5628_2} [inst5628_0 : MeasurableSpace O] [inst5628_1 : MeasurableSpace M]
  [inst5628_2 : Fintype ι] [inst5628_3 : DecidableEq ι]
  (A : ℕ → Type v5628_3) [inst5628_4 : ∀ n, AddCommGroup (A n)] [inst5628_5 : ∀ n, Module ℂ (A n)]
  [inst5628_6 : ∀ n, One (A n)] [inst5628_7 : ∀ n, LE (A n)]
  (κ : (n : ℕ) → Kernel (LocalHistory O M n) O)
  (send : (n : ℕ) → (LocalHistory O M n) × O → M)

structure LocalObservableExecution where
  state : (n : ℕ) → LocalHistory O M n → ReferenceFunctional (A n) ι
  positive_state : ∀ n h, PositiveFunctional (state n h)
  positive_unit : ∀ n, (0 : A n) ≤ 1
  normalized : ∀ n h, trace (state n h 1) = 1
  measurable_reference : ∀ n, Measurable (fun h => state n h 1)
  instrument : (n : ℕ) → (h : LocalHistory O M n) → ObservableInstrument O (A n) (A (n+1))
  run : ∀ n h, InstrumentRun (instrument n h) (state n h)
  run_law : ∀ n h, (run n h).law = κ n h
  active_update : ∀ n h,
    (fun o => state (n+1) (localActive h o (send n (h,o)))) =ᵐ[κ n h] (run n h).posterior
  receive : (n : ℕ) → LocalHistory O M n → M → (A (n+1) →ₗ[ℂ] A n)
  receive_positive : ∀ n h m x, 0 ≤ x → 0 ≤ receive n h m x
  receive_unit : ∀ n h m, receive n h m 1 = 1
  passive_update : ∀ n h m,
    state (n+1) (localPassive h m) = (state n h).comp (receive n h m)

namespace LocalObservableExecution

variable {A κ send} (e : LocalObservableExecution (ι := ι) A κ send)

def reference (n : ℕ) (h : LocalHistory O M n) : Matrix ι ι ℂ := e.state n h 1

omit inst5628_3 in
lemma reference_density [DecidableEq ι] (n : ℕ) (h : LocalHistory O M n) :
    ZeroKey.Density (e.reference n h) :=
  ⟨e.positive_state n h 1 (e.positive_unit n), e.normalized n h⟩

omit inst5628_3 in
lemma reference_measurable [DecidableEq ι] (n : ℕ) : Measurable (e.reference n) := e.measurable_reference n

lemma active_mean (n : ℕ) (h : LocalHistory O M n) (i j : ι) :
    (∫ o, e.reference (n+1) (localActive h o (send n (h,o))) i j ∂κ n h) =
      e.reference n h i j := by
  calc
    _ = ∫ o, (e.run n h).posterior o 1 i j ∂κ n h := by
      apply integral_congr_ae
      filter_upwards [e.active_update n h] with o ho
      exact congrArg (fun S : ReferenceFunctional (A (n+1)) ι => S 1 i j) ho
    _ = _ := by
      rw [← e.run_law]
      exact InstrumentRun.reference_mean (e.instrument n h) (e.state n h) (e.run n h) i j

omit inst5628_3 in
lemma passive_reference [DecidableEq ι] (n : ℕ) (h : LocalHistory O M n) (m : M) :
    e.reference (n+1) (localPassive h m) = e.reference n h := by
  simp only [reference,e.passive_update,LinearMap.comp_apply,e.receive_unit]

end LocalObservableExecution

end UnrestrictedQuantum

namespace ZeroKey

section

open MeasureTheory ProbabilityTheory

universe v5828_0 v5828_1

theorem condIndep_adaptive_public_message {Ω : Type v5828_0} {M : Type v5828_1}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [MeasurableSpace M]
    {P : Measure Ω} [IsFiniteMeasure P]
    {C A B : MeasurableSpace Ω}
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndep C A B hC P)
    (q : Ω → Bool) (a b : Ω → M) (d : M)
    (hq : @Measurable Ω Bool C _ q)
    (ha : @Measurable Ω M (A ⊔ C) _ a)
    (hb : @Measurable Ω M (B ⊔ C) _ b) :
    let message := fun x => if q x then a x else b x
    let N := C ⊔ MeasurableSpace.comap message inferInstance
    CondIndep N A B (sup_le hC ((ha.mono (sup_le hA hC) le_rfl).ite
      ((measurableSet_singleton true).preimage (hq.mono hC le_rfl))
      (hb.mono (sup_le hB hC) le_rfl)).comap_le) P := by
  let left := fun x => if q x then a x else d
  let right := fun x => if q x then d else b x
  let NA := C ⊔ MeasurableSpace.comap left inferInstance
  let NB := NA ⊔ MeasurableSpace.comap right inferInstance
  let g := fun x => if q x then a x else b x
  let N := C ⊔ MeasurableSpace.comap g inferInstance
  have hqset : MeasurableSet[C] {x | q x = true} := hq (measurableSet_singleton true)
  have hleft : @Measurable Ω M (A ⊔ C) _ left :=
    ha.ite ((show C ≤ A ⊔ C from le_sup_right) _ hqset) measurable_const
  have hCA : C ≤ NA := le_sup_left
  have hNAA : NA ≤ A ⊔ C := sup_le le_sup_right hleft.comap_le
  have hNAM : NA ≤ mΩ := hNAA.trans (sup_le hA hC)
  have h₁ : CondIndep NA A B hNAM P := condIndep_local_message hC hA hB hCA hNAA h
  have hright : @Measurable Ω M (B ⊔ NA) _ right :=
    measurable_const.ite ((hCA.trans le_sup_right) _ hqset)
      (hb.mono (sup_le_sup_left hCA B) le_rfl)
  have hNBB : NB ≤ B ⊔ NA := sup_le le_sup_right hright.comap_le
  have hNBM : NB ≤ mΩ := hNBB.trans (sup_le hB hNAM)
  have h₂ : CondIndep NB A B hNBM P :=
    (condIndep_local_message hNAM hB hA le_sup_left hNBB h₁.symm).symm
  have hCN : C ≤ N := le_sup_left
  have hgN : @Measurable Ω M N _ g := Measurable.of_comap_le le_sup_right
  have hlN : @Measurable Ω M N _ left := by
    have hh : @Measurable Ω M N _ (fun x => if q x then g x else d) :=
      hgN.ite (hCN _ hqset) measurable_const
    convert hh using 1
    ext x
    cases hqx : q x <;> simp [left,g,hqx]
  have hrN : @Measurable Ω M N _ right := by
    have hh : @Measurable Ω M N _ (fun x => if q x then d else g x) :=
      measurable_const.ite (hCN _ hqset) hgN
    convert hh using 1
    ext x
    cases hqx : q x <;> simp [right,g,hqx]
  have hNBN : NB ≤ N := sup_le (sup_le hCN hlN.comap_le) hrN.comap_le
  have hCNB : C ≤ NB := le_sup_left.trans le_sup_left
  have hlNB : @Measurable Ω M NB _ left :=
    Measurable.of_comap_le (le_sup_right.trans le_sup_left)
  have hrNB : @Measurable Ω M NB _ right := Measurable.of_comap_le le_sup_right
  have hgNB : @Measurable Ω M NB _ g := by
    have hh : @Measurable Ω M NB _ (fun x => if q x then left x else right x) :=
      hlNB.ite (hCNB _ hqset) hrNB
    convert hh using 1
    ext x
    cases hqx : q x <;> simp [left,right,g,hqx]
  have he : NB = N := le_antisymm hNBN (sup_le hCNB hgNB.comap_le)
  simpa only [he] using h₂

open MeasureTheory ProbabilityTheory

universe v5898_0 v5898_1

theorem adaptive_tapes_given_full_transcript {Ω : Type v5898_0} {M : Type v5898_1}
    {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [MeasurableSpace M]
    {P : Measure Ω} [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (A B : MeasurableSpace Ω)
    (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (hinitial : CondIndep (F 0) A B (F.le 0) P)
    (q : ℕ → Ω → Bool) (a b : ℕ → Ω → M) (d : M)
    (hq : ∀ n, @Measurable Ω Bool (F n) _ (q n))
    (ha : ∀ n, @Measurable Ω M (A ⊔ F n) _ (a n))
    (hb : ∀ n, @Measurable Ω M (B ⊔ F n) _ (b n))
    (hF : ∀ n, F (n+1) = F n ⊔ MeasurableSpace.comap
      (fun x => if q n x then a n x else b n x) inferInstance) :
    CondIndep (⨆ n, F n) (A ⊔ ⨆ n, F n) (B ⊔ ⨆ n, F n)
      (iSup_le F.le) P := by
  have hfinite : ∀ n, CondIndep (F n) A B (F.le n) P := by
    intro n
    induction n with
    | zero => exact hinitial
    | succ n ih =>
      have h := condIndep_adaptive_public_message (F.le n) hA hB ih
        (q n) (a n) (b n) d (hq n) (ha n) (hb n)
      simpa only [hF n] using h
  have h := condIndep_full_transcript F A B hA hB hfinite
  have hC := iSup_le F.le
  have h1 := (condIndep_join_public_right hC hB hA h.symm).symm
  exact condIndep_join_public_right hC (sup_le hA hC) hB h1

universe v5935_0 v5935_1 v5935_2

structure AdaptiveTapeProgram (U : Type v5935_0) (V : Type v5935_1) (M : Type v5935_2) [MeasurableSpace U]
    [MeasurableSpace V] [MeasurableSpace M] where
  alice : (n : ℕ) → (Fin n → M) → Bool
  measAlice : ∀ n, Measurable (alice n)
  sendA : (n : ℕ) → U × (Fin n → M) → M
  sendB : (n : ℕ) → V × (Fin n → M) → M
  measA : ∀ n, Measurable (sendA n)
  measB : ∀ n, Measurable (sendB n)

namespace AdaptiveTapeProgram

universe v5945_0 v5945_1 v5945_2

variable {U : Type v5945_0} {V : Type v5945_1} {M : Type v5945_2} [inst5945_0 : MeasurableSpace U] [inst5945_1 : MeasurableSpace V] [inst5945_2 : MeasurableSpace M]
  (p : AdaptiveTapeProgram U V M)

def publicPrefix : (n : ℕ) → U × V → (Fin n → M)
  | 0, _ => Fin.elim0
  | n+1, ω => Fin.snoc (publicPrefix n ω)
      (if p.alice n (publicPrefix n ω) then p.sendA n (ω.1,publicPrefix n ω) else p.sendB n (ω.2,publicPrefix n ω))

def message (n : ℕ) (ω : U × V) : M :=
  if p.alice n (p.publicPrefix n ω) then p.sendA n (ω.1,p.publicPrefix n ω) else p.sendB n (ω.2,p.publicPrefix n ω)

lemma prefix_succ (n : ℕ) (ω : U × V) :
    p.publicPrefix (n+1) ω = Fin.snoc (p.publicPrefix n ω) (p.message n ω) := rfl

lemma measurable_prefix : ∀ n, Measurable (p.publicPrefix n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [publicPrefix, Fin.snoc_last]
      exact ((p.measA n).comp (measurable_fst.prodMk ih)).ite
        ((measurableSet_singleton true).preimage ((p.measAlice n).comp ih))
        ((p.measB n).comp (measurable_snd.prodMk ih))
    · simpa only [publicPrefix, Fin.snoc_castSucc] using ih.eval (a := j)

lemma measurable_message (n : ℕ) : Measurable (p.message n) := by
  exact ((p.measA n).comp (measurable_fst.prodMk (p.measurable_prefix n))).ite
    ((measurableSet_singleton true).preimage ((p.measAlice n).comp (p.measurable_prefix n)))
    ((p.measB n).comp (measurable_snd.prodMk (p.measurable_prefix n)))

abbrev field (n : ℕ) : MeasurableSpace (U × V) :=
  MeasurableSpace.comap (p.publicPrefix n) inferInstance

lemma field_le (n : ℕ) : p.field n ≤ (inferInstance : MeasurableSpace (U × V)) := (p.measurable_prefix n).comap_le

lemma field_mono : Monotone p.field := by
  apply monotone_nat_of_le_succ
  intro n
  have h : @Measurable (U × V) (Fin n → M) (p.field (n+1)) _ (p.publicPrefix n) := by
    let : MeasurableSpace (U × V) := p.field (n+1)
    apply Measurable.of_eval
    intro i
    have hh := (@Measurable.of_comap_le (U × V) (Fin (n+1) → M)
      (p.field (n+1)) _ (p.publicPrefix (n+1)) le_rfl).eval (a := i.castSucc)
    simpa only [publicPrefix, Fin.snoc_castSucc] using hh
  exact h.comap_le

def filtration : Filtration ℕ (inferInstance : MeasurableSpace (U × V)) where
  seq := p.field
  mono' := p.field_mono
  le' := p.field_le

lemma field_zero : p.field 0 = ⊥ := by
  exact MeasurableSpace.comap_const Fin.elim0

lemma field_succ (n : ℕ) :
    p.field (n+1) = p.field n ⊔ MeasurableSpace.comap (p.message n) inferInstance := by
  apply le_antisymm
  · let : MeasurableSpace (U × V) := p.field n ⊔ MeasurableSpace.comap (p.message n) inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [prefix_succ,Fin.snoc_last] using
        (Measurable.of_comap_le (f := p.message n) le_sup_right)
    · simpa only [prefix_succ,Fin.snoc_castSucc,field] using
        (Measurable.of_comap_le (f := p.publicPrefix n) le_sup_left).eval (a := j)
  · apply sup_le (p.field_mono (Nat.le_succ n))
    let : MeasurableSpace (U × V) := p.field (n+1)
    have h := (@Measurable.of_comap_le (U × V) (Fin (n+1) → M)
      (p.field (n+1)) _ (p.publicPrefix (n+1)) le_rfl).eval (a := Fin.last n)
    have hh : Measurable[p.field (n+1)] (p.message n) := by
      simpa only [prefix_succ,Fin.snoc_last] using h
    exact hh.comap_le

theorem tapes_conditionally_independent [StandardBorelSpace U] [StandardBorelSpace V]
    [Nonempty M]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    CondIndep (⨆ n, p.field n)
      (MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ ⨆ n, p.field n)
      (MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ ⨆ n, p.field n)
      (iSup_le p.field_le) (μ.prod ν) := by
  refine adaptive_tapes_given_full_transcript (P := μ.prod ν) p.filtration _ _
    measurable_fst.comap_le measurable_snd.comap_le ?_
    (fun n ω => p.alice n (p.publicPrefix n ω))
    (fun n ω => p.sendA n (ω.1,p.publicPrefix n ω))
    (fun n ω => p.sendB n (ω.2,p.publicPrefix n ω)) (Classical.arbitrary M) ?_ ?_ ?_ ?_
  · change CondIndep (p.field 0) _ _ _ _
    have h0 := indep_condIndep_bot measurable_fst.comap_le measurable_snd.comap_le
      (P := μ.prod ν) (indepFun_prod (μ := μ) (ν := ν) measurable_id measurable_id)
    simpa only [p.field_zero] using h0
  · intro n
    exact (p.measAlice n).comp (Measurable.of_comap_le le_rfl)
  · intro n
    exact (p.measA n).comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le le_sup_right))
  · intro n
    exact (p.measB n).comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le le_sup_right))
  · exact p.field_succ

def record (ω : U × V) (n : ℕ) : M := p.message n ω

lemma measurable_record : Measurable p.record :=
  Measurable.of_eval p.measurable_message

lemma prefix_eq_record (n : ℕ) (ω : U × V) (i : Fin n) :
    p.publicPrefix n ω i = p.record ω i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [publicPrefix, Fin.snoc_last, record, message, Fin.val_last]
    · simpa only [publicPrefix, Fin.snoc_castSucc, Fin.val_castSucc] using ih j

lemma full_record_field :
    MeasurableSpace.comap p.record inferInstance = ⨆ n, p.field n := by
  apply le_antisymm
  · let : MeasurableSpace (U × V) := ⨆ n, p.field n
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro n
    have h : @Measurable (U × V) (Fin (n+1) → M) (⨆ n, p.field n) _
        (p.publicPrefix (n+1)) := Measurable.of_comap_le (le_iSup p.field (n+1))
    simpa only [publicPrefix, Fin.snoc_last, record, message] using h.eval (a := Fin.last n)
  · apply iSup_le
    intro n
    let : MeasurableSpace (U × V) := MeasurableSpace.comap p.record inferInstance
    apply Measurable.comap_le
    apply Measurable.of_eval
    intro i
    simp_rw [prefix_eq_record]
    exact (Measurable.of_comap_le (f := p.record) le_rfl).eval

universe v6086_0 v6086_1

theorem final_records_conditionally_independent [Nonempty M]
    [StandardBorelSpace U] [StandardBorelSpace V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Type v6086_0} {B : Type v6086_1} [MeasurableSpace A] [MeasurableSpace B]
    (readA : U × (ℕ → M) → A) (readB : V × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    CondIndepFun (MeasurableSpace.comap p.record inferInstance)
      p.measurable_record.comap_le
      (fun ω => readA (ω.1,p.record ω))
      (fun ω => readB (ω.2,p.record ω)) (μ.prod ν) := by
  have h := p.tapes_conditionally_independent μ ν
  rw [condIndepFun_iff_condIndep]
  have hA : MeasurableSpace.comap (fun ω => readA (ω.1,p.record ω)) inferInstance ≤
      MeasurableSpace.comap Prod.fst ‹MeasurableSpace U› ⊔ ⨆ n, p.field n := by
    apply Measurable.comap_le
    exact ha.comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le (p.full_record_field ▸ le_sup_right)))
  have hB : MeasurableSpace.comap (fun ω => readB (ω.2,p.record ω)) inferInstance ≤
      MeasurableSpace.comap Prod.snd ‹MeasurableSpace V› ⊔ ⨆ n, p.field n := by
    apply Measurable.comap_le
    exact hb.comp ((Measurable.of_comap_le le_sup_left).prodMk
      (Measurable.of_comap_le (p.full_record_field ▸ le_sup_right)))
  have h' := condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left h hA) hB
  simpa only [p.full_record_field] using h'

end AdaptiveTapeProgram

end

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

section

universe v6124_0

variable {N : Type v6124_0} [inst6124_0 : MeasurableSpace N] (ν : Measure N) [inst6124_1 : IsProbabilityMeasure ν]

def noiseTapeLaw : Measure (ℕ → N) := Measure.infinitePi (fun _ => ν)

instance noiseTapeLaw_probability : IsProbabilityMeasure (noiseTapeLaw ν) := by
  unfold noiseTapeLaw
  infer_instance

lemma noise_prefix_fresh_independent (n : ℕ) :
    IndepFun (fun u : (ℕ → N) => fun i : Fin n => u i) (fun u => u n) (noiseTapeLaw ν) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => ν)
    (X := fun _ x => x) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have hh := h.indepFun_finset (Finset.range n) {n} hd (fun i => measurable_pi_apply i)
  have hh' := hh.comp
    (show Measurable (fun x : (i : Finset.range n) → N => fun j : Fin n =>
      x ⟨j,Finset.mem_range.mpr j.isLt⟩) from by fun_prop)
    (show Measurable (fun x : (i : ({n} : Finset ℕ)) → N => x ⟨n,by simp⟩) from by fun_prop)
  exact hh'

lemma noise_tape_eval (n : ℕ) : (noiseTapeLaw ν).map (fun u => u n) = ν :=
  Measure.infinitePi_map_eval _ _

universe v6146_0 v6146_1

structure NoiseSampler (N : Type v6146_0) (O : Type v6146_1) [MeasurableSpace N] [MeasurableSpace O] where
  step : (n : ℕ) → (Fin n → O) × N → O
  measurable_step : ∀ n, Measurable (step n)

namespace NoiseSampler

variable {ν}

universe v6152_0

variable {O : Type v6152_0} [inst6152_0 : MeasurableSpace O] (f : NoiseSampler N O)

def finiteHistory : (n : ℕ) → (Fin n → N) → (Fin n → O)
  | 0, _ => Fin.elim0
  | n+1, u => Fin.snoc (finiteHistory n (fun i => u i.castSucc))
      (f.step n (finiteHistory n (fun i => u i.castSucc), u (Fin.last n)))

lemma measurable_finiteHistory : ∀ n, Measurable (f.finiteHistory n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hr : Measurable (fun u : Fin (n+1) → N => fun i : Fin n => u i.castSucc) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [finiteHistory, Fin.snoc_last,Function.comp_def] using
        (f.measurable_step n).comp ((ih.comp hr).prodMk (measurable_pi_apply (Fin.last n)))
    · simpa only [finiteHistory, Fin.snoc_castSucc,Function.comp_def] using (ih.comp hr).eval (a := j)

def history (n : ℕ) (u : (ℕ → N)) : Fin n → O :=
  f.finiteHistory n (fun i => u i)

lemma measurable_prefix (n : ℕ) : Measurable (f.history n) :=
  (f.measurable_finiteHistory n).comp (by fun_prop)

lemma prefix_succ (n : ℕ) (u : (ℕ → N)) :
    f.history (n+1) u = Fin.snoc (f.history n u) (f.step n (f.history n u,u n)) := rfl

lemma prefix_fresh_independent (n : ℕ) :
    IndepFun (f.history n) (fun u => u n) (noiseTapeLaw ν) :=
  (noise_prefix_fresh_independent ν n).comp (f.measurable_finiteHistory n) measurable_id

lemma prefix_fresh_law (n : ℕ) :
    (noiseTapeLaw ν).map (fun u => (f.history n u,u n)) =
      ((noiseTapeLaw ν).map (f.history n)).prod ν := by
  rw [(f.prefix_fresh_independent (ν := ν) n).map_prod_eq_prod_map_map
    (f.measurable_prefix n).aemeasurable (measurable_pi_apply n).aemeasurable,
    noise_tape_eval]

theorem prefix_law_succ (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, ν.map (fun u => f.step n (s,u)) = κ n s)
    (n : ℕ) :
    (noiseTapeLaw ν).map (f.history (n+1)) =
      (((noiseTapeLaw ν).map (f.history n)) ⊗ₘ κ n).map (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2) := by
  have hfresh := f.prefix_fresh_law (ν := ν) n
  have hsample : (((noiseTapeLaw ν).map (f.history n)).prod ν).map
      (fun p => (p.1, f.step n p)) = ((noiseTapeLaw ν).map (f.history n)) ⊗ₘ κ n := by
    ext B hB
    rw [Measure.map_apply (measurable_fst.prodMk (f.measurable_step n)) hB,
      Measure.prod_apply (hB.preimage (measurable_fst.prodMk (f.measurable_step n))),
      Measure.compProd_apply hB]
    congr 1
    funext s
    have hm : Measurable (fun u : N => f.step n (s,u)) := by
      simpa only [Function.comp_def, id_eq] using
        ((f.measurable_step n).comp ((measurable_const (a := s)).prodMk measurable_id))
    rw [← hlaw n s, Measure.map_apply hm (measurable_prodMk_left hB)]
    rfl
  have hs : Measurable (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using measurable_snd
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  rw [← hsample, ← hfresh,
    Measure.map_map (measurable_fst.prodMk (f.measurable_step n))
      ((f.measurable_prefix n).prodMk (measurable_pi_apply n)),
    Measure.map_map hs ((measurable_fst.prodMk (f.measurable_step n)).comp
      ((f.measurable_prefix n).prodMk (measurable_pi_apply n)))]
  rfl

def record (u : (ℕ → N)) (n : ℕ) : O := f.step n (f.history n u,u n)

lemma measurable_record : Measurable f.record :=
  Measurable.of_eval (fun n =>
    (f.measurable_step n).comp ((f.measurable_prefix n).prodMk (measurable_pi_apply n)))

lemma prefix_eq_record (n : ℕ) (u : (ℕ → N)) (i : Fin n) :
    f.history n u i = f.record u i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [f.prefix_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last,record, Fin.val_last]
    · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using ih j

theorem finite_law_unique (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, ν.map (fun u => f.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2)) :
    ∀ n, P.map (fun x => fun i : Fin n => x i) = (noiseTapeLaw ν).map (f.history n) := by
  intro n
  induction n with
  | zero =>
    have ht : (fun x : ℕ → O => fun i : Fin 0 => x i) = fun _ => Fin.elim0 := by
      funext x i
      exact Fin.elim0 i
    rw [ht]
    change P.map (fun _ : ℕ → O => Fin.elim0) =
      (noiseTapeLaw ν).map (fun _ : (ℕ → N) => Fin.elim0)
    simp
  | succ n ih => rw [hP n, ih, f.prefix_law_succ κ hlaw]

theorem record_law_unique (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, ν.map (fun u => f.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun p : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) p.1 p.2)) :
    P = (noiseTapeLaw ν).map f.record := by
  let Q := (noiseTapeLaw ν).map f.record
  have hQ : IsProbabilityMeasure Q := inferInstance
  apply IsProjectiveLimit.unique (P := fun J : Finset ℕ => Q.map J.restrict) ?_
    (show IsProjectiveLimit Q (fun J : Finset ℕ => Q.map J.restrict) from fun _ => rfl)
  intro J
  let n := J.sup id + 1
  let index : J → Fin n := fun j => ⟨j.1,Nat.lt_succ_of_le (Finset.le_sup (f := id) j.2)⟩
  let cut : (Fin n → O) → (J → O) := fun x j => x (index j)
  have hc : Measurable cut := by fun_prop
  have h := congrArg (fun ν : Measure (Fin n → O) => ν.map cut)
    (f.finite_law_unique κ hlaw P hP n)
  rw [Measure.map_map hc (by fun_prop), Measure.map_map hc (f.measurable_prefix n)] at h
  change P.map J.restrict = ((noiseTapeLaw ν).map f.record).map J.restrict
  rw [Measure.map_map (Finset.measurable_restrict J) f.measurable_record]
  have heL : cut ∘ (fun x : ℕ → O => fun i : Fin n => x i) = J.restrict := rfl
  have heR : cut ∘ f.history n = J.restrict ∘ f.record := by
    funext u j
    exact f.prefix_eq_record n u (index j)
  rwa [heL,heR] at h

end NoiseSampler

end

universe v6315_0 v6315_1

structure AdaptiveOutcomeSampler (O : Type v6315_0) (M : Type v6315_1) [MeasurableSpace O] [MeasurableSpace M] where
  alice : (n : ℕ) → (Fin n → M) → Bool
  alice_meas : ∀ n, Measurable (alice n)
  sampleA : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × I → O
  sampleB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × I → O
  sendA : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M
  sendB : (n : ℕ) → ((Fin n → (O ⊕ Unit)) × (Fin n → M)) × O → M
  sampleA_meas : ∀ n, Measurable (sampleA n)
  sampleB_meas : ∀ n, Measurable (sampleB n)
  sendA_meas : ∀ n, Measurable (sendA n)
  sendB_meas : ∀ n, Measurable (sendB n)

namespace AdaptiveOutcomeSampler

section

universe v6328_0 v6328_1

variable {O : Type v6328_0} {M : Type v6328_1} [inst6328_0 : MeasurableSpace O] [inst6328_1 : MeasurableSpace M]
  (p : AdaptiveOutcomeSampler O M)

def privatePrefix (a : Bool) : (n : ℕ) → UniformTape × (Fin n → M) → (Fin n → (O ⊕ Unit))
  | 0, _ => Fin.elim0
  | n+1, pair =>
    let old := privatePrefix a n (pair.1,fun i => pair.2 i.castSucc)
    let pubPast := fun i : Fin n => pair.2 i.castSucc
    Fin.snoc old (if p.alice n pubPast = a then Sum.inl
      (if a then p.sampleA n ((old,pubPast),pair.1 n)
       else p.sampleB n ((old,pubPast),pair.1 n)) else Sum.inr ())

lemma measurable_privatePrefix (a : Bool) : ∀ n, Measurable (p.privatePrefix a n) := by
  intro n
  induction n with
  | zero => exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
    have hr : Measurable (fun pair : UniformTape × (Fin (n+1) → M) =>
      (pair.1,fun i : Fin n => pair.2 i.castSucc)) := by fun_prop
    have hv : Measurable (fun pair : UniformTape × (Fin (n+1) → M) =>
      fun i : Fin n => pair.2 i.castSucc) := by fun_prop
    apply Measurable.of_eval
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [privatePrefix,Fin.snoc_last]
      apply Measurable.ite ((measurableSet_singleton a).preimage ((p.alice_meas n).comp hv)) _ measurable_const
      apply measurable_inl.comp
      cases a
      · exact (p.sampleB_meas n).comp (((ih.comp hr).prodMk hv).prodMk
          ((measurable_pi_apply n).comp measurable_fst))
      · exact (p.sampleA_meas n).comp (((ih.comp hr).prodMk hv).prodMk
          ((measurable_pi_apply n).comp measurable_fst))
    · simpa only [privatePrefix,Fin.snoc_castSucc,Function.comp_def] using
        (ih.comp hr).eval (a := j)

def tapeProgram : AdaptiveTapeProgram UniformTape UniformTape M where
  alice := p.alice
  measAlice := p.alice_meas
  sendA n pair := p.sendA n ((p.privatePrefix true n pair,pair.2),
    p.sampleA n ((p.privatePrefix true n pair,pair.2),pair.1 n))
  sendB n pair := p.sendB n ((p.privatePrefix false n pair,pair.2),
    p.sampleB n ((p.privatePrefix false n pair,pair.2),pair.1 n))
  measA n := (p.sendA_meas n).comp
    (((p.measurable_privatePrefix true n).prodMk measurable_snd).prodMk
      ((p.sampleA_meas n).comp (((p.measurable_privatePrefix true n).prodMk measurable_snd).prodMk
        ((measurable_pi_apply n).comp measurable_fst))))
  measB n := (p.sendB_meas n).comp
    (((p.measurable_privatePrefix false n).prodMk measurable_snd).prodMk
      ((p.sampleB_meas n).comp (((p.measurable_privatePrefix false n).prodMk measurable_snd).prodMk
        ((measurable_pi_apply n).comp measurable_fst))))

def replay : (n : ℕ) → (Fin n → O) →
    ((Fin n → (O ⊕ Unit)) × (Fin n → (O ⊕ Unit))) × (Fin n → M) :=
  Nat.rec (fun _ => ((Fin.elim0,Fin.elim0),Fin.elim0)) (fun n previous x =>
    let r := previous (fun i => x i.castSucc)
    let o := x (Fin.last n)
    let q := p.alice n r.2
    ((Fin.snoc r.1.1 (if q then Sum.inl o else Sum.inr ()),
      Fin.snoc r.1.2 (if q then Sum.inr () else Sum.inl o)),
     Fin.snoc r.2 (if q then p.sendA n ((r.1.1,r.2),o) else p.sendB n ((r.1.2,r.2),o))))

universe v6393_0 v6393_1

lemma measurable_snoc {Z : Type v6393_0} {X : Type v6393_1} [MeasurableSpace Z] [MeasurableSpace X]
    {n : ℕ} (f : Z → (Fin n → X)) (g : Z → X)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => Fin.snoc (α := fun _ : Fin (n+1) => X) (f x) (g x)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hg
  · simpa only [Fin.snoc_castSucc] using hf.eval (a := j)

lemma measurable_replay : ∀ n, Measurable (p.replay n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hr : Measurable (fun x : Fin (n+1) → O => fun i : Fin n => x i.castSucc) := by fun_prop
    have hR := ih.comp hr
    have hq := (p.alice_meas n).comp hR.snd
    have hqs := (measurableSet_singleton true).preimage hq
    exact ((measurable_snoc _ _ hR.fst.fst ((measurable_inl.comp (measurable_pi_apply (Fin.last n))).ite hqs measurable_const)).prodMk
      (measurable_snoc _ _ hR.fst.snd (measurable_const.ite hqs (measurable_inl.comp (measurable_pi_apply (Fin.last n)))))).prodMk
      (measurable_snoc _ _ hR.snd (((p.sendA_meas n).comp ((hR.fst.fst.prodMk hR.snd).prodMk (measurable_pi_apply (Fin.last n)))).ite hqs
        ((p.sendB_meas n).comp ((hR.fst.snd.prodMk hR.snd).prodMk (measurable_pi_apply (Fin.last n))))))

def extractPrivate (a : Bool) (n : ℕ) (x : Fin n → O) : Fin n → O ⊕ Unit :=
  if a then (p.replay n x).1.1 else (p.replay n x).1.2

def publicFrom (n : ℕ) (x : Fin n → O) : Fin n → M := (p.replay n x).2

lemma measurable_extractPrivate (a : Bool) (n : ℕ) : Measurable (p.extractPrivate a n) := by
  cases a
  · exact (p.measurable_replay n).fst.snd
  · exact (p.measurable_replay n).fst.fst

lemma measurable_publicFrom (n : ℕ) : Measurable (p.publicFrom n) := (p.measurable_replay n).snd

lemma extractPrivate_snoc (a : Bool) (n : ℕ) (x : Fin n → O) (z : O) :
    p.extractPrivate a (n+1) (Fin.snoc (α := fun _ => O) x z) =
      Fin.snoc (p.extractPrivate a n x) (if p.alice n (p.publicFrom n x) = a then Sum.inl z else Sum.inr ()) := by
  cases a <;> cases hq : p.alice n (p.publicFrom n x) <;>
    simp only [extractPrivate,replay,Fin.snoc_castSucc,Fin.snoc_last,publicFrom] at hq ⊢ <;> simp [hq]

lemma publicFrom_snoc (n : ℕ) (x : Fin n → O) (z : O) :
    p.publicFrom (n+1) (Fin.snoc (α := fun _ => O) x z) =
      Fin.snoc (p.publicFrom n x) (if p.alice n (p.publicFrom n x) then
        p.sendA n ((p.extractPrivate true n x,p.publicFrom n x),z) else
        p.sendB n ((p.extractPrivate false n x,p.publicFrom n x),z)) := by
  simp only [publicFrom,replay,extractPrivate,Fin.snoc_castSucc,Fin.snoc_last,Bool.false_eq_true,↓reduceIte]

lemma privatePrefix_snoc (a : Bool) (n : ℕ) (u : UniformTape) (h : Fin n → M) (z : M) :
    p.privatePrefix a (n+1) (u,Fin.snoc (α := fun _ => M) h z) =
      Fin.snoc (p.privatePrefix a n (u,h)) (if p.alice n h = a then Sum.inl
        (if a then p.sampleA n ((p.privatePrefix a n (u,h),h),u n)
        else p.sampleB n ((p.privatePrefix a n (u,h),h),u n)) else Sum.inr ()) := by
  simp only [privatePrefix,Fin.snoc_castSucc]

/-- The sampled outcome history, without a bundled measurability certificate. -/
def causalStep (n : ℕ) (pair : (Fin n → O) × (I × I)) : O :=
  if p.alice n (p.publicFrom n pair.1) then
    p.sampleA n ((p.extractPrivate true n pair.1, p.publicFrom n pair.1), pair.2.1)
  else p.sampleB n ((p.extractPrivate false n pair.1, p.publicFrom n pair.1), pair.2.2)

def causalHistory : (n : ℕ) → (Fin n → I × I) → (Fin n → O)
  | 0, _ => Fin.elim0
  | n+1, u => Fin.snoc (causalHistory n (fun i => u i.castSucc))
      (p.causalStep n (causalHistory n (fun i => u i.castSucc), u (Fin.last n)))

def causalRecord (u : ℕ → I × I) (n : ℕ) : O :=
  p.causalStep n (p.causalHistory n (fun i => u i), u n)

def causal : NoiseSampler (I × I) O where
  step n pair := if p.alice n (p.publicFrom n pair.1) then
    p.sampleA n ((p.extractPrivate true n pair.1,p.publicFrom n pair.1),pair.2.1) else
    p.sampleB n ((p.extractPrivate false n pair.1,p.publicFrom n pair.1),pair.2.2)
  measurable_step n :=
    ((p.sampleA_meas n).comp ((((p.measurable_extractPrivate true n).comp measurable_fst).prodMk
        ((p.measurable_publicFrom n).comp measurable_fst)).prodMk measurable_snd.fst)).ite
      ((measurableSet_singleton true).preimage ((p.alice_meas n).comp ((p.measurable_publicFrom n).comp measurable_fst)))
      ((p.sampleB_meas n).comp ((((p.measurable_extractPrivate false n).comp measurable_fst).prodMk
        ((p.measurable_publicFrom n).comp measurable_fst)).prodMk measurable_snd.snd))

lemma causalRecord_eq : p.causalRecord = p.causal.record := by
  have h (n : ℕ) : p.causalHistory n = p.causal.finiteHistory n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      funext u
      simp only [causalHistory, NoiseSampler.finiteHistory, ih]
      rfl
  funext u n
  change p.causalStep n (p.causalHistory n (fun i => u i), u n) =
    p.causal.step n (p.causal.finiteHistory n (fun i => u i), u n)
  rw [h n]
  rfl

def pairedTape (uv : UniformTape × UniformTape) (n : ℕ) : I × I := (uv.1 n,uv.2 n)

lemma measurable_pairedTape : Measurable pairedTape := by unfold pairedTape; fun_prop

theorem replay_matches (n : ℕ) (uv : UniformTape × UniformTape) :
    p.publicFrom n (p.causal.history n (pairedTape uv)) = p.tapeProgram.publicPrefix n uv ∧
    (∀ a, p.extractPrivate a n (p.causal.history n (pairedTape uv)) =
      p.privatePrefix a n ((if a then uv.1 else uv.2),p.tapeProgram.publicPrefix n uv)) := by
  induction n with
  | zero => exact ⟨rfl,fun a => by cases a <;> rfl⟩
  | succ n ih =>
    have hs : p.causal.step n (p.causal.history n (pairedTape uv),pairedTape uv n) =
      if p.alice n (p.tapeProgram.publicPrefix n uv) then
        p.sampleA n ((p.privatePrefix true n (uv.1,p.tapeProgram.publicPrefix n uv),
          p.tapeProgram.publicPrefix n uv),uv.1 n) else
        p.sampleB n ((p.privatePrefix false n (uv.2,p.tapeProgram.publicPrefix n uv),
          p.tapeProgram.publicPrefix n uv),uv.2 n) := by
      change (if p.alice n (p.publicFrom n (p.causal.history n (pairedTape uv))) then
        p.sampleA n ((p.extractPrivate true n (p.causal.history n (pairedTape uv)),
          p.publicFrom n (p.causal.history n (pairedTape uv))),uv.1 n)
        else p.sampleB n ((p.extractPrivate false n (p.causal.history n (pairedTape uv)),
          p.publicFrom n (p.causal.history n (pairedTape uv))),uv.2 n)) = _
      rw [ih.1,ih.2 true,ih.2 false]
      simp only [Bool.false_eq_true,↓reduceIte]
    rw [p.causal.prefix_succ,p.publicFrom_snoc,hs,ih.1,ih.2 true,ih.2 false]
    simp only [Bool.false_eq_true,↓reduceIte]
    constructor
    · rw [p.tapeProgram.prefix_succ]
      congr 1
      unfold AdaptiveTapeProgram.message tapeProgram
      split <;> simp_all only []
    · intro a
      rw [p.extractPrivate_snoc,ih.2 a,ih.1,p.tapeProgram.prefix_succ,p.privatePrefix_snoc]
      congr 1
      cases a <;> cases hrole : p.alice n (p.tapeProgram.publicPrefix n uv) <;>
        simp only [Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]

end

universe v6532_0 v6532_1

variable {O : Type v6532_0} {M : Type v6532_1} [inst6532_0 : MeasurableSpace O] [inst6532_1 : MeasurableSpace M]
  (p : AdaptiveOutcomeSampler O M)

def instrumentKernel
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    (n : ℕ) : Kernel (Fin n → O) O := by
  classical
  exact Kernel.piecewise
    ((measurableSet_singleton true).preimage ((p.alice_meas n).comp (p.measurable_publicFrom n)))
    ((κA n).comap (fun x => (p.extractPrivate true n x,p.publicFrom n x))
      ((p.measurable_extractPrivate true n).prodMk (p.measurable_publicFrom n)))
    ((κB n).comap (fun x => (p.extractPrivate false n x,p.publicFrom n x))
      ((p.measurable_extractPrivate false n).prodMk (p.measurable_publicFrom n)))

lemma instrumentKernel_apply
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    (n : ℕ) (s : Fin n → O) :
    p.instrumentKernel κA κB n s = if p.alice n (p.publicFrom n s) then
      κA n (p.extractPrivate true n s,p.publicFrom n s) else
      κB n (p.extractPrivate false n s,p.publicFrom n s) := by
  classical
  simp only [instrumentKernel,Kernel.piecewise_apply,Set.mem_preimage,Set.mem_singleton_iff,
    Function.comp_def,Kernel.comap_apply]

instance instrumentKernel_markov
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) :
    IsMarkovKernel (p.instrumentKernel κA κB n) := by
  unfold instrumentKernel
  infer_instance

lemma causal_step_law
    (κA κB : (n : ℕ) → Kernel ((Fin n → (O ⊕ Unit)) × (Fin n → M)) O)
    (ha : ∀ n s, volume.map (fun u => p.sampleA n (s,u)) = κA n s)
    (hb : ∀ n s, volume.map (fun u => p.sampleB n (s,u)) = κB n s) :
    ∀ n s, (volume.prod volume).map (fun u => p.causal.step n (s,u)) =
      p.instrumentKernel κA κB n s := by
  intro n s
  rw [p.instrumentKernel_apply κA κB n s]
  change (volume.prod volume).map (fun u => if p.alice n (p.publicFrom n s) then
    p.sampleA n ((p.extractPrivate true n s,p.publicFrom n s),u.1) else
    p.sampleB n ((p.extractPrivate false n s,p.publicFrom n s),u.2)) = _
  split
  · have hm : Measurable (fun u : I => p.sampleA n ((p.extractPrivate true n s,p.publicFrom n s),u)) :=
      (p.sampleA_meas n).comp (measurable_const.prodMk measurable_id)
    have hh := Measure.map_map (μ := (volume : Measure I).prod volume) hm
      (measurable_fst : Measurable (Prod.fst : I × I → I))
    simp only [Measure.map_fst_prod, measure_univ, one_smul] at hh
    exact hh.symm.trans (ha n _)
  · have hm : Measurable (fun u : I => p.sampleB n ((p.extractPrivate false n s,p.publicFrom n s),u)) :=
      (p.sampleB_meas n).comp (measurable_const.prodMk measurable_id)
    have hh := Measure.map_map (μ := (volume : Measure I).prod volume) hm
      (measurable_snd : Measurable (Prod.snd : I × I → I))
    simp only [Measure.map_snd_prod, measure_univ, one_smul] at hh
    exact hh.symm.trans (hb n _)

end AdaptiveOutcomeSampler

end

namespace AdaptiveQuantum

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v6604_0 v6604_1 v6604_2 v6604_3 v6604_4 v6604_5

variable {O : Type v6604_0} {M : Type v6604_1} {ι : Type v6604_2} {η : Type v6604_3} [inst6604_0 : MeasurableSpace O] [inst6604_1 : MeasurableSpace M]
  [inst6604_2 : Fintype ι] [inst6604_3 : Fintype η] [inst6604_4 : DecidableEq ι] [inst6604_5 : DecidableEq η]
  {A : ℕ → Type v6604_4} {B : ℕ → Type v6604_5}
  [inst6604_6 : ∀ n, AddCommGroup (A n)] [inst6604_7 : ∀ n, Module ℂ (A n)] [inst6604_8 : ∀ n, One (A n)] [inst6604_9 : ∀ n, LE (A n)]
  [inst6604_10 : ∀ n, AddCommGroup (B n)] [inst6604_11 : ∀ n, Module ℂ (B n)] [inst6604_12 : ∀ n, One (B n)] [inst6604_13 : ∀ n, LE (B n)]
  (p : AdaptiveOutcomeSampler O M)
  (κA κB : (n : ℕ) → Kernel (LocalHistory O M n) O)
  [inst6604_14 : ∀ n, IsMarkovKernel (κA n)] [inst6604_15 : ∀ n, IsMarkovKernel (κB n)]
  (eA : LocalObservableExecution (ι := ι) A κA p.sendA)
  (eB : LocalObservableExecution (ι := η) B κB p.sendB)

def globalLocalReferenceA (n : ℕ) (s : Fin n → O) : Matrix ι ι ℂ :=
  eA.reference n (p.extractPrivate true n s,p.publicFrom n s)

def globalLocalReferenceB (n : ℕ) (s : Fin n → O) : Matrix η η ℂ :=
  eB.reference n (p.extractPrivate false n s,p.publicFrom n s)

omit inst6604_14 in
lemma globalLocalReferenceA_measurable [∀ n, IsMarkovKernel (κA n)] (n : ℕ) :
    Measurable (globalLocalReferenceA p κA eA n) :=
  (eA.reference_measurable n).comp
    ((p.measurable_extractPrivate true n).prodMk (p.measurable_publicFrom n))

omit inst6604_15 in
lemma globalLocalReferenceB_measurable [∀ n, IsMarkovKernel (κB n)] (n : ℕ) :
    Measurable (globalLocalReferenceB p κB eB n) :=
  (eB.reference_measurable n).comp
    ((p.measurable_extractPrivate false n).prodMk (p.measurable_publicFrom n))

omit inst6604_14 in
lemma globalLocalReferenceA_mean [∀ n, IsMarkovKernel (κA n)] (n : ℕ) (s : Fin n → O) (i j : ι) :
    (∫ o, globalLocalReferenceA p κA eA (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = globalLocalReferenceA p κA eA n s i j := by
  unfold globalLocalReferenceA
  simp_rw [p.extractPrivate_snoc, p.publicFrom_snoc]
  rw [p.instrumentKernel_apply]
  cases hrole : p.alice n (p.publicFrom n s) with
  | true =>
    simp only [↓reduceIte]
    exact eA.active_mean n _ i j
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    change (∫ o, eA.reference (n+1) (localPassive
      (p.extractPrivate true n s,p.publicFrom n s)
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i j
      ∂κB n (p.extractPrivate false n s,p.publicFrom n s)) = _
    simp only [eA.passive_reference]
    simp

omit inst6604_15 in
lemma globalLocalReferenceB_mean [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) (i j : η) :
    (∫ o, globalLocalReferenceB p κB eB (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = globalLocalReferenceB p κB eB n s i j := by
  unfold globalLocalReferenceB
  simp_rw [p.extractPrivate_snoc, p.publicFrom_snoc]
  rw [p.instrumentKernel_apply]
  cases hrole : p.alice n (p.publicFrom n s) with
  | false =>
    simp only [↓reduceIte]
    exact eB.active_mean n _ i j
  | true =>
    simp only [Bool.true_eq_false,↓reduceIte]
    change (∫ o, eB.reference (n+1) (localPassive
      (p.extractPrivate false n s,p.publicFrom n s)
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i j
      ∂κA n (p.extractPrivate true n s,p.publicFrom n s)) = _
    simp only [eB.passive_reference]
    simp

def jointReference (n : ℕ) (s : Fin n → O) : Matrix (ι × η) (ι × η) ℂ :=
  globalLocalReferenceA p κA eA n s ⊗ₖ globalLocalReferenceB p κB eB n s

omit inst6604_14 inst6604_15 in
lemma jointReference_density [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) :
    Density (jointReference p κA κB eA eB n s) := by
  refine ⟨(eA.reference_density n _).1.kronecker (eB.reference_density n _).1,?_⟩
  simp only [jointReference, Matrix.trace_kronecker,globalLocalReferenceA,
    globalLocalReferenceB,(eA.reference_density n _).2,(eB.reference_density n _).2,one_mul]

lemma jointReference_measurable (n : ℕ) :
    Measurable (jointReference p κA κB eA eB n) := by
  have hm : Measurable (fun s i j => jointReference p κA κB eA eB n s i j) := by
    apply Measurable.of_eval; intro i
    apply Measurable.of_eval; intro j
    exact (((Matrix.entryLinearMap ℂ ℂ i.1 j.1).toContinuousLinearMap).measurable.comp
      (globalLocalReferenceA_measurable p κA eA n)).mul
      (((Matrix.entryLinearMap ℂ ℂ i.2 j.2).toContinuousLinearMap).measurable.comp
      (globalLocalReferenceB_measurable p κB eB n))
  have hM : Continuous (Matrix.of : ((ι × η) → (ι × η) → ℂ) → Matrix (ι × η) (ι × η) ℂ) :=
    continuous_matrix (fun i j => continuous_apply_apply i j)
  exact hM.measurable.comp hm

omit inst6604_14 inst6604_15 in
lemma jointReference_mean [∀ n, IsMarkovKernel (κA n)] [∀ n, IsMarkovKernel (κB n)] (n : ℕ) (s : Fin n → O) (i j : ι × η) :
    (∫ o, jointReference p κA κB eA eB (n+1) (Fin.snoc s o) i j
      ∂p.instrumentKernel κA κB n s) = jointReference p κA κB eA eB n s i j := by
  change (∫ o, globalLocalReferenceA p κA eA (n+1) (Fin.snoc s o) i.1 j.1 *
    globalLocalReferenceB p κB eB (n+1) (Fin.snoc s o) i.2 j.2
    ∂p.instrumentKernel κA κB n s) =
    globalLocalReferenceA p κA eA n s i.1 j.1 * globalLocalReferenceB p κB eB n s i.2 j.2
  simp only [globalLocalReferenceA,globalLocalReferenceB]
  simp_rw [p.extractPrivate_snoc,p.publicFrom_snoc]
  rw [p.instrumentKernel_apply]
  cases hrole : p.alice n (p.publicFrom n s) with
  | true =>
    simp only [Bool.true_eq_false,↓reduceIte]
    change (∫ o, eA.reference (n+1) (localActive
      (p.extractPrivate true n s,p.publicFrom n s) o
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i.1 j.1 *
      eB.reference (n+1) (localPassive (p.extractPrivate false n s,p.publicFrom n s)
      (p.sendA n ((p.extractPrivate true n s,p.publicFrom n s),o))) i.2 j.2
      ∂κA n (p.extractPrivate true n s,p.publicFrom n s)) = _
    simp_rw [eB.passive_reference]
    rw [integral_mul_const,eA.active_mean]
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    change (∫ o, eA.reference (n+1) (localPassive
      (p.extractPrivate true n s,p.publicFrom n s)
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i.1 j.1 *
      eB.reference (n+1) (localActive (p.extractPrivate false n s,p.publicFrom n s) o
      (p.sendB n ((p.extractPrivate false n s,p.publicFrom n s),o))) i.2 j.2
      ∂κB n (p.extractPrivate false n s,p.publicFrom n s)) = _
    simp_rw [eA.passive_reference]
    rw [integral_const_mul,eB.active_mean]

end AdaptiveQuantum

section

open MeasureTheory ProbabilityTheory Set Function unitInterval

theorem paired_tapes_law :
    (uniformTapeLaw.prod uniformTapeLaw).map
      (fun uv : UniformTape × UniformTape => fun n => (uv.1 n,uv.2 n)) =
      noiseTapeLaw ((volume : Measure I).prod volume) := by
  let ν : Measure ((Fin 2 × ℕ) → I) := Measure.infinitePi (fun _ => (volume : Measure I))
  let split : ((Fin 2 × ℕ) → I) → UniformTape × UniformTape :=
    fun u => (fun n => u (0,n),fun n => u (1,n))
  have hs : Measurable split := by fun_prop
  have hsplit : ν.map split = uniformTapeLaw.prod uniformTapeLaw := by
    have hc := Measure.infinitePi_map_curry (fun (_ : Fin 2) (_ : ℕ) => (volume : Measure I))
    change ν.map (MeasurableEquiv.curry (Fin 2) ℕ I) =
      Measure.infinitePi (fun _ : Fin 2 => uniformTapeLaw) at hc
    rw [Measure.infinitePi_eq_pi (fun _ : Fin 2 => uniformTapeLaw)] at hc
    have h := congrArg (fun P : Measure (Fin 2 → UniformTape) => P.map MeasurableEquiv.finTwoArrow) hc
    rw [Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _),
      (measurePreserving_finTwoArrow uniformTapeLaw).map_eq] at h
    exact h
  have hswap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin 2 × ℕ => (volume : Measure I))
    (f := fun p : ℕ × Fin 2 => (p.2,p.1)) (by intro a b h; cases a; cases b; simpa only [Prod.mk.injEq,and_comm] using h)
  have hc := Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin 2) => (volume : Measure I))
  have hp := Measure.infinitePi_map_pi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin 2 => (volume : Measure I)))
    (f := fun _ => MeasurableEquiv.finTwoArrow) (fun _ => MeasurableEquiv.measurable _)
  simp only [Measure.infinitePi_eq_pi, (measurePreserving_finTwoArrow (volume : Measure I)).map_eq] at hp
  rw [← hsplit, Measure.map_map (by fun_prop) hs]
  unfold noiseTapeLaw
  rw [Measure.infinitePi_eq_pi (fun _ : Fin 2 => (volume : Measure I))] at hc
  rw [← hp, ← hc, ← hswap]
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end

section

open MeasureTheory ProbabilityTheory

universe v6786_0 v6786_1 v6786_2 v6786_3 v6786_4

theorem condIndepFun_of_joint_law {Ω : Type v6786_0} {Ω' : Type v6786_1} {T : Type v6786_2} {A : Type v6786_3} {B : Type v6786_4}
    [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    [MeasurableSpace T] [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {t : Ω → T} {a : Ω → A} {b : Ω → B}
    {t' : Ω' → T} {a' : Ω' → A} {b' : Ω' → B}
    (ht : Measurable t) (ha : Measurable a) (hb : Measurable b)
    (ht' : Measurable t') (ha' : Measurable a') (hb' : Measurable b')
    (hlaw : P.map (fun x => (t x,a x,b x)) = Q.map (fun x => (t' x,a' x,b' x)))
    (hind : CondIndepFun (MeasurableSpace.comap t' inferInstance) ht'.comap_le a' b' Q) :
    CondIndepFun (MeasurableSpace.comap t inferInstance) ht.comap_le a b P := by
  have hm : Measurable (fun x => (t x,a x,b x)) := ht.prodMk (ha.prodMk hb)
  have hm' : Measurable (fun x => (t' x,a' x,b' x)) := ht'.prodMk (ha'.prodMk hb')
  have hT : P.map t = Q.map t' := by
    have h := congrArg (fun ν : Measure (T × A × B) => ν.map Prod.fst) hlaw
    simpa only [Measure.map_map measurable_fst hm,
      Measure.map_map measurable_fst hm', Function.comp_def] using h
  have hA : P.map (fun x => (t x,a x)) = Q.map (fun x => (t' x,a' x)) := by
    have hp : Measurable (fun x : T × A × B => (x.1,x.2.1)) := by fun_prop
    have h := congrArg (fun ν : Measure (T × A × B) => ν.map (fun x => (x.1,x.2.1))) hlaw
    simpa only [Measure.map_map hp hm, Measure.map_map hp hm', Function.comp_def] using h
  have hB : P.map (fun x => (t x,b x)) = Q.map (fun x => (t' x,b' x)) := by
    have hp : Measurable (fun x : T × A × B => (x.1,x.2.2)) := by fun_prop
    have h := congrArg (fun ν : Measure (T × A × B) => ν.map (fun x => (x.1,x.2.2))) hlaw
    simpa only [Measure.map_map hp hm, Measure.map_map hp hm', Function.comp_def] using h
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib ha hb ht]
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib ha' hb' ht'] at hind
  have hca : condDistrib a t P = condDistrib a' t' Q := by
    rw [condDistrib, condDistrib]
    congr 1
  have hcb : condDistrib b t P = condDistrib b' t' Q := by
    rw [condDistrib, condDistrib]
    congr 1
  rw [hlaw,hca,hcb,hT]
  exact hind

end

namespace AdaptiveOutcomeSampler

open MeasureTheory ProbabilityTheory Set Function unitInterval

universe v6835_0 v6835_1

variable {O : Type v6835_0} {M : Type v6835_1} [inst6835_0 : MeasurableSpace O] [inst6835_1 : MeasurableSpace M]
  (p : AdaptiveOutcomeSampler O M)

def privateRecord (a : Bool) (pair : UniformTape × (ℕ → M)) (n : ℕ) : O ⊕ Unit :=
  p.privatePrefix a (n+1) (pair.1,fun i => pair.2 i) (Fin.last n)

lemma measurable_privateRecord (a : Bool) : Measurable (p.privateRecord a) := by
  apply Measurable.of_eval
  intro n
  exact ((p.measurable_privatePrefix a (n+1)).comp (by fun_prop)).eval (a := Fin.last n)

universe v6846_0 v6846_1

theorem final_records_independent [Nonempty M] {A : Type v6846_0} {B : Type v6846_1} [MeasurableSpace A] [MeasurableSpace B]
    (readA : (ℕ → (O ⊕ Unit)) × (ℕ → M) → A)
    (readB : (ℕ → (O ⊕ Unit)) × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    CondIndepFun (MeasurableSpace.comap p.tapeProgram.record inferInstance)
      p.tapeProgram.measurable_record.comap_le
      (fun uv => readA (p.privateRecord true (uv.1,p.tapeProgram.record uv),p.tapeProgram.record uv))
      (fun uv => readB (p.privateRecord false (uv.2,p.tapeProgram.record uv),p.tapeProgram.record uv))
      (uniformTapeLaw.prod uniformTapeLaw) := by
  exact p.tapeProgram.final_records_conditionally_independent uniformTapeLaw uniformTapeLaw
    (fun pair => readA (p.privateRecord true pair,pair.2))
    (fun pair => readB (p.privateRecord false pair,pair.2))
    (ha.comp ((p.measurable_privateRecord true).prodMk measurable_snd))
    (hb.comp ((p.measurable_privateRecord false).prodMk measurable_snd))

def outcomeRecord (uv : UniformTape × UniformTape) : ℕ → O :=
  p.causal.record (pairedTape uv)

lemma measurable_outcomeRecord : Measurable p.outcomeRecord :=
  p.causal.measurable_record.comp measurable_pairedTape

lemma outcomeRecord_law (κ : (n : ℕ) → Kernel (Fin n → O) O)
    [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, (volume.prod volume).map (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2)) :
    (uniformTapeLaw.prod uniformTapeLaw).map p.outcomeRecord = P := by
  rw [p.causal.record_law_unique κ hlaw P hP]
  change (uniformTapeLaw.prod uniformTapeLaw).map (p.causal.record ∘ pairedTape) = _
  rw [← Measure.map_map p.causal.measurable_record measurable_pairedTape]
  congr 1
  exact paired_tapes_law

def publicRecord (x : ℕ → O) (n : ℕ) : M :=
  p.publicFrom (n+1) (fun i => x i) (Fin.last n)

def localRecord (a : Bool) (x : ℕ → O) (n : ℕ) : O ⊕ Unit :=
  p.extractPrivate a (n+1) (fun i => x i) (Fin.last n)

lemma measurable_publicRecord : Measurable p.publicRecord := by
  apply Measurable.of_eval
  intro n
  exact ((p.measurable_publicFrom (n+1)).comp (by fun_prop)).eval (a := Fin.last n)

lemma measurable_localRecord (a : Bool) : Measurable (p.localRecord a) := by
  apply Measurable.of_eval
  intro n
  exact ((p.measurable_extractPrivate a (n+1)).comp (by fun_prop)).eval (a := Fin.last n)

lemma publicRecord_replay (uv : UniformTape × UniformTape) :
    p.publicRecord (p.outcomeRecord uv) = p.tapeProgram.record uv := by
  funext n
  have h := congrFun (p.replay_matches (n+1) uv).1 (Fin.last n)
  have he : (fun i : Fin (n+1) => p.outcomeRecord uv i) =
      p.causal.history (n+1) (pairedTape uv) := by
    funext i
    exact (p.causal.prefix_eq_record (n+1) (pairedTape uv) i).symm
  change p.publicFrom (n+1) (fun i => p.outcomeRecord uv i) (Fin.last n) = _
  rw [he,h,p.tapeProgram.prefix_eq_record]
  rfl

lemma localRecord_replay (a : Bool) (uv : UniformTape × UniformTape) :
    p.localRecord a (p.outcomeRecord uv) =
      p.privateRecord a ((if a then uv.1 else uv.2),p.tapeProgram.record uv) := by
  funext n
  have h := congrFun ((p.replay_matches (n+1) uv).2 a) (Fin.last n)
  have he : (fun i : Fin (n+1) => p.outcomeRecord uv i) =
      p.causal.history (n+1) (pairedTape uv) := by
    funext i
    exact (p.causal.prefix_eq_record (n+1) (pairedTape uv) i).symm
  change p.extractPrivate a (n+1) (fun i => p.outcomeRecord uv i) (Fin.last n) = _
  rw [he,h]
  congr 2
  funext i
  exact p.tapeProgram.prefix_eq_record (n+1) uv i

universe v6928_0 v6928_1

theorem full_readout_law {A : Type v6928_0} {B : Type v6928_1} [MeasurableSpace A] [MeasurableSpace B]
    (κ : (n : ℕ) → Kernel (Fin n → O) O) [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, (volume.prod volume).map (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
    (readA : (ℕ → (O ⊕ Unit)) × (ℕ → M) → A)
    (readB : (ℕ → (O ⊕ Unit)) × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    P.map (fun x => (p.publicRecord x,
      readA (p.localRecord true x,p.publicRecord x),
      readB (p.localRecord false x,p.publicRecord x))) =
    (uniformTapeLaw.prod uniformTapeLaw).map (fun uv => (p.tapeProgram.record uv,
      readA (p.privateRecord true (uv.1,p.tapeProgram.record uv),p.tapeProgram.record uv),
      readB (p.privateRecord false (uv.2,p.tapeProgram.record uv),p.tapeProgram.record uv))) := by
  rw [← p.outcomeRecord_law κ hlaw P hP]
  have hm : Measurable (fun x => (p.publicRecord x,
      readA (p.localRecord true x,p.publicRecord x),
      readB (p.localRecord false x,p.publicRecord x))) := by
    exact p.measurable_publicRecord.prodMk
      ((ha.comp ((p.measurable_localRecord true).prodMk p.measurable_publicRecord)).prodMk
        (hb.comp ((p.measurable_localRecord false).prodMk p.measurable_publicRecord)))
  rw [Measure.map_map hm p.measurable_outcomeRecord]
  congr 1
  funext uv
  simp only [Function.comp_def,p.publicRecord_replay,p.localRecord_replay,
    Bool.false_eq_true,↓reduceIte]

universe v6957_0 v6957_1

theorem actual_records_independent [StandardBorelSpace O] [Nonempty M] {A : Type v6957_0} {B : Type v6957_1}
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (κ : (n : ℕ) → Kernel (Fin n → O) O) [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, (volume.prod volume).map (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (fun x => fun i : Fin (n+1) => x i) =
      ((P.map (fun x => fun i : Fin n => x i)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
    (readA : (ℕ → (O ⊕ Unit)) × (ℕ → M) → A)
    (readB : (ℕ → (O ⊕ Unit)) × (ℕ → M) → B)
    (ha : Measurable readA) (hb : Measurable readB) :
    CondIndepFun (MeasurableSpace.comap p.publicRecord inferInstance)
      p.measurable_publicRecord.comap_le
      (fun x => readA (p.localRecord true x,p.publicRecord x))
      (fun x => readB (p.localRecord false x,p.publicRecord x)) P := by
  apply condIndepFun_of_joint_law p.measurable_publicRecord
    (ha.comp ((p.measurable_localRecord true).prodMk p.measurable_publicRecord))
    (hb.comp ((p.measurable_localRecord false).prodMk p.measurable_publicRecord))
    p.tapeProgram.measurable_record
    (ha.comp (((p.measurable_privateRecord true).comp
      (measurable_fst.prodMk p.tapeProgram.measurable_record)).prodMk
        p.tapeProgram.measurable_record))
    (hb.comp (((p.measurable_privateRecord false).comp
      (measurable_snd.prodMk p.tapeProgram.measurable_record)).prodMk
        p.tapeProgram.measurable_record))
    (p.full_readout_law κ hlaw P hP readA readB ha hb)
    (p.final_records_independent readA readB ha hb)

end AdaptiveOutcomeSampler

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

universe v7004_0 v7004_1

variable {ι : Type v7004_0} {η : Type v7004_1} [inst7004_0 : Fintype ι] [inst7004_1 : Fintype η] [inst7004_2 : DecidableEq ι] [inst7004_3 : DecidableEq η]

omit inst7004_2 inst7004_3 in
lemma continuous_matrix_kronecker [DecidableEq ι] [DecidableEq η] : Continuous
    (fun z : Matrix ι ι ℂ × Matrix η η ℂ => z.1 ⊗ₖ z.2) := by
  apply continuous_matrix
  intro i j
  exact (((Matrix.entryLinearMap ℂ ℂ i.1 j.1).toContinuousLinearMap).continuous.comp
    continuous_fst).mul
    (((Matrix.entryLinearMap ℂ ℂ i.2 j.2).toContinuousLinearMap).continuous.comp
    continuous_snd)

universe v7015_0

lemma measurable_matrix_kronecker {Ω : Type v7015_0} [MeasurableSpace Ω]
    {U : Ω → Matrix ι ι ℂ} {V : Ω → Matrix η η ℂ}
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun x => U x ⊗ₖ V x) :=
  continuous_matrix_kronecker.measurable.comp (hU.prodMk hV)

omit inst7004_2 inst7004_3 in
lemma density_kronecker [DecidableEq ι] [DecidableEq η] {U : Matrix ι ι ℂ} {V : Matrix η η ℂ}
    (hU : Density U) (hV : Density V) : Density (U ⊗ₖ V) := by
  refine ⟨hU.1.kronecker hV.1,?_⟩
  rw [Matrix.trace_kronecker,hU.2,hV.2,one_mul]

universe v7027_0

variable {Ω : Type v7027_0} {LA LB : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [inst7027_0 : IsFiniteMeasure μ] {F : Filtration ℕ mΩ}

theorem local_product_reference_extension
    (U : ℕ → Ω → Matrix ι ι ℂ) (V : ℕ → Ω → Matrix η η ℂ)
    (hU : ∀ n x, Density (U n x)) (hV : ∀ n x, Density (V n x))
    (hLA : LA ≤ mΩ) (hLB : LB ≤ mΩ)
    (hmU : ∀ n, Measurable[LA] (U n)) (hmV : ∀ n, Measurable[LB] (V n))
    (hrU : ∀ i j, Martingale (fun n x => (U n x i j).re) F μ)
    (hiU : ∀ i j, Martingale (fun n x => (U n x i j).im) F μ)
    (hrV : ∀ i j, Martingale (fun n x => (V n x i j).re) F μ)
    (hiV : ∀ i j, Martingale (fun n x => (V n x i j).im) F μ)
    (hrUV : ∀ i j, Martingale (fun n x => ((U n x ⊗ₖ V n x) i j).re) F μ)
    (hiUV : ∀ i j, Martingale (fun n x => ((U n x ⊗ₖ V n x) i j).im) F μ) :
    ∃ G : Ω → Matrix ι ι ℂ, ∃ H : Ω → Matrix η η ℂ,
      Measurable[LA] G ∧ Measurable[LB] H ∧
      (∀ x, Density (G x)) ∧ (∀ x, Density (H x)) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => U n x) atTop (𝓝 (G x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => V n x) atTop (𝓝 (H x))) ∧
      (∀ n S, MeasurableSet[F n] S →
        (∫ x in S, G x ∂μ) = ∫ x in S, U n x ∂μ) ∧
      (∀ n S, MeasurableSet[F n] S →
        (∫ x in S, H x ∂μ) = ∫ x in S, V n x ∂μ) ∧
      ∃ W : PositiveMatrixMeasure Ω (ι × η),
        (∀ S, MeasurableSet S → W.value S = ∫ x in S, G x ⊗ₖ H x ∂μ) ∧
        (∀ n S, MeasurableSet[F n] S →
          W.value S = ∫ x in S, U n x ⊗ₖ V n x ∂μ) := by
  obtain ⟨G,hGm,hG,hGi,hGt,hGc⟩ := local_reference_limit U hU hmU hLA hrU hiU
  obtain ⟨H,hHm,hH,hHi,hHt,hHc⟩ := local_reference_limit V hV hmV hLB hrV hiV
  obtain ⟨J,hJm,hJ,hJi,hJt,hJc⟩ := local_reference_limit
    (fun n x => U n x ⊗ₖ V n x)
    (fun n x => density_kronecker (hU n x) (hV n x))
    (fun n => measurable_matrix_kronecker ((hmU n).mono hLA le_rfl)
      ((hmV n).mono hLB le_rfl)) le_rfl hrUV hiUV
  have hprod : (fun x => G x ⊗ₖ H x) =ᵐ[μ] J := by
    filter_upwards [hGt,hHt,hJt] with x hx hy hz
    have ht : Tendsto (fun n => U n x ⊗ₖ V n x) atTop (𝓝 (G x ⊗ₖ H x)) :=
      continuous_matrix_kronecker.continuousAt.tendsto.comp (hx.prodMk_nhds hy)
    exact tendsto_nhds_unique ht hz
  let W := positiveMatrixMeasureOfDensity hJi
    (Eventually.of_forall (fun x => (hJ x).1))
  refine ⟨G,H,hGm,hHm,hG,hH,hGt,hHt,hGc,hHc,W,?_,?_⟩
  · intro S hS
    rw [positiveMatrixMeasureOfDensity_value hJi _ S hS]
    exact integral_congr_ae (ae_restrict_of_ae hprod.symm)
  · intro n S hS
    rw [positiveMatrixMeasureOfDensity_value hJi _ S (F.le n S hS)]
    exact hJc n S hS

end

section

open Matrix MeasureTheory ProbabilityTheory Filter unitInterval

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

namespace AdaptiveOutcomeSampler

universe v7093_0 v7093_1

variable {O : Type v7093_0} {M : Type v7093_1} [inst7093_0 : MeasurableSpace O] [inst7093_1 : MeasurableSpace M]
  (p : AdaptiveOutcomeSampler O M)

lemma publicFrom_eq_record (n : ℕ) (x : ℕ → O) (i : Fin n) :
    p.publicFrom n (historyPrefix n x) i = p.publicRecord x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · simp only [publicFrom,replay,Fin.snoc_castSucc]
      exact ih j

lemma extractPrivate_eq_record (a : Bool) (n : ℕ) (x : ℕ → O) (i : Fin n) :
    p.extractPrivate a n (historyPrefix n x) i = p.localRecord a x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rfl
    · cases a <;> simp only [extractPrivate,replay,Bool.false_eq_true,↓reduceIte,
          Fin.snoc_castSucc] <;> exact ih j

abbrev localField (a : Bool) : MeasurableSpace (ℕ → O) :=
  MeasurableSpace.comap (fun x => (p.localRecord a x,p.publicRecord x)) inferInstance

lemma localField_le (a : Bool) : p.localField a ≤ (inferInstance : MeasurableSpace (ℕ → O)) :=
  ((p.measurable_localRecord a).prodMk p.measurable_publicRecord).comap_le

lemma local_history_measurable (a : Bool) (n : ℕ) :
    Measurable[p.localField a] (fun x =>
      (p.extractPrivate a n (historyPrefix n x),p.publicFrom n (historyPrefix n x))) := by
  have he : (fun x => (p.extractPrivate a n (historyPrefix n x),p.publicFrom n (historyPrefix n x))) =
      fun x => ((fun i : Fin n => p.localRecord a x i),fun i : Fin n => p.publicRecord x i) := by
    funext x
    congr 1 <;> funext i
    · exact p.extractPrivate_eq_record a n x i
    · exact p.publicFrom_eq_record n x i
  rw [he]
  let : MeasurableSpace (ℕ → O) := p.localField a
  have hm : Measurable (fun x : ℕ → O => (p.localRecord a x,p.publicRecord x)) :=
    Measurable.of_comap_le le_rfl
  exact (Measurable.of_eval (fun i => hm.fst.eval)).prodMk
    (Measurable.of_eval (fun i => hm.snd.eval))

lemma localFields_independent [StandardBorelSpace O] [Nonempty O]
    [StandardBorelSpace M] [Nonempty M]
    (κ : (n : ℕ) → Kernel (Fin n → O) O) [∀ n, IsMarkovKernel (κ n)]
    (hlaw : ∀ n s, ((volume : Measure I).prod volume).map
      (fun u => p.causal.step n (s,u)) = κ n s)
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ κ n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2)) :
    CondIndep (MeasurableSpace.comap p.publicRecord inferInstance)
      (p.localField true) (p.localField false) p.measurable_publicRecord.comap_le P := by
  classical
  rw [condIndep_iff _ _ _ _ (p.localField_le true) (p.localField_le false)]
  intro SA SB hSA hSB
  obtain ⟨EA,hEA,rfl⟩ := hSA
  obtain ⟨EB,hEB,rfl⟩ := hSB
  let fa : (ℕ → O ⊕ Unit) × (ℕ → M) → Bool :=
    fun x => if x ∈ EA then true else false
  let fb : (ℕ → O ⊕ Unit) × (ℕ → M) → Bool :=
    fun x => if x ∈ EB then true else false
  have hfa : Measurable fa := measurable_const.ite hEA measurable_const
  have hfb : Measurable fb := measurable_const.ite hEB measurable_const
  have hi := p.actual_records_independent κ hlaw P hP fa fb hfa hfb
  apply (condIndepFun_iff _ _ _ _
    (hfa.comp ((p.measurable_localRecord true).prodMk p.measurable_publicRecord))
    (hfb.comp ((p.measurable_localRecord false).prodMk p.measurable_publicRecord)) P).mp hi
  · refine ⟨{true},measurableSet_singleton true,?_⟩
    ext x
    simp [fa]
  · refine ⟨{true},measurableSet_singleton true,?_⟩
    ext x
    simp [fb]

end AdaptiveOutcomeSampler

namespace AdaptiveQuantum

open UnrestrictedQuantum

universe v7175_0 v7175_1 v7175_2 v7175_3 v7175_4 v7175_5

variable {O : Type v7175_0} {M : Type v7175_1} {ι : Type v7175_2} {η : Type v7175_3} [inst7175_0 : MeasurableSpace O] [inst7175_1 : MeasurableSpace M]
  [inst7175_2 : Fintype ι] [inst7175_3 : Fintype η] [inst7175_4 : DecidableEq ι] [inst7175_5 : DecidableEq η]
  {A : ℕ → Type v7175_4} {B : ℕ → Type v7175_5}
  [inst7175_6 : ∀ n, AddCommGroup (A n)] [inst7175_7 : ∀ n, Module ℂ (A n)] [inst7175_8 : ∀ n, One (A n)] [inst7175_9 : ∀ n, LE (A n)]
  [inst7175_10 : ∀ n, AddCommGroup (B n)] [inst7175_11 : ∀ n, Module ℂ (B n)] [inst7175_12 : ∀ n, One (B n)] [inst7175_13 : ∀ n, LE (B n)]
  (p : AdaptiveOutcomeSampler O M)
  (κA κB : (n : ℕ) → Kernel (LocalHistory O M n) O)
  [inst7175_14 : ∀ n, IsMarkovKernel (κA n)] [inst7175_15 : ∀ n, IsMarkovKernel (κB n)]
  (eA : LocalObservableExecution (ι := ι) A κA p.sendA)
  (eB : LocalObservableExecution (ι := η) B κB p.sendB)

theorem full_reference_extension
    (P : Measure (ℕ → O)) [IsProbabilityMeasure P]
    (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ p.instrumentKernel κA κB n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2)) :
    ∃ G : (ℕ → O) → Matrix ι ι ℂ, ∃ H : (ℕ → O) → Matrix η η ℂ,
      Measurable[p.localField true] G ∧ Measurable[p.localField false] H ∧
      (∀ x, Density (G x)) ∧ (∀ x, Density (H x)) ∧
      (∀ n S, MeasurableSet[historyFiltration n] S →
        (∫ x in S, G x ∂P) = ∫ x in S, globalLocalReferenceA p κA eA n (historyPrefix n x) ∂P) ∧
      (∀ n S, MeasurableSet[historyFiltration n] S →
        (∫ x in S, H x ∂P) = ∫ x in S, globalLocalReferenceB p κB eB n (historyPrefix n x) ∂P) ∧
      ∃ W : PositiveMatrixMeasure (ℕ → O) (ι × η),
        (∀ S, MeasurableSet S → W.value S = ∫ x in S, G x ⊗ₖ H x ∂P) ∧
        (∀ n S, MeasurableSet[historyFiltration n] S →
          W.value S = ∫ x in S, jointReference p κA κB eA eB n (historyPrefix n x) ∂P) := by
  let U := globalLocalReferenceA p κA eA
  let V := globalLocalReferenceB p κB eB
  have hU (n : ℕ) (s : Fin n → O) : Density (U n s) := eA.reference_density n _
  have hV (n : ℕ) (s : Fin n → O) : Density (V n s) := eB.reference_density n _
  have hmU := globalLocalReferenceA_measurable p κA eA
  have hmV := globalLocalReferenceB_measurable p κB eB
  have hmeanU := globalLocalReferenceA_mean p κA κB eA
  have hmeanV := globalLocalReferenceB_mean p κA κB eB
  have hrU := reference_history_martingale_re P (p.instrumentKernel κA κB) hP U hU hmU hmeanU
  have hiU := reference_history_martingale_im P (p.instrumentKernel κA κB) hP U hU hmU hmeanU
  have hrV := reference_history_martingale_re P (p.instrumentKernel κA κB) hP V hV hmV hmeanV
  have hiV := reference_history_martingale_im P (p.instrumentKernel κA κB) hP V hV hmV hmeanV
  have hrUV := reference_history_martingale_re P (p.instrumentKernel κA κB) hP
    (jointReference p κA κB eA eB) (jointReference_density p κA κB eA eB)
    (jointReference_measurable p κA κB eA eB) (jointReference_mean p κA κB eA eB)
  have hiUV := reference_history_martingale_im P (p.instrumentKernel κA κB) hP
    (jointReference p κA κB eA eB) (jointReference_density p κA κB eA eB)
    (jointReference_measurable p κA κB eA eB) (jointReference_mean p κA κB eA eB)
  obtain ⟨G,H,hGm,hHm,hG,hH,_,_,hGc,hHc,W,hW,hWc⟩ :=
    local_product_reference_extension
      (fun n x => U n (historyPrefix n x)) (fun n x => V n (historyPrefix n x))
      (fun n x => hU n _) (fun n x => hV n _) (p.localField_le true) (p.localField_le false)
      (fun n => (eA.reference_measurable n).comp (p.local_history_measurable true n))
      (fun n => (eB.reference_measurable n).comp (p.local_history_measurable false n))
      hrU hiU hrV hiV hrUV hiUV
  exact ⟨G,H,hGm,hHm,hG,hH,hGc,hHc,W,hW,hWc⟩

end AdaptiveQuantum

end

section

open MeasureTheory ProbabilityTheory Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v7253_0

lemma condIndepFun_ae_indep_complex {Ω : Type v7253_0} {C : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [inst7253_0 : StandardBorelSpace Ω] {μ : Measure Ω}
    [inst7253_1 : IsFiniteMeasure μ] (hC : C ≤ mΩ)
    {f g : Ω → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (h : CondIndepFun C hC f g μ) :
    ∀ᵐ x ∂μ.trim hC, IndepFun f g (condExpKernel μ C x) := by
  have he := (condIndepFun_iff_map_prod_eq_prod_map_map hf hg).mp h
  filter_upwards [he] with x hx
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).mpr
  simpa only [Kernel.prod_apply, Kernel.map_apply _ (hf.prodMk hg),
    Kernel.map_apply _ hf, Kernel.map_apply _ hg] using hx

lemma condIndepFun_kernel_integral_mul {Ω : Type v7253_0} {C : MeasurableSpace Ω}
    {mΩ : MeasurableSpace Ω} [inst7253_0 : StandardBorelSpace Ω] {μ : Measure Ω}
    [inst7253_1 : IsFiniteMeasure μ] (hC : C ≤ mΩ)
    {f g : Ω → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (h : CondIndepFun C hC f g μ) :
    ∀ᵐ x ∂μ.trim hC,
      (∫ y, f y * g y ∂condExpKernel μ C x) =
        (∫ y, f y ∂condExpKernel μ C x) *
        (∫ y, g y ∂condExpKernel μ C x) := by
  filter_upwards [condIndepFun_ae_indep_complex hC hf hg h] with x hx
  exact hx.integral_fun_mul_eq_mul_integral hf.stronglyMeasurable.aestronglyMeasurable
    hg.stronglyMeasurable.aestronglyMeasurable

universe v7283_0 v7283_1 v7283_2

variable {Ω : Type v7283_0} {ι : Type v7283_1} {κ : Type v7283_2} {C A B : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst7283_0 : StandardBorelSpace Ω] [inst7283_1 : Fintype ι] [inst7283_2 : Fintype κ] [inst7283_3 : DecidableEq ι] [inst7283_4 : DecidableEq κ]
  {μ : Measure Ω} [inst7283_5 : IsFiniteMeasure μ]

def publicMatrix (C : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Matrix ι ι ℂ) (x : Ω) : Matrix ι ι ℂ :=
  ∫ y, W y ∂condExpKernel μ C x

lemma publicMatrix_measurable (_hC : C ≤ mΩ) {W : Ω → Matrix ι ι ℂ}
    (hW : Measurable W) : Measurable[C] (publicMatrix C μ W) := by
  exact hW.stronglyMeasurable.integral_condExpKernel.measurable

lemma publicMatrix_entry (W : Ω → Matrix ι ι ℂ)
    (hWi : ∀ x, Integrable W (condExpKernel μ C x)) (x : Ω) (i j : ι) :
    publicMatrix C μ W x i j = ∫ y, W y i j ∂condExpKernel μ C x :=
  integral_matrix_entry (hWi x) i j

theorem condIndep_publicMatrix_kronecker
    (hC : C ≤ mΩ) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndep C A B hC μ)
    (U : Ω → Matrix ι ι ℂ) (V : Ω → Matrix κ κ ℂ)
    (hUm : Measurable[A] U) (hVm : Measurable[B] V)
    (hUi : ∀ x, Integrable U (condExpKernel μ C x))
    (hVi : ∀ x, Integrable V (condExpKernel μ C x))
    (hUVi : ∀ x, Integrable (fun y => U y ⊗ₖ V y) (condExpKernel μ C x)) :
    publicMatrix C μ (fun y => U y ⊗ₖ V y) =ᵐ[μ.trim hC]
      fun x => publicMatrix C μ U x ⊗ₖ publicMatrix C μ V x := by
  have he (i j : ι) (k l : κ) :
      ∀ᵐ x ∂μ.trim hC,
        (∫ y, U y i j * V y k l ∂condExpKernel μ C x) =
          (∫ y, U y i j ∂condExpKernel μ C x) *
          (∫ y, V y k l ∂condExpKernel μ C x) := by
    have huf : Measurable[A] (fun y => U y i j) :=
      ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).measurable.comp hUm
    have hvf : Measurable[B] (fun y => V y k l) :=
      ((Matrix.entryLinearMap ℂ ℂ k l).toContinuousLinearMap).measurable.comp hVm
    have hfg : CondIndepFun C hC (fun y => U y i j) (fun y => V y k l) μ := by
      exact condIndep_of_condIndep_of_le_right
        (condIndep_of_condIndep_of_le_left h huf.comap_le) hvf.comap_le
    exact condIndepFun_kernel_integral_mul hC (huf.mono hA le_rfl)
      (hvf.mono hB le_rfl) hfg
  have he' := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (he i j k))))
  filter_upwards [he'] with x hx
  ext ⟨i,k⟩ ⟨j,l⟩
  rw [publicMatrix_entry _ hUVi, Matrix.kronecker_apply,
    publicMatrix_entry _ hUi, publicMatrix_entry _ hVi]
  exact hx i j k l

end

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v7361_0 v7361_1

variable {ι : Type v7361_0} {η : Type v7361_1} [inst7361_0 : Fintype ι] [inst7361_1 : Fintype η] [inst7361_2 : DecidableEq ι] [inst7361_3 : DecidableEq η]

def Subdensity (U : Matrix ι ι ℂ) : Prop := U.PosSemidef ∧ (trace U).re ≤ 1

omit inst7361_2 in
lemma subdensity_zero [DecidableEq ι] : Subdensity (0 : Matrix ι ι ℂ) := by
  exact ⟨Matrix.PosSemidef.zero, by simp⟩

omit inst7361_2 inst7361_3 in
lemma subdensity_kronecker [DecidableEq ι] [DecidableEq η] {U : Matrix ι ι ℂ} {V : Matrix η η ℂ}
    (hU : Subdensity U) (hV : Subdensity V) : Subdensity (U ⊗ₖ V) := by
  refine ⟨hU.1.kronecker hV.1,?_⟩
  have hUi : (trace U).im = 0 := (RCLike.nonneg_iff.mp hU.1.trace_nonneg).2
  have hVi : (trace V).im = 0 := (RCLike.nonneg_iff.mp hV.1.trace_nonneg).2
  rw [Matrix.trace_kronecker, Complex.mul_re,hUi,hVi,mul_zero,sub_zero]
  exact (mul_le_of_le_one_left ((RCLike.nonneg_iff.mp hV.1.trace_nonneg).1) hU.2).trans hV.2

universe v7376_0

lemma integrable_subdensity {Ω : Type v7376_0} [MeasurableSpace Ω]
    (U : Ω → Matrix ι ι ℂ) (hU : ∀ x, Subdensity (U x)) (hm : Measurable U)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Integrable U μ := by
  apply integrable_matrix_of_entries
  intro i j
  apply Integrable.of_bound
    (((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).measurable.comp hm).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun x =>
    (psd_entry_norm_le_trace (hU x).1 i j).trans (hU x).2)

universe v7386_0

lemma integral_subdensity {Ω : Type v7386_0} [MeasurableSpace Ω]
    (U : Ω → Matrix ι ι ℂ) (hU : ∀ x, Subdensity (U x)) (hm : Measurable U)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Subdensity (∫ x, U x ∂μ) := by
  have hi := integrable_subdensity U hU hm μ
  refine ⟨(integral_nonneg_of_ae (Filter.Eventually.of_forall
    (fun x => (hU x).1.nonneg))).posSemidef,?_⟩
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  have htrace : trace (∫ x, U x ∂μ) = ∫ x, trace (U x) ∂μ := (L.integral_comp_comm hi).symm
  rw [htrace]
  change RCLike.re (∫ x, L (U x) ∂μ) ≤ 1
  rw [← integral_re (L.integrable_comp hi)]
  calc
    _ ≤ ∫ _ : Ω, (1 : ℝ) ∂μ := integral_mono ((L.integrable_comp hi).re)
      (integrable_const 1) (fun x => (hU x).2)
    _ = 1 := by simp

universe v7402_0 v7402_1

lemma measurable_positive_factor {Ω : Type v7402_0} {T : Type v7402_1} [MeasurableSpace Ω]
    [MeasurableSpace T] (r : Ω → T)
    (U : Ω → Matrix ι ι ℂ) (hU : ∀ x, Subdensity (U x))
    (hm : Measurable[MeasurableSpace.comap r inferInstance] U) :
    ∃ V : T → Matrix ι ι ℂ, Measurable V ∧ (∀ t, Subdensity (V t)) ∧ U = V ∘ r := by
  classical
  obtain ⟨V,hVm,hV⟩ := hm.exists_eq_measurable_comp
  let good : Set T := {t | 0 ≤ V t ∧ (trace (V t)).re ≤ 1}
  have hg : MeasurableSet good :=
    (measurableSet_le measurable_const hVm).inter
      (measurableSet_le (((Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap).measurable.comp hVm).re measurable_const)
  let W : T → Matrix ι ι ℂ := good.piecewise V (fun _ => 0)
  refine ⟨W,hVm.piecewise hg measurable_const,?_,?_⟩
  · intro t
    by_cases ht : t ∈ good
    · simpa only [W,Set.piecewise_eq_of_mem good V _ ht] using
        (show Subdensity (V t) from ⟨ht.1.posSemidef,ht.2⟩)
    · simpa only [W,Set.piecewise_eq_of_notMem good V _ ht] using subdensity_zero (ι := ι)
  · funext x
    have he : U x = V (r x) := congrFun hV x
    have hgx : r x ∈ good := by
      change 0 ≤ V (r x) ∧ (trace (V (r x))).re ≤ 1
      rw [← he]
      exact ⟨(hU x).1.nonneg,(hU x).2⟩
    simpa only [Function.comp_apply,W,Set.piecewise_eq_of_mem good V _ hgx] using he

universe v7429_0 v7429_1

variable {Ω : Type v7429_0} {T : Type v7429_1} {A B : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst7429_0 : StandardBorelSpace Ω] [inst7429_1 : MeasurableSpace T]
  {μ : Measure Ω} [inst7429_2 : IsFiniteMeasure μ]
  (r : Ω → T) (hr : Measurable r)

theorem terminal_public_factors
    (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (h : CondIndep (MeasurableSpace.comap r inferInstance) A B hr.comap_le μ)
    (U : Bool → Ω → Matrix ι ι ℂ) (V : Bool → Ω → Matrix η η ℂ)
    (hU : ∀ i x, Subdensity (U i x)) (hV : ∀ j x, Subdensity (V j x))
    (hmU : ∀ i, Measurable[A] (U i)) (hmV : ∀ j, Measurable[B] (V j)) :
    ∃ X : Bool → T → Matrix ι ι ℂ, ∃ Y : Bool → T → Matrix η η ℂ,
      (∀ i, Measurable (X i)) ∧ (∀ j, Measurable (Y j)) ∧
      (∀ i t, Subdensity (X i t)) ∧ (∀ j t, Subdensity (Y j t)) ∧
      (∀ i j, publicMatrix (MeasurableSpace.comap r inferInstance) μ
        (fun x => U i x ⊗ₖ V j x) =ᵐ[μ]
        fun x => X i (r x) ⊗ₖ Y j (r x)) := by
  have hUm (i : Bool) := (hmU i).mono hA le_rfl
  have hVm (j : Bool) := (hmV j).mono hB le_rfl
  have hpU (i : Bool) : ∀ x, Subdensity (publicMatrix (MeasurableSpace.comap r inferInstance) μ (U i) x) :=
    fun x => integral_subdensity (U i) (hU i) (hUm i) (condExpKernel μ (MeasurableSpace.comap r inferInstance) x)
  have hpV (j : Bool) : ∀ x, Subdensity (publicMatrix (MeasurableSpace.comap r inferInstance) μ (V j) x) :=
    fun x => integral_subdensity (V j) (hV j) (hVm j) (condExpKernel μ (MeasurableSpace.comap r inferInstance) x)
  choose X hXm hXp hX using fun i => measurable_positive_factor r
    (publicMatrix (MeasurableSpace.comap r inferInstance) μ (U i)) (hpU i) (publicMatrix_measurable hr.comap_le (hUm i))
  choose Y hYm hYp hY using fun j => measurable_positive_factor r
    (publicMatrix (MeasurableSpace.comap r inferInstance) μ (V j)) (hpV j) (publicMatrix_measurable hr.comap_le (hVm j))
  refine ⟨X,Y,hXm,hYm,hXp,hYp,?_⟩
  intro i j
  have he := condIndep_publicMatrix_kronecker hr.comap_le hA hB h
    (U i) (V j) (hmU i) (hmV j)
    (fun x => integrable_subdensity (U i) (hU i) (hUm i) (condExpKernel μ (MeasurableSpace.comap r inferInstance) x))
    (fun x => integrable_subdensity (V j) (hV j) (hVm j) (condExpKernel μ (MeasurableSpace.comap r inferInstance) x))
    (fun x => integrable_subdensity (fun y => U i y ⊗ₖ V j y)
      (fun y => subdensity_kronecker (hU i y) (hV j y))
      (measurable_matrix_kronecker (hUm i) (hVm j)) (condExpKernel μ (MeasurableSpace.comap r inferInstance) x))
  have he' := ae_of_ae_trim hr.comap_le he
  filter_upwards [he'] with x hx
  exact hx.trans (by rw [congrFun (hX i) x,congrFun (hY j) x]; rfl)

end

open MeasureTheory Matrix Filter

open scoped ComplexOrder MatrixOrder

namespace PositiveMatrixMeasure

universe v7485_0 v7485_1

variable {Ω : Type v7485_0} {ι : Type v7485_1} {mΩ : MeasurableSpace Ω} [inst7485_0 : Fintype ι] [inst7485_1 : DecidableEq ι]

omit inst7485_1 in
lemma ext_on_generating_piSystem [DecidableEq ι] (W V : PositiveMatrixMeasure Ω ι) (C : Set (Set Ω))
    (hC : IsPiSystem C) (hm : mΩ = MeasurableSpace.generateFrom C)
    (h : ∀ S ∈ C, W.value S = V.value S) (hu : W.value Set.univ = V.value Set.univ) : W = V := by
  have he : W.entry = V.entry := by
    funext i j
    refine VectorMeasure.ext_of_generateFrom C ?_ hm hC ?_
    · intro S hS
      exact congrArg (fun M : Matrix ι ι ℂ => M i j) (h S hS)
    · exact congrArg (fun M : Matrix ι ι ℂ => M i j) hu
  cases W
  cases V
  cases he
  rfl

lemma ext_on_filtration (W V : PositiveMatrixMeasure Ω ι) (F : Filtration ℕ mΩ)
    (hm : mΩ = ⨆ n, F n)
    (h : ∀ n S, MeasurableSet[F n] S → W.value S = V.value S) : W = V := by
  let C : Set (Set Ω) := {S | ∃ n, MeasurableSet[F n] S}
  have hc : IsPiSystem C := by
    intro S hS T hT _
    obtain ⟨n,hn⟩ := hS
    obtain ⟨k,hk⟩ := hT
    exact ⟨max n k, ((F.mono (le_max_left n k)) S hn).inter ((F.mono (le_max_right n k)) T hk)⟩
  have hgen : mΩ = MeasurableSpace.generateFrom C := by
    rw [hm]
    apply le_antisymm
    · apply iSup_le; intro n S hS
      exact MeasurableSpace.measurableSet_generateFrom ⟨n,hS⟩
    · apply MeasurableSpace.generateFrom_le
      rintro S ⟨n,hn⟩
      exact (le_iSup (fun n => F n) n) S hn
  exact W.ext_on_generating_piSystem V C hc hgen (fun S ⟨n,hn⟩ => h n S hn)
    (h 0 Set.univ MeasurableSet.univ)

end PositiveMatrixMeasure

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v7551_0 v7551_1 v7551_2

variable {A : Type v7551_0} {B : Type v7551_1} {ι : Type v7551_2} [inst7551_0 : AddCommGroup A] [inst7551_1 : Module ℂ A] [inst7551_2 : One A] [inst7551_3 : LE A]
  [inst7551_4 : AddCommGroup B] [inst7551_5 : Module ℂ B] [inst7551_6 : One B] [inst7551_7 : LE B]
  [inst7551_8 : Fintype ι] [inst7551_9 : DecidableEq ι]
  (J : ObservableInstrument Bool A B) (S : ReferenceFunctional A ι)
  (r : InstrumentRun J S)

def bitReference (i : Bool) : Matrix ι ι ℂ := S (J.operation {i} 1)

omit inst7551_8 inst7551_9 in
lemma bitReference_positive [Fintype ι] [DecidableEq ι] (hS : PositiveFunctional S) (h1 : (0 : B) ≤ 1)
    (i : Bool) : (bitReference J S i).PosSemidef :=
  hS _ (J.positive {i} (measurableSet_singleton i) 1 h1)

omit inst7551_9 in
lemma bitReference_entry [DecidableEq ι] (i : Bool) (k l : ι) :
    bitReference J S i k l = ∫ b in {i}, r.posterior b 1 k l ∂r.law :=
  (r.update {i} (measurableSet_singleton i) 1 k l).symm

include r in
theorem bitReference_sum : bitReference J S false + bitReference J S true = S 1 := by
  ext k l
  rw [Matrix.add_apply, bitReference_entry J S r false,
    bitReference_entry J S r true]
  have hd : Disjoint ({false} : Set Bool) {true} := by simp
  have hu : ({false} : Set Bool) ∪ {true} = Set.univ := by
    ext b; cases b <;> simp
  rw [← setIntegral_union hd (measurableSet_singleton true)
    (r.integrable 1 k l).integrableOn (r.integrable 1 k l).integrableOn, hu,
    Measure.restrict_univ]
  exact InstrumentRun.reference_mean J S r k l

end UnrestrictedQuantum

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace ZeroKey

universe v7614_0 v7614_1

variable {Ω : Type v7614_0} {ι : Type v7614_1} [inst7614_0 : Fintype ι] [inst7614_1 : DecidableEq ι]
  {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [inst7614_2 : IsFiniteMeasure μ]

omit inst7614_1 in
lemma density_subdensity [DecidableEq ι] {U : Matrix ι ι ℂ} (hU : Density U) : Subdensity U :=
  ⟨hU.1,by rw [hU.2]; norm_num⟩

theorem reference_density_unique_on_filtration (F : Filtration ℕ mΩ)
    (hgen : mΩ = ⨆ n, F n)
    (U V : Ω → Matrix ι ι ℂ)
    (hU : ∀ x, Subdensity (U x)) (hV : ∀ x, Subdensity (V x))
    (hmU : Measurable U) (hmV : Measurable V)
    (hEq : ∀ n S, MeasurableSet[F n] S →
      (∫ x in S, U x ∂μ) = ∫ x in S, V x ∂μ) : U =ᵐ[μ] V := by
  have hUi := integrable_subdensity U hU hmU μ
  have hVi := integrable_subdensity V hV hmV μ
  have hUe (i j : ι) : Integrable (fun x => U x i j) μ :=
    ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).integrable_comp hUi
  have hVe (i j : ι) : Integrable (fun x => V x i j) μ :=
    ((Matrix.entryLinearMap ℂ ℂ i j).toContinuousLinearMap).integrable_comp hVi
  let P := positiveMatrixMeasureOfDensity hUe
    (Filter.Eventually.of_forall (fun x => (hU x).1))
  let Q := positiveMatrixMeasureOfDensity hVe
    (Filter.Eventually.of_forall (fun x => (hV x).1))
  have hpq : P = Q := by
    apply PositiveMatrixMeasure.ext_on_filtration P Q F hgen
    intro n S hS
    dsimp only [P,Q]
    rw [positiveMatrixMeasureOfDensity_value hUe _ S (F.le n S hS),
      positiveMatrixMeasureOfDensity_value hVe _ S (F.le n S hS)]
    exact hEq n S hS
  apply Integrable.ae_eq_of_forall_setIntegral_eq U V hUi hVi
  intro S hS _
  have he := congrArg (fun P : PositiveMatrixMeasure Ω ι => P.value S) hpq
  dsimp only [P,Q] at he
  simpa only [positiveMatrixMeasureOfDensity_value hUe _ S hS,
    positiveMatrixMeasureOfDensity_value hVe _ S hS] using he

end ZeroKey

namespace UnrestrictedQuantum

universe v7657_0 v7657_1 v7657_2 v7657_3

variable {Ω : Type v7657_0} {ι : Type v7657_1} {A : Type v7657_2} {B : Type v7657_3} [inst7657_0 : Fintype ι] [inst7657_1 : DecidableEq ι]
  {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst7657_2 : AddCommGroup A] [inst7657_3 : Module ℂ A] [inst7657_4 : One A] [inst7657_5 : LE A]
  [inst7657_6 : AddCommGroup B] [inst7657_7 : Module ℂ B] [inst7657_8 : One B] [inst7657_9 : LE B]
  (μ : Measure Ω) (F : Filtration ℕ mΩ)
  (U : ℕ → Ω → Matrix ι ι ℂ)

structure IncomingObservableProcess where
  state : Ω → ReferenceFunctional A ι
  positive : ∀ x, PositiveFunctional (state x)
  positive_unit : (0 : A) ≤ 1
  normalized : ∀ x, trace (state x 1) = 1
  local_measurable : Measurable[L] (fun x => state x 1)
  causality : ∀ n S, MeasurableSet[F n] S →
    (∫ x in S, state x 1 ∂μ) = ∫ x in S, U n x ∂μ

namespace IncomingObservableProcess

variable {μ F U} (e : IncomingObservableProcess (L := L) (A := A) μ F U)

lemma reference_density (x : Ω) : ZeroKey.Density (e.state x 1) :=
  ⟨e.positive x 1 e.positive_unit,e.normalized x⟩

structure BitReadout where
  instrument : Ω → ObservableInstrument Bool A B
  run : ∀ x, InstrumentRun (instrument x) (e.state x)
  positive_unit : (0 : B) ≤ 1
  local_measurable : ∀ i, Measurable[L] (fun x => bitReference (instrument x) (e.state x) i)

namespace BitReadout

variable {e}

variable (b : e.BitReadout (B := B))

def value (i : Bool) (x : Ω) : Matrix ι ι ℂ := bitReference (b.instrument x) (e.state x) i

lemma positive (i : Bool) (x : Ω) : (b.value i x).PosSemidef :=
  bitReference_positive (b.instrument x) (e.state x) (e.positive x) b.positive_unit i

lemma sum (x : Ω) : b.value false x + b.value true x = e.state x 1 :=
  bitReference_sum (b.instrument x) (e.state x) (b.run x)

lemma subdensity (i : Bool) (x : Ω) : ZeroKey.Subdensity (b.value i x) := by
  refine ⟨b.positive i x,?_⟩
  have hsum := congrArg (fun M : Matrix ι ι ℂ => (trace M).re) (b.sum x)
  rw [Matrix.trace_add,Complex.add_re,e.normalized x,Complex.one_re] at hsum
  have h0 := (RCLike.nonneg_iff.mp (b.positive false x).trace_nonneg).1
  have h1 := (RCLike.nonneg_iff.mp (b.positive true x).trace_nonneg).1
  change 0 ≤ (trace (b.value false x)).re at h0
  change 0 ≤ (trace (b.value true x)).re at h1
  cases i <;> linarith

lemma measurable (i : Bool) : Measurable[L] (b.value i) := b.local_measurable i

end BitReadout

end IncomingObservableProcess

end UnrestrictedQuantum

end

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v7730_0 v7730_1 v7730_2 v7730_3

variable {Ω : Type v7730_0} {T : Type v7730_1} {ι : Type v7730_2} {η : Type v7730_3} {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  [inst7730_0 : StandardBorelSpace Ω] [inst7730_1 : MeasurableSpace T]
  [inst7730_2 : Fintype ι] [inst7730_3 : Fintype η] [inst7730_4 : DecidableEq ι] [inst7730_5 : DecidableEq η]
  {P : Measure Ω} [inst7730_6 : IsFiniteMeasure P]

lemma setIntegral_publicMatrix (hL : L ≤ mΩ) (U : Ω → Matrix ι ι ℂ)
    (hU : Integrable U P) (S : Set Ω) (hS : MeasurableSet[L] S) :
    (∫ x in S, publicMatrix L P U x ∂P) = ∫ x in S, U x ∂P := by
  calc
    _ = ∫ x in S, P[U | L] x ∂P := integral_congr_ae
      (ae_restrict_of_ae (condExp_ae_eq_integral_condExpKernel hL hU).symm)
    _ = _ := setIntegral_condExp hL hU hS

lemma public_factor_event (r : Ω → T) (hr : Measurable r)
    (U : Ω → Matrix ι ι ℂ) (V : T → Matrix ι ι ℂ)
    (hU : Integrable U P) (hV : Measurable V)
    (he : publicMatrix (MeasurableSpace.comap r inferInstance) P U =ᵐ[P] V ∘ r)
    (S : Set T) (hS : MeasurableSet S) :
    (∫ t in S, V t ∂P.map r) = ∫ x in r ⁻¹' S, U x ∂P := by
  rw [setIntegral_map hS hV.aestronglyMeasurable hr.aemeasurable]
  calc
    _ = ∫ x in r ⁻¹' S, publicMatrix (MeasurableSpace.comap r inferInstance) P U x ∂P :=
      integral_congr_ae (ae_restrict_of_ae he.symm)
    _ = _ := setIntegral_publicMatrix hr.comap_le U hU _ ⟨S,hS,rfl⟩

end

namespace AdaptiveQuantum

open Matrix MeasureTheory ProbabilityTheory Filter unitInterval

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker Topology

section

open UnrestrictedQuantum

universe v7771_0 v7771_1 v7771_2 v7771_3 v7771_4 v7771_5 v7771_6 v7771_7 v7771_8 v7771_9

variable {O : Type v7771_0} {M : Type v7771_1} {ι : Type v7771_2} {η : Type v7771_3} [inst7771_0 : MeasurableSpace O] [inst7771_1 : MeasurableSpace M]
  [inst7771_2 : StandardBorelSpace O] [inst7771_3 : Nonempty O] [inst7771_4 : StandardBorelSpace M] [inst7771_5 : Nonempty M]
  [inst7771_6 : Fintype ι] [inst7771_7 : Fintype η] [inst7771_8 : DecidableEq ι] [inst7771_9 : DecidableEq η]
  {A : ℕ → Type v7771_4} {B : ℕ → Type v7771_5}
  [inst7771_10 : ∀ n, AddCommGroup (A n)] [inst7771_11 : ∀ n, Module ℂ (A n)] [inst7771_12 : ∀ n, One (A n)] [inst7771_13 : ∀ n, LE (A n)]
  [inst7771_14 : ∀ n, AddCommGroup (B n)] [inst7771_15 : ∀ n, Module ℂ (B n)] [inst7771_16 : ∀ n, One (B n)] [inst7771_17 : ∀ n, LE (B n)]
  (p : AdaptiveOutcomeSampler O M)
  (κA κB : (n : ℕ) → Kernel (LocalHistory O M n) O)
  [inst7771_18 : ∀ n, IsMarkovKernel (κA n)] [inst7771_19 : ∀ n, IsMarkovKernel (κB n)]
  (eA : LocalObservableExecution (ι := ι) A κA p.sendA)
  (eB : LocalObservableExecution (ι := η) B κB p.sendB)
  {TA : Type v7771_6} {TB : Type v7771_7} {CA : Type v7771_8} {CB : Type v7771_9}
  [inst7771_20 : AddCommGroup TA] [inst7771_21 : Module ℂ TA] [inst7771_22 : One TA] [inst7771_23 : LE TA]
  [inst7771_24 : AddCommGroup TB] [inst7771_25 : Module ℂ TB] [inst7771_26 : One TB] [inst7771_27 : LE TB]
  [inst7771_28 : AddCommGroup CA] [inst7771_29 : Module ℂ CA] [inst7771_30 : One CA] [inst7771_31 : LE CA]
  [inst7771_32 : AddCommGroup CB] [inst7771_33 : Module ℂ CB] [inst7771_34 : One CB] [inst7771_35 : LE CB]
  (P : Measure (ℕ → O)) [inst7771_36 : IsProbabilityMeasure P]
  (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ p.instrumentKernel κA κB n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
  (eTA : IncomingObservableProcess (L := p.localField true) (A := TA) P historyFiltration
    (fun n x => globalLocalReferenceA p κA eA n (historyPrefix n x)))
  (eTB : IncomingObservableProcess (L := p.localField false) (A := TB) P historyFiltration
    (fun n x => globalLocalReferenceB p κB eB n (historyPrefix n x)))
  (bA : eTA.BitReadout (B := CA)) (bB : eTB.BitReadout (B := CB))

include hP

omit inst7771_2 inst7771_3 inst7771_4 inst7771_5 in
theorem incoming_joint_reference_consistency [StandardBorelSpace O] [Nonempty O] [StandardBorelSpace M] [Nonempty M] :
    ∀ n S, MeasurableSet[historyFiltration n] S →
      (∫ x in S, (eTA.state x 1) ⊗ₖ (eTB.state x 1) ∂P) =
        ∫ x in S, jointReference p κA κB eA eB n (historyPrefix n x) ∂P := by
  obtain ⟨G,H,hGm,hHm,hG,hH,hGc,hHc,W,hW,hWc⟩ :=
    full_reference_extension p κA κB eA eB P hP
  have hGa : (fun x => eTA.state x 1) =ᵐ[P] G :=
    reference_density_unique_on_filtration historyFiltration historyFiltration_generates
      (fun x => eTA.state x 1) G
      (fun x => density_subdensity (eTA.reference_density x))
      (fun x => density_subdensity (hG x))
      (eTA.local_measurable.mono (p.localField_le true) le_rfl)
      (hGm.mono (p.localField_le true) le_rfl)
      (fun n S hS => (eTA.causality n S hS).trans (hGc n S hS).symm)
  have hHa : (fun x => eTB.state x 1) =ᵐ[P] H :=
    reference_density_unique_on_filtration historyFiltration historyFiltration_generates
      (fun x => eTB.state x 1) H
      (fun x => density_subdensity (eTB.reference_density x))
      (fun x => density_subdensity (hH x))
      (eTB.local_measurable.mono (p.localField_le false) le_rfl)
      (hHm.mono (p.localField_le false) le_rfl)
      (fun n S hS => (eTB.causality n S hS).trans (hHc n S hS).symm)
  intro n S hS
  rw [← hWc n S hS,hW S (historyFiltration.le n S hS)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hGa,ae_restrict_of_ae hHa] with x hx hy
  rw [hx,hy]

theorem genuine_terminal_public_factors
    (hlaw : ∀ n s, ((volume : Measure I).prod volume).map
      (fun u => p.causal.step n (s,u)) = p.instrumentKernel κA κB n s) :
    ∃ X : Bool → (ℕ → M) → Matrix ι ι ℂ,
    ∃ Y : Bool → (ℕ → M) → Matrix η η ℂ,
      (∀ i, Measurable (X i)) ∧ (∀ j, Measurable (Y j)) ∧
      (∀ i t, Subdensity (X i t)) ∧ (∀ j t, Subdensity (Y j t)) ∧
      ∀ i j S, MeasurableSet S →
        (∫ t in S, X i t ⊗ₖ Y j t ∂P.map p.publicRecord) =
          ∫ x in p.publicRecord ⁻¹' S, bA.value i x ⊗ₖ bB.value j x ∂P := by
  obtain ⟨X,Y,hXm,hYm,hXp,hYp,hXY⟩ := terminal_public_factors p.publicRecord
    p.measurable_publicRecord (p.localField_le true) (p.localField_le false)
    (p.localFields_independent (p.instrumentKernel κA κB) hlaw P hP)
    bA.value bB.value bA.subdensity bB.subdensity bA.measurable bB.measurable
  refine ⟨X,Y,hXm,hYm,hXp,hYp,?_⟩
  intro i j S hS
  exact public_factor_event p.publicRecord p.measurable_publicRecord
    (fun x => bA.value i x ⊗ₖ bB.value j x) (fun t => X i t ⊗ₖ Y j t)
    (integrable_subdensity _ (fun x => subdensity_kronecker (bA.subdensity i x) (bB.subdensity j x))
      (measurable_matrix_kronecker ((bA.measurable i).mono (p.localField_le true) le_rfl)
        ((bB.measurable j).mono (p.localField_le false) le_rfl)) P)
    (measurable_matrix_kronecker (hXm i) (hYm j)) (hXY i j) S hS

end

open UnrestrictedQuantum

universe v7869_0 v7869_1 v7869_2 v7869_3 v7869_4 v7869_5 v7869_6 v7869_7 v7869_8 v7869_9

variable {O : Type v7869_0} {M : Type v7869_1} {ι : Type v7869_2} {η : Type v7869_3} [inst7869_0 : MeasurableSpace O] [inst7869_1 : MeasurableSpace M]
  [inst7869_2 : StandardBorelSpace O] [inst7869_3 : Nonempty O] [inst7869_4 : StandardBorelSpace M] [inst7869_5 : Nonempty M]
  [inst7869_6 : Fintype ι] [inst7869_7 : Fintype η] [inst7869_8 : DecidableEq ι] [inst7869_9 : DecidableEq η]
  {A : ℕ → Type v7869_4} {B : ℕ → Type v7869_5}
  [inst7869_10 : ∀ n, AddCommGroup (A n)] [inst7869_11 : ∀ n, Module ℂ (A n)] [inst7869_12 : ∀ n, One (A n)] [inst7869_13 : ∀ n, LE (A n)]
  [inst7869_14 : ∀ n, AddCommGroup (B n)] [inst7869_15 : ∀ n, Module ℂ (B n)] [inst7869_16 : ∀ n, One (B n)] [inst7869_17 : ∀ n, LE (B n)]
  (p : AdaptiveOutcomeSampler O M)
  (κA κB : (n : ℕ) → Kernel (LocalHistory O M n) O)
  [inst7869_18 : ∀ n, IsMarkovKernel (κA n)] [inst7869_19 : ∀ n, IsMarkovKernel (κB n)]
  (eA : LocalObservableExecution (ι := ι) A κA p.sendA)
  (eB : LocalObservableExecution (ι := η) B κB p.sendB)
  {TA : Type v7869_6} {TB : Type v7869_7} {CA : Type v7869_8} {CB : Type v7869_9}
  [inst7869_20 : AddCommGroup TA] [inst7869_21 : Module ℂ TA] [inst7869_22 : One TA] [inst7869_23 : LE TA]
  [inst7869_24 : AddCommGroup TB] [inst7869_25 : Module ℂ TB] [inst7869_26 : One TB] [inst7869_27 : LE TB]
  [inst7869_28 : AddCommGroup CA] [inst7869_29 : Module ℂ CA] [inst7869_30 : One CA] [inst7869_31 : LE CA]
  [inst7869_32 : AddCommGroup CB] [inst7869_33 : Module ℂ CB] [inst7869_34 : One CB] [inst7869_35 : LE CB]
  (P : Measure (ℕ → O)) [inst7869_36 : IsProbabilityMeasure P]
  (hP : ∀ n, P.map (historyPrefix (n+1)) =
      ((P.map (historyPrefix n)) ⊗ₘ p.instrumentKernel κA κB n).map
        (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2))
  (eTA : IncomingObservableProcess (L := p.localField true) (A := TA) P historyFiltration
    (fun n x => globalLocalReferenceA p κA eA n (historyPrefix n x)))
  (eTB : IncomingObservableProcess (L := p.localField false) (A := TB) P historyFiltration
    (fun n x => globalLocalReferenceB p κB eB n (historyPrefix n x)))
  (bA : eTA.BitReadout (B := CA)) (bB : eTB.BitReadout (B := CB))

include hP

theorem terminal_reference_total :
    (∫ x, bA.value false x ⊗ₖ bB.value false x ∂P) +
    (∫ x, bA.value false x ⊗ₖ bB.value true x ∂P) +
    (∫ x, bA.value true x ⊗ₖ bB.value false x ∂P) +
    (∫ x, bA.value true x ⊗ₖ bB.value true x ∂P) =
      jointReference p κA κB eA eB 0 Fin.elim0 := by
  have hi (i j : Bool) : Integrable (fun x => bA.value i x ⊗ₖ bB.value j x) P :=
    integrable_subdensity _ (fun x => subdensity_kronecker (bA.subdensity i x) (bB.subdensity j x))
      (measurable_matrix_kronecker ((bA.measurable i).mono (p.localField_le true) le_rfl)
        ((bB.measurable j).mono (p.localField_le false) le_rfl)) P
  have h2 := (integral_add ((hi false false).add (hi false true)) (hi true false)).symm
  have h3 := (integral_add (((hi false false).add (hi false true)).add (hi true false)) (hi true true)).symm
  simp only [Pi.add_apply] at h2 h3
  rw [← integral_add (hi false false) (hi false true),h2,h3]
  have hs (x : ℕ → O) : bA.value false x ⊗ₖ bB.value false x +
      bA.value false x ⊗ₖ bB.value true x + bA.value true x ⊗ₖ bB.value false x +
      bA.value true x ⊗ₖ bB.value true x = eTA.state x 1 ⊗ₖ eTB.state x 1 := by
    rw [← bA.sum x,← bB.sum x,Matrix.add_kronecker,Matrix.kronecker_add,Matrix.kronecker_add]
    abel
  simp_rw [hs]
  have hc := incoming_joint_reference_consistency p κA κB eA eB P hP eTA eTB
    0 Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hc
  rw [hc]
  have he (x : ℕ → O) : historyPrefix 0 x = Fin.elim0 := Subsingleton.elim _ _
  simp_rw [he]
  simp

theorem terminal_public_normalization
    (hlaw : ∀ n s, ((volume : Measure I).prod volume).map
      (fun u => p.causal.step n (s,u)) = p.instrumentKernel κA κB n s) :
    ∃ X : Bool → (ℕ → M) → Matrix ι ι ℂ,
    ∃ Y : Bool → (ℕ → M) → Matrix η η ℂ,
      (∀ i, Measurable (X i)) ∧ (∀ j, Measurable (Y j)) ∧
      (∀ i t, Subdensity (X i t)) ∧ (∀ j t, Subdensity (Y j t)) ∧
      (∀ i j S, MeasurableSet S →
        (∫ t in S, X i t ⊗ₖ Y j t ∂P.map p.publicRecord) =
          ∫ x in p.publicRecord ⁻¹' S, bA.value i x ⊗ₖ bB.value j x ∂P) ∧
      (∫ t, X false t ⊗ₖ Y false t ∂P.map p.publicRecord) +
      (∫ t, X false t ⊗ₖ Y true t ∂P.map p.publicRecord) +
      (∫ t, X true t ⊗ₖ Y false t ∂P.map p.publicRecord) +
      (∫ t, X true t ⊗ₖ Y true t ∂P.map p.publicRecord) =
        jointReference p κA κB eA eB 0 Fin.elim0 := by
  obtain ⟨X,Y,hXm,hYm,hX,hY,hXY⟩ := genuine_terminal_public_factors
    p κA κB eA eB P hP eTA eTB bA bB hlaw
  refine ⟨X,Y,hXm,hYm,hX,hY,hXY,?_⟩
  have ht (i j : Bool) := hXY i j Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ,Set.preimage_univ] at ht
  simp_rw [ht]
  exact terminal_reference_total p κA κB eA eB P hP eTA eTB bA bB

end AdaptiveQuantum

section

open Matrix

open scoped ComplexOrder MatrixOrder Kronecker

universe v7966_0 v7966_1

variable {ι : Type v7966_0} {η : Type v7966_1} [inst7966_0 : Fintype ι] [inst7966_1 : Fintype η] [inst7966_2 : DecidableEq ι] [inst7966_3 : DecidableEq η]

lemma localProbe_reference :
    keepReference (outer (localProbe (ι := ι)) localProbe) =
      (Fintype.card ι : ℂ)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [localProbe,keepReference_vectorize]
  simp only [Matrix.conjTranspose_smul,Matrix.conjTranspose_one,
    Matrix.smul_mul,Matrix.mul_smul,one_mul,Matrix.transpose_smul,Matrix.transpose_one]
  have hc : star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℂ)) *
      ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℂ) = (Fintype.card ι : ℂ)⁻¹ := by
    simp only [map_inv₀,Complex.star_def,Complex.conj_ofReal]
    rw [← mul_inv,← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  rw [smul_smul,mul_comm,hc]

lemma localProbe_reference_product :
    keepReference (outer (localProbe (ι := ι)) localProbe) ⊗ₖ
      keepReference (outer (localProbe (ι := η)) localProbe) =
    keepReference (outer (localProbe (ι := ι × η)) localProbe) := by
  simp only [localProbe_reference,Matrix.smul_kronecker,Matrix.kronecker_smul,
    Matrix.one_kronecker_one,smul_smul,Fintype.card_prod,Nat.cast_mul,mul_inv]
  rw [mul_comm]

end

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v8064_0 v8064_1

structure Discussion (O : Type v8064_0) (M : Type v8064_1) [MeasurableSpace O] [MeasurableSpace M] where
  alice : (n : ℕ) → (Fin n → M) → Bool
  alice_measurable : ∀ n, Measurable (alice n)
  kernelA : (n : ℕ) → Kernel (LocalHistory O M n) O
  kernelB : (n : ℕ) → Kernel (LocalHistory O M n) O
  markovA : ∀ n, IsMarkovKernel (kernelA n)
  markovB : ∀ n, IsMarkovKernel (kernelB n)
  sendA : (n : ℕ) → LocalHistory O M n × O → M
  sendB : (n : ℕ) → LocalHistory O M n × O → M
  sendA_measurable : ∀ n, Measurable (sendA n)
  sendB_measurable : ∀ n, Measurable (sendB n)

namespace Discussion

universe v8077_0 v8077_1

variable {O : Type v8077_0} {M : Type v8077_1} [inst8077_0 : MeasurableSpace O] [inst8077_1 : MeasurableSpace M]
  [inst8077_2 : StandardBorelSpace O] [inst8077_3 : Nonempty O] (d : Discussion O M)

attribute [instance] markovA markovB

def sampler : AdaptiveOutcomeSampler O M := by
  have sample (n : ℕ) (κ : Kernel (LocalHistory O M n) O) [IsMarkovKernel κ] :
      ∃ f : LocalHistory O M n → I → O, Measurable (uncurry f) ∧
        (∀ h, volume.map (f h) = κ h) ∧
        ∀ (μ : Measure (LocalHistory O M n)) [IsFiniteMeasure μ],
          (μ.prod (volume : Measure I)).map (fun p => (p.1, f p.1 p.2)) = μ ⊗ₘ κ := by
    obtain ⟨f, hf, hfLaw⟩ := κ.exists_measurable_map_eq_unitInterval
    change Measurable (fun pair : LocalHistory O M n × I => f pair.1 pair.2) at hf
    refine ⟨f, hf, hfLaw, ?_⟩
    intro μ hμ
    ext B hB
    rw [Measure.map_apply (measurable_fst.prodMk hf) hB,
      Measure.prod_apply (hB.preimage (measurable_fst.prodMk hf)),
      Measure.compProd_apply hB]
    congr 1
    funext h
    rw [← hfLaw h, Measure.map_apply hf.of_uncurry_left (measurable_prodMk_left hB)]
    rfl
  exact {
    alice := d.alice
    alice_meas := d.alice_measurable
    sampleA n := uncurry (Classical.choose (sample n (d.kernelA n)))
    sampleB n := uncurry (Classical.choose (sample n (d.kernelB n)))
    sendA := d.sendA
    sendB := d.sendB
    sampleA_meas n := (Classical.choose_spec (sample n (d.kernelA n))).1
    sampleB_meas n := (Classical.choose_spec (sample n (d.kernelB n))).1
    sendA_meas := d.sendA_measurable
    sendB_meas := d.sendB_measurable }

lemma sampler_law : ∀ n s, ((volume : Measure I).prod volume).map
    (fun u => d.sampler.causal.step n (s,u)) =
      d.sampler.instrumentKernel d.kernelA d.kernelB n s := by
  apply d.sampler.causal_step_law
  · intro n s
    exact (Classical.choose_spec (sample_instrument_kernel (d.kernelA n))).2.1 s
  · intro n s
    exact (Classical.choose_spec (sample_instrument_kernel (d.kernelB n))).2.1 s

def probeLaw : Measure (ℕ → O) :=
  (noiseTapeLaw ((volume : Measure I).prod volume)).map d.sampler.causalRecord

instance probeLaw_probability : IsProbabilityMeasure d.probeLaw :=
  inferInstanceAs (IsProbabilityMeasure ((noiseTapeLaw ((volume : Measure I).prod volume)).map d.sampler.causal.record))

lemma probeLaw_prefix (n : ℕ) : d.probeLaw.map (historyPrefix (n+1)) =
    ((d.probeLaw.map (historyPrefix n)) ⊗ₘ
      d.sampler.instrumentKernel d.kernelA d.kernelB n).map
      (fun pair : (Fin n → O) × O => Fin.snoc (α := fun _ : Fin (n+1) => O) pair.1 pair.2) := by
  have he (k : ℕ) : historyPrefix k ∘ d.sampler.causal.record =
      d.sampler.causal.history k := by
    funext u i
    exact (d.sampler.causal.prefix_eq_record k u i).symm
  simp only [probeLaw, AdaptiveOutcomeSampler.causalRecord_eq, Measure.map_map (measurable_historyPrefix _) d.sampler.causal.measurable_record,he]
  exact d.sampler.causal.prefix_law_succ _ d.sampler_law n

def transcriptLaw : Measure (ℕ → M) := d.probeLaw.map d.sampler.publicRecord

instance transcriptLaw_probability : IsProbabilityMeasure d.transcriptLaw :=
  inferInstanceAs (IsProbabilityMeasure (d.probeLaw.map d.sampler.publicRecord))

end Discussion

end

section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

universe v8144_0 v8144_1

variable {ι : Type v8144_0} {κ : Type v8144_1} [inst8144_0 : Fintype ι] [inst8144_1 : Fintype κ] [inst8144_2 : DecidableEq ι] [inst8144_3 : DecidableEq κ]

lemma preparationFilter_product (R : Matrix (ι × κ) (ι × κ) ℂ)
    (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) :
    preparationFilter R * (U ⊗ₖ V) * (preparationFilter R)ᴴ =
      (CFC.sqrt R * (((Fintype.card ι : ℂ) • Uᵀ) ⊗ₖ ((Fintype.card κ : ℂ) • Vᵀ)) * CFC.sqrt R)ᵀ := by
  have hs : (CFC.sqrt R)ᴴ = CFC.sqrt R := (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq
  have ht : ((CFC.sqrt R)ᵀ)ᴴ = (CFC.sqrt R)ᵀ := by
    rw [Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,hs]
  have hc : (Real.sqrt (Fintype.card (ι × κ) : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card (ι × κ) : ℝ) : ℂ) =
      (Fintype.card ι : ℂ)*(Fintype.card κ : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _),
      Fintype.card_prod,Nat.cast_mul]
    simp
  unfold preparationFilter
  simp only [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,ht,
    smul_mul_assoc,mul_smul_comm,smul_smul,Matrix.transpose_mul,
    ← Matrix.kroneckerMap_transpose,Matrix.transpose_smul,Matrix.transpose_transpose,
    Matrix.smul_kronecker,Matrix.kronecker_smul]
  rw [hc]
  congr 1
  · ring
  · exact Matrix.mul_assoc _ _ _

end

section

open scoped MatrixOrder ComplexOrder Kronecker

open Matrix

universe v8360_0

def eveBlock {ι : Type v8360_0} [inst8360_0 : Fintype ι] [inst8360_1 : DecidableEq ι]
    (R D : Matrix ι ι ℂ) : Matrix ι ι ℂ := (CFC.sqrt R * D * CFC.sqrt R)ᵀ

open MeasureTheory

open scoped Matrix.Norms.L2Operator

universe v8632_0 v8632_1

variable {ι : Type v8632_0} {Ω : Type v8632_1} [inst8632_0 : Fintype ι] [inst8632_1 : DecidableEq ι] [inst8632_2 : MeasurableSpace Ω]

universe v8637_0

structure BitDensity (μ : Measure Ω) (ι : Type v8637_0) [Fintype ι] where
  block : Bool → Bool → Ω → Matrix ι ι ℂ
  positive : ∀ i j t, (block i j t).PosSemidef
  measurable : ∀ i j, Measurable (block i j)
  integrable : ∀ i j, Integrable (fun t => (trace (block i j t)).re) μ
  normalized : (∫ t, (trace (block false false t)).re ∂μ) +
    (∫ t, (trace (block false true t)).re ∂μ) +
    (∫ t, (trace (block true false t)).re ∂μ) +
    (∫ t, (trace (block true true t)).re ∂μ) = 1

def BitDensity.mass {μ : Measure Ω} (τ : BitDensity μ ι) (i j : Bool) : ℝ :=
  ∫ t, (trace (τ.block i j t)).re ∂μ

def BitDensity.idealBitError {μ : Measure Ω} (τ : BitDensity μ ι)
    (σ : Ω → Matrix ι ι ℂ) : ℝ :=
  τ.mass false true + τ.mass true false +
  (∫ t, traceNorm (τ.block false false t - (1/2 : ℝ) • σ t) ∂μ) +
  (∫ t, traceNorm (τ.block true true t - (1/2 : ℝ) • σ t) ∂μ)

end

section

open Matrix MeasureTheory ProbabilityTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

section MatrixFiltering

universe v8879_0 v8879_1 v8879_2

variable {ι : Type v8879_0} {η : Type v8879_1} {Ω : Type v8879_2} [inst8879_0 : Fintype ι] [inst8879_1 : Fintype η] [inst8879_2 : DecidableEq ι] [inst8879_3 : DecidableEq η]
  [inst8879_4 : MeasurableSpace Ω] {μ : Measure Ω}

def matrixFilterLinear (K : Matrix η ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix η η ℂ where
  toFun U := K * U * Kᴴ
  map_add' U V := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' c U := by simp only [Matrix.mul_smul,Matrix.smul_mul,RingHom.id_apply]

lemma integral_filter (K : Matrix η ι ℂ) {U : Ω → Matrix ι ι ℂ}
    (hi : Integrable U μ) :
    (∫ x, K * U x * Kᴴ ∂μ) = K * (∫ x, U x ∂μ) * Kᴴ :=
  (matrixFilterLinear K).toContinuousLinearMap.integral_comp_comm hi

lemma integrable_filter (K : Matrix η ι ℂ) {U : Ω → Matrix ι ι ℂ}
    (hi : Integrable U μ) : Integrable (fun x => K * U x * Kᴴ) μ :=
  (matrixFilterLinear K).toContinuousLinearMap.integrable_comp hi

lemma integral_realTrace {U : Ω → Matrix ι ι ℂ} (hi : Integrable U μ) :
    (∫ x, (trace (U x)).re ∂μ) = (trace (∫ x, U x ∂μ)).re := by
  let L : Matrix ι ι ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap ι ℂ ℂ).toContinuousLinearMap
  change (∫ x, RCLike.re (L (U x)) ∂μ) = (L (∫ x,U x ∂μ)).re
  rw [integral_re (L.integrable_comp hi)]
  exact congrArg Complex.re (L.integral_comp_comm hi)

lemma preparationFilter_probe_reference [Nonempty ι]
    (R : Matrix ι ι ℂ) (hR : R.PosSemidef) :
    preparationFilter R * keepReference (outer (localProbe (ι := ι)) localProbe) *
      (preparationFilter R)ᴴ = Rᵀ := by
  rw [← keepReference_filter,preparation_filter_identity,canonical_reference R hR]

end MatrixFiltering

universe v8912_0 v8912_1 v8912_2

variable {ι : Type v8912_0} {η : Type v8912_1} {T : Type v8912_2} [inst8912_0 : Fintype ι] [inst8912_1 : Fintype η] [inst8912_2 : DecidableEq ι] [inst8912_3 : DecidableEq η]
  [inst8912_4 : Nonempty ι] [inst8912_5 : Nonempty η] [inst8912_6 : MeasurableSpace T]
  (μ : Measure T) [inst8912_7 : IsFiniteMeasure μ]
  (X : Bool → T → Matrix ι ι ℂ) (Y : Bool → T → Matrix η η ℂ)
  (hXm : ∀ i, Measurable (X i)) (hYm : ∀ j, Measurable (Y j))
  (hX : ∀ i t, Subdensity (X i t)) (hY : ∀ j t, Subdensity (Y j t))
  (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)

omit inst8912_4 inst8912_5 in
include hXm hYm hX hY in
lemma public_product_integrable [Nonempty ι] [Nonempty η] (i j : Bool) : Integrable (fun t => X i t ⊗ₖ Y j t) μ :=
  integrable_subdensity _ (fun t => subdensity_kronecker (hX i t) (hY j t))
    (measurable_matrix_kronecker (hXm i) (hYm j)) μ

def filteredPublicDensity
    (hInit : (∫ t, X false t ⊗ₖ Y false t ∂μ) +
      (∫ t, X false t ⊗ₖ Y true t ∂μ) +
      (∫ t, X true t ⊗ₖ Y false t ∂μ) +
      (∫ t, X true t ⊗ₖ Y true t ∂μ) =
        keepReference (outer (localProbe (ι := ι × η)) localProbe)) : BitDensity μ (ι × η) where
  block i j t := preparationFilter R * (X i t ⊗ₖ Y j t) * (preparationFilter R)ᴴ
  positive i j t := ((hX i t).1.kronecker (hY j t).1).mul_mul_conjTranspose_same _
  measurable i j := (matrixFilterLinear (preparationFilter R)).toContinuousLinearMap.measurable.comp
    (measurable_matrix_kronecker (hXm i) (hYm j))
  integrable i j := by
    let L : Matrix (ι × η) (ι × η) ℂ →L[ℂ] ℂ :=
      (Matrix.traceLinearMap (ι × η) ℂ ℂ).toContinuousLinearMap
    exact (L.integrable_comp (integrable_filter _ (public_product_integrable μ X Y hXm hYm hX hY i j))).re
  normalized := by
    have hi (i j : Bool) := integrable_filter (preparationFilter R)
      (public_product_integrable μ X Y hXm hYm hX hY i j)
    rw [integral_realTrace (hi false false),integral_realTrace (hi false true),
      integral_realTrace (hi true false),integral_realTrace (hi true true)]
    simp_rw [integral_filter _ (public_product_integrable μ X Y hXm hYm hX hY _ _)]
    rw [← Complex.add_re,← Matrix.trace_add,← Complex.add_re,← Matrix.trace_add,
      ← Complex.add_re,← Matrix.trace_add]
    rw [← Matrix.add_mul,← Matrix.mul_add,← Matrix.add_mul,← Matrix.mul_add,
      ← Matrix.add_mul,← Matrix.mul_add,hInit,preparationFilter_probe_reference R hR.1,
      Matrix.trace_transpose,hR.2]
    rfl

lemma filteredPublicDensity_common_factors
    (hInit : (∫ t, X false t ⊗ₖ Y false t ∂μ) +
      (∫ t, X false t ⊗ₖ Y true t ∂μ) +
      (∫ t, X true t ⊗ₖ Y false t ∂μ) +
      (∫ t, X true t ⊗ₖ Y true t ∂μ) =
        keepReference (outer (localProbe (ι := ι × η)) localProbe)) (i j : Bool) (t : T) :
    (filteredPublicDensity μ X Y hXm hYm hX hY R hR hInit).block i j t =
      eveBlock R (((Fintype.card ι : ℂ) • (X i t)ᵀ) ⊗ₖ ((Fintype.card η : ℂ) • (Y j t)ᵀ)) :=
  preparationFilter_product R (X i t) (Y j t)

end

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v8979_0 v8979_1 v8979_2 v8979_3 v8979_4 v8979_5 v8979_6 v8979_7 v8979_8 v8979_9

variable {O : Type v8979_0} {M : Type v8979_1} {ι : Type v8979_2} {η : Type v8979_3} [inst8979_0 : MeasurableSpace O] [inst8979_1 : MeasurableSpace M]
  [inst8979_2 : StandardBorelSpace O] [inst8979_3 : Nonempty O] [inst8979_4 : StandardBorelSpace M] [inst8979_5 : Nonempty M]
  [inst8979_6 : Fintype ι] [inst8979_7 : Fintype η] [inst8979_8 : DecidableEq ι] [inst8979_9 : DecidableEq η]
  (d : Discussion O M)
  (A : ℕ → Type v8979_4) (B : ℕ → Type v8979_5)
  [inst8979_10 : ∀ n, AddCommGroup (A n)] [inst8979_11 : ∀ n, Module ℂ (A n)] [inst8979_12 : ∀ n, One (A n)] [inst8979_13 : ∀ n, LE (A n)]
  [inst8979_14 : ∀ n, AddCommGroup (B n)] [inst8979_15 : ∀ n, Module ℂ (B n)] [inst8979_16 : ∀ n, One (B n)] [inst8979_17 : ∀ n, LE (B n)]
  (TA : Type v8979_6) (TB : Type v8979_7) (CA : Type v8979_8) (CB : Type v8979_9)
  [inst8979_18 : AddCommGroup TA] [inst8979_19 : Module ℂ TA] [inst8979_20 : One TA] [inst8979_21 : LE TA]
  [inst8979_22 : AddCommGroup TB] [inst8979_23 : Module ℂ TB] [inst8979_24 : One TB] [inst8979_25 : LE TB]
  [inst8979_26 : AddCommGroup CA] [inst8979_27 : Module ℂ CA] [inst8979_28 : One CA] [inst8979_29 : LE CA]
  [inst8979_30 : AddCommGroup CB] [inst8979_31 : Module ℂ CB] [inst8979_32 : One CB] [inst8979_33 : LE CB]

structure BitProtocol where
  executionA : LocalObservableExecution (ι := ι) A d.kernelA d.sendA
  executionB : LocalObservableExecution (ι := η) B d.kernelB d.sendB
  initialA : executionA.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := ι)) localProbe)
  initialB : executionB.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := η)) localProbe)
  incomingA : IncomingObservableProcess (L := d.sampler.localField true) (A := TA)
    d.probeLaw historyFiltration
    (fun n x => AdaptiveQuantum.globalLocalReferenceA d.sampler d.kernelA executionA n (historyPrefix n x))
  incomingB : IncomingObservableProcess (L := d.sampler.localField false) (A := TB)
    d.probeLaw historyFiltration
    (fun n x => AdaptiveQuantum.globalLocalReferenceB d.sampler d.kernelB executionB n (historyPrefix n x))
  readoutA : incomingA.BitReadout (B := CA)
  readoutB : incomingB.BitReadout (B := CB)

variable {d A B TA TB CA CB}

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)

def completeReference (i j : Bool) (x : ℕ → O) : Matrix (ι × η) (ι × η) ℂ :=
  p.readoutA.value i x ⊗ₖ p.readoutB.value j x

omit inst8979_4 inst8979_5 in
lemma completeReference_positive [StandardBorelSpace M] [Nonempty M] (i j : Bool) (x : ℕ → O) :
    (p.completeReference i j x).PosSemidef :=
  (p.readoutA.positive i x).kronecker (p.readoutB.positive j x)

omit inst8979_4 inst8979_5 in
lemma completeReference_measurable [StandardBorelSpace M] [Nonempty M] (i j : Bool) : Measurable (p.completeReference i j) :=
  measurable_matrix_kronecker
    ((p.readoutA.measurable i).mono (d.sampler.localField_le true) le_rfl)
    ((p.readoutB.measurable j).mono (d.sampler.localField_le false) le_rfl)

lemma completeReference_integrable (i j : Bool) : Integrable (p.completeReference i j) d.probeLaw :=
  integrable_subdensity _
    (fun x => subdensity_kronecker (p.readoutA.subdensity i x) (p.readoutB.subdensity j x))
    (p.completeReference_measurable i j) d.probeLaw

lemma completeReference_entry_integrable (i j : Bool) (k l : ι × η) :
    Integrable (fun x => p.completeReference i j x k l) d.probeLaw :=
  ((Matrix.entryLinearMap ℂ ℂ k l).toContinuousLinearMap).integrable_comp
    (p.completeReference_integrable i j)

def probeOutput (i j : Bool) : PositiveMatrixMeasure (ℕ → M) (ι × η) :=
  (positiveMatrixMeasureOfDensity (p.completeReference_entry_integrable i j)
    (Eventually.of_forall (p.completeReference_positive i j))).pushforward
    d.sampler.publicRecord d.sampler.measurable_publicRecord

lemma probeOutput_event (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.probeOutput i j).value S =
      ∫ x in d.sampler.publicRecord ⁻¹' S, p.completeReference i j x ∂d.probeLaw := by
  rw [probeOutput,PositiveMatrixMeasure.pushforward_value _ _ _ S hS,
    positiveMatrixMeasureOfDensity_value _ _ _ (d.sampler.measurable_publicRecord hS)]

omit inst8979_4 inst8979_5 in
lemma initial_joint_reference [StandardBorelSpace M] [Nonempty M] :
    AdaptiveQuantum.jointReference d.sampler d.kernelA d.kernelB p.executionA p.executionB
      0 Fin.elim0 = keepReference (outer (localProbe (ι := ι × η)) localProbe) := by
  unfold AdaptiveQuantum.jointReference AdaptiveQuantum.globalLocalReferenceA
    AdaptiveQuantum.globalLocalReferenceB
  have ha : (d.sampler.extractPrivate true 0 Fin.elim0,d.sampler.publicFrom 0 Fin.elim0) =
      (Fin.elim0,Fin.elim0) := Subsingleton.elim _ _
  have hb : (d.sampler.extractPrivate false 0 Fin.elim0,d.sampler.publicFrom 0 Fin.elim0) =
      (Fin.elim0,Fin.elim0) := Subsingleton.elim _ _
  rw [ha,hb]
  change p.executionA.reference 0 (Fin.elim0,Fin.elim0) ⊗ₖ
    p.executionB.reference 0 (Fin.elim0,Fin.elim0) = _
  rw [p.initialA,p.initialB,localProbe_reference_product]

theorem public_factors :
    ∃ X : Bool → (ℕ → M) → Matrix ι ι ℂ,
    ∃ Y : Bool → (ℕ → M) → Matrix η η ℂ,
      (∀ i, Measurable (X i)) ∧ (∀ j, Measurable (Y j)) ∧
      (∀ i t, Subdensity (X i t)) ∧ (∀ j t, Subdensity (Y j t)) ∧
      (∀ i j S, MeasurableSet S → (p.probeOutput i j).value S =
        ∫ t in S, X i t ⊗ₖ Y j t ∂d.transcriptLaw) ∧
      (∫ t, X false t ⊗ₖ Y false t ∂d.transcriptLaw) +
      (∫ t, X false t ⊗ₖ Y true t ∂d.transcriptLaw) +
      (∫ t, X true t ⊗ₖ Y false t ∂d.transcriptLaw) +
      (∫ t, X true t ⊗ₖ Y true t ∂d.transcriptLaw) =
        keepReference (outer (localProbe (ι := ι × η)) localProbe) := by
  obtain ⟨X,Y,hXm,hYm,hX,hY,hXY,hn⟩ := AdaptiveQuantum.terminal_public_normalization
    d.sampler d.kernelA d.kernelB p.executionA p.executionB d.probeLaw d.probeLaw_prefix
    p.incomingA p.incomingB p.readoutA p.readoutB d.sampler_law
  refine ⟨X,Y,hXm,hYm,hX,hY,?_,hn.trans p.initial_joint_reference⟩
  intro i j S hS
  exact (p.probeOutput_event i j S hS).trans (hXY i j S hS).symm

def canonicalOutput (R : Matrix (ι × η) (ι × η) ℂ) (i j : Bool) :
    PositiveMatrixMeasure (ℕ → M) (ι × η) :=
  (p.probeOutput i j).filter (preparationFilter R)

end BitProtocol

end

namespace PositiveMatrixMeasure

open MeasureTheory Matrix Filter

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

universe v9237_0 v9237_1

variable {Ω : Type v9237_0} {ι : Type v9237_1} [inst9237_0 : MeasurableSpace Ω] [inst9237_1 : Fintype ι] [inst9237_2 : DecidableEq ι]

def positiveDensity (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) (t : Ω) : Matrix ι ι ℂ :=
  by classical exact if (W.density μ t).PosSemidef then W.density μ t else 0

omit inst9237_2 in
lemma positiveDensity_pos [DecidableEq ι] (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) (t : Ω) :
    (W.positiveDensity μ t).PosSemidef := by
  unfold positiveDensity
  split
  · assumption
  · exact Matrix.PosSemidef.zero

lemma measurable_positiveDensity (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) :
    Measurable (W.positiveDensity μ) := by
  have hm : MeasurableSet {t | (W.density μ t).PosSemidef} := by
    have he : {t | (W.density μ t).PosSemidef} = (W.density μ) ⁻¹' Set.Ici 0 := by
      ext t
      exact Matrix.nonneg_iff_posSemidef.symm
    rw [he]
    exact (W.measurable_density μ) measurableSet_Ici
  exact (W.measurable_density μ).ite hm measurable_const

lemma positiveDensity_ae (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ S, MeasurableSet S → μ S=0 → W.value S=0) :
    W.positiveDensity μ =ᵐ[μ] W.density μ := by
  filter_upwards [density_posSemidef_ae W μ hAC] with t ht
  exact ite_eq_left ht

lemma integrable_positiveDensity_trace (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω)
    [SigmaFinite μ] (hAC : ∀ S, MeasurableSet S → μ S=0 → W.value S=0) :
    Integrable (fun t => (trace (W.positiveDensity μ t)).re) μ := by
  apply (W.integrable_trace_density μ).re.congr
  filter_upwards [W.positiveDensity_ae μ hAC] with t ht
  rw [ht]
  rfl

lemma integral_positiveDensity_trace (W : PositiveMatrixMeasure Ω ι) (μ : Measure Ω)
    [SigmaFinite μ] (hAC : ∀ S, MeasurableSet S → μ S=0 → W.value S=0) :
    (∫ t, (trace (W.positiveDensity μ t)).re ∂μ) = (trace (W.value Set.univ)).re := by
  calc
    _ = ∫ t, (trace (W.density μ t)).re ∂μ := by
      apply integral_congr_ae
      filter_upwards [W.positiveDensity_ae μ hAC] with t ht
      rw [ht]
    _ = (trace (W.value Set.univ)).re := by
      change (∫ t, RCLike.re (trace (W.density μ t)) ∂μ) = _
      rw [integral_re (W.integrable_trace_density μ)]
      have he := W.integral_trace_density μ hAC Set.univ MeasurableSet.univ
      change (∫ t, trace (W.density μ t) ∂μ).re = _
      simpa only [Measure.restrict_univ] using congrArg Complex.re he

def toBitDensity (W : Bool → Bool → PositiveMatrixMeasure Ω ι)
    (μ : Measure Ω) [SigmaFinite μ]
    (hAC : ∀ i j S, MeasurableSet S → μ S=0 → (W i j).value S=0)
    (hn : (trace ((W false false).value Set.univ)).re +
      (trace ((W false true).value Set.univ)).re +
      (trace ((W true false).value Set.univ)).re +
      (trace ((W true true).value Set.univ)).re = 1) : BitDensity μ ι where
  block i j := (W i j).positiveDensity μ
  positive i j := (W i j).positiveDensity_pos μ
  measurable i j := (W i j).measurable_positiveDensity μ
  integrable i j := (W i j).integrable_positiveDensity_trace μ (hAC i j)
  normalized := by
    simp only [integral_positiveDensity_trace _ μ (hAC _ _)]
    exact hn

end PositiveMatrixMeasure

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v9409_0 v9409_1 v9409_2 v9409_3 v9409_4 v9409_5 v9409_6 v9409_7 v9409_8 v9409_9

variable {O : Type v9409_0} {M : Type v9409_1} {ι : Type v9409_2} {η : Type v9409_3} [inst9409_0 : MeasurableSpace O] [inst9409_1 : MeasurableSpace M]
  [inst9409_2 : StandardBorelSpace O] [inst9409_3 : Nonempty O] [inst9409_4 : StandardBorelSpace M] [inst9409_5 : Nonempty M]
  [inst9409_6 : Fintype ι] [inst9409_7 : Fintype η] [inst9409_8 : DecidableEq ι] [inst9409_9 : DecidableEq η]
  [inst9409_10 : Nonempty ι] [inst9409_11 : Nonempty η]
  {d : Discussion O M} {A : ℕ → Type v9409_4} {B : ℕ → Type v9409_5}
  [inst9409_12 : ∀ n, AddCommGroup (A n)] [inst9409_13 : ∀ n, Module ℂ (A n)] [inst9409_14 : ∀ n, One (A n)] [inst9409_15 : ∀ n, LE (A n)]
  [inst9409_16 : ∀ n, AddCommGroup (B n)] [inst9409_17 : ∀ n, Module ℂ (B n)] [inst9409_18 : ∀ n, One (B n)] [inst9409_19 : ∀ n, LE (B n)]
  {TA : Type v9409_6} {TB : Type v9409_7} {CA : Type v9409_8} {CB : Type v9409_9}
  [inst9409_20 : AddCommGroup TA] [inst9409_21 : Module ℂ TA] [inst9409_22 : One TA] [inst9409_23 : LE TA]
  [inst9409_24 : AddCommGroup TB] [inst9409_25 : Module ℂ TB] [inst9409_26 : One TB] [inst9409_27 : LE TB]
  [inst9409_28 : AddCommGroup CA] [inst9409_29 : Module ℂ CA] [inst9409_30 : One CA] [inst9409_31 : LE CA]
  [inst9409_32 : AddCommGroup CB] [inst9409_33 : Module ℂ CB] [inst9409_34 : One CB] [inst9409_35 : LE CB]

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)
  (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)

include hR

theorem canonical_density_representation :
    ∃ τ : BitDensity d.transcriptLaw (ι × η),
    ∃ X : Bool → (ℕ → M) → Matrix ι ι ℂ,
    ∃ Y : Bool → (ℕ → M) → Matrix η η ℂ,
      (∀ i t, (X i t).PosSemidef) ∧ (∀ j t, (Y j t).PosSemidef) ∧
      (∀ i j t, τ.block i j t = eveBlock R (X i t ⊗ₖ Y j t)) ∧
      (∀ i j, Integrable (τ.block i j) d.transcriptLaw) ∧
      (∀ i j S, MeasurableSet S → (p.canonicalOutput R i j).value S =
        ∫ t in S, τ.block i j t ∂d.transcriptLaw) := by
  obtain ⟨X,Y,hXm,hYm,hX,hY,hXY,hn⟩ := p.public_factors
  let τ := filteredPublicDensity d.transcriptLaw X Y hXm hYm hX hY R hR hn
  refine ⟨τ,fun i t => (Fintype.card ι : ℂ) • (X i t)ᵀ,
    fun j t => (Fintype.card η : ℂ) • (Y j t)ᵀ,?_,?_,?_,?_,?_⟩
  · intro i t
    exact (hX i t).1.transpose.smul (by exact_mod_cast Nat.zero_le (Fintype.card ι))
  · intro j t
    exact (hY j t).1.transpose.smul (by exact_mod_cast Nat.zero_le (Fintype.card η))
  · exact filteredPublicDensity_common_factors d.transcriptLaw X Y hXm hYm hX hY R hR hn
  · intro i j
    exact integrable_filter _ (public_product_integrable d.transcriptLaw X Y hXm hYm hX hY i j)
  · intro i j S hS
    rw [canonicalOutput,PositiveMatrixMeasure.filter_value,hXY i j S hS]
    exact (integral_filter _
      ((public_product_integrable d.transcriptLaw X Y hXm hYm hX hY i j).integrableOn)).symm

lemma canonicalOutput_normalized :
    (trace ((p.canonicalOutput R false false).value Set.univ)).re +
    (trace ((p.canonicalOutput R false true).value Set.univ)).re +
    (trace ((p.canonicalOutput R true false).value Set.univ)).re +
    (trace ((p.canonicalOutput R true true).value Set.univ)).re = 1 := by
  obtain ⟨τ,X,Y,hX,hY,hτ,hi,he⟩ := p.canonical_density_representation R hR
  simp_rw [he _ _ Set.univ MeasurableSet.univ,Measure.restrict_univ,← integral_realTrace (hi _ _)]
  exact τ.normalized

end BitProtocol

end

section

open Matrix MeasureTheory

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v9682_0 v9682_1 v9682_2 v9682_3

variable {Ω : Type v9682_0} {ι : Type v9682_1} {K : Type v9682_2} {Λ : Type v9682_3} [inst9682_0 : MeasurableSpace Ω] [inst9682_1 : Fintype ι] [inst9682_2 : DecidableEq ι]
  [inst9682_3 : Fintype K] [inst9682_4 : DecidableEq K] [inst9682_5 : Fintype Λ] [inst9682_6 : DecidableEq Λ] {μ : Measure Ω}

def cqDistance (W V : K → K → Ω → Matrix ι ι ℂ) (μ : Measure Ω) : ℝ :=
  ∑ a, ∑ b, ∫ t, traceNorm (W a b t - V a b t) ∂μ

def idealFiniteBlocks (sigma : Matrix ι ι ℂ) (a b : K) : Matrix ι ι ℂ :=
  if a = b then (1/(Fintype.card K : ℝ)) • sigma else 0

end

section

open Matrix

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

universe v9922_0 v9922_1

variable {ι : Type v9922_0} {κ : Type v9922_1} [inst9922_0 : Fintype ι] [inst9922_1 : Fintype κ] [inst9922_2 : DecidableEq ι] [inst9922_3 : DecidableEq κ]

def compressReference (D : Matrix ι ι ℂ) :
    Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Z := Z.submatrix Sum.inr Sum.inr + trace (Z.submatrix Sum.inl Sum.inl) • D
  map_add' Z W := by simp [Matrix.submatrix_add,Matrix.trace_add,add_smul]; abel
  map_smul' c Z := by simp [Matrix.submatrix_smul,Matrix.trace_smul,smul_smul,smul_add]

omit inst9922_0 inst9922_2 inst9922_3 in
lemma compressReference_pos [Fintype ι] [DecidableEq ι] [DecidableEq κ] (D : Matrix ι ι ℂ) (hD : D.PosSemidef)
    {Z : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ} (hZ : Z.PosSemidef) :
    (compressReference D Z).PosSemidef :=
  (hZ.submatrix Sum.inr).add (hD.smul (hZ.submatrix Sum.inl).trace_nonneg)

omit inst9922_2 inst9922_3 in
lemma compressReference_trace [DecidableEq ι] [DecidableEq κ] (D : Matrix ι ι ℂ) (hD : trace D = 1)
    (Z : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) : trace (compressReference D Z) = trace Z := by
  change trace (Z.submatrix Sum.inr Sum.inr + trace (Z.submatrix Sum.inl Sum.inl) • D) = _
  rw [Matrix.trace_add,Matrix.trace_smul,hD,smul_eq_mul,mul_one]
  simp only [trace,diag,Matrix.submatrix_apply,Fintype.sum_sum_type]
  exact add_comm _ _

omit inst9922_0 inst9922_2 inst9922_3 in
lemma compressReference_right [Fintype ι] [DecidableEq ι] [DecidableEq κ] (D Z : Matrix ι ι ℂ) :
    compressReference (κ := κ) D (fromBlocks 0 0 0 Z) = Z := by
  ext i j
  simp [compressReference,Matrix.submatrix,Matrix.trace,Matrix.diag]

lemma padded_purification_unitary (M : Matrix ι κ ℂ) (S : Matrix ι ι ℂ)
    (hS : S.IsHermitian) (hgram : M * Mᴴ = S * S) :
    ∃ U : Matrix.unitaryGroup (κ ⊕ ι) ℂ,
      fromBlocks (0 : Matrix κ κ ℂ) Mᴴ 0 0 =
        (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) * fromBlocks 0 0 0 S := by
  apply exists_unitary_mul_of_gram_eq
  simp [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,hS.eq,hgram]

def embedReference : Matrix κ κ ℂ →ₗ[ℂ] Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ where
  toFun Z := fromBlocks Z 0 0 0
  map_add' _ _ := by ext i j; cases i <;> cases j <;> simp
  map_smul' _ _ := by ext i j; cases i <;> cases j <;> simp

omit inst9922_2 in
lemma embedReference_pos [DecidableEq ι] {Z : Matrix κ κ ℂ} (hZ : Z.PosSemidef) :
    (embedReference (ι := ι) Z).PosSemidef := by
  have hh := hZ.mul_mul_conjTranspose_same (Matrix.fromRows (1 : Matrix κ κ ℂ) (0 : Matrix ι κ ℂ))
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols] at hh
  simpa [embedReference] using hh

omit inst9922_2 inst9922_3 in
lemma embedReference_trace [DecidableEq ι] [DecidableEq κ] (Z : Matrix κ κ ℂ) :
    trace (embedReference (ι := ι) Z) = trace Z := by
  simp [embedReference,trace,diag,Fintype.sum_sum_type]

def refSandwich (K : Matrix ι κ ℂ) : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun Z := K * Z * Kᴴ
  map_add' _ _ := by simp [Matrix.mul_add,Matrix.add_mul]
  map_smul' _ _ := by simp [Matrix.mul_smul,Matrix.smul_mul]

lemma padded_purification_blocks (M : Matrix ι κ ℂ) (S : Matrix ι ι ℂ)
    (hS : S.IsHermitian) (U : Matrix.unitaryGroup (κ ⊕ ι) ℂ)
    (hU : fromBlocks (0 : Matrix κ κ ℂ) Mᴴ 0 0 =
      (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) * fromBlocks 0 0 0 S)
    (X : Matrix ι ι ℂ) :
    embedReference (ι := ι) (Mᴴ * X * M) =
      (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) * fromBlocks 0 0 0 (S * X * S) *
      (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)ᴴ := by
  let A : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fromBlocks 0 Mᴴ 0 0
  let B : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fromBlocks 0 0 0 S
  let Y : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := fromBlocks 0 0 0 X
  have he : embedReference (ι := ι) (Mᴴ * X * M) = A * Y * Aᴴ := by
    simp [embedReference,A,Y,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  have hb : B * Y * Bᴴ = fromBlocks 0 0 0 (S*X*S) := by
    simp [B,Y,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,hS.eq]
  change A = (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)*B at hU
  rw [he,hU,Matrix.conjTranspose_mul]
  calc
    (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)*B*Y*(Bᴴ*(U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)ᴴ) =
      (U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)*(B*Y*Bᴴ)*(U : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ)ᴴ := by noncomm_ring
    _ = _ := by rw [hb]

theorem purification_recovery (R : Matrix ι ι ℂ) (hR : Density R)
    (M : Matrix ι κ ℂ) (hM : M * Mᴴ = R) :
    ∃ L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ,
      (∀ Z, Z.PosSemidef → (L Z).PosSemidef) ∧
      (∀ Z, trace (L Z) = trace Z) ∧
      ∀ X, L (Mᴴ * X * M) = CFC.sqrt R * X * CFC.sqrt R := by
  let S := CFC.sqrt R
  have hS : S.IsHermitian := (CFC.sqrt_nonneg R).posSemidef.isHermitian
  have hgram : M*Mᴴ = S*S := by rw [hM]; exact (CFC.sqrt_mul_sqrt_self R hR.1.nonneg).symm
  obtain ⟨U,hU⟩ := padded_purification_unitary M S hS hgram
  let V : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ := U
  let L := (compressReference (κ := κ) R).comp ((refSandwich Vᴴ).comp embedReference)
  refine ⟨L,?_,?_,?_⟩
  · intro Z hZ
    exact compressReference_pos R hR.1 ((embedReference_pos hZ).mul_mul_conjTranspose_same Vᴴ)
  · intro Z
    change trace (compressReference R (Vᴴ * embedReference Z * Vᴴᴴ)) = _
    rw [compressReference_trace R hR.2,Matrix.conjTranspose_conjTranspose,
      Matrix.trace_mul_cycle,show V*Vᴴ = 1 from U.prop.2,one_mul,embedReference_trace]
  · intro X
    change compressReference R (Vᴴ * embedReference (Mᴴ*X*M) * Vᴴᴴ) = _
    rw [padded_purification_blocks M S hS U hU X,Matrix.conjTranspose_conjTranspose]
    have hv : Vᴴ * (V * fromBlocks 0 0 0 (S*X*S) * Vᴴ) * V =
        fromBlocks 0 0 0 (S*X*S) := by
      rw [mul_assoc V _ _,← mul_assoc Vᴴ V _,show Vᴴ*V=1 from U.prop.1,one_mul,
        mul_assoc,show Vᴴ*V=1 from U.prop.1,mul_one]
    change compressReference R (Vᴴ*(V*fromBlocks 0 0 0 (S*X*S)*Vᴴ)*V) = _
    rw [hv,compressReference_right]

end

section

open Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v10053_0 v10053_1

theorem purification_recovery_transpose {ι : Type v10053_0} {κ : Type v10053_1}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (R : Matrix ι ι ℂ) (hR : Density R)
    (M : Matrix ι κ ℂ) (hM : M * Mᴴ = R) :
    ∃ L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ,
      (∀ Z, Z.PosSemidef → (L Z).PosSemidef) ∧
      (∀ Z, trace (L Z) = trace Z) ∧
      ∀ X, L ((Mᴴ * X * M)ᵀ) = (CFC.sqrt R * X * CFC.sqrt R)ᵀ := by
  obtain ⟨L,hpos,htr,hrec⟩ := purification_recovery R hR M hM
  let J : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun Z := (L Zᵀ)ᵀ
      map_add' Z W := by simp only [Matrix.transpose_add,map_add]
      map_smul' c Z := by simp only [Matrix.transpose_smul,map_smul,RingHom.id_apply] }
  refine ⟨J,?_,?_,?_⟩
  · intro Z hZ
    exact (hpos Zᵀ hZ.transpose).transpose
  · intro Z
    change trace (L Zᵀ)ᵀ = trace Z
    rw [Matrix.trace_transpose,htr,Matrix.trace_transpose]
  · intro X
    change (L ((Mᴴ*X*M)ᵀ)ᵀ)ᵀ = _
    rw [Matrix.transpose_transpose,hrec]

end

section

open Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

universe v10089_0 v10089_1

variable {ι : Type v10089_0} {κ : Type v10089_1} [inst10089_0 : Fintype ι] [inst10089_1 : Fintype κ] [inst10089_2 : DecidableEq ι] [inst10089_3 : DecidableEq κ]

def purificationFilter (P : Matrix ι κ ℂ) : Matrix κ ι ℂ :=
  (Real.sqrt (Fintype.card ι : ℝ) : ℂ) • Pᵀ

open MeasureTheory

/-- Matrix-valued output entries after purification and publication of the transcript. -/
def publicPurifiedEntries {Ω T K : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (record : Ω → T) (W : K → K → Ω → Matrix ι ι ℂ)
    (P : Matrix ι κ ℂ) (a b : K) (x y : κ) : ComplexMeasure T :=
  ∑ i, ∑ j, (purificationFilter P x i * star (purificationFilter P y j)) •
    (μ.withDensityᵥ (fun ω => W a b ω i j)).map record

/-- The positive representative of the entrywise Radon–Nikodym derivative. -/
def positiveEntryDensity {Ω : Type*} [MeasurableSpace Ω]
    (W : ι → ι → ComplexMeasure Ω) (μ : Measure Ω) (t : Ω) : Matrix ι ι ℂ := by
  classical
  let D : Matrix ι ι ℂ := fun i j => (W i j).rnDeriv μ t
  exact if D.PosSemidef then D else 0

omit inst10089_1 inst10089_2 inst10089_3 in
lemma purificationFilter_block [Fintype κ] [DecidableEq ι] [DecidableEq κ] (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) :
    purificationFilter P * U * (purificationFilter P)ᴴ =
      (Pᴴ * ((Fintype.card ι : ℂ) • Uᵀ) * P)ᵀ := by
  have hc : (Real.sqrt (Fintype.card ι : ℝ) : ℂ) *
      (Real.sqrt (Fintype.card ι : ℝ) : ℂ) = (Fintype.card ι : ℂ) := by
    rw [← Complex.ofReal_mul,Real.mul_self_sqrt (Nat.cast_nonneg _)]
    norm_cast
  simp only [purificationFilter,Matrix.conjTranspose_smul,Complex.star_def,
    Complex.conj_ofReal,Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.transpose_mul,Matrix.transpose_smul,Matrix.transpose_transpose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]
  rw [hc,Matrix.mul_assoc]

lemma preparationFilter_eq_purificationFilter (R : Matrix ι ι ℂ) :
    preparationFilter R = purificationFilter (CFC.sqrt R) := rfl

theorem purification_filter_recovery (R : Matrix ι ι ℂ) (hR : Density R)
    (P : Matrix ι κ ℂ) (hP : P * Pᴴ = R) :
    ∃ L : Matrix κ κ ℂ →ₗ[ℂ] Matrix ι ι ℂ,
      (∀ Z, Z.PosSemidef → (L Z).PosSemidef) ∧
      (∀ Z, trace (L Z) = trace Z) ∧
      ∀ U, L (purificationFilter P * U * (purificationFilter P)ᴴ) =
        preparationFilter R * U * (preparationFilter R)ᴴ := by
  obtain ⟨L,hpos,htr,he⟩ := purification_recovery_transpose R hR P hP
  refine ⟨L,hpos,htr,?_⟩
  intro U
  rw [purificationFilter_block,he,preparationFilter_eq_purificationFilter,
    purificationFilter_block,(CFC.sqrt_nonneg R).posSemidef.isHermitian.eq]

end

open Matrix MeasureTheory ProbabilityTheory Function Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v10227_0 v10227_1 v10227_2 v10227_3 v10227_4 v10227_5 v10227_6 v10227_7 v10227_8 v10227_9 v10227_10

variable {O : Type v10227_0} {M : Type v10227_1} {ι : Type v10227_2} {η : Type v10227_3} [inst10227_0 : MeasurableSpace O] [inst10227_1 : MeasurableSpace M]
  [inst10227_2 : StandardBorelSpace O] [inst10227_3 : Nonempty O] [inst10227_4 : StandardBorelSpace M] [inst10227_5 : Nonempty M]
  [inst10227_6 : Fintype ι] [inst10227_7 : Fintype η] [inst10227_8 : DecidableEq ι] [inst10227_9 : DecidableEq η]
  [inst10227_10 : Nonempty ι] [inst10227_11 : Nonempty η]
  {d : Discussion O M} {A : ℕ → Type v10227_4} {B : ℕ → Type v10227_5}
  [inst10227_12 : ∀ n, AddCommGroup (A n)] [inst10227_13 : ∀ n, Module ℂ (A n)] [inst10227_14 : ∀ n, One (A n)] [inst10227_15 : ∀ n, LE (A n)]
  [inst10227_16 : ∀ n, AddCommGroup (B n)] [inst10227_17 : ∀ n, Module ℂ (B n)] [inst10227_18 : ∀ n, One (B n)] [inst10227_19 : ∀ n, LE (B n)]
  {TA : Type v10227_6} {TB : Type v10227_7} {CA : Type v10227_8} {CB : Type v10227_9}
  [inst10227_20 : AddCommGroup TA] [inst10227_21 : Module ℂ TA] [inst10227_22 : One TA] [inst10227_23 : LE TA]
  [inst10227_24 : AddCommGroup TB] [inst10227_25 : Module ℂ TB] [inst10227_26 : One TB] [inst10227_27 : LE TB]
  [inst10227_28 : AddCommGroup CA] [inst10227_29 : Module ℂ CA] [inst10227_30 : One CA] [inst10227_31 : LE CA]
  [inst10227_32 : AddCommGroup CB] [inst10227_33 : Module ℂ CB] [inst10227_34 : One CB] [inst10227_35 : LE CB]
  {κ : Type v10227_10} [inst10227_36 : Fintype κ] [inst10227_37 : DecidableEq κ]

namespace BitProtocol

variable (p : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB)
  (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
  (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R)

def purifiedOutput (i j : Bool) : PositiveMatrixMeasure (ℕ → M) κ :=
  (p.probeOutput i j).filter (purificationFilter P)

omit inst10227_10 inst10227_11 inst10227_37 in
lemma purifiedOutput_ac [Nonempty ι] [Nonempty η] [DecidableEq κ] (i j : Bool) (S : Set (ℕ → M)) (hS : MeasurableSet S)
    (hnull : d.transcriptLaw S = 0) : (p.purifiedOutput P i j).value S = 0 := by
  obtain ⟨X,Y,hXm,hYm,hX,hY,he,hn⟩ := p.public_factors
  rw [purifiedOutput,PositiveMatrixMeasure.filter_value,he i j S hS,
    Measure.restrict_eq_zero.mpr hnull,integral_zero_measure,Matrix.mul_zero,Matrix.zero_mul]

include hR hP

omit inst10227_10 inst10227_11 in
lemma purifiedOutput_recovery [Nonempty ι] [Nonempty η] :
    ∃ L : Matrix κ κ ℂ →ₗ[ℂ] Matrix (ι × η) (ι × η) ℂ,
      (∀ Z, Z.PosSemidef → (L Z).PosSemidef) ∧
      (∀ Z, trace (L Z) = trace Z) ∧
      ∀ i j S, L ((p.purifiedOutput P i j).value S) = (p.canonicalOutput R i j).value S := by
  obtain ⟨L,hpos,htr,he⟩ := purification_filter_recovery R hR P hP
  refine ⟨L,hpos,htr,?_⟩
  intro i j S
  simpa only [purifiedOutput,canonicalOutput,PositiveMatrixMeasure.filter_value] using
    he ((p.probeOutput i j).value S)

lemma purifiedOutput_normalized :
    (trace ((p.purifiedOutput P false false).value Set.univ)).re +
    (trace ((p.purifiedOutput P false true).value Set.univ)).re +
    (trace ((p.purifiedOutput P true false).value Set.univ)).re +
    (trace ((p.purifiedOutput P true true).value Set.univ)).re = 1 := by
  obtain ⟨L,hpos,htr,he⟩ := p.purifiedOutput_recovery R hR P hP
  have hh i j : trace ((p.purifiedOutput P i j).value Set.univ) =
      trace ((p.canonicalOutput R i j).value Set.univ) := by rw [← he,htr]
  simp_rw [hh]
  exact p.canonicalOutput_normalized R hR

def purifiedDensity (ν : Measure (ℕ → M)) [SigmaFinite ν]
    (hμν : d.transcriptLaw ≪ ν) : BitDensity ν κ :=
  PositiveMatrixMeasure.toBitDensity (p.purifiedOutput P) ν
    (fun i j S hS hz => p.purifiedOutput_ac P i j S hS (hμν hz))
    (p.purifiedOutput_normalized R hR P hP)

/-- The operational bit error written directly in terms of the output entries. -/
def rawPurifiedSecretBitError (P : Matrix (ι × η) κ ℂ)
    (sigma : PositiveMatrixMeasure (ℕ → M) κ) : ℝ :=
  let ν := d.transcriptLaw + sigma.traceMeasure
  let τ := fun i j => positiveEntryDensity
    (publicPurifiedEntries d.probeLaw d.sampler.publicRecord p.completeReference P i j) ν
  let σ := sigma.positiveDensity ν
  (∫ t, (trace (τ false true t)).re ∂ν) +
    (∫ t, (trace (τ true false t)).re ∂ν) +
    (∫ t, traceNorm (τ false false t - (1 / ((2 : ℕ) : ℝ)) • σ t) ∂ν) +
    (∫ t, traceNorm (τ true true t - (1 / ((2 : ℕ) : ℝ)) • σ t) ∂ν)

def purifiedSecretBitError (sigma : PositiveMatrixMeasure (ℕ → M) κ) : ℝ :=
  (p.purifiedDensity R hR P hP (d.transcriptLaw + sigma.traceMeasure)
    (Measure.AbsolutelyContinuous.rfl.add_right _)).idealBitError
      (sigma.positiveDensity (d.transcriptLaw + sigma.traceMeasure))

lemma rawPurifiedSecretBitError_eq (sigma : PositiveMatrixMeasure (ℕ → M) κ) :
    p.rawPurifiedSecretBitError P sigma = p.purifiedSecretBitError R hR P hP sigma := rfl

end BitProtocol

end ZeroKey

namespace UnrestrictedQuantum

open Matrix MeasureTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

section

universe v10363_0 v10363_1 v10363_2 v10363_3

variable {A : Type v10363_0} {B : Type v10363_1} {O : Type v10363_2} {ι : Type v10363_3} [inst10363_0 : AddCommGroup A] [inst10363_1 : Module ℂ A] [inst10363_2 : One A] [inst10363_3 : LE A]
  [inst10363_4 : AddCommGroup B] [inst10363_5 : Module ℂ B] [inst10363_6 : One B] [inst10363_7 : LE B]
  [inst10363_8 : MeasurableSpace O] [inst10363_9 : Nonempty O] [inst10363_10 : Fintype ι] [inst10363_11 : DecidableEq ι]

namespace ObservableInstrument

def postprocess (J : ObservableInstrument O A B) (f : O → Bool) (hf : Measurable f) :
    ObservableInstrument Bool A B where
  operation E := J.operation (f ⁻¹' E)
  positive E hE x hx := J.positive _ (hf hE) x hx
  total_unit := by simpa only [Set.preimage_univ] using J.total_unit

end ObservableInstrument

namespace InstrumentRun

variable {J : ObservableInstrument O A B} {S : ReferenceFunctional A ι}
  (r : InstrumentRun J S)

omit inst10363_9 inst10363_11 in
lemma event_trace [Nonempty O] [DecidableEq ι] (E : Set O) (hE : MeasurableSet E) :
    trace (S (J.operation E 1)) = (r.law.real E : ℂ) := by
  calc
    _ = ∫ o in E, trace (r.posterior o 1) ∂r.law := by
      simp only [trace,diag]
      rw [integral_finsetSum _ (fun i _ => (r.integrable 1 i i).integrableOn)]
      apply Finset.sum_congr rfl
      intro i _
      exact (r.update E hE 1 i i).symm
    _ = _ := by simp [r.posterior_trace,integral_const,Complex.real_smul,Measure.real]

omit inst10363_9 inst10363_11 in
lemma event_zero [Nonempty O] [DecidableEq ι] (E : Set O) (hE : MeasurableSet E) (hz : r.law E = 0) (x : B) :
    S (J.operation E x) = 0 := by
  ext i j
  rw [← r.update E hE x i j,Measure.restrict_eq_zero.mpr hz,integral_zero_measure]
  rfl

variable (f : O → Bool) (hf : Measurable f)

def coarseMass (i : Bool) : ℝ := r.law.real (f ⁻¹' {i})

def coarsePosterior (i : Bool) : ReferenceFunctional B ι :=
  if r.coarseMass f i = 0 then r.posterior (Classical.choice ‹Nonempty O›)
  else ((r.coarseMass f i)⁻¹ : ℝ) • (S.comp (J.operation (f ⁻¹' {i})))

include hf

omit inst10363_11 in
lemma coarsePosterior_positive [DecidableEq ι] (hS : PositiveFunctional S) (i : Bool) :
    PositiveFunctional (r.coarsePosterior f i) := by
  unfold coarsePosterior
  split
  · exact r.posterior_positive _
  · intro x hx
    exact (hS _ (J.positive _ (hf (measurableSet_singleton i)) x hx)).smul
      (inv_nonneg.mpr (ENNReal.toReal_nonneg))

lemma coarsePosterior_trace (_hS : PositiveFunctional S) (i : Bool) :
    trace (r.coarsePosterior f i 1) = 1 := by
  unfold coarsePosterior
  split
  · exact r.posterior_trace _
  · rename_i hn
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,Matrix.trace_smul]
    rw [r.event_trace _ (hf (measurableSet_singleton i))]
    change ((r.coarseMass f i)⁻¹ : ℝ) • ((r.coarseMass f i : ℝ) : ℂ) = 1
    simp only [Complex.real_smul,Complex.ofReal_inv,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hn)]

lemma coarsePosterior_weighted (i : Bool) (x : B) :
    r.coarseMass f i • r.coarsePosterior f i x = S (J.operation (f ⁻¹' {i}) x) := by
  let : IsProbabilityMeasure r.law := r.probability
  unfold coarsePosterior
  split
  · rename_i hz
    rw [hz,zero_smul]
    symm
    apply r.event_zero _ (hf (measurableSet_singleton i))
    exact (ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right (measure_ne_top _ _)
  · rename_i hn
    simp only [LinearMap.smul_apply,LinearMap.comp_apply,smul_smul,mul_inv_cancel₀ hn,one_smul]

lemma coarsePosterior_singleton (i : Bool) (x : B) (k l : ι) :
    (∫ b in {i}, r.coarsePosterior f b x k l ∂(r.law.map f)) =
      S (J.operation (f ⁻¹' {i}) x) k l := by
  rw [integral_singleton]
  have hm : (r.law.map f).real {i} = r.coarseMass f i := by
    rw [Measure.real,Measure.map_apply hf (measurableSet_singleton i)]
    rfl
  rw [hm]
  exact congrArg (fun U : Matrix ι ι ℂ => U k l) (r.coarsePosterior_weighted f hf i x)

lemma coarsePosterior_integral (E : Set Bool) (x : B) (k l : ι) :
    (∫ b in E, r.coarsePosterior f b x k l ∂(r.law.map f)) =
      S (J.operation (f ⁻¹' E) x) k l := by
  let : IsProbabilityMeasure r.law := r.probability
  let : IsProbabilityMeasure (r.law.map f) := inferInstance
  have hpart : E = ∅ ∨ E = {false} ∨ E = {true} ∨ E = Set.univ := by
    by_cases h0 : false ∈ E <;> by_cases h1 : true ∈ E
    · right; right; right; ext b; cases b <;> simp_all
    · right; left; ext b; cases b <;> simp_all
    · right; right; left; ext b; cases b <;> simp_all
    · left; ext b; cases b <;> simp_all
  rcases hpart with rfl | rfl | rfl | rfl
  · simp only [setIntegral_empty,Set.preimage_empty]
    exact (congrArg (fun U : Matrix ι ι ℂ => U k l)
      (r.event_zero ∅ MeasurableSet.empty (measure_empty) x)).symm
  · exact r.coarsePosterior_singleton f hf false x k l
  · exact r.coarsePosterior_singleton f hf true x k l
  · have hd : Disjoint (f ⁻¹' {false}) (f ⁻¹' {true}) := by
      apply Set.disjoint_left.mpr
      intro o h0 h1
      simp only [Set.mem_preimage,Set.mem_singleton_iff] at h0 h1
      rw [h0] at h1
      contradiction
    have hu : (f ⁻¹' {false}) ∪ (f ⁻¹' {true}) = Set.univ := by
      ext o; cases f o <;> simp
    have hb : ({false} : Set Bool) ∪ {true} = Set.univ := by ext b; cases b <;> simp
    rw [← hb,setIntegral_union (by simp) (measurableSet_singleton true)
      Integrable.of_finite.integrableOn Integrable.of_finite.integrableOn,
      r.coarsePosterior_singleton f hf false x k l,
      r.coarsePosterior_singleton f hf true x k l]
    rw [← r.update _ (hf (measurableSet_singleton false)) x k l,
      ← r.update _ (hf (measurableSet_singleton true)) x k l]
    rw [← setIntegral_union hd (hf (measurableSet_singleton true))
      (r.integrable x k l).integrableOn (r.integrable x k l).integrableOn,hu]
    simpa only [Set.preimage_union,Set.preimage_univ,hu] using
      r.update Set.univ MeasurableSet.univ x k l

def postprocess (hS : PositiveFunctional S) :
    InstrumentRun (J.postprocess f hf) S where
  law := r.law.map f
  probability := by
    let : IsProbabilityMeasure r.law := r.probability
    exact inferInstance
  posterior := r.coarsePosterior f
  posterior_positive := r.coarsePosterior_positive f hf hS
  posterior_trace := r.coarsePosterior_trace f hf hS
  integrable x k l := by
    let : IsProbabilityMeasure r.law := r.probability
    let : IsProbabilityMeasure (r.law.map f) := inferInstance
    exact Integrable.of_finite
  update E hE x k l := r.coarsePosterior_integral f hf E x k l

end InstrumentRun

end

universe v10518_0 v10518_1 v10518_2 v10518_3 v10518_4

variable {A : Type v10518_0} {B : Type v10518_1} {K : Type v10518_2} {ι : Type v10518_3} {Ω : Type v10518_4} [inst10518_0 : AddCommGroup A] [inst10518_1 : Module ℂ A] [inst10518_2 : One A] [inst10518_3 : LE A]
  [inst10518_4 : AddCommGroup B] [inst10518_5 : Module ℂ B] [inst10518_6 : One B] [inst10518_7 : LE B]
  [inst10518_8 : MeasurableSpace K] [inst10518_9 : MeasurableSingletonClass K] [inst10518_10 : Fintype K] [inst10518_11 : DecidableEq K] [inst10518_12 : Nonempty K]
  [inst10518_13 : Fintype ι] [inst10518_14 : DecidableEq ι]

omit inst10518_10 inst10518_11 inst10518_12 inst10518_14 in
lemma InstrumentRun.event_finset [Fintype K] [DecidableEq K] [Nonempty K] [DecidableEq ι] {J : ObservableInstrument K A B}
    {S : ReferenceFunctional A ι} (r : InstrumentRun J S) (s : Finset K) (x : B) :
    S (J.operation s x) = ∑ k ∈ s, S (J.operation {k} x) := by
  ext i j
  simp only [Matrix.sum_apply]
  rw [← r.update s (s.finite_toSet.measurableSet) x i j,
    setIntegral_finset s (r.integrable x i j).integrableOn]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← r.update {k} (measurableSet_singleton k) x i j,integral_singleton]

lemma InstrumentRun.event_total {J : ObservableInstrument K A B}
    {S : ReferenceFunctional A ι} (r : InstrumentRun J S) :
    (∑ k, S (J.operation {k} 1)) = S 1 := by
  simpa only [Finset.coe_univ,J.total_unit] using (r.event_finset Finset.univ 1).symm

variable {L : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} {F : Filtration ℕ mΩ} {U : ℕ → Ω → Matrix ι ι ℂ}
  (e : IncomingObservableProcess (L := L) (A := A) μ F U)

namespace IncomingObservableProcess

structure FiniteReadout where
  instrument : Ω → ObservableInstrument K A B
  run : ∀ x, InstrumentRun (instrument x) (e.state x)
  positive_unit : (0 : B) ≤ 1
  local_measurable : ∀ k, Measurable[L] (fun x => e.state x ((instrument x).operation {k} 1))

namespace FiniteReadout

variable {e} (b : e.FiniteReadout (B := B) (K := K))

def value (k : K) (x : Ω) : Matrix ι ι ℂ := e.state x ((b.instrument x).operation {k} 1)

omit inst10518_9 inst10518_10 inst10518_11 inst10518_12 in
lemma measurable [MeasurableSingletonClass K] [Fintype K] [DecidableEq K] [Nonempty K] (k : K) : Measurable[L] (b.value k) := b.local_measurable k

omit inst10518_10 inst10518_11 inst10518_12 in
lemma positive [Fintype K] [DecidableEq K] [Nonempty K] (k : K) (x : Ω) : (b.value k x).PosSemidef :=
  e.positive x _ ((b.instrument x).positive {k} (measurableSet_singleton k) 1 b.positive_unit)

lemma sum (x : Ω) : (∑ k, b.value k x) = e.state x 1 := (b.run x).event_total

lemma subdensity (k : K) (x : Ω) : ZeroKey.Subdensity (b.value k x) := by
  refine ⟨b.positive k x,?_⟩
  have hsum := congrArg (fun M : Matrix ι ι ℂ => (trace M).re) (b.sum x)
  simp only [Matrix.trace_sum,Complex.re_sum,e.normalized x,Complex.one_re] at hsum
  rw [← hsum]
  exact Finset.single_le_sum (fun l _ => (RCLike.nonneg_iff.mp (b.positive l x).trace_nonneg).1)
    (Finset.mem_univ k)

lemma event_finset (s : Finset K) (x : Ω) :
    e.state x ((b.instrument x).operation s 1) = ∑ k ∈ s, b.value k x :=
  (b.run x).event_finset s 1

lemma eventMeasurable (s : Finset K) :
    Measurable[L] (fun x => e.state x ((b.instrument x).operation s 1)) := by
  simp_rw [b.event_finset s]
  exact Finset.measurable_sum s (fun k _ => b.local_measurable k)

def postprocess (f : K → Bool) : e.BitReadout (B := B) where
  instrument x := (b.instrument x).postprocess f (measurable_of_finite f)
  run x := (b.run x).postprocess f (measurable_of_finite f) (e.positive x)
  positive_unit := b.positive_unit
  local_measurable i := by
    let s := Finset.univ.filter (fun k => f k = i)
    have hs : (s : Set K) = f ⁻¹' {i} := by ext k; simp [s]
    change Measurable[L] (fun x => e.state x ((b.instrument x).operation (f ⁻¹' {i}) 1))
    rw [← hs]
    exact b.eventMeasurable s

end FiniteReadout

end IncomingObservableProcess

end UnrestrictedQuantum

namespace ZeroKey

section

open Matrix MeasureTheory ProbabilityTheory Function unitInterval Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

section

open UnrestrictedQuantum

universe v10619_0 v10619_1 v10619_2 v10619_3 v10619_4 v10619_5 v10619_6 v10619_7 v10619_8 v10619_9 v10619_10

variable {O : Type v10619_0} {M : Type v10619_1} {ι : Type v10619_2} {η : Type v10619_3} [inst10619_0 : MeasurableSpace O] [inst10619_1 : MeasurableSpace M]
  [inst10619_2 : StandardBorelSpace O] [inst10619_3 : Nonempty O] [inst10619_4 : StandardBorelSpace M] [inst10619_5 : Nonempty M]
  [inst10619_6 : Fintype ι] [inst10619_7 : Fintype η] [inst10619_8 : DecidableEq ι] [inst10619_9 : DecidableEq η]
  {K : Type v10619_4} [inst10619_10 : MeasurableSpace K] [inst10619_11 : MeasurableSingletonClass K]
  [inst10619_12 : Fintype K] [inst10619_13 : DecidableEq K] [inst10619_14 : Nonempty K]
  (d : Discussion O M)
  (A : ℕ → Type v10619_5) (B : ℕ → Type v10619_6)
  [inst10619_15 : ∀ n, AddCommGroup (A n)] [inst10619_16 : ∀ n, Module ℂ (A n)] [inst10619_17 : ∀ n, One (A n)] [inst10619_18 : ∀ n, LE (A n)]
  [inst10619_19 : ∀ n, AddCommGroup (B n)] [inst10619_20 : ∀ n, Module ℂ (B n)] [inst10619_21 : ∀ n, One (B n)] [inst10619_22 : ∀ n, LE (B n)]
  (TA : Type v10619_7) (TB : Type v10619_8) (CA : Type v10619_9) (CB : Type v10619_10)
  [inst10619_23 : AddCommGroup TA] [inst10619_24 : Module ℂ TA] [inst10619_25 : One TA] [inst10619_26 : LE TA]
  [inst10619_27 : AddCommGroup TB] [inst10619_28 : Module ℂ TB] [inst10619_29 : One TB] [inst10619_30 : LE TB]
  [inst10619_31 : AddCommGroup CA] [inst10619_32 : Module ℂ CA] [inst10619_33 : One CA] [inst10619_34 : LE CA]
  [inst10619_35 : AddCommGroup CB] [inst10619_36 : Module ℂ CB] [inst10619_37 : One CB] [inst10619_38 : LE CB]

structure FiniteProtocol where
  executionA : LocalObservableExecution (ι := ι) A d.kernelA d.sendA
  executionB : LocalObservableExecution (ι := η) B d.kernelB d.sendB
  initialA : executionA.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := ι)) localProbe)
  initialB : executionB.reference 0 (Fin.elim0,Fin.elim0) =
    keepReference (outer (localProbe (ι := η)) localProbe)
  incomingA : IncomingObservableProcess (L := d.sampler.localField true) (A := TA)
    d.probeLaw historyFiltration
    (fun n x => AdaptiveQuantum.globalLocalReferenceA d.sampler d.kernelA executionA n (historyPrefix n x))
  incomingB : IncomingObservableProcess (L := d.sampler.localField false) (A := TB)
    d.probeLaw historyFiltration
    (fun n x => AdaptiveQuantum.globalLocalReferenceB d.sampler d.kernelB executionB n (historyPrefix n x))
  readoutA : incomingA.FiniteReadout (B := CA) (K := K)
  readoutB : incomingB.FiniteReadout (B := CB) (K := K)

variable {d A B TA TB CA CB}

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

def toBit (f : K → Bool) : BitProtocol (ι := ι) (η := η) d A B TA TB CA CB where
  executionA := p.executionA
  executionB := p.executionB
  initialA := p.initialA
  initialB := p.initialB
  incomingA := p.incomingA
  incomingB := p.incomingB
  readoutA := p.readoutA.postprocess f
  readoutB := p.readoutB.postprocess f

def completeReference (i j : K) (x : ℕ → O) : Matrix (ι × η) (ι × η) ℂ :=
  p.readoutA.value i x ⊗ₖ p.readoutB.value j x

omit inst10619_4 inst10619_5 in
lemma completeReference_positive [StandardBorelSpace M] [Nonempty M] (i j : K) (x : ℕ → O) :
    (p.completeReference i j x).PosSemidef :=
  (p.readoutA.positive i x).kronecker (p.readoutB.positive j x)

omit inst10619_4 inst10619_5 in
lemma completeReference_measurable [StandardBorelSpace M] [Nonempty M] (i j : K) : Measurable (p.completeReference i j) :=
  measurable_matrix_kronecker
    ((p.readoutA.measurable i).mono (d.sampler.localField_le true) le_rfl)
    ((p.readoutB.measurable j).mono (d.sampler.localField_le false) le_rfl)

lemma completeReference_integrable (i j : K) : Integrable (p.completeReference i j) d.probeLaw :=
  integrable_subdensity _
    (fun x => subdensity_kronecker (p.readoutA.subdensity i x) (p.readoutB.subdensity j x))
    (p.completeReference_measurable i j) d.probeLaw

lemma completeReference_entry_integrable (i j : K) (k l : ι × η) :
    Integrable (fun x => p.completeReference i j x k l) d.probeLaw :=
  ((Matrix.entryLinearMap ℂ ℂ k l).toContinuousLinearMap).integrable_comp
    (p.completeReference_integrable i j)

def probeOutput (i j : K) : PositiveMatrixMeasure (ℕ → M) (ι × η) :=
  (positiveMatrixMeasureOfDensity (p.completeReference_entry_integrable i j)
    (Eventually.of_forall (p.completeReference_positive i j))).pushforward
    d.sampler.publicRecord d.sampler.measurable_publicRecord

lemma probeOutput_event (i j : K) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.probeOutput i j).value S =
      ∫ x in d.sampler.publicRecord ⁻¹' S, p.completeReference i j x ∂d.probeLaw := by
  rw [probeOutput,PositiveMatrixMeasure.pushforward_value _ _ _ S hS,
    positiveMatrixMeasureOfDensity_value _ _ _ (d.sampler.measurable_publicRecord hS)]

def canonicalOutput (R : Matrix (ι × η) (ι × η) ℂ) (i j : K) :
    PositiveMatrixMeasure (ℕ → M) (ι × η) :=
  (p.probeOutput i j).filter (preparationFilter R)

lemma canonicalOutput_event (R : Matrix (ι × η) (ι × η) ℂ)
    (i j : K) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.canonicalOutput R i j).value S =
      ∫ x in d.sampler.publicRecord ⁻¹' S,
        preparationFilter R * p.completeReference i j x * (preparationFilter R)ᴴ ∂d.probeLaw := by
  rw [canonicalOutput,PositiveMatrixMeasure.filter_value,p.probeOutput_event i j S hS,
    integral_filter _ (p.completeReference_integrable i j).integrableOn]

end FiniteProtocol

end

open UnrestrictedQuantum

universe v10926_0 v10926_1 v10926_2 v10926_3 v10926_4 v10926_5 v10926_6 v10926_7 v10926_8 v10926_9 v10926_10

variable {O : Type v10926_0} {M : Type v10926_1} {ι : Type v10926_2} {η : Type v10926_3} [inst10926_0 : MeasurableSpace O] [inst10926_1 : MeasurableSpace M]
  [inst10926_2 : StandardBorelSpace O] [inst10926_3 : Nonempty O] [inst10926_4 : StandardBorelSpace M] [inst10926_5 : Nonempty M]
  [inst10926_6 : Fintype ι] [inst10926_7 : Fintype η] [inst10926_8 : DecidableEq ι] [inst10926_9 : DecidableEq η]
  {K : Type v10926_4} [inst10926_10 : MeasurableSpace K] [inst10926_11 : MeasurableSingletonClass K]
  [inst10926_12 : Fintype K] [inst10926_13 : DecidableEq K] [inst10926_14 : Nonempty K]
  [inst10926_15 : Nonempty ι] [inst10926_16 : Nonempty η]
  (d : Discussion O M)
  (A : ℕ → Type v10926_5) (B : ℕ → Type v10926_6)
  [inst10926_17 : ∀ n, AddCommGroup (A n)] [inst10926_18 : ∀ n, Module ℂ (A n)] [inst10926_19 : ∀ n, One (A n)] [inst10926_20 : ∀ n, LE (A n)]
  [inst10926_21 : ∀ n, AddCommGroup (B n)] [inst10926_22 : ∀ n, Module ℂ (B n)] [inst10926_23 : ∀ n, One (B n)] [inst10926_24 : ∀ n, LE (B n)]
  (TA : Type v10926_7) (TB : Type v10926_8) (CA : Type v10926_9) (CB : Type v10926_10)
  [inst10926_25 : AddCommGroup TA] [inst10926_26 : Module ℂ TA] [inst10926_27 : One TA] [inst10926_28 : LE TA]
  [inst10926_29 : AddCommGroup TB] [inst10926_30 : Module ℂ TB] [inst10926_31 : One TB] [inst10926_32 : LE TB]
  [inst10926_33 : AddCommGroup CA] [inst10926_34 : Module ℂ CA] [inst10926_35 : One CA] [inst10926_36 : LE CA]
  [inst10926_37 : AddCommGroup CB] [inst10926_38 : Module ℂ CB] [inst10926_39 : One CB] [inst10926_40 : LE CB]

variable {d A B TA TB CA CB}

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

omit inst10926_4 inst10926_5 inst10926_15 inst10926_16 in
lemma completeReference_sum [StandardBorelSpace M] [Nonempty M] [Nonempty ι] [Nonempty η] (x : ℕ → O) :
    (∑ i, ∑ j, p.completeReference i j x) =
      p.incomingA.state x 1 ⊗ₖ p.incomingB.state x 1 := by
  rw [← p.readoutA.sum x,← p.readoutB.sum x]
  ext a b
  simp only [completeReference,Matrix.sum_apply,Matrix.kroneckerMap_apply,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

lemma completeReference_total :
    (∑ i, ∑ j, ∫ x, p.completeReference i j x ∂d.probeLaw) =
      keepReference (outer (localProbe (ι := ι × η)) localProbe) := by

  simp_rw [← integral_finsetSum _ (fun j _ => p.completeReference_integrable _ j)]
  rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => p.completeReference_integrable i j))]
  simp_rw [p.completeReference_sum]
  have hc := AdaptiveQuantum.incoming_joint_reference_consistency
    d.sampler d.kernelA d.kernelB p.executionA p.executionB d.probeLaw d.probeLaw_prefix
    p.incomingA p.incomingB 0 Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hc
  rw [hc]
  have hpre (x : ℕ → O) : historyPrefix 0 x = Fin.elim0 := Subsingleton.elim _ _
  simp_rw [hpre]
  have hi := (p.toBit (fun _ => false)).initial_joint_reference
  change AdaptiveQuantum.jointReference d.sampler d.kernelA d.kernelB p.executionA p.executionB
    0 Fin.elim0 = _ at hi
  simp [hi]

lemma canonicalOutput_sum (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R) :
    (∑ i, ∑ j, (p.canonicalOutput R i j).value Set.univ) = Rᵀ := by
  simp_rw [p.canonicalOutput_event R _ _ Set.univ MeasurableSet.univ,
    Set.preimage_univ,Measure.restrict_univ]
  simp_rw [integral_filter _ (p.completeReference_integrable _ _)]
  simp only [← Matrix.sum_mul,← Matrix.mul_sum]
  rw [p.completeReference_total,← keepReference_filter,preparation_filter_identity,
    canonical_reference R hR.1]

lemma canonicalOutput_normalized (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R) :
    (∑ i, ∑ j, (trace ((p.canonicalOutput R i j).value Set.univ)).re) = 1 := by
  have h := congrArg (fun X : Matrix (ι × η) (ι × η) ℂ => (trace X).re)
    (p.canonicalOutput_sum R hR)
  simpa only [Matrix.trace_sum,Complex.re_sum,Matrix.trace_transpose,hR.2,Complex.one_re] using h

end FiniteProtocol

end

section

open Matrix MeasureTheory ProbabilityTheory Function Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

open UnrestrictedQuantum

universe v11008_0 v11008_1 v11008_2 v11008_3 v11008_4 v11008_5 v11008_6 v11008_7 v11008_8 v11008_9 v11008_10 v11008_11

variable {O : Type v11008_0} {M : Type v11008_1} {ι : Type v11008_2} {η : Type v11008_3} [inst11008_0 : MeasurableSpace O] [inst11008_1 : MeasurableSpace M]
  [inst11008_2 : StandardBorelSpace O] [inst11008_3 : Nonempty O] [inst11008_4 : StandardBorelSpace M] [inst11008_5 : Nonempty M]
  [inst11008_6 : Fintype ι] [inst11008_7 : Fintype η] [inst11008_8 : DecidableEq ι] [inst11008_9 : DecidableEq η] [inst11008_10 : Nonempty ι] [inst11008_11 : Nonempty η]
  {K : Type v11008_4} [inst11008_12 : MeasurableSpace K] [inst11008_13 : MeasurableSingletonClass K]
  [inst11008_14 : Fintype K] [inst11008_15 : DecidableEq K] [inst11008_16 : Nonempty K]
  {d : Discussion O M} {A : ℕ → Type v11008_5} {B : ℕ → Type v11008_6}
  [inst11008_17 : ∀ n, AddCommGroup (A n)] [inst11008_18 : ∀ n, Module ℂ (A n)] [inst11008_19 : ∀ n, One (A n)] [inst11008_20 : ∀ n, LE (A n)]
  [inst11008_21 : ∀ n, AddCommGroup (B n)] [inst11008_22 : ∀ n, Module ℂ (B n)] [inst11008_23 : ∀ n, One (B n)] [inst11008_24 : ∀ n, LE (B n)]
  {TA : Type v11008_7} {TB : Type v11008_8} {CA : Type v11008_9} {CB : Type v11008_10}
  [inst11008_25 : AddCommGroup TA] [inst11008_26 : Module ℂ TA] [inst11008_27 : One TA] [inst11008_28 : LE TA]
  [inst11008_29 : AddCommGroup TB] [inst11008_30 : Module ℂ TB] [inst11008_31 : One TB] [inst11008_32 : LE TB]
  [inst11008_33 : AddCommGroup CA] [inst11008_34 : Module ℂ CA] [inst11008_35 : One CA] [inst11008_36 : LE CA]
  [inst11008_37 : AddCommGroup CB] [inst11008_38 : Module ℂ CB] [inst11008_39 : One CB] [inst11008_40 : LE CB]
  {κ : Type v11008_11} [inst11008_41 : Fintype κ] [inst11008_42 : DecidableEq κ]

namespace FiniteProtocol

variable (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)

def purifiedOutput (P : Matrix (ι × η) κ ℂ) (i j : K) : PositiveMatrixMeasure (ℕ → M) κ :=
  (p.probeOutput i j).filter (purificationFilter P)

omit inst11008_10 inst11008_11 in
lemma purifiedOutput_event [Nonempty ι] [Nonempty η] (P : Matrix (ι × η) κ ℂ)
    (i j : K) (S : Set (ℕ → M)) (hS : MeasurableSet S) :
    (p.purifiedOutput P i j).value S =
      ∫ x in d.sampler.publicRecord ⁻¹' S,
        purificationFilter P * p.completeReference i j x * (purificationFilter P)ᴴ ∂d.probeLaw := by
  rw [purifiedOutput,PositiveMatrixMeasure.filter_value,p.probeOutput_event i j S hS,
    integral_filter _ (p.completeReference_integrable i j).integrableOn]

lemma purifiedOutput_ac (P : Matrix (ι × η) κ ℂ) (i j : K)
    (S : Set (ℕ → M)) (hS : MeasurableSet S) (hz : d.transcriptLaw S = 0) :
    (p.purifiedOutput P i j).value S = 0 := by
  have hp : d.probeLaw (d.sampler.publicRecord ⁻¹' S) = 0 := by
    simpa only [Discussion.transcriptLaw,Measure.map_apply d.sampler.measurable_publicRecord hS] using hz
  rw [p.purifiedOutput_event P i j S hS,Measure.restrict_eq_zero.mpr hp,integral_zero_measure]

lemma purifiedOutput_normalized (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R) :
    (trace (∑ i, ∑ j, (p.purifiedOutput P i j).value Set.univ)).re = 1 := by
  obtain ⟨L,hpos,htr,he⟩ := purification_filter_recovery R hR P hP
  have hh i j : trace ((p.purifiedOutput P i j).value Set.univ) =
      trace ((p.canonicalOutput R i j).value Set.univ) := by
    rw [← htr]
    simpa only [purifiedOutput, canonicalOutput, PositiveMatrixMeasure.filter_value] using
      congrArg trace (he ((p.probeOutput i j).value Set.univ))
  simp_rw [Matrix.trace_sum,Complex.re_sum,hh]
  simpa only [Matrix.trace_sum,Complex.re_sum] using p.canonicalOutput_normalized R hR

def purifiedOutputDensity (P : Matrix (ι × η) κ ℂ) (ν : Measure (ℕ → M)) (i j : K) :
    (ℕ → M) → Matrix κ κ ℂ := (p.purifiedOutput P i j).positiveDensity ν

end FiniteProtocol

end

section

open Matrix MeasureTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe v11165_0 v11165_1 v11165_2

variable {Ω : Type v11165_0} {ι : Type v11165_1} {K : Type v11165_2} [inst11165_0 : MeasurableSpace Ω] [inst11165_1 : Fintype ι] [inst11165_2 : DecidableEq ι]
  [inst11165_3 : Fintype K] [inst11165_4 : DecidableEq K] {μ : Measure Ω}

universe v11171_0 v11171_1

structure KeyDensity (μ : Measure Ω) (K : Type v11171_0) (ι : Type v11171_1) [Fintype K] [Fintype ι] [DecidableEq ι] where
  block : K → K → Ω → Matrix ι ι ℂ
  measurable : ∀ a b, Measurable (block a b)
  positive : ∀ a b t, (block a b t).PosSemidef
  integrable : ∀ a b, Integrable (fun t => (trace (block a b t)).re) μ
  normalized : (∑ a, ∑ b, ∫ t, (trace (block a b t)).re ∂μ) = 1

universe v11179_0

structure EveDensity (μ : Measure Ω) (ι : Type v11179_0) [Fintype ι] [DecidableEq ι] where
  block : Ω → Matrix ι ι ℂ
  measurable : Measurable block
  positive : ∀ t, (block t).PosSemidef
  integrable : Integrable (fun t => (trace (block t)).re) μ
  normalized : (∫ t, (trace (block t)).re ∂μ) = 1

namespace KeyDensity

variable (τ υ : KeyDensity μ K ι) (sigma : EveDensity μ ι)

def idealError : ℝ := cqDistance τ.block (fun a b t => idealFiniteBlocks (sigma.block t) a b) μ

def distance : ℝ := cqDistance τ.block υ.block μ

end KeyDensity

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open UnrestrictedQuantum

universe v11244_0 v11244_1 v11244_2 v11244_3 v11244_4 v11244_5 v11244_6 v11244_7 v11244_8 v11244_9 v11244_10 v11244_11

variable {O : Type v11244_0} {M : Type v11244_1} {ι : Type v11244_2} {η : Type v11244_3} [inst11244_0 : MeasurableSpace O] [inst11244_1 : MeasurableSpace M]
  [inst11244_2 : StandardBorelSpace O] [inst11244_3 : Nonempty O] [inst11244_4 : StandardBorelSpace M] [inst11244_5 : Nonempty M]
  [inst11244_6 : Fintype ι] [inst11244_7 : Fintype η] [inst11244_8 : DecidableEq ι] [inst11244_9 : DecidableEq η] [inst11244_10 : Nonempty ι] [inst11244_11 : Nonempty η]
  {K : Type v11244_4} [inst11244_12 : MeasurableSpace K] [inst11244_13 : MeasurableSingletonClass K]
  [inst11244_14 : Fintype K] [inst11244_15 : DecidableEq K] [inst11244_16 : Nonempty K]
  {d : Discussion O M} {A : ℕ → Type v11244_5} {B : ℕ → Type v11244_6}
  [inst11244_17 : ∀ n, AddCommGroup (A n)] [inst11244_18 : ∀ n, Module ℂ (A n)] [inst11244_19 : ∀ n, One (A n)] [inst11244_20 : ∀ n, LE (A n)]
  [inst11244_21 : ∀ n, AddCommGroup (B n)] [inst11244_22 : ∀ n, Module ℂ (B n)] [inst11244_23 : ∀ n, One (B n)] [inst11244_24 : ∀ n, LE (B n)]
  {TA : Type v11244_7} {TB : Type v11244_8} {CA : Type v11244_9} {CB : Type v11244_10}
  [inst11244_25 : AddCommGroup TA] [inst11244_26 : Module ℂ TA] [inst11244_27 : One TA] [inst11244_28 : LE TA]
  [inst11244_29 : AddCommGroup TB] [inst11244_30 : Module ℂ TB] [inst11244_31 : One TB] [inst11244_32 : LE TB]
  [inst11244_33 : AddCommGroup CA] [inst11244_34 : Module ℂ CA] [inst11244_35 : One CA] [inst11244_36 : LE CA]
  [inst11244_37 : AddCommGroup CB] [inst11244_38 : Module ℂ CB] [inst11244_39 : One CB] [inst11244_40 : LE CB]
  {κ : Type v11244_11} [inst11244_41 : Fintype κ] [inst11244_42 : DecidableEq κ]

def FiniteProtocol.purifiedKeyDensity
    (p : FiniteProtocol (ι := ι) (η := η) (K := K) d A B TA TB CA CB)
    (R : Matrix (ι × η) (ι × η) ℂ) (hR : Density R)
    (P : Matrix (ι × η) κ ℂ) (hP : P * Pᴴ = R)
    (ν : Measure (ℕ → M)) [SigmaFinite ν] (hμν : d.transcriptLaw ≪ ν) : KeyDensity ν K κ where
  block := p.purifiedOutputDensity P ν
  measurable := fun i j => (p.purifiedOutput P i j).measurable_positiveDensity ν
  positive := fun i j => (p.purifiedOutput P i j).positiveDensity_pos ν
  integrable := fun i j => (p.purifiedOutput P i j).integrable_positiveDensity_trace ν
    (fun S hS hz => p.purifiedOutput_ac P i j S hS (hμν hz))
  normalized := by
    have he i j := (p.purifiedOutput P i j).integral_positiveDensity_trace ν
      (fun S hS hz => p.purifiedOutput_ac P i j S hS (hμν hz))
    change (∑ i, ∑ j, ∫ t, (trace ((p.purifiedOutput P i j).positiveDensity ν t)).re ∂ν) = 1
    simp_rw [he]
    simpa only [Matrix.trace_sum,Complex.re_sum] using p.purifiedOutput_normalized R hR P hP

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

section

universe u

def KeyWord : ℕ → Type
  | 0 => Unit
  | n+1 => Bool × KeyWord n

instance keyWordFintype (n : ℕ) : Fintype (KeyWord n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => letI := ih; exact inferInstanceAs (Fintype (Bool × KeyWord n))

instance keyWordDecidableEq (n : ℕ) : DecidableEq (KeyWord n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih => letI := ih; exact inferInstanceAs (DecidableEq (Bool × KeyWord n))

instance keyWordNonempty (n : ℕ) : Nonempty (KeyWord n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih => let := ih; exact inferInstanceAs (Nonempty (Bool × KeyWord n))

instance keyWordMeasurableSpace (n : ℕ) : MeasurableSpace (KeyWord n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace Unit)
  | succ n ih => letI := ih; exact inferInstanceAs (MeasurableSpace (Bool × KeyWord n))

instance keyWordMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (KeyWord n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSingletonClass Unit)
  | succ n ih => let := ih; exact inferInstanceAs (MeasurableSingletonClass (Bool × KeyWord n))

structure QuantumMemory where
  Carrier : Type u
  additive : AddCommGroup Carrier
  complexModule : Module ℂ Carrier
  unit : One Carrier
  order : LE Carrier

attribute [instance] QuantumMemory.additive QuantumMemory.complexModule QuantumMemory.unit QuantumMemory.order

instance : CoeSort QuantumMemory (Type u) := ⟨QuantumMemory.Carrier⟩

structure ClassicalRecordSpace where
  Carrier : Type u
  measurableSpace : MeasurableSpace Carrier
  standardBorel : StandardBorelSpace Carrier
  nonempty : Nonempty Carrier

attribute [instance] ClassicalRecordSpace.measurableSpace ClassicalRecordSpace.standardBorel ClassicalRecordSpace.nonempty

instance : CoeSort ClassicalRecordSpace (Type u) := ⟨ClassicalRecordSpace.Carrier⟩

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

structure KeyImplementation (a b ell : ℕ) (messages : ClassicalRecordSpace.{u}) where
  outcomes : ClassicalRecordSpace.{u}
  discussion : Discussion outcomes messages
  memoryA : ℕ → QuantumMemory.{u}
  memoryB : ℕ → QuantumMemory.{u}
  incomingMemoryA : QuantumMemory.{u}
  incomingMemoryB : QuantumMemory.{u}
  outgoingMemoryA : QuantumMemory.{u}
  outgoingMemoryB : QuantumMemory.{u}
  protocol : FiniteProtocol (ι := Fin a) (η := Fin b) (K := KeyWord ell) discussion
    (fun n => memoryA n) (fun n => memoryB n)
    incomingMemoryA incomingMemoryB outgoingMemoryA outgoingMemoryB

namespace KeyImplementation

variable {a b ell : ℕ} {messages : ClassicalRecordSpace.{u}}
  [inst11471_0 : Nonempty (Fin a)] [inst11471_1 : Nonempty (Fin b)]
  (p : KeyImplementation a b ell messages)
  (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R)
  {e : ℕ} (P : Matrix (Fin a × Fin b) (Fin e) ℂ) (hP : P * Pᴴ = R)
  (ν : Measure (ℕ → messages)) [inst11471_2 : SigmaFinite ν] (hμν : p.discussion.transcriptLaw ≪ ν)

def output : KeyDensity ν (KeyWord ell) (Fin e) :=
  p.protocol.purifiedKeyDensity R hR P hP ν hμν

end KeyImplementation

def IsCompletedKeyOutput {a b ell e : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (_hR : Density R)
    (P : Matrix (Fin a × Fin b) (Fin e) ℂ) (_hP : P * Pᴴ = R)
    (messages : ClassicalRecordSpace.{u}) (ν : Measure (ℕ → messages)) [SigmaFinite ν]
    (τ : KeyDensity ν (KeyWord ell) (Fin e)) : Prop :=
  ∃ p : ℕ → KeyImplementation a b ell messages,
    ∃ _hAC : ∀ j, (p j).discussion.transcriptLaw ≪ ν,
      Tendsto (fun j => cqDistance
        (fun a b => positiveEntryDensity
          (publicPurifiedEntries (p j).discussion.probeLaw
            (p j).discussion.sampler.publicRecord (p j).protocol.completeReference P a b) ν)
        τ.block ν) atTop (nhds 0)

theorem isCompletedKeyOutput_iff_original {a b ell e : ℕ}
    [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R)
    (P : Matrix (Fin a × Fin b) (Fin e) ℂ) (hP : P * Pᴴ = R)
    (messages : ClassicalRecordSpace.{u}) (ν : Measure (ℕ → messages)) [SigmaFinite ν]
    (τ : KeyDensity ν (KeyWord ell) (Fin e)) :
    IsCompletedKeyOutput R hR P hP messages ν τ ↔
      ∃ p : ℕ → KeyImplementation a b ell messages,
        ∃ hAC : ∀ j, (p j).discussion.transcriptLaw ≪ ν,
          Tendsto (fun j => ((p j).output R hR P hP ν (hAC j)).distance τ) atTop (nhds 0) :=
  Iff.rfl

structure CompletedKeyTrial {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) (ell : ℕ) where
  messages : ClassicalRecordSpace.{u}
  eveDim : ℕ
  purification : Matrix (Fin a × Fin b) (Fin eveDim) ℂ
  prepares : purification * purificationᴴ = R
  referenceMeasure : Measure (ℕ → messages)
  sigmaFinite : SigmaFinite referenceMeasure
  actual : KeyDensity referenceMeasure (KeyWord ell) (Fin eveDim)
  completed : @IsCompletedKeyOutput _ _ _ _ _ _ R hR purification prepares
    messages referenceMeasure sigmaFinite actual
  ideal : EveDensity referenceMeasure (Fin eveDim)

attribute [instance] CompletedKeyTrial.sigmaFinite

namespace CompletedKeyTrial

variable {a b ell : ℕ} [inst11550_0 : Nonempty (Fin a)] [inst11550_1 : Nonempty (Fin b)]
  {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : Density R}
  (p : CompletedKeyTrial R hR ell)

def error : ℝ := p.actual.idealError p.ideal

end CompletedKeyTrial

end

section

open scoped ComplexOrder MatrixOrder Kronecker

open Matrix

def groupIndex (a b c d : ℕ) :
    (Fin (a*c) × Fin (b*d)) ≃ ((Fin a × Fin b) × (Fin c × Fin d)) where
  toFun i := (((finProdFinEquiv.symm i.1).1,(finProdFinEquiv.symm i.2).1),
    ((finProdFinEquiv.symm i.1).2,(finProdFinEquiv.symm i.2).2))
  invFun i := (finProdFinEquiv (i.1.1,i.2.1),finProdFinEquiv (i.1.2,i.2.2))
  left_inv i := by
    apply Prod.ext <;> exact finProdFinEquiv.apply_symm_apply _
  right_inv i := by simp

def groupTensor {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    Matrix (Fin (a*c) × Fin (b*d)) (Fin (a*c) × Fin (b*d)) ℂ :=
  (R ⊗ₖ S).submatrix (groupIndex a b c d) (groupIndex a b c d)

lemma trace_groupTensor {a b c d : ℕ}
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) :
    trace (groupTensor R S) = trace R * trace S := by
  rw [← trace_kronecker]
  exact Equiv.sum_comp (groupIndex a b c d) (fun x => (R ⊗ₖ S) x x)

lemma Density.groupTensor {a b c d : ℕ}
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ}
    {S : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ}
    (hR : Density R) (hS : Density S) : Density (groupTensor R S) := by
  refine ⟨(hR.1.kronecker hS.1).submatrix _,?_⟩
  rw [trace_groupTensor,hR.2,hS.2,one_mul]

def copyDim (a : ℕ) : ℕ → ℕ
  | 0 => a
  | k+1 => copyDim a k * a

lemma copyDim_eq (a k : ℕ) : copyDim a k = a^(k+1) := by
  induction k with
  | zero => simp [copyDim]
  | succ k ih => simp only [copyDim,ih,pow_succ]

def positiveCopies {a b : ℕ} (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (k : ℕ) → Matrix (Fin (copyDim a k) × Fin (copyDim b k))
      (Fin (copyDim a k) × Fin (copyDim b k)) ℂ
  | 0 => R
  | k+1 => groupTensor (positiveCopies R k) R

end

section

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

universe u

lemma Density.positiveCopies {a b : ℕ}
    {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} (hR : Density R) (k : ℕ) :
    Density (positiveCopies R k) := by
  induction k with
  | zero => exact hR
  | succ k ih => exact ih.groupTensor hR

instance positiveCopy_nonempty (a k : ℕ) [Nonempty (Fin a)] : Nonempty (Fin (copyDim a k)) := by
  have ha : 0 < copyDim a k := by
    induction k with
    | zero => exact (show 0 < a from Fin.size_positive')
    | succ k ih => exact Nat.mul_pos ih (show 0 < a from Fin.size_positive')
  exact ⟨⟨0,ha⟩⟩

structure CompletedKeyScheme {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) where
  length : ℕ → ℕ
  trial : (k : ℕ) → CompletedKeyTrial.{u} (positiveCopies R k) (by
      induction k with
      | zero => exact hR
      | succ k ih =>
        refine ⟨(ih.1.kronecker hR.1).submatrix _, ?_⟩
        change trace (groupTensor (positiveCopies R k) R) = 1
        have ht := Equiv.sum_comp (groupIndex (copyDim a k) (copyDim b k) a b)
          (fun x => (Matrix.kronecker (positiveCopies R k) R) x x)
        change trace (groupTensor (positiveCopies R k) R) = trace (Matrix.kronecker (positiveCopies R k) R) at ht
        rw [ht, Matrix.kronecker, trace_kronecker, ih.2, hR.2, one_mul]) (length k)

namespace CompletedKeyScheme

variable {a b : ℕ} [inst11756_0 : Nonempty (Fin a)] [inst11756_1 : Nonempty (Fin b)]
  {R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} {hR : Density R}
  (s : CompletedKeyScheme.{u} R hR)

def error (k : ℕ) : ℝ := (s.trial k).error

def Secure : Prop := Tendsto s.error atTop (nhds 0)

def lowerRate : ℝ≥0∞ := liminf (fun k : ℕ => (s.length k : ℝ≥0∞) / (k+1 : ℕ)) atTop

end CompletedKeyScheme

def distillableSecretKey {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) : ℝ≥0∞ :=
  sSup {r | r = 0 ∨ ∃ s : CompletedKeyScheme.{u} R hR, s.Secure ∧ r = s.lowerRate}

end

open Matrix MeasureTheory ProbabilityTheory Filter

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

universe u

def UniformProtocolGap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (_hR : Density R) : Prop :=
  ∀ (k : ℕ) (O M : Type u) [MeasurableSpace O] [MeasurableSpace M]
    [StandardBorelSpace O] [Nonempty O] [StandardBorelSpace M] [Nonempty M]
    (d : Discussion O M) (A B : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℂ (A n)] [∀ n, One (A n)] [∀ n, LE (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℂ (B n)] [∀ n, One (B n)] [∀ n, LE (B n)]
    (TA TB CA CB : Type u)
    [AddCommGroup TA] [Module ℂ TA] [One TA] [LE TA]
    [AddCommGroup TB] [Module ℂ TB] [One TB] [LE TB]
    [AddCommGroup CA] [Module ℂ CA] [One CA] [LE CA]
    [AddCommGroup CB] [Module ℂ CB] [One CB] [LE CB]
    (p : BitProtocol (ι := Fin (copyDim a k)) (η := Fin (copyDim b k)) d A B TA TB CA CB)
    (e : ℕ) (P : Matrix (Fin (copyDim a k) × Fin (copyDim b k)) (Fin e) ℂ)
    (_hP : P * Pᴴ = positiveCopies R k)
    (sigma : PositiveMatrixMeasure (ℕ → M) (Fin e)),
    (trace (sigma.value Set.univ)).re = 1 →
      1/5 ≤ p.rawPurifiedSecretBitError P sigma

def UniformCompletedGap {a b : ℕ} [Nonempty (Fin a)] [Nonempty (Fin b)]
    (R : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hR : Density R) : Prop :=
  ∀ (k ell : ℕ), 0 < ell →
    ∀ p : CompletedKeyTrial.{u} (positiveCopies R k) (by
      induction k with
      | zero => exact hR
      | succ k ih =>
        refine ⟨(ih.1.kronecker hR.1).submatrix _, ?_⟩
        change trace (groupTensor (positiveCopies R k) R) = 1
        have ht := Equiv.sum_comp (groupIndex (copyDim a k) (copyDim b k) a b)
          (fun x => (Matrix.kronecker (positiveCopies R k) R) x x)
        change trace (groupTensor (positiveCopies R k) R) = trace (Matrix.kronecker (positiveCopies R k) R) at ht
        rw [ht, Matrix.kronecker, trace_kronecker, ih.2, hR.2, one_mul]) ell,
      1/5 ≤ p.error

namespace Explicit

lemma m_pos : 0 < m := by rw [m_eq]; exact Nat.mul_pos Q_pos D_pos

instance output_nonempty : Nonempty (Fin m) := by
  have hb : 0 < b := by
    unfold b
    exact Nat.choose_pos (by decide)
  have hq : 0 < Q := by unfold Q; exact pow_pos hb 3
  have hd (q : ℕ) : 0 < dimensionFunction q := pow_pos (by decide) _
  have hD : 0 < D := by unfold D; exact hd Q
  have hm (q d : ℕ) (hq : 0 < q) (hd : 0 < d) :
      0 < outputDimensionFunction q d := Nat.mul_pos hq hd
  exact ⟨⟨0, by unfold m; exact hm Q D hq hD⟩⟩

def MainClaim : Prop :=
  ∃ hR : Density rhoFin, ¬ Separable rhoFin ∧
    distillableSecretKey.{u} rhoFin hR = 0 ∧
    UniformProtocolGap.{u} rhoFin hR ∧
    UniformCompletedGap.{u} rhoFin hR

end Explicit

end ZeroKey

end

end OAI
