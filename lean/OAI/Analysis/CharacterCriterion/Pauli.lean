import OAI.Analysis.CharacterCriterion.Definitions
import Mathlib

namespace OAI

noncomputable section


namespace KirchbergRordam.Pauli
open scoped Matrix BigOperators Kronecker
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

def e : Fin 4 → M2 := ![1,!![0,1;1,0],!![0,-Complex.I;Complex.I,0],!![1,0;0,-1]]

lemma e_zero : e 0=1 := rfl
lemma e_star (i : Fin 4) : star (e i)=e i := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [e]
lemma e_square (i : Fin 4) : e i*e i=1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;>
    norm_num [e,Matrix.mul_apply,Fin.sum_univ_two]
lemma e_gram (i : Fin 4) : star (e i)*e i=1 := by rw [e_star,e_square]

lemma trace_mul (i j : Fin 4) : Matrix.trace (e i*e j)=if i=j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [e,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_two]

def coeff (i : Fin 4) : M2 →ₗ[ℂ] ℂ :=
  (2:ℂ)⁻¹ • (Matrix.traceLinearMap (Fin 2) ℂ ℂ).comp (LinearMap.mulLeft ℂ (e i))
lemma coeff_apply (i : Fin 4) (a : M2) : coeff i a=2⁻¹*Matrix.trace (e i*a) := rfl
lemma coeff_e (i j : Fin 4) : coeff i (e j)=if i=j then 1 else 0 := by
  rw [coeff_apply,trace_mul]
  split_ifs <;> norm_num

lemma independent : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h := congrArg (coeff i) hf
  simpa [map_sum,map_smul,coeff_e] using h

def basis : Module.Basis (Fin 4) ℂ M2 :=
  basisOfLinearIndependentOfCardEqFinrank' e independent (by
    simp [M2,Module.finrank_matrix])

lemma basis_apply (i : Fin 4) : basis i=e i := by
  simp [basis]
lemma coeff_sum (a : M2) : ∑ i,coeff i a • e i=a := by
  have he (i : Fin 4) : basis.repr a i=coeff i a := by
    have h := congrArg (coeff i) (basis.sum_repr a)
    simpa [map_sum,map_smul,basis_apply,coeff_e] using h
  simpa only [he,basis_apply] using basis.sum_repr a
end KirchbergRordam.Pauli

namespace KirchbergRordam.PauliPower
open scoped Matrix BigOperators Kronecker

def Row : ℕ→Type
  | 0 => Fin 2
  | n+1 => Fin 2 × Row n

def Label : ℕ→Type
  | 0 => Fin 4
  | n+1 => Fin 4 × Label n

instance rowFintype : (n : ℕ) → Fintype (Row n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n+1 => letI := rowFintype n; inferInstanceAs (Fintype (Fin 2 × Row n))
instance rowDecidableEq : (n : ℕ) → DecidableEq (Row n)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | n+1 => letI := rowDecidableEq n; inferInstanceAs (DecidableEq (Fin 2 × Row n))
instance labelFintype : (n : ℕ) → Fintype (Label n)
  | 0 => inferInstanceAs (Fintype (Fin 4))
  | n+1 => letI := labelFintype n; inferInstanceAs (Fintype (Fin 4 × Label n))
instance labelDecidableEq : (n : ℕ) → DecidableEq (Label n)
  | 0 => inferInstanceAs (DecidableEq (Fin 4))
  | n+1 => letI := labelDecidableEq n; inferInstanceAs (DecidableEq (Fin 4 × Label n))

abbrev Mat (n : ℕ) := Matrix (Row n) (Row n) ℂ

def e : (n : ℕ) → Label n → Mat n
  | 0,a => Pauli.e a
  | n+1,a => Matrix.kronecker (Pauli.e a.1) (e n a.2)

lemma row_card (n : ℕ) : Fintype.card (Row n)=2^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 × Row n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    omega
lemma label_card (n : ℕ) : Fintype.card (Label n)=4^(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 4 × Label n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    omega

lemma e_star (n : ℕ) (a : Label n) : star (e n a)=e n a := by
  induction n with
  | zero => exact Pauli.e_star a
  | succ n ih =>
    change (Matrix.kronecker (Pauli.e a.1) (e n a.2)).conjTranspose=_
    dsimp only [Matrix.kronecker]
    rw [Matrix.conjTranspose_kronecker]
    change Matrix.kronecker (star (Pauli.e a.1)) (star (e n a.2))=_
    rw [Pauli.e_star,ih]
    rfl

lemma e_square (n : ℕ) (a : Label n) : e n a*e n a=1 := by
  induction n with
  | zero => exact Pauli.e_square a
  | succ n ih =>
    change Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e a.1) (e n a.2)=
      (1 : Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Pauli.e_square,ih,Matrix.one_kronecker_one]

lemma trace_mul (n : ℕ) (a b : Label n) :
    Matrix.trace (e n a*e n b)=if a=b then (2:ℂ)^(n+1) else 0 := by
  induction n with
  | zero =>
    change Matrix.trace (Pauli.e a * Pauli.e b) = if a = b then (2 : ℂ)^1 else 0
    rw [pow_one]
    exact Pauli.trace_mul a b
  | succ n ih =>
    change Matrix.trace (Matrix.kronecker (Pauli.e a.1) (e n a.2)*
      Matrix.kronecker (Pauli.e b.1) (e n b.2))=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,Pauli.trace_mul,ih]
    have hab : a=b ↔ a.1=b.1 ∧ a.2=b.2 := Prod.ext_iff
    by_cases h1 : a.1=b.1 <;> by_cases h2 : a.2=b.2 <;>
      simp [h1,h2,hab,pow_succ,mul_comm]

def coeff (n : ℕ) (a : Label n) : Mat n →ₗ[ℂ] ℂ :=
  ((2:ℂ)^(n+1))⁻¹ • (Matrix.traceLinearMap (Row n) ℂ ℂ).comp (LinearMap.mulLeft ℂ (e n a))
lemma coeff_apply (n : ℕ) (a : Label n) (x : Mat n) :
    coeff n a x=((2:ℂ)^(n+1))⁻¹*Matrix.trace (e n a*x) := rfl
lemma coeff_e (n : ℕ) (a b : Label n) : coeff n a (e n b)=if a=b then 1 else 0 := by
  rw [coeff_apply,trace_mul]
  split_ifs <;> simp

lemma independent (n : ℕ) : LinearIndependent ℂ (e n) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h := congrArg (coeff n i) hf
  simpa [map_sum,map_smul,coeff_e] using h

def basis (n : ℕ) : Module.Basis (Label n) ℂ (Mat n) :=
  basisOfLinearIndependentOfCardEqFinrank' (e n) (independent n) (by
    simp only [Mat,Module.finrank_matrix,label_card,row_card,Module.finrank_self,mul_one]
    rw [← mul_pow]
    norm_num)

lemma basis_apply (n : ℕ) (a : Label n) : basis n a=e n a := by simp [basis]
lemma coeff_sum (n : ℕ) (x : Mat n) : ∑ a,coeff n a x • e n a=x := by
  have he (a : Label n) : (basis n).repr x a=coeff n a x := by
    have h := congrArg (coeff n a) ((basis n).sum_repr x)
    simpa [map_sum,map_smul,basis_apply,coeff_e] using h
  simpa only [he,basis_apply] using (basis n).sum_repr x

abbrev CMat (n : ℕ) := CStarMatrix (Row n) (Row n) ℂ
instance (n : ℕ) : FiniteDimensional ℂ (CMat n) :=
  inferInstanceAs (FiniteDimensional ℂ (Mat n))
def ce (n : ℕ) (a : Label n) : CMat n := CStarMatrix.ofMatrix (e n a)
def ccoeff (n : ℕ) (a : Label n) : CMat n →L[ℂ] ℂ :=
  ((coeff n a).comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.toLinearMap).toContinuousLinearMap
lemma ccoeff_ce (n : ℕ) (a b : Label n) : ccoeff n a (ce n b)=if a=b then 1 else 0 :=
  coeff_e n a b
lemma ccoeff_sum (n : ℕ) (x : CMat n) : ∑ a,ccoeff n a x • ce n a=x := by
  exact congrArg CStarMatrix.ofMatrix (coeff_sum n (CStarMatrix.ofMatrix.symm x))
lemma ce_star (n : ℕ) (a : Label n) : star (ce n a)=ce n a :=
  congrArg CStarMatrix.ofMatrix (e_star n a)
lemma ce_square (n : ℕ) (a : Label n) : ce n a*ce n a=1 :=
  congrArg CStarMatrix.ofMatrix (e_square n a)
end KirchbergRordam.PauliPower

namespace KirchbergRordam.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


lemma algebra_legs_commute (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    Commute (leftMatrixAlgebra (κ:=κ) a) (rightMatrixAlgebra (ι:=ι) b) := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker 1 b * Matrix.kronecker a 1
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp

lemma legs_commute (a : Mat ι) (b : Mat κ) :
    Commute (leftMatrix (κ:=κ) a) (rightMatrix (ι:=ι) b) :=
  (algebra_legs_commute (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)).map
    CStarMatrix.ofMatrixStarAlgEquiv

lemma algebra_legs_product (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    leftMatrixAlgebra (κ:=κ) a*rightMatrixAlgebra (ι:=ι) b=Matrix.kronecker a b := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker a b
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma legs_product (a : Mat ι) (b : Mat κ) :
    leftMatrix (κ:=κ) a*rightMatrix (ι:=ι) b=CStarMatrix.ofMatrix (Matrix.kronecker a b) := by
  exact congrArg CStarMatrix.ofMatrix
    (algebra_legs_product (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
end KirchbergRordam.MatrixTensor

namespace KirchbergRordam.PauliSupport
open scoped Matrix Kronecker BigOperators
open PauliPower

def partner (a : Fin 4) : Fin 4 := if a=1 then 2 else 1
lemma anti (a : Fin 4) (ha : a≠0) : Pauli.e (partner a)*Pauli.e a= -(Pauli.e a*Pauli.e (partner a)) := by
  fin_cases a
  · exact (ha rfl).elim
  all_goals
    dsimp [partner,Pauli.e]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Pauli.e,Matrix.mul_apply,Fin.sum_univ_two]

def coord : (n : ℕ)→Label n→Fin (n+1)→Fin 4
  | 0,a,_ => a
  | n+1,a,i => Fin.cases a.1 (fun j=>coord n a.2 j) i

def leg : (n : ℕ)→Fin (n+1)→Pauli.M2→⋆ₐ[ℂ] Mat n
  | 0,_ => StarAlgHom.id ℂ Pauli.M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrixAlgebra
      (fun j=>MatrixTensor.rightMatrixAlgebra.comp (leg n j)) i

lemma anti_leg (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : coord n a j≠0) :
    leg n j (Pauli.e (partner (coord n a j)))*e n a=
      -(e n a*leg n j (Pauli.e (partner (coord n a j)))) := by
  induction n with
  | zero => exact anti a hj
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      change @Eq (Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
        (Matrix.kronecker (Pauli.e (partner a.1)) 1*Matrix.kronecker (Pauli.e a.1) (e n a.2))
        (-(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e (partner a.1)) 1))
      dsimp only [Matrix.kronecker]
      erw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,anti a.1 hj,one_mul,mul_one ]
      ext r s
      simp [Matrix.kroneckerMap_apply]
      rfl
    | succ j =>
      change @Eq (Matrix (Fin 2 × Row n) (Fin 2 × Row n) ℂ)
        (Matrix.kronecker 1 (leg n j (Pauli.e (partner (coord n a.2 j))))*Matrix.kronecker (Pauli.e a.1) (e n a.2))
        (-(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker 1 (leg n j (Pauli.e (partner (coord n a.2 j))))))
      dsimp only [Matrix.kronecker]
      erw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,mul_one,ih a.2 j hj ]
      ext r s
      simp [Matrix.kroneckerMap_apply]
      rfl

lemma trace_zero_of_anti {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b e x : Matrix ι ι ℂ) (hb : b*b=1) (he : b*e= -(e*b)) (hx : Commute b x) :
    Matrix.trace (e*x)=0 := by
  have hneg : b*(e*x)*b= -(e*x) := by
    calc
      _ = (b*e)*x*b := by noncomm_ring
      _ = -(e*(b*x)*b) := by rw [he]; noncomm_ring
      _ = -(e*x*(b*b)) := by rw [hx.eq]; noncomm_ring
      _ = -(e*x) := by rw [hb,mul_one]
  have ht : Matrix.trace (b*(e*x)*b)=Matrix.trace (e*x) := by
    rw [mul_assoc,Matrix.trace_mul_comm b,mul_assoc (e*x),hb,mul_one]
  rw [hneg,Matrix.trace_neg] at ht
  linear_combination -ht / 2

lemma coeff_zero (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : coord n a j≠0)
    (x : Mat n) (hx : ∀ b,Commute (leg n j b) x) : coeff n a x=0 := by
  rw [coeff_apply,trace_zero_of_anti _ _ _ _ (anti_leg n a j hj) (hx _),mul_zero]
  rw [← map_mul,Pauli.e_square,map_one]
end KirchbergRordam.PauliSupport

namespace KirchbergRordam.PauliPower

def zeroLabel : (n : ℕ) → Label n
  | 0 => (0 : Fin 4)
  | n+1 => (0, zeroLabel n)

lemma e_zeroLabel (n : ℕ) : e n (zeroLabel n) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Matrix.kronecker (Pauli.e 0) (e n (zeroLabel n)) = _
    rw [Pauli.e_zero, ih]
    exact Matrix.one_kronecker_one

lemma coord_zero_iff (n : ℕ) (a : Label n) :
    (∀ j, PauliSupport.coord n a j = 0) ↔ a = zeroLabel n := by
  induction n with
  | zero =>
    constructor
    · intro h; exact h 0
    · intro h j; exact h
  | succ n ih =>
    constructor
    · intro h
      have h0 := h 0
      have ht : ∀ j, PauliSupport.coord n a.2 j = 0 := fun j => h j.succ
      exact Prod.ext h0 ((ih a.2).mp ht)
    · intro h
      subst a
      intro j
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (ih (zeroLabel n)).mpr rfl j

lemma exists_anti (n : ℕ) (a : Label n) (ha : a ≠ zeroLabel n) :
    ∃ b : Mat n, b*b=1 ∧ b*e n a = -(e n a*b) := by
  have h : ¬ ∀ j, PauliSupport.coord n a j = 0 :=
    fun h => ha ((coord_zero_iff n a).mp h)
  obtain ⟨j,hj⟩ := not_forall.mp h
  refine ⟨PauliSupport.leg n j (Pauli.e (PauliSupport.partner (PauliSupport.coord n a j))), ?_,
    PauliSupport.anti_leg n a j hj⟩
  rw [← map_mul, Pauli.e_square, map_one]

end KirchbergRordam.PauliPower

namespace KirchbergRordam.GenericRW
class Size where
  n : ℕ
  positive : 0 < n
instance [Size] : NeZero Size.n := ⟨Nat.ne_of_gt Size.positive⟩

section
open scoped Matrix BigOperators
variable [Size]
local notation "N" => Size.n


class PauliData where
  Label : Type
  [finite : Fintype Label]
  [decidable : DecidableEq Label]
  zero : Label
  e : Label → Matrix (Fin N) (Fin N) ℂ
  e_zero : e zero = 1
  e_star : ∀ a, star (e a) = e a
  e_square : ∀ a, e a * e a = 1
  trace_mul : ∀ a b, Matrix.trace (e a * e b) = if a=b then (N:ℂ) else 0
  card : Fintype.card Label = N*N
  anti : ∀ a, a ≠ zero → ∃ b : Matrix (Fin N) (Fin N) ℂ,
    b*b=1 ∧ b*e a= -(e a*b)
  two_le : 2 ≤ N
attribute [instance_reducible] PauliData.finite PauliData.decidable
attribute [instance] PauliData.finite PauliData.decidable
instance [PauliData] : Zero PauliData.Label := ⟨PauliData.zero⟩

omit [Size] in
abbrev powerSize (k : ℕ) : Size := ⟨2^(k+1), by positivity⟩

omit [Size] in
def rowEquiv (k : ℕ) : PauliPower.Row k ≃ Fin (2^(k+1)) :=
  (Fintype.equivFin _).trans (finCongr (PauliPower.row_card k))

omit [Size] in
def rowReindex (k : ℕ) : PauliPower.Mat k ≃⋆ₐ[ℂ]
    Matrix (Fin (2^(k+1))) (Fin (2^(k+1))) ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ (rowEquiv k) with
    map_smul' := fun c x => rfl
    map_star' := fun x => by
      exact (Matrix.conjTranspose_reindex (rowEquiv k) (rowEquiv k) x).symm }

omit [Size] in
lemma reindex_trace (k : ℕ) (x : PauliPower.Mat k) :
    Matrix.trace (rowReindex k x) = Matrix.trace x := by
  change (∑ i, x ((rowEquiv k).symm i) ((rowEquiv k).symm i)) = ∑ i, x i i
  exact (rowEquiv k).symm.sum_comp (fun i => x i i)

end
open scoped Matrix BigOperators

@[instance_reducible] def powerPauliData (k : ℕ) : @PauliData (powerSize k) := by
  letI : Size := powerSize k
  exact {
    Label := PauliPower.Label k
    zero := PauliPower.zeroLabel k
    e := fun a => rowReindex k (PauliPower.e k a)
    e_zero := by rw [PauliPower.e_zeroLabel, map_one]
    e_star a := by rw [← map_star, PauliPower.e_star]
    e_square a := by rw [← map_mul, PauliPower.e_square, map_one]
    trace_mul a b := by
      change Matrix.trace (rowReindex k (PauliPower.e k a) * rowReindex k (PauliPower.e k b)) =
        if a=b then ((2^(k+1):ℕ):ℂ) else 0
      rw [← map_mul, reindex_trace, PauliPower.trace_mul, Nat.cast_pow, Nat.cast_ofNat]
    card := by
      rw [PauliPower.label_card]
      change 4^(k+1) = 2^(k+1)*2^(k+1)
      rw [← mul_pow]
      norm_num
    anti a ha := by
      obtain ⟨b,hb,he⟩ := PauliPower.exists_anti k a ha
      refine ⟨rowReindex k b, ?_, ?_⟩
      · rw [← map_mul, hb, map_one]
      · rw [← map_mul, he, map_neg, map_mul]
    two_le := by
      change 2 ≤ 2^(k+1)
      calc
        2 = 2^1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  }
end KirchbergRordam.GenericRW

end

end OAI
