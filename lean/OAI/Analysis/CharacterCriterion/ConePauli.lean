import OAI.Analysis.CharacterCriterion.FunctionalCalculus

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
variable [instSize : KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n


variable [instPauliData : KirchbergRordam.GenericRW.PauliData]
namespace KirchbergRordam.GenericRW.Pauli
open scoped Matrix BigOperators Kronecker
abbrev Label := PauliData.Label
abbrev M2 := Matrix (Fin rankNum) (Fin rankNum) ℂ
abbrev e : Label → M2 := PauliData.e
lemma e_zero : e (0:Label)=1 := PauliData.e_zero
lemma e_star (i : Label) : star (e i)=e i := PauliData.e_star i
lemma e_square (i : Label) : e i*e i=1 := PauliData.e_square i
lemma e_gram (i : Label) : star (e i)*e i=1 := by rw [e_star,e_square]
lemma trace_mul (i j : Label) : Matrix.trace (e i*e j)=if i=j then (rankNum:ℂ) else 0 :=
  PauliData.trace_mul i j
omit instSize instPauliData in
lemma ne_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    : (rankNum:ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne rankNum)
def coeff (i : Label) : M2 →ₗ[ℂ] ℂ :=
  (rankNum:ℂ)⁻¹ • (Matrix.traceLinearMap (Fin rankNum) ℂ ℂ).comp (LinearMap.mulLeft ℂ (e i))
lemma coeff_apply (i : Label) (a : M2) : coeff i a=(rankNum:ℂ)⁻¹*Matrix.trace (e i*a) := rfl
lemma coeff_e (i j : Label) : coeff i (e j)=if i=j then 1 else 0 := by
  rw [coeff_apply,trace_mul]
  split_ifs <;> simp
lemma independent : LinearIndependent ℂ e := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have h := congrArg (coeff i) hf
  simpa [map_sum,map_smul,coeff_e] using h
def basis : Module.Basis Label ℂ M2 :=
  basisOfLinearIndependentOfCardEqFinrank' e independent (by
    simp [M2,Module.finrank_matrix,PauliData.card])
lemma basis_apply (i : Label) : basis i=e i := by simp [basis]
lemma coeff_sum (a : M2) : ∑ i,coeff i a • e i=a := by
  have he (i : Label) : basis.repr a i=coeff i a := by
    have h := congrArg (coeff i) (basis.sum_repr a)
    simpa [map_sum,map_smul,basis_apply,coeff_e] using h
  simpa only [he,basis_apply] using basis.sum_repr a
end KirchbergRordam.GenericRW.Pauli

namespace KirchbergRordam.GenericRW.PauliPower
open scoped Matrix BigOperators Kronecker

def Row : ℕ→Type
  | 0 => Fin rankNum
  | n+1 => Fin rankNum × Row n

def Label : ℕ→Type
  | 0 => Pauli.Label
  | n+1 => Pauli.Label × Label n

instance rowFintype : (n : ℕ) → Fintype (Row n)
  | 0 => inferInstanceAs (Fintype (Fin rankNum))
  | n+1 => letI := rowFintype n; inferInstanceAs (Fintype (Fin rankNum × Row n))
instance rowDecidableEq : (n : ℕ) → DecidableEq (Row n)
  | 0 => inferInstanceAs (DecidableEq (Fin rankNum))
  | n+1 => letI := rowDecidableEq n; inferInstanceAs (DecidableEq (Fin rankNum × Row n))
instance labelFintype : (n : ℕ) → Fintype (Label n)
  | 0 => inferInstanceAs (Fintype (Pauli.Label))
  | n+1 => letI := labelFintype n; inferInstanceAs (Fintype (Pauli.Label × Label n))
instance labelDecidableEq : (n : ℕ) → DecidableEq (Label n)
  | 0 => inferInstanceAs (DecidableEq (Pauli.Label))
  | n+1 => letI := labelDecidableEq n; inferInstanceAs (DecidableEq (Pauli.Label × Label n))

abbrev Mat (n : ℕ) := Matrix (Row n) (Row n) ℂ

def e : (n : ℕ) → Label n → Mat n
  | 0,a => Pauli.e a
  | n+1,a => Matrix.kronecker (Pauli.e a.1) (e n a.2)

omit instSize instPauliData in
lemma row_card
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) : Fintype.card (Row n)=rankNum^(n+1) := by
  induction n with
  | zero =>
    change Fintype.card (Fin rankNum) = rankNum ^ (0 + 1)
    simp
  | succ n ih =>
    change Fintype.card (Fin rankNum × Row n)=_
    simp only [Fintype.card_prod,Fintype.card_fin,ih,pow_succ]
    ring
lemma label_card (n : ℕ) : Fintype.card (Label n)=(rankNum*rankNum)^(n+1) := by
  induction n with
  | zero =>
    change Fintype.card PauliData.Label = (rankNum * rankNum) ^ (0 + 1)
    simpa only [Nat.zero_add, pow_one] using PauliData.card
  | succ n ih =>
    change Fintype.card (Pauli.Label × Label n)=_
    simp only [Fintype.card_prod,PauliData.card,ih,pow_succ]
    ring

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
    change Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker (Pauli.e a.1) (e n a.2)=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Pauli.e_square,ih,Matrix.one_kronecker_one]
    rfl

lemma trace_mul (n : ℕ) (a b : Label n) :
    Matrix.trace (e n a*e n b)=if a=b then (rankNum:ℂ)^(n+1) else 0 := by
  induction n with
  | zero =>
    change Matrix.trace (Pauli.e a * Pauli.e b) =
      if (a : Pauli.Label) = b then (rankNum : ℂ) ^ (0 + 1) else 0
    split_ifs with hab
    · have hab' : (a : Pauli.Label) = b := hab
      simpa only [Nat.zero_add, pow_one] using
        (Pauli.trace_mul a b).trans (ite_eq_left hab')
    · have hab' : (a : Pauli.Label) ≠ b := hab
      exact (Pauli.trace_mul a b).trans (ite_eq_right hab')
  | succ n ih =>
    change Matrix.trace (Matrix.kronecker (Pauli.e a.1) (e n a.2)*
      Matrix.kronecker (Pauli.e b.1) (e n b.2))=_
    dsimp only [Matrix.kronecker]
    rw [← Matrix.mul_kronecker_mul,Matrix.trace_kronecker,Pauli.trace_mul,ih]
    have hab : a=b ↔ a.1=b.1 ∧ a.2=b.2 := Prod.ext_iff
    by_cases h1 : a.1=b.1 <;> by_cases h2 : a.2=b.2 <;>
      simp [h1,h2,hab,pow_succ,mul_comm]

def coeff (n : ℕ) (a : Label n) : Mat n →ₗ[ℂ] ℂ :=
  ((rankNum:ℂ)^(n+1))⁻¹ • (Matrix.traceLinearMap (Row n) ℂ ℂ).comp (LinearMap.mulLeft ℂ (e n a))
lemma coeff_apply (n : ℕ) (a : Label n) (x : Mat n) :
    coeff n a x=((rankNum:ℂ)^(n+1))⁻¹*Matrix.trace (e n a*x) := rfl
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
    rw [← mul_pow])

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
end KirchbergRordam.GenericRW.PauliPower

namespace KirchbergRordam.GenericRW.ConePauli
open Topology
open scoped CStarAlgebra BigOperators
open ConeModel
abbrev E (i : Pauli.Label) : M2 := PauliPower.ce 0 i
lemma E_zero : E (0:Pauli.Label)=1 := congrArg CStarMatrix.ofMatrix Pauli.e_zero
def p (i : Pauli.Label) : C(unitInterval,ℂ) := if i=0 then 1 else ⟨fun t => ((t:ℝ):ℂ), by fun_prop⟩
def u (i : Pauli.Label) : Cone := ⟨⟨fun t => p i t • E i,(p i).continuous.smul continuous_const⟩,by
  change p i 0 • E i ∈ (⊥ : StarSubalgebra ℂ M2)
  by_cases hi : i=0
  · subst i
    simp only [p, E_zero]
    change (1:ℂ) • (1:M2)∈(⊥ : StarSubalgebra ℂ M2)
    simpa only [one_smul] using (one_mem (⊥ : StarSubalgebra ℂ M2))
  · simp only [p,ite_eq_right hi,ContinuousMap.coe_mk,Set.Icc.coe_zero,Complex.ofReal_zero,zero_smul]
    exact zero_mem _⟩
omit instSize instPauliData in
lemma scalar_commute
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (f : C(unitInterval,ℂ)) (a : Cone) : Commute (scalar f) a := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact Algebra.commutes (f t) ((a:C(unitInterval,M2)) t)
lemma u_gram (i : Pauli.Label) : star (u i)*u i=scalar (star (p i)*p i) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change star (p i t • E i)*(p i t • E i)=algebraMap ℂ M2 (star (p i t)*p i t)
  have hstar : star (E i) = E i := PauliPower.ce_star 0 i
  have hsquare : E i * E i = 1 := PauliPower.ce_square 0 i
  rw [star_smul,smul_mul_smul_comm,hstar,hsquare]
  exact (Algebra.algebraMap_eq_smul_one _).symm

def sectionMap (i : Pauli.Label) : C(unitInterval,ℂ) →L[ℂ] C(unitInterval,M2) :=
  (ContinuousLinearMap.toSpanSingleton ℂ (E i)).compLeftContinuous ℂ unitInterval

lemma sectionMap_apply (i : Pauli.Label) (f : C(unitInterval,ℂ)) (t : unitInterval) : sectionMap i f t=f t • E i := rfl

def coeff (i : Pauli.Label) (f : Cone) : C(unitInterval,ℂ) :=
  ⟨fun t => PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) t),(PauliPower.ccoeff 0 i).continuous.comp f.val.continuous⟩
lemma coeff_zero (i : Pauli.Label) (hi : i≠0) (f : Cone) : coeff i f 0=0 := by
  obtain ⟨c,hc⟩ := f.property
  change PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) 0)=0
  change algebraMap ℂ M2 c=(f:C(unitInterval,M2)) 0 at hc
  rw [← hc]
  rw [Algebra.algebraMap_eq_smul_one]
  have hcoeff : PauliPower.ccoeff 0 i (1 : M2) = 0 := by
    calc
      _ = PauliPower.ccoeff 0 i (E (0 : Pauli.Label)) :=
        congrArg (PauliPower.ccoeff 0 i) E_zero.symm
      _ = if i = 0 then 1 else 0 := PauliPower.ccoeff_ce 0 i (0 : Pauli.Label)
      _ = 0 := ite_eq_right hi
  exact ((PauliPower.ccoeff 0 i).map_smul c (1 : M2)).trans
    ((congrArg (c • ·) hcoeff).trans (smul_zero c))
lemma reconstruct (f : Cone) : ∑ i,sectionMap i (coeff i f)=(f:C(unitInterval,M2)) := by
  apply ContinuousMap.ext
  intro t
  simp only [ContinuousMap.sum_apply]
  change ∑ i:Pauli.Label,PauliPower.ccoeff 0 i ((f:C(unitInterval,M2)) t) • E i=_
  exact PauliPower.ccoeff_sum 0 ((f:C(unitInterval,M2)) t)

def expansion : (Pauli.Label→C(unitInterval,ℂ)) →ₗ[ℂ] Cone where
  toFun f := ∑ i,scalar (f i)*u i
  map_add' f g := by simp [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c f := by simp [map_smul,Finset.smul_sum]

lemma expansion_single (i : Pauli.Label) (f : C(unitInterval,ℂ)) :
    expansion (Pi.single i f)=scalar f*u i := by
  dsimp only [expansion,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro b _ hbi
    rw [Pi.single_eq_of_ne hbi,map_zero,zero_mul]
  · intro hi; exact (hi (Finset.mem_univ i)).elim

lemma dense : DenseRange expansion := by
  let S : Submodule ℂ Cone := (LinearMap.range expansion).topologicalClosure
  have hclosed : IsClosed (S:Set Cone) := Submodule.isClosed_topologicalClosure _
  have hbase (i : Pauli.Label) (f : C(unitInterval,ℂ)) : scalar f*u i ∈ S := by
    apply (LinearMap.range expansion).le_topologicalClosure
    exact ⟨Pi.single i f,expansion_single i f⟩
  have hsec (i : Pauli.Label) (f : C(unitInterval,ℂ)) (hf : i≠0→f 0=0) :
      ∃ a:Cone,a∈S ∧ (a:C(unitInterval,M2))=sectionMap i f := by
    have hz : ∀ t,p i t=0→f t=0 := by
      intro t ht
      by_cases hi : i=0
      · simp [p,hi] at ht
      · have ht0 : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          exact_mod_cast (show ((t:ℝ):ℂ)=0 by simpa [p,hi] using ht)
        rw [ht0]
        exact hf hi
    let v : Vanish.Functions {t | p i t=0} := ⟨f,fun t ht => hz t ht⟩
    have hmem (g : Vanish.Functions {t | p i t=0}) :
        sectionMap i g.val ∈ Set.range (fun a:S => (a.val:C(unitInterval,M2))) := by
      refine (Vanish.multiplier_dense (p i)).induction_on g ?_ ?_
      · have hs : IsClosedEmbedding (fun a:S => (a.val:C(unitInterval,M2))) :=
          coneClosed.isClosedEmbedding_subtypeVal.comp hclosed.isClosedEmbedding_subtypeVal
        exact hs.isClosed_range.preimage ((sectionMap i).continuous.comp continuous_subtype_val)
      · intro f
        refine ⟨⟨scalar f*u i,hbase i f⟩,?_⟩
        apply ContinuousMap.ext
        intro t
        change algebraMap ℂ M2 (f t)*(p i t • E i)=(p i t*f t) • E i
        rw [Algebra.algebraMap_eq_smul_one,smul_mul_smul_comm,one_mul,mul_comm]
    obtain ⟨a,ha⟩ := hmem v
    exact ⟨a.val,a.property,ha⟩
  have hall (f : Cone) : f∈S := by
    have h (i : Pauli.Label) := hsec i (coeff i f) (fun hi => coeff_zero i hi f)
    choose a ha he using h
    have hf : ∑ i,a i=f := by
      apply Subtype.ext
      change coneSubalgebra.subtype (∑ i,a i)=_
      rw [map_sum]
      change ∑ i,(a i:C(unitInterval,M2))=(f:C(unitInterval,M2))
      simp_rw [he]
      exact reconstruct f
    rw [← hf]
    exact Submodule.sum_mem S (fun i _ => ha i)
  intro f
  exact hall f
end KirchbergRordam.GenericRW.ConePauli

namespace KirchbergRordam.GenericRW.MatrixTensor
open scoped Matrix Kronecker
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Mat (ι : Type*) := CStarMatrix ι ι ℂ

def leftMatrixAlgebra : Matrix ι ι ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := a ⊗ₖ (1 : Matrix κ κ ℂ)
  map_zero' := Matrix.zero_kronecker _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.add_kronecker _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul a b
      (1 : Matrix κ κ ℂ) (1 : Matrix κ κ ℂ)
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  map_star' a := by
    change aᴴ ⊗ₖ (1 : Matrix κ κ ℂ) = (a ⊗ₖ 1)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def rightMatrixAlgebra : Matrix κ κ ℂ →⋆ₐ[ℂ]
    Matrix (ι × κ) (ι × κ) ℂ where
  toFun a := (1 : Matrix ι ι ℂ) ⊗ₖ a
  map_zero' := Matrix.kronecker_zero _
  map_one' := Matrix.one_kronecker_one
  map_add' a b := Matrix.kronecker_add _ _ _
  map_mul' a b := by
    simpa only [mul_one] using Matrix.mul_kronecker_mul
      (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) a b
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul,
      Matrix.one_kronecker_one]
  map_star' a := by
    change (1 : Matrix ι ι ℂ) ⊗ₖ aᴴ = (1 ⊗ₖ a)ᴴ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]


def leftMatrix : Mat ι →⋆ₐ[ℂ] Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (leftMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


def rightMatrix : Mat κ →⋆ₐ[ℂ] Mat (ι×κ) :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    (rightMatrixAlgebra.comp CStarMatrix.ofMatrixStarAlgEquiv.symm.toStarAlgHom)


omit instSize instPauliData in
lemma algebra_legs_commute.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    Commute (leftMatrixAlgebra (κ:=κ) a) (rightMatrixAlgebra (ι:=ι) b) := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker 1 b * Matrix.kronecker a 1
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]
  simp

lemma legs_commute (a : Mat ι) (b : Mat κ) :
    Commute (leftMatrix (κ:=κ) a) (rightMatrix (ι:=ι) b) :=
  (algebra_legs_commute (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b)).map
    CStarMatrix.ofMatrixStarAlgEquiv

omit instSize instPauliData in
lemma algebra_legs_product.{contextLevel1, contextLevel2}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    {κ : Type contextLevel2}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    leftMatrixAlgebra (κ:=κ) a*rightMatrixAlgebra (ι:=ι) b=Matrix.kronecker a b := by
  change Matrix.kronecker a 1 * Matrix.kronecker 1 b = Matrix.kronecker a b
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  simp

lemma legs_product (a : Mat ι) (b : Mat κ) :
    leftMatrix (κ:=κ) a*rightMatrix (ι:=ι) b=CStarMatrix.ofMatrix (Matrix.kronecker a b) := by
  exact congrArg CStarMatrix.ofMatrix
    (algebra_legs_product (CStarMatrix.ofMatrix.symm a) (CStarMatrix.ofMatrix.symm b))
end KirchbergRordam.GenericRW.MatrixTensor
end

end OAI
