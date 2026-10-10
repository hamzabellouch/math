import OAI.Analysis.CharacterCriterion.EndpointMultiplicity

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

namespace KirchbergRordam.MultiplicativeChannel
open scoped CStarAlgebra ComplexOrder
variable (A B : Type*) [CStarAlgebra A] [CStarAlgebra B]


structure Channel where
  linear : A →ₗ[ℂ] B
  norm_le : ∀ a, ‖linear a‖≤‖a‖
  mul_eq : ∀ a b, linear a*linear b=linear 1*linear (a*b)
variable {A B}
instance : CoeFun (Channel A B) (fun _ => A→B) := ⟨fun φ => φ.linear⟩
@[simp] lemma map_zero (φ : Channel A B) : φ 0=0 := φ.linear.map_zero
@[simp] lemma map_add (φ : Channel A B) (a b : A) : φ (a+b)=φ a+φ b := φ.linear.map_add a b
@[simp] lemma map_smul (φ : Channel A B) (z : ℂ) (a : A) : φ (z • a)=z • φ a := φ.linear.map_smul z a
lemma norm_map_le (φ : Channel A B) (a : A) : ‖φ a‖≤‖a‖ := φ.norm_le a
lemma mul_eq (φ : Channel A B) (a b : A) : φ a*φ b=φ 1*φ (a*b) := φ.mul_eq a b
variable {C : Type*} [CStarAlgebra C]
def postcompose (φ : Channel A B) (f : B →⋆ₐ[ℂ] C) : Channel A C where
  linear := f.toAlgHom.toLinearMap.comp φ.linear
  norm_le a := (NonUnitalStarAlgHom.norm_apply_le f _).trans (φ.norm_le a)
  mul_eq a b := by
    change f (φ a)*f (φ b)=f (φ 1)*f (φ (a*b))
    simpa only [_root_.map_mul] using congrArg f (φ.mul_eq a b)
def normalized (φ : Channel A B) (χ : B →⋆ₐ[ℂ] ℂ) (h : χ (φ 1)≠0) : A →+* ℂ where
  toFun a := (χ (φ 1))⁻¹ * χ (φ a)
  map_zero' := by simp
  map_one' := inv_mul_cancel₀ h
  map_add' a b := by simp [mul_add]
  map_mul' a b := by
    have hm := congrArg χ (φ.mul_eq a b)
    simp only [map_mul] at hm
    calc
      _ = (χ (φ 1))⁻¹ * ((χ (φ 1))⁻¹ * (χ (φ a)*χ (φ b))) := by rw [hm]; field_simp
      _ = _ := by ring
lemma no_character_of_pair (φ ψ : Channel DimensionDrop23 B) (h : φ 1+ψ 1=1) :
    IsEmpty (B →⋆ₐ[ℂ] ℂ) := by
  refine ⟨fun χ => ?_⟩
  have hs := congrArg χ h
  simp only [_root_.map_add,_root_.map_one] at hs
  by_cases hφ : χ (φ 1)=0
  · have hψ : χ (ψ 1)≠0 := by rw [hφ,zero_add] at hs; rw [hs]; exact one_ne_zero
    exact dimensionDrop23_no_ringhom.false (normalized ψ χ hψ)
  · exact dimensionDrop23_no_ringhom.false (normalized φ χ hφ)

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
def weighted (h : C(X,ℂ)) (hh : ∀ x, ‖h x‖≤1)
    (φ : A →⋆ₐ[ℂ] C(X,B)) : Channel A C(X,B) where
  linear := {
    toFun a := ⟨fun x => h x • φ a x,h.continuous.smul (φ a).continuous⟩
    map_add' a b := by ext x; simp [smul_add]
    map_smul' z a := by ext x; simp [smul_smul,mul_comm] }
  norm_le a := by
    apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
    intro x
    change ‖h x • φ a x‖≤‖a‖
    rw [norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hh x)).trans
      ((ContinuousMap.norm_coe_le_norm (φ a) x).trans (NonUnitalStarAlgHom.norm_apply_le φ a))
  mul_eq a b := by
    ext x
    change (h x • φ a x)*(h x • φ b x)=(h x • φ 1 x)*(h x • φ (a*b) x)
    simp only [map_one,ContinuousMap.one_apply,map_mul,ContinuousMap.mul_apply,
      smul_mul_assoc,mul_smul_comm,smul_smul,one_mul]

def restrictDrop (p q : ℕ) (φ : Channel A C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (hφ : ∀ a, φ a∈PrimeDimensionDrop.subalgebra p q) :
    Channel A (PrimeDimensionDrop.Algebra p q) where
  linear := {
    toFun a := ⟨φ a,hφ a⟩
    map_add' a b := by apply Subtype.ext; exact map_add φ a b
    map_smul' z a := by apply Subtype.ext; exact map_smul φ z a }
  norm_le a := φ.norm_le a
  mul_eq a b := by apply Subtype.ext; exact φ.mul_eq a b
end KirchbergRordam.MultiplicativeChannel
namespace KirchbergRordam.DropChannels
open MatrixDiagonalPath DiagonalIteration
open MultiplicativeChannel (Channel weighted restrictDrop)
open scoped CStarAlgebra ComplexOrder
variable {D B : Type*} [CStarAlgebra D] [CStarAlgebra B]
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
def conjugated (w : X→unitary B) (hw : Continuous w) (ρ : D →⋆ₐ[ℂ] B) :
    D →⋆ₐ[ℂ] C(X,B) where
  toFun d := ⟨fun t => conj (w t) (ρ d),by
    change Continuous (fun t => (w t:B)*ρ d*star (w t:B))
    exact ((continuous_subtype_val.comp hw).mul continuous_const).mul
      (continuous_subtype_val.comp hw).star⟩
  map_zero' := by ext t; change conj (w t) (ρ 0)=0; rw [map_zero,map_zero]
  map_one' := by ext t; change conj (w t) (ρ 1)=1; rw [map_one,map_one]
  map_add' a b := by ext t; change conj (w t) (ρ (a+b))=_; rw [map_add,map_add]; rfl
  map_mul' a b := by ext t; change conj (w t) (ρ (a*b))=_; rw [map_mul,map_mul]; rfl
  commutes' z := by ext t; change conj (w t) (ρ (algebraMap ℂ D z))=_; rw [AlgHomClass.commutes,AlgHomClass.commutes]; rfl
  map_star' a := by ext t; change conj (w t) (ρ (star a))=_; rw [map_star,map_star]; rfl

def leftScalar : C(unitInterval,ℂ) :=
  ⟨fun t => ((1-(t:ℝ):ℝ):ℂ), Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)⟩
def rightScalar : C(unitInterval,ℂ) :=
  ⟨fun t => ((t:ℝ):ℂ),Complex.continuous_ofReal.comp continuous_subtype_val⟩
@[simp] lemma leftScalar_zero : leftScalar 0=1 := by norm_num [leftScalar]
@[simp] lemma leftScalar_one : leftScalar 1=0 := by norm_num [leftScalar]
@[simp] lemma rightScalar_zero : rightScalar 0=0 := rfl
@[simp] lemma rightScalar_one : rightScalar 1=1 := rfl
lemma leftScalar_norm (t : unitInterval) : ‖leftScalar t‖≤1 := by
  change ‖((1-(t:ℝ):ℝ):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr t.property.2)]
  linarith [t.property.1]
lemma rightScalar_norm (t : unitInterval) : ‖rightScalar t‖≤1 := by
  change ‖((t:ℝ):ℂ)‖≤1
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t.property.1]
  exact t.property.2
variable (p q : ℕ)
variable (w : unitInterval → unitary (PrimeDimensionDrop.Fiber p q)) (hw : Continuous w)
def left (h0 : w 0=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin p)) :
    Channel D (PrimeDimensionDrop.Algebra p q) :=
  restrictDrop p q (weighted leftScalar leftScalar_norm
    (conjugated w hw (MatrixTensor.leftMatrix.comp ρ))) (fun d => by
      constructor
      · refine ⟨ρ d,?_⟩
        change MatrixTensor.leftMatrix (ρ d)=leftScalar 0 • conj (w 0) (MatrixTensor.leftMatrix (ρ d))
        rw [leftScalar_zero,h0,conj_one,one_smul]
      · refine ⟨0,?_⟩
        change MatrixTensor.rightMatrix 0=leftScalar 1 • _
        rw [map_zero,leftScalar_one,zero_smul])
def right (h1 : w 1=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin q)) :
    Channel D (PrimeDimensionDrop.Algebra p q) :=
  restrictDrop p q (weighted rightScalar rightScalar_norm
    (conjugated w hw (MatrixTensor.rightMatrix.comp ρ))) (fun d => by
      constructor
      · refine ⟨0,?_⟩
        change MatrixTensor.leftMatrix 0=rightScalar 0 • _
        rw [map_zero,rightScalar_zero,zero_smul]
      · refine ⟨ρ d,?_⟩
        change MatrixTensor.rightMatrix (ρ d)=rightScalar 1 • conj (w 1) (MatrixTensor.rightMatrix (ρ d))
        rw [rightScalar_one,h1,conj_one,one_smul])
lemma left_apply (h0 : w 0=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin p)) (d : D) (t : unitInterval) :
    (left p q w hw h0 ρ d).val t=leftScalar t • conj (w t) (MatrixTensor.leftMatrix (ρ d)) := rfl
lemma right_apply (h1 : w 1=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin q)) (d : D) (t : unitInterval) :
    (right p q w hw h1 ρ d).val t=rightScalar t • conj (w t) (MatrixTensor.rightMatrix (ρ d)) := rfl
lemma unit_sum (h0 : w 0=1) (ρ : D →⋆ₐ[ℂ] Mat (Fin p))
    (v : unitInterval → unitary (PrimeDimensionDrop.Fiber p q)) (hv : Continuous v)
    (h1 : v 1=1) (σ : D →⋆ₐ[ℂ] Mat (Fin q)) :
    left p q w hw h0 ρ 1+right p q v hv h1 σ 1=1 := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change leftScalar t • conj (w t) (MatrixTensor.leftMatrix (ρ 1))+
    rightScalar t • conj (v t) (MatrixTensor.rightMatrix (σ 1))=1
  rw [map_one,map_one,map_one,map_one,map_one,map_one,←add_smul]
  have he : leftScalar t+rightScalar t=1 := by simp [leftScalar,rightScalar]
  rw [he,one_smul]

variable {p q w hw}
lemma norm_conjugate_commutator (u : unitary B) (r a : B) :
    ‖conj u r*a-a*conj u r‖=‖r*conj (star u) a-conj (star u) a*r‖ := by
  rw [←StarAlgEquiv.norm_map (conj (star u)) (conj u r*a-a*conj u r)]
  rw [map_sub,map_mul,map_mul,conj_star]
lemma norm_commutator_change (r x a : B) :
    ‖r*x-x*r‖≤‖r*a-a*r‖+2*‖x-a‖*‖r‖ := by
  have he : r*x-x*r=(r*a-a*r)+(r*(x-a)-(x-a)*r) := by
    simp only [mul_sub,sub_mul]; abel
  rw [he]
  calc
    _ ≤ ‖r*a-a*r‖+(‖r‖*‖x-a‖+‖x-a‖*‖r‖) :=
      (norm_add_le _ _).trans (add_le_add_right
        ((norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) _)
    _ = _ := by ring
lemma smul_commutator (z : ℂ) (r a : B) (hz : ‖z‖≤1) :
    ‖(z • r)*a-a*(z • r)‖≤‖r*a-a*r‖ := by
  rw [smul_mul_assoc,mul_smul_comm,←smul_sub,norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hz
end KirchbergRordam.DropChannels
namespace KirchbergRordam.DropChannels
open DiagonalIteration
open scoped CStarAlgebra ComplexOrder
variable {A B D : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]
lemma commutator_map_bound (φ : A →⋆ₐ[ℂ] B) (r a : A) :
    ‖φ r*φ a-φ a*φ r‖≤‖r*a-a*r‖ := by
  rw [←map_mul φ,←map_mul φ,←map_sub φ]
  exact NonUnitalStarAlgHom.norm_apply_le φ _
lemma norm_sub_conj (u : unitary A) (a b : A) :
    ‖a-conj u b‖=‖conj (star u) a-b‖ := by
  rw [←StarAlgEquiv.norm_map (conj (star u)) (a-conj u b),map_sub,conj_star]
lemma norm_twisted_difference (u v : unitary A) (a b : A) :
    ‖conj (star (u*star v)) a-b‖=‖conj (star u) a-conj (star v) b‖ := by
  have hb : conj v (conj (star v) b)=b := by simpa only [star_star] using conj_star (star v) b
  calc
    _ = ‖conj v (conj (star u) a-conj (star v) b)‖ := by
      rw [map_sub,hb,star_mul,star_star,DiagonalIteration.conj_mul]
    _ = _ := StarAlgEquiv.norm_map _ _
lemma transport_bound (ρ : D →⋆ₐ[ℂ] A) (d : D) (u : unitary A) (a b : A)
    {ε δ : ℝ} (hε : 0≤ε) (hv : ‖conj (star u) a-b‖≤ε)
    (hb : ‖ρ d*b-b*ρ d‖≤δ*‖d‖) :
    ‖conj u (ρ d)*a-a*conj u (ρ d)‖≤(δ+2*ε)*‖d‖ := by
  rw [norm_conjugate_commutator]
  calc
    _ ≤ ‖ρ d*b-b*ρ d‖+2*‖conj (star u) a-b‖*‖ρ d‖ := norm_commutator_change _ _ _
    _ ≤ δ*‖d‖+2*ε*‖d‖ := add_le_add hb
      (mul_le_mul (mul_le_mul_of_nonneg_left hv (by norm_num))
        (NonUnitalStarAlgHom.norm_apply_le ρ d) (norm_nonneg _) (by positivity))
    _ = _ := by ring
end KirchbergRordam.DropChannels

namespace KirchbergRordam.BalancedDropChannels
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open DropMatrixRepresentations DropChannels BalancedDropSystem BalancedDropMultiplicity
open scoped CStarAlgebra ComplexOrder
lemma zeroCount (p : ℕ) (hp : 2≤p) : 2≤Fintype.card (Unit ⊕ (Q p×Fin (p-1))) := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,Q]
  have h : 1≤p-1 := by omega
  nlinarith
lemma oneCount (p : ℕ) (hp : 2≤p) : 2≤Fintype.card (Unit ⊕ (P p×Fin (p-1))) := by
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_unit,P]
  have h : 1≤p-1 := by omega
  nlinarith
def zeroRep (p : ℕ) (hp : 2≤p) (v : unitary (PrimeDimensionDrop.Fiber p (p+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (P (next p)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter p hp)).toStarAlgHom.comp
    (leftRep (P:=P p) (Q:=Q p) (R:=Fin (p-1)) (zeroCount p hp) v)
def oneRep (p : ℕ) (hp : 2≤p) (v : unitary (PrimeDimensionDrop.Fiber p (p+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Q (next p)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (oneOuter p hp)).toStarAlgHom.comp
    (rightRep (P:=P p) (Q:=Q p) (R:=Fin (p-1)) (oneCount p hp) v)
lemma zeroRep_bound (p : ℕ) (hp : 2≤p) [NeZero p]
    (v : unitary (PrimeDimensionDrop.Fiber p (p+1)))
    (f : PrimeDimensionDrop.Algebra p (p+1)) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 0‖≤ε) :
    ‖MatrixTensor.leftMatrix (κ:=Q (next p)) (zeroRep p hp v d)*(step p hp f).val 0-
      (step p hp f).val 0*MatrixTensor.leftMatrix (κ:=Q (next p)) (zeroRep p hp v d)‖≤2*ε*‖d‖ := by
  have he : (step p hp f).val 0=MatrixTensor.leftMatrix (κ:=Q (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter p hp)
        (sumBlock (leftValue p (p+1) f,block (fun _ : Fin (p-1) => f.val half)))) :=
    rawStep_zero p hp f.val _ (leftValue_spec p (p+1) f)
  rw [he]
  let φ := (MatrixTensor.leftMatrix (κ:=Q (next p))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter p hp)).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply leftRep_bound (zeroCount p hp)
  rw [leftValue_spec,norm_sub_conj]
  exact hf
lemma oneRep_bound (p : ℕ) (hp : 2≤p) [NeZero p]
    (v : unitary (PrimeDimensionDrop.Fiber p (p+1)))
    (f : PrimeDimensionDrop.Algebra p (p+1)) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 1‖≤ε) :
    ‖MatrixTensor.rightMatrix (ι:=P (next p)) (oneRep p hp v d)*(step p hp f).val 1-
      (step p hp f).val 1*MatrixTensor.rightMatrix (ι:=P (next p)) (oneRep p hp v d)‖≤2*ε*‖d‖ := by
  have he : (step p hp f).val 1=MatrixTensor.rightMatrix (ι:=P (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (oneOuter p hp)
        (sumBlock (rightValue p (p+1) f,block (fun _ : Fin (p-1) => f.val half)))) :=
    rawStep_one p hp f.val _ (rightValue_spec p (p+1) f)
  rw [he]
  let φ := (MatrixTensor.rightMatrix (ι:=P (next p))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (oneOuter p hp)).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply rightRep_bound (oneCount p hp)
  rw [rightValue_spec,norm_sub_conj]
  exact hf
end KirchbergRordam.BalancedDropChannels
end

end OAI
