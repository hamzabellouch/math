import OAI.Analysis.CharacterCriterion.DropSections

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


namespace KirchbergRordam.GenericRW.OrderZero.Pair
open scoped Matrix Kronecker BigOperators
open IntervalCalculus
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (P : Pair ι κ A)
local instance : SMul ℂ P.field.Domain := (NonUnitalStarSubalgebra.instModule P.field.Domain).toSMul

def weighted : Matrix (ι×κ) (ι×κ) ℂ →ₗ[ℂ] P.field.Matrices where
  toFun m u v := Vanish.multiplier P.weight (ContinuousMap.const _ (m u v))
  map_add' m n := by ext u v t; change P.weight t*(m u v+n u v)=P.weight t*m u v+P.weight t*n u v; ring
  map_smul' z m := by ext u v t; change P.weight t*(z*m u v)=z*(P.weight t*m u v); ring

lemma weighted_coeff (u v : ι×κ) (z : ℂ) :
    P.field.coeff u v (Vanish.multiplier P.weight (ContinuousMap.const _ z)) = z • P.field.x u v := by
  change P.field.coeff u v (Vanish.multiplier P.field.p (ContinuousMap.const _ z)) = _
  rw [P.field.coeff_mul]
  have he : ContinuousMap.const unitInterval z=z • (1:C(unitInterval,ℂ)) := by ext t; simp
  rw [he,map_smul,map_one,mul_smul_comm,mul_one]

lemma weighted_single (u v : ι×κ) (z : ℂ) :
    P.weighted (Matrix.single u v z)=
      Matrix.single u v (Vanish.multiplier P.weight (ContinuousMap.const _ z)) := by
  ext i j t
  change P.weight t * (Matrix.single u v z) i j =
    ((Matrix.single u v (Vanish.multiplier P.weight (ContinuousMap.const _ z))) i j).val t
  by_cases hi : u=i <;> by_cases hj : v=j <;> simp [Matrix.single,hi,hj]

lemma weighted_kronecker (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ) :
    P.field.matrices (P.weighted (a ⊗ₖ b)) = P.left.linear a*P.right.linear b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [Matrix.add_kronecker,map_add,add_mul,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [Matrix.kronecker_add,map_add,mul_add,hb,hb']
    | h_std_basis k l w =>
      rw [Matrix.single_kronecker_single,P.weighted_single]
      change P.field.matrices (Matrix.single (i,k) (j,l)
        (Vanish.multiplier P.field.p (ContinuousMap.const _ (z*w)))) = _
      rw [P.field.matrices_single]
      change P.field.coeff (i,k) (j,l)
        (Vanish.multiplier P.weight (ContinuousMap.const _ (z*w))) = _
      rw [P.weighted_coeff,P.left.linear_single,P.right.linear_single]
      change (z*w) • (P.left.x i j*P.right.x k l) = _
      rw [smul_mul_assoc,mul_smul_comm,smul_smul]

lemma weighted_left (a : Matrix ι ι ℂ) :
    P.field.matrices (P.weighted (a ⊗ₖ (1:Matrix κ κ ℂ))) = P.left.linear a*P.right.h := by
  rw [P.weighted_kronecker,P.right.linear_one]

lemma weighted_right (b : Matrix κ κ ℂ) :
    P.field.matrices (P.weighted ((1:Matrix ι ι ℂ) ⊗ₖ b)) = P.left.h*P.right.linear b := by
  rw [P.weighted_kronecker,P.left.linear_one]

def actionLeft (a : Matrix ι ι ℂ) (m : P.field.Matrices) : P.field.Matrices :=
  fun u v => ∑ j, (@HSMul.hSMul ℂ P.field.Domain P.field.Domain inferInstance (a u.1 j) (P.field.scalarMul (1-coord) (m (j,u.2) v)))

def actionRight (a : Matrix κ κ ℂ) (m : P.field.Matrices) : P.field.Matrices :=
  fun u v => ∑ j, (@HSMul.hSMul ℂ P.field.Domain P.field.Domain inferInstance (a u.2 j) (P.field.scalarMul coord (m (u.1,j) v)))

lemma left_x_matrices (i j : ι) (m : P.field.Matrices) :
    P.left.x i j*P.field.matrices m =
      ∑ l : κ,∑ v : ι×κ, P.field.coeff (i,l) v (P.field.scalarMul (1-coord) (m (j,l) v)) := by
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.mul_sum,P.left_x_coeff,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma right_x_matrices (i j : κ) (m : P.field.Matrices) :
    P.right.x i j*P.field.matrices m =
      ∑ k : ι,∑ v : ι×κ, P.field.coeff (k,i) v (P.field.scalarMul coord (m (k,j) v)) := by
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,
    Finset.mul_sum,P.right_x_coeff,Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

lemma linear_field_left (a : Matrix ι ι ℂ) (m : P.field.Matrices) :
    P.left.linear a*P.field.matrices m = P.field.matrices (P.actionLeft a m) := by
  change (∑ i,∑ j,a i j • P.left.x i j)*P.field.matrices m = _
  conv_lhs =>
    simp only [Finset.sum_mul,smul_mul_assoc,P.left_x_matrices,Finset.smul_sum]
  change (∑ i,∑ j,∑ l,∑ v,a i j • P.field.coeff (i,l) v
    (P.field.scalarMul (1-coord) (m (j,l) v))) = _
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,actionLeft,
    Fintype.sum_prod_type,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

lemma linear_field_right (a : Matrix κ κ ℂ) (m : P.field.Matrices) :
    P.right.linear a*P.field.matrices m = P.field.matrices (P.actionRight a m) := by
  change (∑ i,∑ j,a i j • P.right.x i j)*P.field.matrices m = _
  conv_lhs =>
    simp only [Finset.sum_mul,smul_mul_assoc,P.right_x_matrices,Finset.smul_sum]
  change (∑ i,∑ j,∑ k,∑ v,a i j • P.field.coeff (k,i) v
    (P.field.scalarMul coord (m (k,j) v))) = _
  simp only [FieldCalculus.Data.matrices,LinearMap.coe_mk,AddHom.coe_mk,actionRight,
    Fintype.sum_prod_type,map_sum,map_smul]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]

end KirchbergRordam.GenericRW.OrderZero.Pair

namespace KirchbergRordam.GenericRW.OrderZero.Pair
open scoped Matrix Kronecker BigOperators ComplexOrder
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (P : Pair (Fin rankNum) (Fin (rankNum+1)) A)

lemma interior_matrices_star (m : DropSections.Interior) :
    P.field.matrices (star m) = star (P.field.matrices m) :=
  P.field.matrices_star m

lemma interior_matrices_product (m n : DropSections.Interior) :
    P.field.matrices (m*n) = P.field.matrices m * P.field.matrices n :=
  P.field.matrices_product m n

lemma interior_matrices_add (m n : DropSections.Interior) :
    P.field.matrices (m+n) = P.field.matrices m + P.field.matrices n :=
  P.field.matrices.map_add m n

lemma interior_matrices_sub (m n : DropSections.Interior) :
    P.field.matrices (m-n) = P.field.matrices m - P.field.matrices n :=
  map_sub P.field.matrices m n

lemma interior_matrices_neg (m : DropSections.Interior) :
    P.field.matrices (-m) = -P.field.matrices m :=
  map_neg P.field.matrices m

lemma interior_matrices_zero : P.field.matrices (0 : DropSections.Interior) = 0 :=
  map_zero P.field.matrices

omit [Nontrivial A] [StarOrderedRing A] in
lemma left_linear_commute_h (a : DropSections.Small2) : Commute (P.left.linear a) P.right.h := by
  change Commute (∑ i,∑ j,a i j • P.left.x i j) P.right.h
  exact Commute.sum_left _ _ _ fun i _ =>
    Commute.sum_left _ _ _ fun j _ => (P.left_commute_right_h i j).smul_left (a i j)

omit [Nontrivial A] [StarOrderedRing A] in
lemma left_right_linear_commute (a : DropSections.Small2) (b : DropSections.Small3) :
    Commute (P.left.linear a) (P.right.linear b) := by
  change Commute (∑ i,∑ j,a i j • P.left.x i j) (∑ k,∑ l,b k l • P.right.x k l)
  exact Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
    Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ =>
      ((P.commute i j k l).smul_left (a i j)).smul_right (b k l)

lemma left_product (a c : DropSections.Small2) :
    P.left.linear a*P.left.linear c = P.left.linear (a*c)-P.field.matrices
      (DropSections.weighted ((a*c) ⊗ₖ (1:DropSections.Small3))) := by
  change _=P.left.linear (a*c)-P.field.matrices (P.weighted ((a*c) ⊗ₖ 1))
  rw [P.left.linear_mul,P.weighted_left,P.left_h,sub_mul,one_mul,
    (P.left_linear_commute_h (a*c)).eq]

lemma right_product (b d : DropSections.Small3) :
    P.right.linear b*P.right.linear d = P.right.linear (b*d)-P.field.matrices
      (DropSections.weighted ((1:DropSections.Small2) ⊗ₖ (b*d))) := by
  change _=P.right.linear (b*d)-P.field.matrices (P.weighted (1 ⊗ₖ (b*d)))
  rw [P.right.linear_mul,P.weighted_right]
  have he : P.right.h=1-P.left.h := (eq_sub_iff_add_eq).mpr (by rw [add_comm,P.sum_one])
  rw [he,sub_mul,one_mul]

lemma cross_product (a : DropSections.Small2) (b : DropSections.Small3) :
    P.left.linear a*P.right.linear b=P.field.matrices (DropSections.weighted (a ⊗ₖ b)) :=
  (P.weighted_kronecker a b).symm

lemma cross_product_rev (a : DropSections.Small2) (b : DropSections.Small3) :
    P.right.linear b*P.left.linear a=P.field.matrices (DropSections.weighted (a ⊗ₖ b)) := by
  rw [← (P.left_right_linear_commute a b).eq,P.cross_product]

lemma field_left (a : DropSections.Small2) (m : DropSections.Interior) :
    P.left.linear a*P.field.matrices m=P.field.matrices (DropSections.actionLeft a m) :=
  P.linear_field_left a m

lemma field_right (b : DropSections.Small3) (m : DropSections.Interior) :
    P.right.linear b*P.field.matrices m=P.field.matrices (DropSections.actionRight b m) :=
  P.linear_field_right b m

lemma field_left_rev (a : DropSections.Small2) (m : DropSections.Interior) :
    P.field.matrices m*P.left.linear a=P.field.matrices (DropSections.actionLeftRev m a) := by
  calc
    _ = star (star (P.left.linear a) * star (P.field.matrices m)) := by
      rw [star_mul, star_star, star_star]
    _ = star (P.left.linear (star a) * P.field.matrices (star m)) :=
      congrArg star (congrArg₂ (· * ·) (P.left.linear_star a).symm
        (P.interior_matrices_star m).symm)
    _ = star (P.field.matrices (DropSections.actionLeft (star a) (star m))) :=
      congrArg star (P.field_left _ _)
    _ = _ := (P.interior_matrices_star _).symm

lemma field_right_rev (b : DropSections.Small3) (m : DropSections.Interior) :
    P.field.matrices m*P.right.linear b=P.field.matrices (DropSections.actionRightRev m b) := by
  calc
    _ = star (star (P.right.linear b) * star (P.field.matrices m)) := by
      rw [star_mul, star_star, star_star]
    _ = star (P.right.linear (star b) * P.field.matrices (star m)) :=
      congrArg star (congrArg₂ (· * ·) (P.right.linear_star b).symm
        (P.interior_matrices_star m).symm)
    _ = star (P.field.matrices (DropSections.actionRight (star b) (star m))) :=
      congrArg star (P.field_right _ _)
    _ = _ := (P.interior_matrices_star _).symm


def liftLinear : DimensionDrop23 →ₗ[ℂ] A :=
  P.left.linear.comp DropSections.endLeft + P.right.linear.comp DropSections.endRight +
    P.field.matrices.comp DropSections.interior

lemma lift_apply (f : DimensionDrop23) : P.liftLinear f=
    P.left.linear (DropSections.endLeft f)+P.right.linear (DropSections.endRight f)+
      P.field.matrices (DropSections.interior f) := rfl

lemma lift_mul (f g : DimensionDrop23) : P.liftLinear (f*g)=P.liftLinear f*P.liftLinear g := by
  simp only [P.lift_apply,DropSections.endLeft_mul,DropSections.endRight_mul,DropSections.interior_mul,
    P.interior_matrices_add,P.interior_matrices_sub,P.interior_matrices_neg,
    P.interior_matrices_product]
  simp only [add_mul,mul_add,P.left_product,P.right_product,P.cross_product,P.cross_product_rev,
    P.field_left,P.field_right,P.field_left_rev,P.field_right_rev]
  abel

lemma lift_one : P.liftLinear 1=1 := by
  rw [P.lift_apply,DropSections.endLeft_one,DropSections.endRight_one,DropSections.interior_one,
    P.interior_matrices_zero,add_zero,P.left.linear_one,P.right.linear_one,P.sum_one]

lemma lift_star (f : DimensionDrop23) : P.liftLinear (star f)=star (P.liftLinear f) := by
  simp only [P.lift_apply,DropSections.endLeft_star,DropSections.endRight_star,DropSections.interior_star,
    P.left.linear_star,P.right.linear_star,star_add]
  exact congrArg (fun value => star (P.left.linear (DropSections.endLeft f)) +
    star (P.right.linear (DropSections.endRight f)) + value)
    (P.interior_matrices_star (DropSections.interior f))


def dimensionDropHom : DimensionDrop23 →⋆ₐ[ℂ] A where
  toFun := P.liftLinear
  map_zero' := map_zero P.liftLinear
  map_one' := P.lift_one
  map_add' := map_add P.liftLinear
  map_mul' := P.lift_mul
  commutes' c := by simp only [Algebra.algebraMap_eq_smul_one,map_smul,P.lift_one]
  map_star' := P.lift_star

end KirchbergRordam.GenericRW.OrderZero.Pair

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped BigOperators CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W : WeightedUnits ι A)

lemma mul_eq_zero_of_total {z : A} (hz : W.h*z=0) (i j : ι) : W.x i j*z=0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [hz,norm_zero] using W.norm_mul_le i j z


lemma commute_of_total_commutator (y : A) (hy : Commute y W.h) (i j : ι)
    (hz : W.h*(y*W.x i j-W.x i j*y)=0) : Commute y (W.x i j) := by
  let z := y*W.x i j-W.x i j*y
  have hy' : Commute (star y) W.h := by
    simpa only [(IsSelfAdjoint.of_nonneg W.nonneg).star_eq] using hy.star_star
  have h₁ : W.x j i*z=0 := W.mul_eq_zero_of_total hz j i
  have h₂ : W.x j i*(star y*z)=0 := by
    apply W.mul_eq_zero_of_total
    rw [← mul_assoc,hy'.symm.eq,mul_assoc,hz,mul_zero]
  have he : star z*z=0 := by
    dsimp only [z] at h₁ h₂ ⊢
    rw [star_sub,star_mul,star_mul,W.star_x,sub_mul,mul_assoc (W.x j i),h₂,
      mul_assoc (star y),h₁,mul_zero,sub_self]
  have hn : ‖z‖*‖z‖=0 := by rw [← CStarRing.norm_star_mul_self,he,norm_zero]
  have zz : z=0 := norm_eq_zero.mp (mul_self_eq_zero.mp hn)
  exact sub_eq_zero.mp zz


lemma commute_of_spokes (r : ι) (hd : ∀ i,0≤W.x i i) (y : A)
    (hy : ∀ i,Commute y (W.x i r)) (hy' : ∀ i,Commute y (W.x r i)) :
    ∀ i j,Commute y (W.x i j) := by
  have hc (i : ι) : Commute y (W.x i i) := by
    have he : W.x i r*W.x r i=W.x i i*W.x i i := by simp only [W.mul_x,ite_true]
    have ht := ((hy i).mul_right (hy' i)).symm.cfcₙ_nnreal NNReal.sqrt
    change Commute (CFC.sqrt (W.x i r*W.x r i)) y at ht
    rw [he,CFC.sqrt_mul_self _ (hd i)] at ht
    exact ht.symm
  have htotal : Commute y W.h := by
    rw [← W.diagonal]
    exact Commute.sum_right Finset.univ (fun i => W.x i i) y fun i _ => hc i
  intro i j
  apply W.commute_of_total_commutator y htotal
  have hh := (hy i).mul_right (hy' j)
  rw [W.mul_x,ite_eq_left rfl] at hh
  change y*(W.h*W.x i j)=(W.h*W.x i j)*y at hh
  calc
    _=y*(W.h*W.x i j)-(W.h*W.x i j)*y := by
      rw [mul_sub,← mul_assoc,htotal.symm.eq]; noncomm_ring
    _=0 := sub_eq_zero.mpr hh

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
open scoped CStarAlgebra BigOperators
open ConeModel FlipPath HereditaryTransport RWFunctions
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]
variable (W : WeightedUnits (Fin rankNum) A)
variable {v : A} (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v)

lemma rwAlpha_diagonal (i : Fin (rankNum+1)) : 0 ≤ (W.rwAlpha hv h0).x i i := by
  change 0 ≤ star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i)*
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ i
  exact star_mul_self_nonneg _

lemma rwAlpha_corner : (W.rwAlpha hv h0).x (Fin.last rankNum) (Fin.last rankNum)=(W.rwH:A) := by
  change star (triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum)) *
    triple W.defect_selfAdjoint (W.polarVectors v) W.rwK W.rwQ (Fin.last rankNum) = (W.rwH:A)
  rw [triple_last]
  rw [show star (W.rwQ:A)=(W.rwQ:A) from congrArg Subtype.val W.rwQ_star]
  exact congrArg Subtype.val W.rwQ_sq

lemma rw_commute_corner (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.last rankNum) (Fin.last rankNum)) := by
  rw [W.rwAlpha_corner hv h0,W.rwH_val]
  change Commute (W.rwL hv h0*W.toWeightedMatrix.eval RWFunctions.j*W.x j k)
    (W.toWeightedMatrix.eval g)
  exact ((W.rwL_commute_scalar hv h0 g).mul_left
    ((Commute.all RWFunctions.j g).map W.toWeightedMatrix.eval)).mul_left
      (W.toWeightedMatrix.commute_eval j k g)

lemma rw_commute_row (i : Fin (rankNum+1)) (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x i (Fin.last rankNum)) := by
  induction i using Fin.lastCases with
  | last => exact W.rw_commute_corner hv h0 j k
  | cast i => exact W.rw_commute_spoke hv h0 i j k

lemma rw_commute_col (i : Fin (rankNum+1)) (j k : Fin rankNum) :
    Commute ((W.rwBeta hv h0).x j k) ((W.rwAlpha hv h0).x (Fin.last rankNum) i) := by
  have h := (W.rw_commute_row hv h0 i k j).star_star
  simpa only [(W.rwBeta hv h0).star_x,(W.rwAlpha hv h0).star_x] using h


def rwPair : OrderZero.Pair (Fin rankNum) (Fin (rankNum+1)) A where
  left := W.rwBeta hv h0
  right := W.rwAlpha hv h0
  commute j k := (W.rwAlpha hv h0).commute_of_spokes (Fin.last rankNum) (W.rwAlpha_diagonal hv h0) _
    (fun i => W.rw_commute_row hv h0 i j k) (fun i => W.rw_commute_col hv h0 i j k)
  sum_one := by rw [add_comm]; exact W.rw_complementary hv h0

end KirchbergRordam.GenericRW.OrderZero.WeightedUnits

namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

def rwHom (W : WeightedUnits (Fin rankNum) A) {v : A}
    (hv : star v*v=1-W.h) (h0 : W.x 0 0*v=v) : DimensionDrop23 →⋆ₐ[ℂ] A :=
  (W.rwPair hv h0).dimensionDropHom
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits
end

end OAI
