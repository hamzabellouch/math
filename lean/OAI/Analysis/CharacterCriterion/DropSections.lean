import OAI.Analysis.CharacterCriterion.FieldCalculus

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


namespace KirchbergRordam.GenericRW.DropSections
open scoped Matrix Kronecker BigOperators ComplexOrder
open IntervalCalculus
abbrev Ix := Fin rankNum × Fin (rankNum+1)
abbrev Scalar := C(unitInterval,ℂ)
abbrev Mat := Matrix Ix Ix Scalar
abbrev Small2 := Matrix (Fin rankNum) (Fin rankNum) ℂ
abbrev Small3 := Matrix (Fin (rankNum+1)) (Fin (rankNum+1)) ℂ


def entries : C(unitInterval,M6) →⋆ₐ[ℂ] Mat where
  toFun f i j := ⟨fun t => f t i j, by
    exact (continuous_apply j).comp ((continuous_apply i).comp
      f.continuous)⟩
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' f g := by
    ext i j t
    change (∑ k, f t i k * g t k j) = ((∑ k, _ * _) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply]
    rfl
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' f := by ext i j t; rfl

lemma entries_apply (f : C(unitInterval,M6)) (i j : Ix) (t : unitInterval) :
    entries f i j t = f t i j := rfl


def constMat : Matrix Ix Ix ℂ →⋆ₐ[ℂ] Mat where
  toFun a i j := ContinuousMap.const _ (a i j)
  map_zero' := by ext i j t; rfl
  map_one' := by ext i j t; by_cases h : i=j <;> simp [Matrix.one_apply,h]
  map_add' _ _ := by ext i j t; rfl
  map_mul' a b := by
    ext i j t
    change (∑ k, a i k * b k j) =
      ((∑ k, ContinuousMap.const _ (a i k) * ContinuousMap.const _ (b k j)) : Scalar) t
    simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.const_apply]
  commutes' c := by ext i j t; by_cases h : i=j <;> simp [Algebra.algebraMap_eq_smul_one,h]
  map_star' _ := by ext i j t; rfl

def leftConst : Small2 →⋆ₐ[ℂ] Mat := constMat.comp leftMatrixAlgebra

def rightConst : Small3 →⋆ₐ[ℂ] Mat := constMat.comp rightMatrixAlgebra


def times (p : Scalar) : Mat →ₗ[ℂ] Mat where
  toFun a i j := p*a i j
  map_add' a b := by ext i j t; change p t*(a i j t+b i j t)=p t*a i j t+p t*b i j t; ring
  map_smul' c a := by ext i j t; change p t*(c*a i j t)=c*(p t*a i j t); ring

lemma times_mul (p q : Scalar) (a b : Mat) : times p a*times q b=times (p*q) (a*b) := by
  ext i j t
  change ((∑ k, (p * a i k) * (q * b k j)) : Scalar) t =
    ((p * q) * (∑ k, a i k * b k j)) t
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma mul_times (p : Scalar) (a b : Mat) : a*times p b=times p (a*b) := by
  simpa only [one_mul,show times 1 a=a from by ext i j; exact one_mul _] using times_mul 1 p a b

lemma times_mul_left (p : Scalar) (a b : Mat) : times p a*b=times p (a*b) := by
  simpa only [mul_one,show times 1 b=b from by ext i j; exact one_mul _] using times_mul p 1 a b

lemma times_times (p q : Scalar) (a : Mat) : times p (times q a)=times (p*q) a := by
  ext i j; exact (mul_assoc _ _ _).symm

def leftPart : Small2 →ₗ[ℂ] Mat := (times (1-coord)).comp leftConst.toLinearMap
def rightPart : Small3 →ₗ[ℂ] Mat := (times coord).comp rightConst.toLinearMap


def endLeft : DimensionDrop23 →ₗ[ℂ] Small2 where
  toFun f i j := entries f.val (i,0) (j,0) 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def endRight : DimensionDrop23 →ₗ[ℂ] Small3 where
  toFun f i j := entries f.val (0,i) (0,j) 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma at_zero (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 0 = leftMatrixAlgebra (endLeft f) i j := by
  obtain ⟨a,ha⟩ := f.property.1
  change leftMatrix a = f.val 0 at ha
  have he : endLeft f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 0) (u,0) (v,0) = _
    rw [← ha]
    change (CStarMatrix.ofMatrixL.symm a u v)*(1:ℂ)=_
    exact mul_one _
  rw [he,entries_apply,← ha]
  rfl

lemma at_one (f : DimensionDrop23) (i j : Ix) :
    entries f.val i j 1 = rightMatrixAlgebra (endRight f) i j := by
  obtain ⟨a,ha⟩ := f.property.2
  change rightMatrix a = f.val 1 at ha
  have he : endRight f = CStarMatrix.ofMatrixL.symm a := by
    ext u v
    change CStarMatrix.ofMatrixL.symm (f.val 1) (0,u) (0,v) = _
    rw [← ha]
    change (1:ℂ)*(CStarMatrix.ofMatrixL.symm a u v)=_
    exact one_mul _
  rw [he,entries_apply,← ha]
  rfl



def weight : Scalar := (1-coord)*coord
abbrev InteriorScalar := Vanish.Functions {t | weight t=0}
abbrev Interior := Matrix Ix Ix InteriorScalar

omit instSize in
lemma weight_zero
    [KirchbergRordam.GenericRW.Size]
    (t : unitInterval) : weight t=0 ↔ t=0 ∨ t=1 := by
  change (1-(t:ℝ):ℂ)*(t:ℝ)=0 ↔ _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h|h
    · right
      apply Subtype.ext
      exact_mod_cast (sub_eq_zero.mp h).symm
    · left
      apply Subtype.ext
      exact_mod_cast h
  · rintro (rfl|rfl) <;> simp


def embed : Interior →ₗ[ℂ] Mat where
  toFun m i j := m i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma embed_injective : Function.Injective embed := by
  intro a b h
  funext i j
  apply Subtype.ext
  exact congr_fun (congr_fun h i) j

lemma embed_mul (m n : Interior) : embed (m*n)=embed m*embed n := by
  ext i j t
  change ((∑ k, m i k*n k j : InteriorScalar) : Scalar) t =
    (∑ k, (m i k : Scalar)*(n k j : Scalar)) t
  simp

lemma embed_star (m : Interior) : embed (star m)=star (embed m) := rfl

lemma interior_at_zero (m : Interior) (i j : Ix) : embed m i j 0 = 0 :=
  (m i j).property 0 ((weight_zero 0).mpr (Or.inl rfl))

lemma interior_at_one (m : Interior) (i j : Ix) : embed m i j 1 = 0 :=
  (m i j).property 1 ((weight_zero 1).mpr (Or.inr rfl))

def residual : DimensionDrop23 →ₗ[ℂ] Mat :=
  entries.toLinearMap.comp dimensionDropSubalgebra.subtype.toLinearMap -
    leftPart.comp endLeft - rightPart.comp endRight


def interior : DimensionDrop23 →ₗ[ℂ] Interior where
  toFun f i j := ⟨residual f i j, by
    intro t ht
    rcases (weight_zero t).mp ht with rfl|rfl
    · change entries f.val i j 0 - (1-coord 0)*leftMatrixAlgebra (endLeft f) i j -
        coord 0*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_zero]
    · change entries f.val i j 1 - (1-coord 1)*leftMatrixAlgebra (endLeft f) i j -
        coord 1*rightMatrixAlgebra (endRight f) i j = 0
      simp [at_one]⟩
  map_add' f g := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_add residual f g) i) j
  map_smul' c f := by
    funext i j
    apply Subtype.ext
    exact congr_fun (congr_fun (map_smul residual c f) i) j

lemma decomposition (f : DimensionDrop23) :
    entries f.val = leftPart (endLeft f)+rightPart (endRight f)+embed (interior f) := by
  change entries f.val = leftPart (endLeft f)+rightPart (endRight f)+
    (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  abel



lemma endLeft_mul (f g : DimensionDrop23) : endLeft (f*g)=endLeft f*endLeft g := by
  ext i j
  change ∑ u : Ix, entries f.val (i,0) u 0*entries g.val u (j,0) 0 = _
  simp [at_zero,leftMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]

lemma endRight_mul (f g : DimensionDrop23) : endRight (f*g)=endRight f*endRight g := by
  ext i j
  change ∑ u : Ix, entries f.val (0,i) u 1*entries g.val u (0,j) 1 = _
  simp [at_one,rightMatrixAlgebra,Fintype.sum_prod_type,Matrix.mul_apply,Matrix.one_apply]

lemma endLeft_one : endLeft 1=1 := by
  ext i j
  change (1 : M6) (i,0) (j,0) = (1 : Small2) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]

lemma endRight_one : endRight 1=1 := by
  ext i j
  change (1 : M6) (0,i) (0,j) = (1 : Small3) i j
  simp [CStarMatrix.one_apply,Matrix.one_apply]

lemma endLeft_star (f : DimensionDrop23) : endLeft (star f)=star (endLeft f) := rfl
lemma endRight_star (f : DimensionDrop23) : endRight (star f)=star (endRight f) := rfl

lemma times_star (p : Scalar) (m : Mat) : star (times p m)=times (star p) (star m) := by
  ext i j t
  change star (p t*m j i t)=star (p t)*star (m j i t)
  rw [star_mul,mul_comm]

lemma leftPart_star (a : Small2) : leftPart (star a)=star (leftPart a) := by
  change times (1-coord) (leftConst (star a))=star (times (1-coord) (leftConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [star_sub,star_one,hc]

lemma rightPart_star (a : Small3) : rightPart (star a)=star (rightPart a) := by
  change times coord (rightConst (star a))=star (times coord (rightConst a))
  rw [times_star,map_star]
  have hc : star coord=coord := by ext t; simp [coord]
  rw [hc]

lemma interior_star (f : DimensionDrop23) : interior (star f)=star (interior f) := by
  apply embed_injective
  change entries (star f.val)-leftPart (endLeft (star f))-rightPart (endRight (star f)) =
    star (entries f.val-leftPart (endLeft f)-rightPart (endRight f))
  rw [map_star,endLeft_star,endRight_star,leftPart_star,rightPart_star,star_sub,star_sub]

lemma interior_one : interior 1=0 := by
  apply embed_injective
  change entries 1-leftPart (endLeft 1)-rightPart (endRight 1)=0
  simp only [show entries 1=1 from entries.map_one',endLeft_one,endRight_one]
  change 1-times (1-coord) (leftConst 1)-times coord (rightConst 1)=0
  rw [show leftConst 1=1 from leftConst.map_one',show rightConst 1=1 from rightConst.map_one']
  ext i j t
  change (1:Mat) i j t-((1-coord)* (1:Mat) i j) t-(coord*(1:Mat) i j) t=0
  simp only [ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.one_apply]
  ring


local instance : SMul ℂ InteriorScalar := (NonUnitalStarSubalgebra.instModule InteriorScalar).toSMul

def weighted : Matrix Ix Ix ℂ →ₗ[ℂ] Interior where
  toFun m u v := Vanish.multiplier weight (ContinuousMap.const _ (m u v))
  map_add' m n := by ext u v t; change weight t*(m u v+n u v)=weight t*m u v+weight t*n u v; ring
  map_smul' z m := by ext u v t; change weight t*(z*m u v)=z*(weight t*m u v); ring

lemma embed_weighted (m : Matrix Ix Ix ℂ) : embed (weighted m)=times weight (constMat m) := rfl

def scalarMul (p : Scalar) (f : InteriorScalar) : InteriorScalar :=
  ⟨p*f.val,by intro t ht; simp [f.property t ht]⟩

def actionLeft (a : Small2) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v)

def actionRight (a : Small3) (m : Interior) : Interior :=
  fun u v => ∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v)

lemma embed_actionLeft (a : Small2) (m : Interior) :
    embed (actionLeft a m)=leftPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.1 j) • scalarMul (1-coord) (m (j,u.2) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, ((1-coord) * ContinuousMap.const _ (a u.1 k.1 * (1 : Small3) u.2 k.2)) *
      (m k v).val) : Scalar) t
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]

lemma embed_actionRight (a : Small3) (m : Interior) :
    embed (actionRight a m)=rightPart a*embed m := by
  ext u v t
  change ((∑ j, (a u.2 j) • scalarMul coord (m (u.1,j) v) : InteriorScalar) : Scalar) t =
    ((∑ k : Ix, (coord * ContinuousMap.const _ ((1 : Small2) u.1 k.1 * a u.2 k.2)) *
      (m k v).val) : Scalar) t
  rcases u with ⟨u1,u2⟩
  simp [scalarMul, Fintype.sum_prod_type, Matrix.one_apply, mul_left_comm, mul_comm]

def actionLeftRev (m : Interior) (a : Small2) : Interior := star (actionLeft (star a) (star m))
def actionRightRev (m : Interior) (a : Small3) : Interior := star (actionRight (star a) (star m))

lemma embed_actionLeftRev (m : Interior) (a : Small2) :
    embed (actionLeftRev m a)=embed m*leftPart a := by
  rw [actionLeftRev,embed_star,embed_actionLeft,embed_star,leftPart_star]
  exact (star_mul (star (leftPart a)) (star (embed m))).trans (by rw [star_star,star_star])

lemma embed_actionRightRev (m : Interior) (a : Small3) :
    embed (actionRightRev m a)=embed m*rightPart a := by
  rw [actionRightRev,embed_star,embed_actionRight,embed_star,rightPart_star]
  exact (star_mul (star (rightPart a)) (star (embed m))).trans (by rw [star_star,star_star])

lemma leftPart_mul (a c : Small2) :
    leftPart a*leftPart c=leftPart (a*c)-embed (weighted ((a*c) ⊗ₖ (1:Small3))) := by
  change times (1-coord) (leftConst a)*times (1-coord) (leftConst c)=
    times (1-coord) (leftConst (a*c))-times weight (constMat ((a*c) ⊗ₖ (1:Small3)))
  rw [times_mul,← map_mul]
  ext i j t
  change ((1-coord t)*(1-coord t))*leftMatrixAlgebra (a*c) i j =
    (1-coord t)*leftMatrixAlgebra (a*c) i j-((1-coord t)*coord t)*leftMatrixAlgebra (a*c) i j
  ring

lemma rightPart_mul (b d : Small3) :
    rightPart b*rightPart d=rightPart (b*d)-embed (weighted ((1:Small2) ⊗ₖ (b*d))) := by
  change times coord (rightConst b)*times coord (rightConst d)=
    times coord (rightConst (b*d))-times weight (constMat ((1:Small2) ⊗ₖ (b*d)))
  rw [times_mul,← map_mul]
  ext i j t
  change (coord t*coord t)*rightMatrixAlgebra (b*d) i j =
    coord t*rightMatrixAlgebra (b*d) i j-((1-coord t)*coord t)*rightMatrixAlgebra (b*d) i j
  ring

lemma leftConst_rightConst (a : Small2) (b : Small3) :
    leftConst a*rightConst b=constMat (a ⊗ₖ b) := by
  change constMat (a ⊗ₖ (1:Small3))*constMat ((1:Small2) ⊗ₖ b)=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]

lemma rightConst_leftConst (a : Small2) (b : Small3) :
    rightConst b*leftConst a=constMat (a ⊗ₖ b) := by
  change constMat ((1:Small2) ⊗ₖ b)*constMat (a ⊗ₖ (1:Small3))=_
  rw [← map_mul,← Matrix.mul_kronecker_mul,mul_one,one_mul]

lemma leftPart_rightPart (a : Small2) (b : Small3) :
    leftPart a*rightPart b=embed (weighted (a ⊗ₖ b)) := by
  change times (1-coord) (leftConst a)*times coord (rightConst b)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,leftConst_rightConst]
  rfl

lemma rightPart_leftPart (a : Small2) (b : Small3) :
    rightPart b*leftPart a=embed (weighted (a ⊗ₖ b)) := by
  change times coord (rightConst b)*times (1-coord) (leftConst a)=times weight (constMat (a ⊗ₖ b))
  rw [times_mul,rightConst_leftConst,mul_comm coord]
  rfl


lemma interior_mul (f g : DimensionDrop23) :
    interior (f*g) = -weighted ((endLeft f*endLeft g) ⊗ₖ (1:Small3))-
      weighted ((1:Small2) ⊗ₖ (endRight f*endRight g))+
      weighted (endLeft f ⊗ₖ endRight g)+weighted (endLeft g ⊗ₖ endRight f)+
      actionLeft (endLeft f) (interior g)+actionRight (endRight f) (interior g)+
      actionLeftRev (interior f) (endLeft g)+actionRightRev (interior f) (endRight g)+
      interior f*interior g := by
  apply embed_injective
  change entries ((f*g).val)-leftPart (endLeft (f*g))-rightPart (endRight (f*g)) = _
  rw [show entries ((f*g).val)=entries f.val*entries g.val from entries.map_mul' f.val g.val,
    endLeft_mul,endRight_mul,decomposition f,decomposition g]
  simp only [map_add,map_sub,map_neg,embed_actionLeft,embed_actionRight,
    embed_actionLeftRev,embed_actionRightRev,embed_mul,mul_add,add_mul,
    leftPart_mul,rightPart_mul,leftPart_rightPart,rightPart_leftPart]
  abel

end KirchbergRordam.GenericRW.DropSections
end

end OAI
