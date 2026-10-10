import OAI.Analysis.CharacterCriterion.CubeCalculus

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


namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra BigOperators ComplexOrder
open ConeModel _root_.OAI.KirchbergRordam.GenericRW.MaxTensor
abbrev Cube (n : ℕ) := Fin (n+1)→unitInterval
abbrev Tensor (n : ℕ) := powerPack Cone n
abbrev Fiber (n : ℕ) := PauliPower.CMat n
abbrev Label (n : ℕ) := PauliPower.Label n

def post {X A B : Type*} [TopologicalSpace X] [CStarAlgebra A] [CStarAlgebra B]
    (φ : A→⋆ₐ[ℂ] B) : C(X,A)→⋆ₐ[ℂ] C(X,B) where
  toFun f := ⟨φ∘f,(map_continuous φ).comp f.continuous⟩
  map_zero' := by ext t; exact map_zero φ
  map_one' := by ext t; exact map_one φ
  map_add' f g := by ext t; exact map_add φ _ _
  map_mul' f g := by ext t; exact map_mul φ _ _
  commutes' c := by ext t; exact φ.commutes c
  map_star' f := by ext t; exact map_star φ _

def first (n : ℕ) : C(Cube n,unitInterval) := ⟨fun t=>t 0,continuous_apply 0⟩
def tail (n : ℕ) : C(Cube (n+1),Cube n) := ⟨fun t i=>t i.succ,by fun_prop⟩

def matLeg : (n : ℕ)→Fin (n+1)→M2→⋆ₐ[ℂ] Fiber n
  | 0,_ => StarAlgHom.id ℂ M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrix
      (fun j=>MatrixTensor.rightMatrix.comp (matLeg n j)) i

def repr : (n : ℕ)→Tensor n→⋆ₐ[ℂ] C(Cube n,Fiber n)
  | 0 => ((first 0).compStarAlgHom' ℂ M2).comp coneSubalgebra.subtype
  | n+1 =>
    let l := (post (MatrixTensor.leftMatrix (κ:=PauliPower.Row n))).comp
      (((first (n+1)).compStarAlgHom' ℂ M2).comp coneSubalgebra.subtype)
    let r := (post (MatrixTensor.rightMatrix (ι:=Fin Size.n))).comp
      (((tail n).compStarAlgHom' ℂ (Fiber n)).comp (repr n))
    lift l r (by intro a b; apply ContinuousMap.ext; intro t; exact (MatrixTensor.legs_commute _ _).eq)

lemma repr_left (n : ℕ) (a : Cone) (t : Cube (n+1)) :
    repr (n+1) (includeLeft a) t=MatrixTensor.leftMatrix (κ:=PauliPower.Row n) ((a:C(unitInterval,M2)) (t 0)) := by
  exact DFunLike.congr_fun (DFunLike.congr_fun (lift_includeLeft _ _ _) a) t
lemma repr_right (n : ℕ) (b : Tensor n) (t : Cube (n+1)) :
    repr (n+1) (includeRight b) t=MatrixTensor.rightMatrix (ι:=Fin Size.n) (repr n b (tail n t)) := by
  exact DFunLike.congr_fun (DFunLike.congr_fun (lift_includeRight _ _ _) b) t
lemma repr_leg (n : ℕ) (i : Fin (n+1)) (a : Cone) (t : Cube n) :
    repr n (leg Cone n i a) t=matLeg n i ((a:C(unitInterval,M2)) (t i)) := by
  induction n with
  | zero =>
    change (a:C(unitInterval,M2)) (t 0)=(a:C(unitInterval,M2)) (t i)
    rw [Fin.eq_zero i]
  | succ n ih =>
    induction i using Fin.cases with
    | zero => exact repr_left n a t
    | succ i =>
      change repr (n+1) (includeRight (leg Cone n i a)) t=_
      rw [repr_right,ih]
      rfl

lemma scalar_leg_commute (n : ℕ) (i : Fin (n+1)) (f : C(unitInterval,ℂ)) (a : Tensor n) :
    Commute (leg Cone n i (scalar f)) a := by
  apply commute_of_power_legs n (StarAlgHom.id ℂ (Tensor n)) _ _ a
  intro j b
  change Commute (leg Cone n i (scalar f)) (leg Cone n j b)
  by_cases hij : i=j
  · subst j; exact (ConePauli.scalar_commute f b).map (leg Cone n i)
  · exact commute_legs Cone n i j hij (scalar f) b

def scalarLeg (n : ℕ) (i : Fin (n+1)) : C(unitInterval,ℂ)→⋆ₐ[ℂ] Tensor n :=
  (leg Cone n i).comp scalar
def κ (n : ℕ) : C(Cube n,ℂ)→⋆ₐ[ℂ] Tensor n :=
  CentralCalculus.hom (scalarLeg n) (scalar_leg_commute n)
lemma κ_commute (n : ℕ) (f : C(Cube n,ℂ)) (a : Tensor n) : Commute (κ n f) a :=
  CentralCalculus.hom_commute _ _ f a
lemma κ_coordinate (n : ℕ) (i : Fin (n+1)) (f : C(unitInterval,ℂ)) :
    κ n (JointCalculus.coordinate i f)=leg Cone n i (scalar f) :=
  CentralCalculus.hom_coordinate _ _ i f

def point {X A : Type*} [TopologicalSpace X] [CStarAlgebra A] (t : X) : C(X,A)→⋆ₐ[ℂ] A where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
lemma repr_κ (n : ℕ) (f : C(Cube n,ℂ)) (t : Cube n) :
    repr n (κ n f) t=algebraMap ℂ (Fiber n) (f t) := by
  let φ := ((point t).comp (repr n)).comp (κ n)
  let ψ := (StarAlgHom.ofId ℂ (Fiber n)).comp (point (A:=ℂ) t)
  have he : φ=ψ := by
    apply CubeCalculus.ext_coord
    intro i
    change repr n (κ n (JointCalculus.coordinate i
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩)) t=_
    rw [κ_coordinate,repr_leg,scalar_apply]
    exact (matLeg n i).commutes _
  exact DFunLike.congr_fun he f

lemma κ_first (n : ℕ) (f : C(unitInterval,ℂ)) :
    κ (n+1) (f.comp (first (n+1)))=includeLeft (scalar f) := κ_coordinate (n+1) 0 f
lemma κ_tail (n : ℕ) (f : C(Cube n,ℂ)) :
    κ (n+1) (f.comp (tail n))=includeRight (κ n f) := by
  let φ := (κ (n+1)).comp ((tail n).compStarAlgHom' ℂ ℂ)
  let ψ := (includeRight (A:=Cone)).comp (κ n)
  have he : φ=ψ := by
    apply CubeCalculus.ext_coord
    intro i
    change κ (n+1) (JointCalculus.coordinate i.succ
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩)=
      includeRight (κ n (JointCalculus.coordinate i
      ⟨fun s:unitInterval=>((s:ℝ):ℂ),by fun_prop⟩))
    rw [κ_coordinate,κ_coordinate]
    rfl
  exact DFunLike.congr_fun he f

def p : (n : ℕ)→Label n→C(Cube n,ℂ)
  | 0,a => (ConePauli.p a).comp (first 0)
  | n+1,a => ((ConePauli.p a.1).comp (first (n+1)))*((p n a.2).comp (tail n))
def u : (n : ℕ)→Label n→Tensor n
  | 0,a => ConePauli.u a
  | n+1,a => includeLeft (ConePauli.u a.1)*includeRight (u n a.2)

omit instSize instPauliData in
lemma commuting_gram
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [CStarAlgebra E] (φ : A→⋆ₐ[ℂ] E) (ψ : B→⋆ₐ[ℂ] E)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (x:A) (y:B) :
    star (φ x*ψ y)*(φ x*ψ y)=φ (star x*x)*ψ (star y*y) := by
  rw [star_mul,← map_star ψ y,← map_star φ x]
  calc
    ψ (star y)*φ (star x)*(φ x*ψ y)=ψ (star y)*φ (star x*x)*ψ y := by
      rw [map_mul]; noncomm_ring
    _ = _ := by rw [← (hc (star x*x) (star y)).eq,mul_assoc,← map_mul]
lemma gram_product {A B : Type*} [CStarAlgebra A] [CStarAlgebra B] (x:A) (y:B) :
    star (includeLeft (B:=B) x*includeRight (A:=A) y)*(includeLeft (B:=B) x*includeRight (A:=A) y)=
      includeLeft (B:=B) (star x*x)*includeRight (A:=A) (star y*y) :=
  commuting_gram includeLeft includeRight legs_commute x y

lemma u_gram (n : ℕ) (a : Label n) : star (u n a)*u n a=κ n (star (p n a)*p n a) := by
  induction n with
  | zero =>
    rw [show star (p 0 a)*p 0 a=JointCalculus.coordinate (0:Fin 1)
      (star (ConePauli.p a)*ConePauli.p a) from rfl,κ_coordinate]
    exact ConePauli.u_gram a
  | succ n ih =>
    have hp : star (p (n+1) a)*p (n+1) a=
        (star (ConePauli.p a.1)*ConePauli.p a.1).comp (first (n+1))*
          (star (p n a.2)*p n a.2).comp (tail n) := by
      apply ContinuousMap.ext; intro t
      simp only [p,ContinuousMap.mul_apply,ContinuousMap.star_apply,ContinuousMap.comp_apply,star_mul]
      ring
    rw [hp,map_mul,κ_first,κ_tail]
    exact (gram_product (ConePauli.u a.1) (u n a.2)).trans
      (congrArg₂ (fun x y => includeLeft (B := Tensor n) x * includeRight (A := Cone) y)
        (ConePauli.u_gram a.1) (ih a.2))

lemma ce_product (n : ℕ) (a : Label (n+1)) :
    MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (ConePauli.E a.1)*MatrixTensor.rightMatrix (ι:=Fin Size.n) (PauliPower.ce n a.2)=
      PauliPower.ce (n+1) a := MatrixTensor.legs_product _ _
lemma repr_u (n : ℕ) (a : Label n) (t : Cube n) :
    repr n (u n a) t=p n a t • PauliPower.ce n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let ρ : MaxTensor.Algebra Cone (Tensor n)→⋆ₐ[ℂ] C(Cube (n+1),Fiber (n+1)) := repr (n+1)
    change ρ (includeLeft (ConePauli.u a.1)*includeRight (u n a.2)) t=_
    rw [map_mul]
    change (repr (n+1) (includeLeft (ConePauli.u a.1))*
      repr (n+1) (includeRight (u n a.2))) t=_
    rw [ContinuousMap.mul_apply,repr_left,repr_right,ih]
    change MatrixTensor.leftMatrix (κ:=PauliPower.Row n) (ConePauli.p a.1 (t 0) • ConePauli.E a.1)*
      MatrixTensor.rightMatrix (ι:=Fin Size.n) (p n a.2 (tail n t) • PauliPower.ce n a.2)=_
    rw [map_smul,map_smul,smul_mul_smul_comm,ce_product]
    rfl

def expansion (n : ℕ) : (Label n→C(Cube n,ℂ))→ₗ[ℂ] Tensor n where
  toFun f := ∑ i,κ n (f i)*u n i
  map_add' f g := by simp [map_add,add_mul,Finset.sum_add_distrib]
  map_smul' c f := by simp [map_smul,Finset.smul_sum]

lemma expansion_zero (f : Pauli.Label→C(unitInterval,ℂ)) :
    expansion 0 (fun i => (f i).comp (first 0))=ConePauli.expansion f := by
  dsimp only [expansion,ConePauli.expansion,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (·*ConePauli.u i) (κ_coordinate 0 (0:Fin 1) (f i))

lemma expansion_product (n : ℕ) (f : Pauli.Label→C(unitInterval,ℂ)) (g : Label n→C(Cube n,ℂ)) :
    includeLeft (ConePauli.expansion f)*includeRight (expansion n g)=
      expansion (n+1) (fun a => (f a.1).comp (first (n+1))*(g a.2).comp (tail n)) := by
  let κ' : C(Cube (n+1),ℂ)→⋆ₐ[ℂ] MaxTensor.Algebra Cone (Tensor n) := κ (n+1)
  have result : (includeLeft (∑ i,scalar (f i)*ConePauli.u i)*includeRight (∑ j,κ n (g j)*u n j) :
    MaxTensor.Algebra Cone (Tensor n)) =
    ∑ a:Pauli.Label×Label n,κ' ((f a.1).comp (first (n+1))*(g a.2).comp (tail n))*
      (includeLeft (ConePauli.u a.1)*includeRight (u n a.2)) := by
    rw [map_sum,map_sum,Finset.sum_mul,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul]
    have hfirst : ∀ h,κ' (h.comp (first (n+1)))=includeLeft (scalar h) := κ_first n
    have htail : ∀ h,κ' (h.comp (tail n))=includeRight (κ n h) := κ_tail n
    rw [hfirst,htail]
    have hc := (legs_commute (ConePauli.u i) (κ n (g j))).eq
    calc
      _ = includeLeft (scalar (f i))*(includeLeft (ConePauli.u i)*includeRight (κ n (g j)))*
        includeRight (u n j) := by noncomm_ring
      _ = _ := by rw [hc]; noncomm_ring
  exact result

lemma dense (n : ℕ) : DenseRange (expansion n) := by
  induction n with
  | zero =>
    let S : Submodule ℂ (Tensor 0) := (LinearMap.range (expansion 0)).topologicalClosure
    have hc : IsClosed (S:Set (Tensor 0)) := Submodule.isClosed_topologicalClosure _
    intro x
    change x∈S
    refine ConePauli.dense.induction_on x hc ?_
    intro f
    apply (LinearMap.range (expansion 0)).le_topologicalClosure
    exact ⟨fun i=>(f i).comp (first 0),expansion_zero f⟩
  | succ n ih =>
    let S : Submodule ℂ (Tensor (n+1)) := (LinearMap.range (expansion (n+1))).topologicalClosure
    have hc : IsClosed (S:Set (Tensor (n+1))) := Submodule.isClosed_topologicalClosure _
    have hp (a : Cone) (b : Tensor n) : includeLeft a*includeRight b ∈ S := by
      refine ConePauli.dense.induction_on a
        (hc.preimage ((map_continuous (includeLeft (B:=Tensor n))).mul continuous_const)) ?_
      intro f
      refine ih.induction_on b
        (hc.preimage (continuous_const.mul (map_continuous (includeRight (A:=Cone))))) ?_
      intro g
      rw [expansion_product]
      exact (LinearMap.range (expansion (n+1))).le_topologicalClosure ⟨_,rfl⟩
    intro x
    change x∈S
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact hc
    | ih x =>
      let inclusion : (Cone ⊗[ℂ] Tensor n) →ₗ[ℂ] Tensor (n+1) :=
        of.toLinearMap.comp rawEquiv.toStarAlgHom.toLinearMap
      suffices ∀ tensor : Cone ⊗[ℂ] Tensor n, inclusion tensor ∈ S from this x
      intro tensor
      induction tensor using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
      | tmul a b =>
        change of (a ⊗ₜ[ℂ] b) ∈ S
        rw [of_tmul]
        exact hp a b


lemma faithful (n : ℕ) : Function.Injective (repr n) :=
  CubeFrame.faithful (κ n) (repr n) (p n) (u n) (PauliPower.ce n)
    (κ_commute n) (u_gram n) (repr_κ n) (repr_u n)
    (PauliPower.ccoeff n) (PauliPower.ccoeff_ce n) (dense n)


theorem exists_unique_lift (n : ℕ) (f : C(Cube n,Fiber n))
    (hf : ∀ a t,p n a t=0 → PauliPower.ccoeff n a (f t)=0) :
    ∃! b : Tensor n,repr n b=f ∧ ‖b‖=‖f‖ :=
  CubeFrame.exists_unique_lift (κ n) (repr n) (p n) (u n) (PauliPower.ce n)
    (repr_κ n) (repr_u n) (PauliPower.ccoeff n) (PauliPower.ccoeff_sum n)
    (κ_commute n) (u_gram n) (PauliPower.ccoeff_ce n) (dense n) f hf

end KirchbergRordam.GenericRW.ConeCube


namespace KirchbergRordam.GenericRW.PauliSupport
open scoped Matrix Kronecker BigOperators
open KirchbergRordam.GenericRW.PauliPower

def coord : (n : ℕ)→Label n→Fin (n+1)→Pauli.Label
  | 0,a,_ => a
  | n+1,a,i => Fin.cases a.1 (fun j=>coord n a.2 j) i

def leg : (n : ℕ)→Fin (n+1)→Pauli.M2→⋆ₐ[ℂ] Mat n
  | 0,_ => StarAlgHom.id ℂ Pauli.M2
  | n+1,i => Fin.cases MatrixTensor.leftMatrixAlgebra
      (fun j=>MatrixTensor.rightMatrixAlgebra.comp (leg n j)) i

lemma anti_leg (n : ℕ) (a : Label n) (j : Fin (n+1)) (b : Pauli.M2)
    (he : b*Pauli.e (coord n a j) = -(Pauli.e (coord n a j)*b)) :
    leg n j b*e n a = -(e n a*leg n j b) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      change b*Pauli.e a.1 = -(Pauli.e a.1*b) at he
      have result : (Matrix.kronecker b 1*Matrix.kronecker (Pauli.e a.1) (e n a.2) :
        Matrix (Fin rankNum × Row n) (Fin rankNum × Row n) ℂ) =
        -(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker b 1) := by
        dsimp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,he,one_mul,mul_one]
        ext row col
        simp [Matrix.kroneckerMap_apply]
      exact result
    | succ j =>
      have result : (Matrix.kronecker 1 (leg n j b)*Matrix.kronecker (Pauli.e a.1) (e n a.2) :
        Matrix (Fin rankNum × Row n) (Fin rankNum × Row n) ℂ) =
        -(Matrix.kronecker (Pauli.e a.1) (e n a.2)*Matrix.kronecker 1 (leg n j b)) := by
        dsimp only [Matrix.kronecker]
        rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul,one_mul,mul_one,ih a.2 j he]
        ext row col
        simp [Matrix.kroneckerMap_apply]
      exact result

lemma coeff_zero (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : coord n a j≠0)
    (x : Mat n) (hx : ∀ b,Commute (leg n j b) x) : coeff n a x=0 := by
  obtain ⟨b,hb,he⟩ := PauliData.anti (coord n a j) hj
  rw [coeff_apply, KirchbergRordam.PauliSupport.trace_zero_of_anti _ _ _ ?_
    (anti_leg n a j b he) (hx b), mul_zero]
  rw [← map_mul,hb,map_one]
end KirchbergRordam.GenericRW.PauliSupport

namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra ComplexOrder BigOperators
open ConeModel

omit instSize instPauliData in
lemma matLeg_plain
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (n : ℕ) (j : Fin (n+1)) (b : Pauli.M2) :
    matLeg n j (CStarMatrix.ofMatrix b)=CStarMatrix.ofMatrix (PauliSupport.leg n j b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      change MatrixTensor.rightMatrix (matLeg n j (CStarMatrix.ofMatrix b))=_
      rw [ih]
      rfl

lemma matLeg_commute (n : ℕ) (i j : Fin (n+1)) (hij : i≠j) (a b : M2) :
    Commute (matLeg n i a) (matLeg n j b) := by
  induction n with
  | zero => exact (hij ((Fin.eq_zero i).trans (Fin.eq_zero j).symm)).elim
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (hij rfl).elim
      | succ j => exact MatrixTensor.legs_commute _ _
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (MatrixTensor.legs_commute _ _).symm
      | succ j => exact (ih i j (fun h=>hij (congrArg Fin.succ h))).map MatrixTensor.rightMatrix

lemma ccoeff_zero (n : ℕ) (a : Label n) (j : Fin (n+1)) (hj : PauliSupport.coord n a j≠0)
    (x : Fiber n) (hx : ∀ b,Commute (matLeg n j b) x) : PauliPower.ccoeff n a x=0 := by
  apply PauliSupport.coeff_zero n a j hj (CStarMatrix.ofMatrix.symm x)
  intro b
  have h := (hx (CStarMatrix.ofMatrix b)).map CStarMatrix.ofMatrixStarAlgEquiv.symm
  rw [matLeg_plain] at h
  exact h


lemma p_zero (n : ℕ) (a : Label n) (t : Cube n) (hp : p n a t=0) :
    ∃ j,t j=0 ∧ PauliSupport.coord n a j≠0 := by
  induction n with
  | zero =>
    refine ⟨0,?_,?_⟩
    · by_cases ha : a=(0:Pauli.Label)
      · subst a; simp [p,ConePauli.p,first] at hp
      · have eval_nonzero : ∀ label : Pauli.Label, label ≠ 0 →
            ConePauli.p label (t 0) = ((t 0 : ℝ) : ℂ) := by
          intro label hlabel
          simp [ConePauli.p, hlabel]
        have hz : ((t 0:ℝ):ℂ)=0 := (eval_nonzero a ha).symm.trans hp
        apply Subtype.ext
        exact_mod_cast hz
    · intro ha
      change a=(0:Pauli.Label) at ha
      subst a
      simp [p,ConePauli.p,first] at hp
  | succ n ih =>
    change ConePauli.p a.1 (t 0)*p n a.2 (tail n t)=0 at hp
    rcases mul_eq_zero.mp hp with hp|hp
    · have ha : a.1≠0 := by intro ha; simp [ha,ConePauli.p] at hp
      refine ⟨0,?_,ha⟩
      have hz : ((t 0:ℝ):ℂ)=0 := by simpa [ConePauli.p,ha] using hp
      apply Subtype.ext
      exact_mod_cast hz
    · obtain ⟨j,hj,hne⟩ := ih a.2 (tail n t) hp
      exact ⟨j.succ,hj,hne⟩
end KirchbergRordam.GenericRW.ConeCube
end

end OAI
