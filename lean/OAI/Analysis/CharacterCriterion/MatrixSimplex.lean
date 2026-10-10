import OAI.Analysis.CharacterCriterion.ConeCube

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


namespace KirchbergRordam.GenericRW.MatrixMix
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Mat (ι : Type*) := Matrix ι ι ℂ
def e (i j : ι) : Mat ι := Matrix.single i j 1
omit [Fintype ι] in
omit instSize instPauliData in
lemma e_star.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [DecidableEq ι]
    (i j : ι) : star (e i j)=e j i := by
  change (Matrix.single i j (1:ℂ)).conjTranspose=_
  simp [Matrix.conjTranspose_single,e]
omit instSize instPauliData in
lemma e_mul.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    (i j k l : ι) : e i j*e k l=if j=k then e i l else 0 := by
  by_cases h : j=k
  · subst k; simp [e]
  · simp [e,h]
omit instSize instPauliData in
lemma e_sum.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι]
    : ∑ i : ι,e i i=1 := by
  ext i j
  simp [e,Matrix.sum_apply,Matrix.single_apply,Matrix.one_apply,ite_and]

variable (φ : Mat ι →⋆ₐ[ℂ] A) (ψ : Mat κ →⋆ₐ[ℂ] A)
variable (hc : ∀ a b,Commute (φ a) (ψ b))
def x (i j : ι×κ) : A := φ (e i.1 j.1)*ψ (e i.2 j.2)
include hc in
lemma x_star (i j : ι×κ) : star (x φ ψ i j)=x φ ψ j i := by
  simp only [x,star_mul,← map_star,e_star]
  exact (hc _ _).eq.symm
include hc in
lemma x_mul (i j k l : ι×κ) : x φ ψ i j*x φ ψ k l=if j=k then x φ ψ i l else 0 := by
  unfold x
  calc
    _=φ (e i.1 j.1)*φ (e k.1 l.1)*(ψ (e i.2 j.2)*ψ (e k.2 l.2)) := by
      rw [mul_assoc,← mul_assoc (ψ _),← (hc _ _).eq]; noncomm_ring
    _=_ := by
      rw [← map_mul,← map_mul,e_mul,e_mul]
      by_cases h1 : j.1=k.1 <;> by_cases h2 : j.2=k.2 <;>
        simp [h1,h2,Prod.ext_iff]
lemma x_sum : ∑ i : ι×κ,x φ ψ i i=1 := by
  simp only [x,Fintype.sum_prod_type,← Finset.mul_sum,← map_sum,e_sum,map_one,mul_one]

def linear : Mat (ι×κ) →ₗ[ℂ] A where
  toFun a := ∑ i,∑ j,a i j • x φ ψ i j
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]
omit instSize instPauliData in
lemma linear_single.{contextLevel1, contextLevel2, contextLevel3}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {ι : Type contextLevel2}
    {κ : Type contextLevel3}
    [Fintype ι]
    [Fintype κ]
    [DecidableEq ι]
    [DecidableEq κ]
    (φ : KirchbergRordam.GenericRW.MatrixMix.Mat ι →⋆ₐ[ℂ] A)
    (ψ : KirchbergRordam.GenericRW.MatrixMix.Mat κ →⋆ₐ[ℂ] A)
    (i j : ι×κ) (z : ℂ) : linear φ ψ (Matrix.single i j z)=z • x φ ψ i j := by
  simp [linear,Matrix.single,ite_and]
lemma linear_one : linear φ ψ 1=1 := by simpa [linear,Matrix.one_apply] using x_sum φ ψ
include hc in
lemma linear_star (a : Mat (ι×κ)) : linear φ ψ (star a)=star (linear φ ψ a) := by
  simp only [linear,LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_smul,x_star φ ψ hc]
  exact Finset.sum_comm
include hc in
lemma linear_mul (a b : Mat (ι×κ)) : linear φ ψ (a*b)=linear φ ψ a*linear φ ψ b := by
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [add_mul,map_add,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [mul_add,map_add,hb,hb']
    | h_std_basis k l w =>
      by_cases h : j=k
      · subst k
        rw [Matrix.single_mul_single_same,linear_single,linear_single,linear_single]
        simp [smul_smul,x_mul φ ψ hc,mul_comm]
      · rw [Matrix.single_mul_single_of_ne (h:=h)]
        simp [linear_single,x_mul φ ψ hc,h]

def tensor : Mat (ι×κ) →⋆ₐ[ℂ] A where
  toFun := linear φ ψ
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,linear_one,Algebra.algebraMap_eq_smul_one]
  map_one' := linear_one φ ψ
  map_mul' := linear_mul φ ψ hc
  map_star' := linear_star φ ψ hc

lemma tensor_kronecker (a : Mat ι) (b : Mat κ) :
    tensor φ ψ hc (Matrix.kronecker a b)=φ a*ψ b := by
  simp only [Matrix.kronecker]
  induction a using Matrix.induction_on' with
  | h_zero => simp
  | h_add a a' ha ha' => simp only [Matrix.add_kronecker,map_add,add_mul,ha,ha']
  | h_std_basis i j z =>
    induction b using Matrix.induction_on' with
    | h_zero => simp
    | h_add b b' hb hb' => simp only [Matrix.kronecker_add,map_add,mul_add,hb,hb']
    | h_std_basis k l w =>
      rw [Matrix.single_kronecker_single]
      change linear φ ψ (Matrix.single (i,k) (j,l) (z*w))=_
      rw [linear_single]
      have he (i j : ι) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      have hf (i j : κ) (z : ℂ) : Matrix.single i j z=z • e i j := by simp [e]
      rw [he,hf,map_smul,map_smul,smul_mul_smul_comm]
      rfl

variable {φ ψ}
lemma tensor_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (a : Mat (ι×κ)) : tensor φ ψ hc a∈S := by
  change (∑ i,∑ j,a i j • x φ ψ i j)∈S
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (S.mul_mem (hφ _) (hψ _)) _
end KirchbergRordam.GenericRW.MatrixMix


namespace KirchbergRordam.GenericRW.MatrixMix
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable [TopologicalSpace X]
lemma tensor_continuous (φ : X → Mat ι →⋆ₐ[ℂ] A) (ψ : X → Mat κ →⋆ₐ[ℂ] A)
    (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (a : X → Mat (ι×κ)) (ha : Continuous a) :
    Continuous fun z => tensor (φ z) (ψ z) (hc z) (a z) := by
  change Continuous fun z => ∑ i,∑ j,a z i j • (φ z (e i.1 j.1)*ψ z (e i.2 j.2))
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply j).comp ((continuous_apply i).comp ha)).smul ((hφ _).mul (hψ _))

variable (φ ψ : Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ a b,Commute (φ a) (ψ b))
lemma tensor_left (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.left a)=φ a := by
  have he : FlipPath.left a=Matrix.kronecker a 1 := by ext i j; simp [FlipPath.left,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,mul_one]
lemma tensor_right (a : Mat (Fin Size.n)) : tensor φ ψ hc (FlipPath.right a)=ψ a := by
  have he : FlipPath.right a=Matrix.kronecker 1 a := by ext i j; simp [FlipPath.right,Matrix.one_apply]
  rw [he,tensor_kronecker,map_one,one_mul]

def u (t : unitInterval) : A := tensor φ ψ hc (FlipPath.path t)
lemma u_star_mul (t : unitInterval) : star (u φ ψ hc t)*u φ ψ hc t=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_star_mul,map_one]
lemma u_mul_star (t : unitInterval) : u φ ψ hc t*star (u φ ψ hc t)=1 := by
  rw [u,← map_star,← map_mul,FlipPath.path_mul_star,map_one]
lemma u_zero : u φ ψ hc 0=1 := by rw [u,FlipPath.path_zero,map_one]

def interpolate (t : unitInterval) : Mat (Fin Size.n) →⋆ₐ[ℂ] A where
  toFun a := u φ ψ hc t*φ a*star (u φ ψ hc t)
  map_zero' := by simp
  map_add' a b := by simp [mul_add,add_mul]
  map_one' := by rw [map_one,mul_one,u_mul_star]
  map_mul' a b := by
    rw [map_mul]
    calc
      _=u φ ψ hc t*φ a*(star (u φ ψ hc t)*u φ ψ hc t)*φ b*star (u φ ψ hc t) := by rw [u_star_mul]; noncomm_ring
      _=_ := by noncomm_ring
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one,map_smul,map_one,Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one,smul_mul_assoc,u_mul_star]
  map_star' a := by rw [map_star,star_mul,star_mul,star_star]; noncomm_ring

lemma interpolate_zero (a : Mat (Fin Size.n)) : interpolate φ ψ hc 0 a=φ a := by
  change u φ ψ hc 0*φ a*star (u φ ψ hc 0)=_
  rw [u_zero,star_one,one_mul,mul_one]
lemma interpolate_top {t : unitInterval} (ht : 2/3≤(t:ℝ)) (a : Mat (Fin Size.n)) :
    interpolate φ ψ hc t a=ψ a := by
  calc
    _=tensor φ ψ hc (FlipPath.path t*FlipPath.left a*star (FlipPath.path t)) := by
      rw [map_mul,map_mul,map_star,tensor_left]; rfl
    _=tensor φ ψ hc (FlipPath.right a) := by
      congr 1
      rw [FlipPath.path_top ht,FlipPath.flip_star,← FlipPath.flip_exchange,mul_assoc,FlipPath.flip_mul,mul_one]
    _=_ := tensor_right φ ψ hc a

lemma interpolate_mem (S : StarSubalgebra ℂ A) (hφ : ∀ a,φ a∈S) (hψ : ∀ b,ψ b∈S)
    (t : unitInterval) (a : Mat (Fin Size.n)) : interpolate φ ψ hc t a∈S := by
  have hu : u φ ψ hc t∈S := tensor_mem hc S hφ hψ _
  exact S.mul_mem (S.mul_mem hu (hφ a)) (S.star_mem' hu)

lemma interpolate_continuous
    (φ ψ : X → Mat (Fin Size.n) →⋆ₐ[ℂ] A) (hc : ∀ z a b,Commute (φ z a) (ψ z b))
    (hφ : ∀ a,Continuous fun z => φ z a) (hψ : ∀ b,Continuous fun z => ψ z b)
    (t : X → unitInterval) (ht : Continuous t) (a : Mat (Fin Size.n)) :
    Continuous fun z => interpolate (φ z) (ψ z) (hc z) (t z) a := by
  have hu : Continuous fun z => u (φ z) (ψ z) (hc z) (t z) :=
    tensor_continuous φ ψ hc hφ hψ _ (FlipPath.path_continuous.comp ht)
  exact (hu.mul (hφ a)).mul hu.star
end KirchbergRordam.GenericRW.MatrixMix
namespace KirchbergRordam.GenericRW

def CoordinateSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

namespace CoordinateSimplex

variable {ι : Type*} [Fintype ι]

instance : FunLike (CoordinateSimplex ι) ι ℝ where
  coe weights := weights.val
  coe_injective := Subtype.val_injective

omit instSize instPauliData in
@[ext] lemma ext.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    {weights other : CoordinateSimplex ι}
    (heq : ∀ index, weights index = other index) : weights = other :=
  Subtype.ext (funext heq)

omit instSize instPauliData in
@[simp] lemma zero_le.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) (index : ι) :
    0 ≤ weights index := weights.2.1 index

omit instSize instPauliData in
@[simp] lemma sum_eq_one.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    (weights : CoordinateSimplex ι) :
    ∑ index, weights index = 1 := weights.2.2

lemma le_one (weights : CoordinateSimplex ι) (index : ι) : weights index ≤ 1 := by
  rw [← sum_eq_one weights]
  exact Finset.single_le_sum (fun entry _ => zero_le weights entry) (Finset.mem_univ index)

abbrev vertex [DecidableEq ι] (index : ι) : CoordinateSimplex ι :=
  ⟨Pi.single index 1, by
    constructor
    · intro entry
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp⟩

omit instSize instPauliData in
@[simp] lemma vertex_coe.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {ι : Type contextLevel1}
    [Fintype ι]
    [DecidableEq ι] (index : ι) :
    ⇑(vertex index) = Pi.single index 1 := rfl

end CoordinateSimplex
end KirchbergRordam.GenericRW
namespace KirchbergRordam.GenericRW.MatrixSimplex
open scoped BigOperators
open MatrixMix
variable {A : Type*} [CStarAlgebra A]
abbrev Simplex (n : ℕ) := CoordinateSimplex (Fin (n+1))

def last {n : ℕ} (r : Simplex (n+1)) : unitInterval :=
  ⟨r (Fin.last (n+1)),CoordinateSimplex.zero_le r _,CoordinateSimplex.le_one r _⟩
def den {n : ℕ} (r : Simplex (n+1)) : ℝ := max (1-last r) (1/3)
include instSize instPauliData in
lemma den_pos {n : ℕ} (r : Simplex (n+1)) : 0<den r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
include instSize instPauliData in
lemma prev_sum {n : ℕ} (r : Simplex (n+1)) :
    ∑ i : Fin (n+1),r i.castSucc=1-(last r:ℝ) := by
  have h := CoordinateSimplex.sum_eq_one r
  rw [Fin.sum_univ_castSucc] at h
  change _+ (last r:ℝ)=1 at h
  linarith

def prev {n : ℕ} (r : Simplex (n+1)) : Simplex n :=
  ⟨fun i => r i.castSucc/den r + if i=0 then 1-(1-last r)/den r else 0,by
    constructor
    · intro i
      apply add_nonneg (div_nonneg (CoordinateSimplex.zero_le r _) (den_pos r).le)
      split_ifs
      · apply sub_nonneg.mpr
        exact (div_le_one (den_pos r)).mpr (le_max_left _ _)
      · exact le_rfl
    · rw [Finset.sum_add_distrib,← Finset.sum_div,prev_sum]
      simp⟩
lemma prev_apply {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1)) :
    prev r i=r i.castSucc/(1-last r) := by
  have hd : den r=1-last r := max_eq_left (by linarith)
  have hn : (1-(last r:ℝ))≠0 := by linarith
  change r i.castSucc / den r + (if i=0 then 1-(1-last r)/den r else 0)=_
  simp [hd,div_self hn]
lemma prev_pos {n : ℕ} (r : Simplex (n+1)) (h : (last r:ℝ)≤2/3) (i : Fin (n+1))
    (hi : 0<prev r i) : 0<r i.castSucc := by
  rw [prev_apply r h] at hi
  exact (div_pos_iff.mp hi).elim (fun h => h.1) (fun h => False.elim (by linarith [CoordinateSimplex.zero_le r i.castSucc]))
include instSize instPauliData in
lemma last_continuous {n : ℕ} : Continuous (last (n:=n)) := by
  apply Continuous.subtype_mk
  exact (continuous_apply _).comp continuous_subtype_val
lemma prev_continuous {n : ℕ} : Continuous (prev (n:=n)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hd : Continuous (den (n:=n)) := by
    exact (continuous_const.sub (continuous_subtype_val.comp last_continuous)).max continuous_const
  have hq : Continuous fun r : Simplex (n+1) => (1-(last r:ℝ))/den r :=
    (continuous_const.sub (continuous_subtype_val.comp last_continuous)).div hd (fun r => (den_pos r).ne')
  apply Continuous.add
  · exact ((continuous_apply _).comp continuous_subtype_val).div hd (fun r => (den_pos r).ne')
  · by_cases hi : i=0
    · simp only [ite_eq_left hi]
      exact (show Continuous (fun _ : Simplex (n+1) => (1:ℝ)) from continuous_const).sub hq
    · simp only [ite_eq_right hi]; exact continuous_const

structure Family {n : ℕ} (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A) where
  hom : Simplex n → Mat (Fin Size.n) →⋆ₐ[ℂ] A
  continuous : ∀ a,Continuous fun r => hom r a
  support : ∀ r (S : StarSubalgebra ℂ A), (∀ i,0<r i → ∀ a,φ i a∈S) → ∀ a,hom r a∈S
  vertex : ∀ i a,hom (CoordinateSimplex.vertex i) a=φ i a

variable {n : ℕ} {φ : Fin (n+2) → Mat (Fin Size.n) →⋆ₐ[ℂ] A}
variable (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b))
variable (F : Family (fun i : Fin (n+1) => φ i.castSucc))

include hc in
lemma family_commute (r : Simplex (n+1)) (a b : Mat (Fin Size.n)) :
    Commute (F.hom (prev r) a) (φ (Fin.last (n+1)) b) := by
  let S := StarSubalgebra.centralizer ℂ (Set.range (φ (Fin.last (n+1))))
  have hm : F.hom (prev r) a∈S := F.support _ S (by
    intro i _ c
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨d,rfl⟩
    constructor
    · exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c d).eq.symm
    · rw [← map_star]
      exact (hc i.castSucc (Fin.last _) (Fin.castSucc_ne_last i) c (star d)).eq.symm) a
  exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp hm) _ ⟨b,rfl⟩).1.symm

def extendHom (r : Simplex (n+1)) : Mat (Fin Size.n) →⋆ₐ[ℂ] A :=
  interpolate (F.hom (prev r)) (φ (Fin.last (n+1))) (family_commute hc F r) (last r)

lemma extend_support (r : Simplex (n+1)) (S : StarSubalgebra ℂ A)
    (hs : ∀ i,0<r i → ∀ a,φ i a∈S) (a : Mat (Fin Size.n)) : extendHom hc F r a∈S := by
  by_cases ht : 2/3≤(last r:ℝ)
  · rw [extendHom,interpolate_top _ _ _ ht]
    exact hs _ (by change 0<(last r:ℝ); linarith) a
  · have ht' : (last r:ℝ)≤2/3 := (lt_of_not_ge ht).le
    have hp : ∀ a,F.hom (prev r) a∈S := F.support _ S (fun i hi => hs _ (prev_pos r ht' i hi))
    by_cases hz : last r=0
    · rw [extendHom,hz,interpolate_zero]; exact hp a
    · apply interpolate_mem _ _ _ S hp (hs _ ?_) _ a
      have hne : (last r:ℝ)≠0 := fun h => hz (Subtype.ext h)
      exact lt_of_le_of_ne (last r).2.1 hne.symm

lemma prev_vertex (i : Fin (n+1)) :
    prev (CoordinateSimplex.vertex i.castSucc)=CoordinateSimplex.vertex i := by
  have hz : last (CoordinateSimplex.vertex i.castSucc)=0 := by
    apply Subtype.ext
    simp [last,Fin.castSucc_ne_last,eq_comm]
  ext j
  rw [prev_apply _ (by rw [hz]; norm_num)]
  simp [hz,Pi.single_apply,Fin.castSucc_inj]

lemma extend_vertex (i : Fin (n+2)) (a : Mat (Fin Size.n)) :
    extendHom hc F (CoordinateSimplex.vertex i) a=φ i a := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · apply interpolate_top
    norm_num [last]
  · have hz : last (CoordinateSimplex.vertex j.castSucc)=0 := by
      apply Subtype.ext
      simp [last,Fin.castSucc_ne_last,eq_comm]
    rw [extendHom,hz,interpolate_zero,prev_vertex,F.vertex]

def extend : Family φ where
  hom := extendHom hc F
  continuous a := interpolate_continuous _ _ _ (fun b => (F.continuous b).comp prev_continuous)
    (fun _ => continuous_const) last last_continuous a
  support := extend_support hc F
  vertex := extend_vertex hc F


theorem exists_family (n : ℕ) (φ : Fin (n+1) → Mat (Fin Size.n) →⋆ₐ[ℂ] A)
    (hc : ∀ i j,i≠j → ∀ a b,Commute (φ i a) (φ j b)) : Nonempty (Family φ) := by
  induction n with
  | zero =>
    refine ⟨{hom := fun _ => φ 0
             continuous := fun _ => continuous_const
             support := ?_
             vertex := ?_}⟩
    · intro r S hs a
      have coordinate_one : r 0 = 1 := by
        simpa using CoordinateSimplex.sum_eq_one r
      exact hs 0 (by rw [coordinate_one]; norm_num) a
    · intro i a
      have : i=0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
    obtain ⟨F⟩ := ih (fun i => φ i.castSucc) (fun i j hij => hc _ _ (fun h => hij (Fin.castSucc_inj.mp h)))
    exact ⟨extend hc F⟩
end KirchbergRordam.GenericRW.MatrixSimplex
namespace KirchbergRordam.GenericRW.CubeWeights
open scoped BigOperators
abbrev Cube (n : ℕ) := Fin (n+1) → unitInterval
abbrev Punctured (n : ℕ) := {t : Cube n // t≠0}
variable {n : ℕ}
def radius (t : Cube n) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => (t i:ℝ))
omit instSize instPauliData in
lemma coord_le_radius
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) (i : Fin (n+1)) : (t i:ℝ)≤radius t :=
  Finset.le_sup' (fun i => (t i:ℝ)) (Finset.mem_univ i)
lemma radius_nonneg (t : Cube n) : 0≤radius t := (t 0).2.1.trans (coord_le_radius t 0)
lemma radius_pos (t : Punctured n) : 0<radius t.1 := by
  by_contra! h
  have ht : t.1=0 := by
    ext i
    apply le_antisymm
    · exact (coord_le_radius t.1 i).trans h
    · exact (t.1 i).2.1
  exact t.2 ht
omit instSize instPauliData in
lemma radius_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    : Continuous (radius (n:=n)) :=
  Continuous.finset_sup'_apply _ (fun i _ => continuous_subtype_val.comp (continuous_apply i))
omit instSize instPauliData in
lemma radius_attained
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Cube n) : ∃ i,radius t=(t i:ℝ) := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => (t i:ℝ))
  exact ⟨i,hi⟩

def weight (t : Punctured n) (i : Fin (n+1)) : ℝ := max ((t.1 i:ℝ)/radius t.1-1/2) 0
def total (t : Punctured n) : ℝ := ∑ i,weight t i
omit instSize instPauliData in
lemma weight_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {n : ℕ}
    (t : Punctured n) (i : Fin (n+1)) : 0≤weight t i := le_max_right _ _
lemma total_pos (t : Punctured n) : 0<total t := by
  obtain ⟨i,hi⟩ := radius_attained t.1
  have hw : weight t i=1/2 := by
    rw [weight,← hi,div_self (radius_pos t).ne']; norm_num
  exact lt_of_lt_of_le (by rw [hw]; norm_num) (Finset.single_le_sum (fun j _ => weight_nonneg t j) (Finset.mem_univ i))

def normalized (t : Punctured n) : CoordinateSimplex (Fin (n+1)) :=
  ⟨fun i => weight t i/total t,fun i => div_nonneg (weight_nonneg t i) (total_pos t).le,by
    rw [← Finset.sum_div,← total,div_self (total_pos t).ne']⟩
lemma normalized_apply (t : Punctured n) (i : Fin (n+1)) : normalized t i=weight t i/total t := rfl
lemma normalized_continuous : Continuous (normalized (n:=n)) := by
  have hw (i : Fin (n+1)) : Continuous fun t : Punctured n => weight t i :=
    (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)).div
      (radius_continuous.comp continuous_subtype_val) (fun t => (radius_pos t).ne')).sub continuous_const).max continuous_const
  have ht : Continuous (total (n:=n)) := continuous_finsetSum _ fun i _ => hw i
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (hw i).div ht (fun t => (total_pos t).ne')
lemma normalized_zero (t : Punctured n) (i : Fin (n+1)) (hi : t.1 i=0) : normalized t i=0 := by
  rw [normalized_apply,weight,hi]
  norm_num
lemma normalized_support (t : Punctured n) (i : Fin (n+1)) (hi : 0<normalized t i) : 0<(t.1 i:ℝ) := by
  by_contra! h
  have hz : t.1 i=0 := Subtype.ext (le_antisymm h (t.1 i).2.1)
  rw [normalized_zero t i hz] at hi
  exact (lt_irrefl _ hi)

lemma localized_normalized (t : Punctured n) {δ : ℝ} (hδ : 0<δ) (j : Fin (n+1))
    (hj : δ<(t.1 j:ℝ)) (hi : ∀ i,i≠j → (t.1 i:ℝ)<δ/2) :
    normalized t=CoordinateSimplex.vertex j := by
  have hd : radius t.1=(t.1 j:ℝ) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      by_cases he : i=j
      · subst i; exact le_rfl
      · linarith [hi i he]
    · exact coord_le_radius _ _
  have hpos : 0<(t.1 j:ℝ) := hδ.trans hj
  have hw (i : Fin (n+1)) : weight t i=if i=j then 1/2 else 0 := by
    unfold weight
    rw [hd]
    by_cases he : i=j
    · subst i; rw [div_self hpos.ne']; norm_num
    · rw [ite_eq_right he,max_eq_right]
      have hh : (t.1 i:ℝ)/(t.1 j:ℝ)<1/2 := (div_lt_iff₀ hpos).mpr (by linarith [hi i he])
      linarith
  have htotal : total t=1/2 := by simp [total,hw]
  ext i
  rw [normalized_apply,hw,htotal]
  by_cases he : i=j <;> simp [he,eq_comm]

def g (δ : ℝ) (t : unitInterval) : ℝ := max (1-2*(t:ℝ)/δ) 0
omit instSize instPauliData in
lemma g_continuous
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : Continuous (g δ) := by unfold g; fun_prop
omit instSize instPauliData in
lemma g_nonneg
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) (t : unitInterval) : 0≤g δ t := le_max_right _ _
omit instSize instPauliData in
lemma g_le_one
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) : g δ t≤1 := by
  apply max_le _ zero_le_one
  have : 0≤2*(t:ℝ)/δ := div_nonneg (mul_nonneg (by norm_num) t.2.1) hδ.le
  linarith
omit instSize instPauliData in
lemma g_zero
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    (δ : ℝ) : g δ 0=1 := by simp [g]
omit instSize instPauliData in
lemma g_pos
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : 0<g δ t) : (t:ℝ)<δ/2 := by
  have hp : 0<1-2*(t:ℝ)/δ := (lt_max_iff.mp h).resolve_right (lt_irrefl _)
  have hh : 2*(t:ℝ)/δ<1 := by linarith
  have := (div_lt_one hδ).mp hh
  linarith
omit instSize instPauliData in
lemma g_of_large
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0<δ) (t : unitInterval) (h : δ≤(t:ℝ)) : g δ t=0 := by
  apply max_eq_right
  have : 1≤2*(t:ℝ)/δ := (one_le_div hδ).mpr (by linarith)
  linarith

def H (δ : ℝ) (t : Cube n) : ℝ := 1-∏ i,g δ (t i)
lemma H_continuous (δ : ℝ) : Continuous (H (n:=n) δ) :=
  continuous_const.sub (continuous_finsetProd _ fun i _ => (g_continuous δ).comp (continuous_apply i))
lemma H_zero (δ : ℝ) : H (n:=n) δ 0=0 := by simp [H,g_zero]
lemma H_nonneg {δ : ℝ} (hδ : 0<δ) (t : Cube n) : 0≤H δ t := by
  apply sub_nonneg.mpr
  exact Finset.prod_le_one₀ (fun i _ => g_nonneg δ (t i)) (fun i _ => g_le_one hδ (t i))
lemma H_le_one (δ : ℝ) (t : Cube n) : H δ t≤1 := by
  have hp : 0≤∏ i,g δ (t i) := Finset.prod_nonneg (fun i _ => g_nonneg δ (t i))
  unfold H; linarith
lemma H_of_large {δ : ℝ} (hδ : 0<δ) (t : Cube n) (j : Fin (n+1)) (h : δ≤(t j:ℝ)) : H δ t=1 := by
  have hz : ∏ i,g δ (t i)=0 := Finset.prod_eq_zero (Finset.mem_univ j) (g_of_large hδ _ h)
  simp [H,hz]
end KirchbergRordam.GenericRW.CubeWeights
end

end OAI
