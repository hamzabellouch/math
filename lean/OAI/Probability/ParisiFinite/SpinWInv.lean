import Mathlib
import OAI.Probability.ParisiFinite.Act

namespace OAI

/-! Spin W Inv. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem spinW_inv (e : E) (x : SpinSpace E) : spinW (-e) (spinW e x)=x := by
  ext i
  exact (weyl e).symm_apply_apply (x i)

@[simp] theorem spinW_inv' (e : E) (x : SpinSpace E) : spinW e (spinW (-e) x)=x := by
  simpa only [neg_neg] using spinW_inv (-e) x

 

theorem center_probe_product {ι : Type*} (l : List ι) (A : ι → Matrix (Fin 2) (Fin 2) ℂ)
    (D : ι → E) (e : E) (x : SpinSpace E) :
    ProbeProduct.act (fun j => (spinW (-e)).comp ((probe (A j) (D j)).comp (spinW e))) l x =
      spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e x)) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [ProbeProduct.act_cons,ContinuousLinearMap.comp_apply,ih,spinW_inv']

 

theorem centered_product_phase_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (D : ι → E) (e : E) (α : ℝ)
    (hα : 0 ≤ α) (hA : ∀ j ∈ l, A j ∈ unitary _)
    (hp : ∀ j ∈ l, |(-2*(⟪D j,e⟫_ℂ).im)| ≤ α) (x : SpinSpace E) :
    ‖spinW (-e) (ProbeProduct.act (fun j => probe (A j) (D j)) l (spinW e x))-
        ProbeProduct.act (fun j => probe (A j) (D j)) l x‖ ≤ l.length*α*‖x‖ := by
  rw [← center_probe_product]
  apply ProbeProduct.perturbation_bound _ _ l α hα
  · intro j hj z
    simp only [ContinuousLinearMap.comp_apply,norm_spinW,norm_probe _ (hA j hj)]
    rfl
  · intro j hj z
    exact (norm_probe _ (hA j hj) _ z).le
  · intro j hj z
    simp only [ContinuousLinearMap.comp_apply]
    rw [centered_toggled_probe _ (hA j hj)]
    calc
      _ ≤ |(-2*(⟪D j,e⟫_ℂ).im)| *‖probe (A j) (D j) z‖ :=
        probePhase_sub_le _ (hA j hj) _ _
      _ ≤ α*‖z‖ := by rw [norm_probe _ (hA j hj)]; gcongr; exact hp j hj

 

theorem centered_zero_clock_bound {ι : Type*} (l : List ι)
    (A : ι → Matrix (Fin 2) (Fin 2) ℂ) (v w : ι → E)
    (r L M Δ α : ℝ) (e : E) (x : PreSpin E)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hΔ : 0 ≤ Δ) (hα : 0 ≤ α)
    (hA : ∀ j ∈ l, A j ∈ unitary _)
    (hv : ∀ j ∈ l, ‖v j‖ ≤ L) (hw : ∀ j ∈ l, ‖w j‖ ≤ L)
    (hd : ∀ j ∈ l, ‖v j-w j‖ ≤ Δ)
    (hMass : ∀ j ∈ l, matrixMass (A j) ≤ M)
    (hMassStar : ∀ j ∈ l, matrixMass (A j).conjTranspose ≤ M)
    (hp : ∀ j ∈ l, |(-2*(⟪r • v j,e⟫_ℂ).im)| ≤ α)
    (hclock : (l.map fun j => Complex.I • probeField (A j) (w j) x).sum=0) :
    ‖spinW (-e) (ProbeProduct.act (fun j => probe (A j) (r • v j)) l (spinW e (spinCoe x)))-spinCoe x‖ ≤
      l.length*((r^2*L^2+|r| *Δ)*M*spinBound x)+
        l.length^2*|r| *(2*|r| *L^2*M^3*spinBound x)+l.length*α*‖spinCoe x‖ := by
  have h1 := centered_product_phase_bound l A (fun j => r • v j) e α hα hA hp (spinCoe x)
  have h2 := zero_clock_spin_probes l A v w r L M Δ x hL hM hΔ hA hv hw hd hMass hMassStar hclock
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (spinW (-e) (ProbeProduct.act (fun j => probe (A j) (r • v j)) l (spinW e (spinCoe x))))
    (ProbeProduct.act (fun j => probe (A j) (r • v j)) l (spinCoe x)) (spinCoe x)
  linarith

end CoherentFock

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
namespace RootSpin

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Y : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Z : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
def R (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos t : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+(-Complex.I*(Real.sin t : ℂ)) • X

@[simp] theorem X_star : X.conjTranspose=X := by ext i j; fin_cases i <;> fin_cases j <;> simp [X]
@[simp] theorem Y_star : Y.conjTranspose=Y := by ext i j; fin_cases i <;> fin_cases j <;> simp [Y]
@[simp] theorem Z_star : Z.conjTranspose=Z := by ext i j; fin_cases i <;> fin_cases j <;> simp [Z]
@[simp] theorem X_sq : X*X=1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [X,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem Y_sq : Y*Y=1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [Y,Matrix.mul_apply,Fin.sum_univ_two]
@[simp] theorem Z_sq : Z*Z=1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [Z,Matrix.mul_apply,Fin.sum_univ_two]

theorem X_unitary : X ∈ unitary _ := by simp [Unitary.mem_iff,Matrix.star_eq_conjTranspose]
theorem Y_unitary : Y ∈ unitary _ := by simp [Unitary.mem_iff,Matrix.star_eq_conjTranspose]
theorem Z_unitary : Z ∈ unitary _ := by simp [Unitary.mem_iff,Matrix.star_eq_conjTranspose]

@[simp] theorem R_apply (t : ℝ) (i j : Fin 2) :
    R t i j=if i=j then (Real.cos t : ℂ) else -Complex.I*(Real.sin t : ℂ) := by
  fin_cases i <;> fin_cases j <;> simp [R,X]

theorem R_star (t : ℝ) : (R t).conjTranspose=R (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply,R_apply,-Complex.ofReal_cos,-Complex.ofReal_sin]

theorem R_add (s t : ℝ) : R s*R t=R (s+t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,R_apply,Complex.mul_re,Complex.mul_im,
      Real.cos_add,Real.sin_add,-Complex.ofReal_cos,-Complex.ofReal_sin] <;> ring

@[simp] theorem R_zero : R 0=1 := by simp [R]

theorem R_unitary (t : ℝ) : R t ∈ unitary _ := by
  rw [Unitary.mem_iff]
  change (R t).conjTranspose*R t=1 ∧ R t*(R t).conjTranspose=1
  simp [R_star,R_add]

def hadamard : Matrix (Fin 2) (Fin 2) ℂ := fun i j => if i=1 ∧ j=1 then -1 else 1

def diagUnit : (Matrix (Fin 2) (Fin 2) ℂ)ˣ where
  val := hadamard
  inv := (1/2:ℂ) • hadamard
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [hadamard,Matrix.mul_apply,Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> norm_num [hadamard,Matrix.mul_apply,Fin.sum_univ_two]

theorem diagonalization (z : ℂ) :
    (diagUnit : Matrix (Fin 2) (Fin 2) ℂ)*Matrix.diagonal (fun i : Fin 2 => if i=0 then z else -z)*
      ((diagUnit⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)=z • X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnit,hadamard,X,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem exp_X (z : ℂ) :
    NormedSpace.exp (z • X)=((Complex.exp z+Complex.exp (-z))/2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)+
      ((Complex.exp z-Complex.exp (-z))/2) • X := by
  rw [← diagonalization z,Matrix.exp_units_conj,Matrix.exp_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagUnit,hadamard,X,Matrix.mul_apply,Fin.sum_univ_two,← Complex.exp_eq_exp_ℂ] <;> ring

theorem R_eq_exp (t : ℝ) : R t=NormedSpace.exp ((-Complex.I*(t:ℂ)) • X) := by
  rw [exp_X]
  have hp : Complex.exp (-Complex.I*(t:ℂ))=(Real.cos t:ℂ)-Complex.I*(Real.sin t:ℂ) := by
    rw [show -Complex.I*(t:ℂ)=(-(t:ℂ))*Complex.I by ring,Complex.exp_mul_I]
    simp [← Complex.ofReal_cos,← Complex.ofReal_sin,sub_eq_add_neg,mul_comm]
  have hm : Complex.exp (-(-Complex.I*(t:ℂ)))=(Real.cos t:ℂ)+Complex.I*(Real.sin t:ℂ) := by
    rw [neg_mul,neg_neg,mul_comm,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
    ring
  rw [hp,hm]
  unfold R
  congr 1 <;> congr 1 <;> ring

theorem R_conjugate_Z (t : ℝ) : (R t).conjTranspose*Z*R t=
    (Real.cos (2*t):ℂ) • Z+(Real.sin (2*t):ℂ) • Y := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,R_apply,Z,Y,
      Real.cos_two_mul,Real.sin_two_mul,-Complex.ofReal_sin,-Complex.ofReal_cos,
      Complex.mul_re,Complex.mul_im,-Complex.ofReal_pow] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

end RootSpin

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
open RootSpin

@[simp] theorem rootX_apply (x : SpinSpace E) (i : Fin 2) :
    SpinOperators.act X x i = x (1-i) := by
  fin_cases i <;> simp [SpinOperators.act_apply,X,Fin.sum_univ_two]

@[simp] theorem rootZ_apply (x : SpinSpace E) (i : Fin 2) :
    SpinOperators.act Z x i = if i=0 then x i else -x i := by
  fin_cases i <;> simp [SpinOperators.act_apply,Z,Fin.sum_univ_two]

 
theorem WZ_rootX (d : E) :
    (WZ d).comp (SpinOperators.act X) =
      (SpinOperators.act X).comp (WZ (-d)) := by
  ext x i
  fin_cases i <;> simp [WZ_apply,X]

 
theorem WZ_rootZ (d : E) :
    (WZ d).comp (SpinOperators.act Z) =
      (SpinOperators.act Z).comp (WZ d) := by
  ext x i
  fin_cases i <;> simp [WZ_apply,Z]

theorem rootR (t : ℝ) :
    (SpinOperators.act (R t) : SpinSpace E →L[ℂ] SpinSpace E) =
      (Real.cos t:ℂ) • ContinuousLinearMap.id ℂ (SpinSpace E)+
        (-Complex.I*(Real.sin t:ℂ)) • SpinOperators.act X := by
  change SpinOperators.rep (R t)=_
  simp only [R,map_add,map_smul,SpinOperators.rep_apply,SpinOperators.act_one]

 

theorem initialization_split (γ δ : ℝ) (v e : E) :
    (WZ (γ • v)).comp ((SpinOperators.act (R δ)).comp (WZ ((-γ) • e))) =
      ((Real.cos δ:ℂ)*phase (γ • v) ((-γ) • e)) • WZ (γ • (v-e))+
      ((-Complex.I*(Real.sin δ:ℂ))*phase ((-γ) • v) ((-γ) • e)) •
        (SpinOperators.act X).comp (WZ ((-γ) • (v+e))) := by
  rw [rootR,ContinuousLinearMap.add_comp,ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_add,ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.comp_smul,← ContinuousLinearMap.comp_assoc,WZ_rootX,
    ContinuousLinearMap.comp_assoc,WZ_mul,WZ_mul,
    ContinuousLinearMap.comp_smul,smul_smul,smul_smul]
  have h1 : γ • v+(-γ) • e=γ • (v-e) := by module
  have h2 : - (γ • v)+(-γ) • e=(-γ) • (v+e) := by module
  rw [h1,h2]
  simp only [neg_smul]

 

theorem initialization_special_norm (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    ‖((-Complex.I*(Real.sin δ:ℂ))*phase ((-γ) • v) ((-γ) • e)) •
      SpinOperators.act (R β) (SpinOperators.act X (WZ ((-γ) • (v+e)) x))‖ =
      |Real.sin δ| *‖x‖ := by
  rw [norm_smul,norm_mul,norm_mul,norm_neg,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs,norm_phase,mul_one,
    SpinOperators.norm_act (R_unitary _),SpinOperators.norm_act X_unitary,norm_WZ]

 

theorem quarter_conjugate : (R (Real.pi/4)).conjTranspose*Z*R (Real.pi/4)=Y := by
  rw [R_conjugate_Z]
  have he : 2*(Real.pi/4)=Real.pi/2 := by ring
  simp [he]

end CoherentFock

 

namespace PointedTree
universe u
structure HilbertData where
  Carrier : Type u
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℂ Carrier]
  [complete : CompleteSpace Carrier]
attribute [instance] HilbertData.normed HilbertData.inner HilbertData.complete
instance : CoeSort HilbertData (Type u) := ⟨HilbertData.Carrier⟩

abbrev doubleData (H : HilbertData) : HilbertData where
  Carrier := SpinOperators.Double H

abbrev fockData (H : HilbertData) : HilbertData where
  Carrier := CoherentFock.Space H

abbrev complexData : HilbertData where
  Carrier := ℂ

variable {H K L : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

def spinMap (T : H →ₗᵢ[ℂ] K) : SpinOperators.Double H →ₗᵢ[ℂ] SpinOperators.Double K where
  toFun x := WithLp.toLp 2 (fun i => T (x i))
  map_add' x y := by ext i; simp
  map_smul' z x := by ext i; simp
  norm_map' x := by
    change ‖WithLp.toLp 2 (fun i : Fin 2 => T (x i))‖=‖x‖
    have he : ‖WithLp.toLp 2 (fun i : Fin 2 => T (x i))‖^2=‖x‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
      simp
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i : Fin 2 => T (x i))),norm_nonneg x]

@[simp] theorem spinMap_apply (T : H →ₗᵢ[ℂ] K) (x : SpinOperators.Double H) (i : Fin 2) :
    spinMap T x i=T (x i) := rfl

@[simp] theorem spinMap_comp (T : H →ₗᵢ[ℂ] K) (S : K →ₗᵢ[ℂ] L) :
    (spinMap S).comp (spinMap T)=spinMap (S.comp T) := by ext x i; rfl

@[simp] theorem spinMap_id : spinMap (LinearIsometry.id : H →ₗᵢ[ℂ] H)=LinearIsometry.id := by
  ext x i
  rfl

theorem spinMap_root (T : H →ₗᵢ[ℂ] K) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (x : SpinOperators.Double H) :
    spinMap T (SpinOperators.act A x)=SpinOperators.act A (spinMap T x) := by
  ext i
  simp [SpinOperators.act_apply]

 
def scalarEmbedding (η : H) (hη : ‖η‖=1) : ℂ →ₗᵢ[ℂ] H where
  toFun z := z • η
  map_add' z w := add_smul _ _ _
  map_smul' z w := by simp [mul_smul]
  norm_map' z := by simp [norm_smul,hη]

@[simp] theorem scalarEmbedding_apply (η : H) (hη : ‖η‖=1) (z : ℂ) :
    scalarEmbedding η hη z=z • η := rfl

def plus : SpinOperators.Double ℂ := WithLp.toLp 2 (fun _ => ((Real.sqrt 2)⁻¹ : ℝ))

theorem norm_plus : ‖plus‖=1 := by
  have h : ‖plus‖^2=1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    change ∑ _ : Fin 2, ‖(((Real.sqrt 2)⁻¹:ℝ):ℂ)‖^2=1
    simp only [Complex.norm_real,Real.norm_eq_abs,
      abs_inv,abs_of_nonneg (Real.sqrt_nonneg 2),Fin.sum_univ_two]
    have hs : Real.sqrt 2^2=2 := Real.sq_sqrt (by norm_num)
    rw [inv_pow,hs]
    norm_num
  nlinarith [norm_nonneg plus]

open CoherentFock

def gammaEmbedding (T : H →ₗᵢ[ℂ] K) : Space H →ₗᵢ[ℂ] Space K where
  toLinearMap := (Gamma T).toLinearMap
  norm_map' := norm_Gamma T

@[simp] theorem gammaEmbedding_coherent (T : H →ₗᵢ[ℂ] K) (d : H) :
    gammaEmbedding T (coherent d)=coherent (T d) := Gamma_coherent T d

def vacuum (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : SpinSpace H :=
  spinMap (scalarEmbedding (coherent (0:H)) (norm_coherent _)) plus

@[simp] theorem vacuum_apply (i : Fin 2) :
    vacuum H i=(((Real.sqrt 2)⁻¹ : ℝ):ℂ) • coherent (0:H) := rfl

@[simp] theorem norm_vacuum : ‖vacuum H‖=1 := by
  unfold vacuum
  rw [(spinMap _).norm_map,norm_plus]

structure PointedData extends HilbertData where
  vac : Carrier
  norm_vac : ‖vac‖=1
instance : CoeSort PointedData (Type u) := ⟨fun H => H.Carrier⟩
instance (H : PointedData) : NormedAddCommGroup H := H.normed
instance (H : PointedData) : InnerProductSpace ℂ H := H.inner
instance (H : PointedData) : CompleteSpace H := H.complete

 

def centered (H : PointedData) : Submodule ℂ H := (ℂ ∙ H.vac)ᗮ

instance (H : PointedData) : CompleteSpace (centered H) := by
  unfold centered
  infer_instance

@[simp] theorem mem_centered (H : PointedData) (x : H) :
    x ∈ centered H ↔ ⟪H.vac,x⟫_ℂ=0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right

structure PointedMap (H K : PointedData) where
  toLinearIsometry : H →ₗᵢ[ℂ] K
  map_vac : toLinearIsometry H.vac=K.vac

def centeredMap {H K : PointedData} (T : PointedMap H K) : centered H →ₗᵢ[ℂ] centered K where
  toFun x := ⟨T.toLinearIsometry x,by
    rw [mem_centered,← T.map_vac,T.toLinearIsometry.inner_map_map]
    exact (mem_centered H x).mp x.property⟩
  map_add' x y := by ext; exact T.toLinearIsometry.map_add _ _
  map_smul' z x := by ext; exact T.toLinearIsometry.map_smul _ _
  norm_map' x := T.toLinearIsometry.norm_map x

@[simp] theorem centeredMap_coe {H K : PointedData} (T : PointedMap H K) (x : centered H) :
    (centeredMap T x : K)=T.toLinearIsometry (x:H) := rfl

abbrev base : PointedData where
  toHilbertData := doubleData complexData
  vac := plus
  norm_vac := norm_plus

abbrev next (H : PointedData) : PointedData where
  toHilbertData := doubleData (fockData { Carrier := centered H })
  vac := vacuum (centered H)
  norm_vac := norm_vacuum

def nextMap {H K : PointedData} (T : PointedMap H K) : PointedMap (next H) (next K) where
  toLinearIsometry := spinMap (gammaEmbedding (centeredMap T))
  map_vac := by
    change spinMap (gammaEmbedding (centeredMap T)) (vacuum (centered H))=vacuum (centered K)
    ext i
    simp [vacuum_apply]

@[reducible] def level : ℕ → PointedData
  | 0 => base
  | n+1 => next (level n)

abbrev Level (n : ℕ) := (level n).Carrier
abbrev Mode (n : ℕ) := centered (level n)

def vac (n : ℕ) : Level n := (level n).vac

@[simp] theorem norm_vac (n : ℕ) : ‖vac n‖=1 := (level n).norm_vac

 
def empty : (n : ℕ) → PointedMap (level n) (level (n+1))
  | 0 => ⟨spinMap (scalarEmbedding (coherent (0:Mode 0)) (norm_coherent _)),rfl⟩
  | n+1 => nextMap (empty n)

@[simp] theorem empty_vac (n : ℕ) : (empty n).toLinearIsometry (vac n)=vac (n+1) :=
  (empty n).map_vac

 
def root (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Level n →L[ℂ] Level n :=
  match n with
  | 0 => SpinOperators.act A
  | _+1 => SpinOperators.act A

@[simp] theorem root_empty (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Level n) :
    (empty n).toLinearIsometry (root n A x)=root (n+1) A ((empty n).toLinearIsometry x) := by
  cases n <;> exact spinMap_root _ _ _

theorem spinMap_cost (T : H →ₗᵢ[ℂ] K) (d : H) (x : SpinSpace H) :
    spinMap (gammaEmbedding T) (WZ d x)=WZ (T d) (spinMap (gammaEmbedding T) x) := by
  ext i
  change Gamma T (W (if i=0 then d else -d) (x i))=
    W (if i=0 then T d else -(T d)) (Gamma T (x i))
  have h := congrArg (fun A => A (x i)) (Gamma_W T (if i=0 then d else -d))
  by_cases hi : i=0 <;> simpa [hi] using h

 
theorem cost_empty (n : ℕ) (d : Mode n) (x : Level (n+1)) :
    (empty (n+1)).toLinearIsometry (WZ d x)=
      WZ (centeredMap (empty n) d) ((empty (n+1)).toLinearIsometry x) :=
  spinMap_cost (centeredMap (empty n)) d x

end PointedTree

namespace SpinOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def actEquiv (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) : Double H ≃ₗᵢ[ℂ] Double H :=
  Unitary.linearIsometryEquiv ⟨act A,act_mem_unitary hA⟩

@[simp] theorem actEquiv_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) (x : Double H) :
    actEquiv A hA x=act A x := rfl
end SpinOperators

namespace PointedTree
open CoherentFock RootSpin
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def spinEquiv (T : H ≃ₗᵢ[ℂ] K) : SpinOperators.Double H ≃ₗᵢ[ℂ] SpinOperators.Double K where
  toFun := spinMap T.toLinearIsometry
  invFun := spinMap T.symm.toLinearIsometry
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' := (spinMap T.toLinearIsometry).map_add
  map_smul' := (spinMap T.toLinearIsometry).map_smul
  norm_map' := (spinMap T.toLinearIsometry).norm_map

@[simp] theorem spinEquiv_apply (T : H ≃ₗᵢ[ℂ] K) (x : SpinOperators.Double H) (i : Fin 2) :
    spinEquiv T x i = T (x i) := rfl

theorem spinFlip_twice (T : H →ₗᵢ[ℂ] H) (hT : Function.Involutive T)
    (x : SpinOperators.Double H) :
    SpinOperators.act X (spinMap T (SpinOperators.act X (spinMap T x)))=x := by
  ext i
  fin_cases i <;> simp [SpinOperators.act_apply,X,Fin.sum_univ_two] <;> exact hT _

 
structure Symmetry (H : PointedData) where
  op : H ≃ₗᵢ[ℂ] H
  invariant : op H.vac=H.vac
  square : Function.Involutive op

namespace Symmetry
variable {A : PointedData}

def centered (S : Symmetry A) : PointedTree.centered A ≃ₗᵢ[ℂ] PointedTree.centered A where
  toFun x := ⟨S.op x,by
    rw [mem_centered,← S.invariant,S.op.inner_map_map]
    exact (mem_centered A x).mp x.property⟩
  invFun x := ⟨S.op x,by
    rw [mem_centered,← S.invariant,S.op.inner_map_map]
    exact (mem_centered A x).mp x.property⟩
  left_inv x := by ext; exact S.square x
  right_inv x := by ext; exact S.square x
  map_add' x y := by ext; exact S.op.map_add _ _
  map_smul' z x := by ext; exact S.op.map_smul _ _
  norm_map' x := S.op.norm_map x

@[simp] theorem centered_coe (S : Symmetry A) (x : PointedTree.centered A) :
    (S.centered x:A)=S.op x := rfl

@[simp] theorem centered_square (S : Symmetry A) (x : PointedTree.centered A) :
    S.centered (S.centered x)=x := by ext; exact S.square x

@[simp] theorem gamma_square (S : Symmetry A) (x : Space (PointedTree.centered A)) :
    Gamma S.centered.toLinearIsometry (Gamma S.centered.toLinearIsometry x)=x := by
  have hc : S.centered.toLinearIsometry.comp S.centered.toLinearIsometry=LinearIsometry.id := by
    apply LinearIsometry.ext
    intro v
    exact S.centered_square v
  have h := congrArg (fun T => T x) (Gamma_comp S.centered.toLinearIsometry S.centered.toLinearIsometry)
  simpa [hc] using h

 
def next (S : Symmetry A) : Symmetry (PointedTree.next A) where
  op := (spinEquiv (secondQuantization S.centered)).trans
    (SpinOperators.actEquiv X X_unitary)
  invariant := by
    change SpinOperators.act X (spinEquiv (secondQuantization S.centered) (vacuum _))=vacuum _
    ext i
    fin_cases i <;> simp [vacuum_apply,secondQuantization,X]
  square x := by
    change SpinOperators.act X (spinMap (gammaEmbedding S.centered.toLinearIsometry)
      (SpinOperators.act X (spinMap (gammaEmbedding S.centered.toLinearIsometry) x)))=x
    exact spinFlip_twice (gammaEmbedding S.centered.toLinearIsometry) (fun y => S.gamma_square y) x

end Symmetry

 
def baseSymmetry : Symmetry base where
  op := SpinOperators.actEquiv X X_unitary
  invariant := by
    change SpinOperators.act (H := ℂ) X plus=plus
    ext i
    fin_cases i <;> simp [plus,SpinOperators.act_apply,X,Fin.sum_univ_two]
  square x := by
    change SpinOperators.act (H := ℂ) X (SpinOperators.act X x)=x
    ext i
    fin_cases i <;> simp [SpinOperators.act_apply,X,Fin.sum_univ_two]

 
def symmetry : (n : ℕ) → Symmetry (level n)
  | 0 => baseSymmetry
  | n+1 => (symmetry n).next

@[simp] theorem symmetry_vac (n : ℕ) : (symmetry n).op (vac n)=vac n :=
  (symmetry n).invariant

@[simp] theorem symmetry_square (n : ℕ) (x : Level n) :
    (symmetry n).op ((symmetry n).op x)=x := (symmetry n).square x

 

theorem odd_centered {A : PointedData} (S : Symmetry A) (x : A) (hx : S.op x=-x) :
    x ∈ centered A := by
  rw [mem_centered]
  have h := S.op.inner_map_map A.vac x
  rw [S.invariant,hx,inner_neg_right] at h
  linear_combination - (1/2:ℂ) * h

end PointedTree

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem W_neg_cancel_left (d : E) (x : Space E) : W (-d) (W d x)=x :=
  (weyl d).symm_apply_apply x

 
def costEquiv (d : E) : SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E where
  toFun := WZ d
  invFun := WZ (-d)
  left_inv x := by
    ext i
    fin_cases i <;> simp [WZ_apply, W_neg_cancel]
  right_inv x := by
    ext i
    fin_cases i <;> simp [WZ_apply, W_neg_cancel]
  map_add' := (WZ d).map_add
  map_smul' := (WZ d).map_smul
  norm_map' := norm_WZ d

@[simp] theorem costEquiv_apply (d : E) (x : SpinSpace E) : costEquiv d x=WZ d x := rfl
@[simp] theorem costEquiv_symm_apply (d : E) (x : SpinSpace E) : (costEquiv d).symm x=WZ (-d) x := rfl
end CoherentFock

namespace PointedTree
open RootSpin CoherentFock
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem flipMap_rootZ (T : H →ₗᵢ[ℂ] H) (x : SpinOperators.Double H) :
    SpinOperators.act X (spinMap T (SpinOperators.act Z x))=
      -SpinOperators.act Z (SpinOperators.act X (spinMap T x)) := by
  rw [spinMap_root]
  ext i
  fin_cases i <;> simp [SpinOperators.act_apply,X,Z,Fin.sum_univ_two]

theorem flipMap_rootR (T : H →ₗᵢ[ℂ] H) (t : ℝ) (x : SpinOperators.Double H) :
    SpinOperators.act X (spinMap T (SpinOperators.act (R t) x))=
      SpinOperators.act (R t) (SpinOperators.act X (spinMap T x)) := by
  rw [spinMap_root]
  ext i
  fin_cases i <;> simp [SpinOperators.act_apply,X,R_apply,Fin.sum_univ_two,add_comm]

 
theorem symmetry_rootZ (n : ℕ) (x : Level n) :
    (symmetry n).op (root n Z x)=-root n Z ((symmetry n).op x) := by
  cases n with
  | zero =>
    change SpinOperators.act (H := ℂ) X (SpinOperators.act Z x)= -SpinOperators.act Z (SpinOperators.act X x)
    simpa only [spinMap_id,LinearIsometry.id_apply] using flipMap_rootZ (LinearIsometry.id : ℂ →ₗᵢ[ℂ] ℂ) x
  | succ n => exact flipMap_rootZ (gammaEmbedding (symmetry n).centered.toLinearIsometry) x

theorem symmetry_rootR (n : ℕ) (t : ℝ) (x : Level n) :
    (symmetry n).op (root n (R t) x)=root n (R t) ((symmetry n).op x) := by
  cases n with
  | zero =>
    change SpinOperators.act (H := ℂ) X (SpinOperators.act (R t) x)=SpinOperators.act (R t) (SpinOperators.act X x)
    simpa only [spinMap_id,LinearIsometry.id_apply] using flipMap_rootR (LinearIsometry.id : ℂ →ₗᵢ[ℂ] ℂ) t x
  | succ n => exact flipMap_rootR (gammaEmbedding (symmetry n).centered.toLinearIsometry) t x

 
def rootEquiv (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) : Level n ≃ₗᵢ[ℂ] Level n :=
  match n with
  | 0 => SpinOperators.actEquiv A hA
  | _+1 => SpinOperators.actEquiv A hA

@[simp] theorem rootEquiv_apply (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A ∈ unitary _) (x : Level n) :
    rootEquiv n A hA x=root n A x := by cases n <;> rfl

@[simp] theorem norm_rootZ (n : ℕ) (x : Level n) : ‖root n Z x‖=‖x‖ :=
  by simpa only [rootEquiv_apply] using (rootEquiv n Z Z_unitary).norm_map x

 

structure EvenUnitary (n : ℕ) where
  op : Level n ≃ₗᵢ[ℂ] Level n
  commutes : ∀x, (symmetry n).op (op x)=op ((symmetry n).op x)

namespace EvenUnitary

def ident (n : ℕ) : EvenUnitary n where
  op := LinearIsometryEquiv.refl ℂ (Level n)
  commutes _ := rfl

 
def followedBy {n : ℕ} (U V : EvenUnitary n) : EvenUnitary n where
  op := U.op.trans V.op
  commutes x := by
    change (symmetry n).op (V.op (U.op x))=V.op (U.op ((symmetry n).op x))
    rw [V.commutes,U.commutes]

theorem symm_commutes {n : ℕ} (U : EvenUnitary n) (x : Level n) :
    (symmetry n).op (U.op.symm x)=U.op.symm ((symmetry n).op x) := by
  apply U.op.injective
  rw [← U.commutes,U.op.apply_symm_apply,U.op.apply_symm_apply]

 
def insertion {n : ℕ} (U : EvenUnitary n) : Mode n :=
  ⟨U.op.symm (root n Z (U.op (vac n))),by
    apply odd_centered (symmetry n)
    rw [U.symm_commutes,symmetry_rootZ,U.commutes,symmetry_vac,map_neg]⟩

@[simp] theorem insertion_coe {n : ℕ} (U : EvenUnitary n) :
    (U.insertion:Level n)=U.op.symm (root n Z (U.op (vac n))) := rfl

@[simp] theorem norm_insertion {n : ℕ} (U : EvenUnitary n) : ‖U.insertion‖=1 := by
  change ‖U.op.symm (root n Z (U.op (vac n)))‖=1
  rw [U.op.symm.norm_map,norm_rootZ,U.op.norm_map,norm_vac]

@[simp] theorem insertion_odd {n : ℕ} (U : EvenUnitary n) :
    (symmetry n).centered U.insertion=-U.insertion := by
  apply Subtype.ext
  change (symmetry n).op (U.op.symm (root n Z (U.op (vac n))))=
    -U.op.symm (root n Z (U.op (vac n)))
  rw [U.symm_commutes,symmetry_rootZ,U.commutes,symmetry_vac,map_neg]

def mixer (n : ℕ) (t : ℝ) : EvenUnitary n where
  op := rootEquiv n (R t) (R_unitary t)
  commutes x := by simpa only [rootEquiv_apply] using symmetry_rootR n t x

 
def cost (n : ℕ) (d : Mode n) (hd : (symmetry n).centered d=-d) : EvenUnitary (n+1) where
  op := costEquiv d
  commutes x := by
    change SpinOperators.act X
      (spinMap (gammaEmbedding (symmetry n).centered.toLinearIsometry) (WZ d x))=
      WZ d (SpinOperators.act X
        (spinMap (gammaEmbedding (symmetry n).centered.toLinearIsometry) x))
    change (symmetry n).centered.toLinearIsometry d=-d at hd
    rw [spinMap_cost,hd]
    exact congrArg (fun A : SpinSpace (Mode n) →L[ℂ] SpinSpace (Mode n) =>
      A (spinMap (gammaEmbedding (symmetry n).centered.toLinearIsometry) x)) (WZ_rootX d).symm

 
theorem cost_insertion (n : ℕ) (U : EvenUnitary (n+1)) (d : Mode n)
    (hd : (symmetry n).centered d=-d) : (U.followedBy (cost n d hd)).insertion=U.insertion := by
  apply Subtype.ext
  change U.op.symm ((costEquiv d).symm (SpinOperators.act Z (costEquiv d (U.op (vac (n+1))))))=
    U.op.symm (SpinOperators.act Z (U.op (vac (n+1))))
  congr 1
  apply (costEquiv d).injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact congrArg (fun A : SpinSpace (Mode n) →L[ℂ] SpinSpace (Mode n) => A (U.op (vac (n+1))))
    (WZ_rootZ d).symm

end EvenUnitary
end PointedTree

end

end OAI
