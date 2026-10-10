import Mathlib
import OAI.Probability.ParisiFinite.Compatible

namespace OAI

/-! Insertion From Forward. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
namespace ForwardControl
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem insertion_from_forward (U A : H ≃ₗᵢ[ℂ] H) (P : H →L[ℂ] H)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (Ω : H) (ζ : ℂ) :
    ‖U.symm (P (U Ω))-A.symm (P (A Ω))‖ ≤
      ‖U Ω-ζ • A Ω‖+‖U (A.symm (P (A Ω)))-ζ • A (A.symm (P (A Ω)))‖ := by
  rw [← U.norm_map (U.symm (P (U Ω))-A.symm (P (A Ω))),map_sub,U.apply_symm_apply]
  calc
    _ ≤ ‖P (U Ω)-ζ • P (A Ω)‖+
        ‖ζ • P (A Ω)-U (A.symm (P (A Ω)))‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖U Ω-ζ • A Ω‖+
        ‖U (A.symm (P (A Ω)))-ζ • A (A.symm (P (A Ω)))‖ := by
      rw [A.apply_symm_apply,norm_sub_rev (ζ • P (A Ω))]
      exact add_le_add (by simpa only [map_sub,map_smul] using hP (U Ω-ζ • A Ω)) le_rfl

 
theorem insertion_split_bound (U A : H ≃ₗᵢ[ℂ] H) (P : H →L[ℂ] H)
    (hP : ∀x, ‖P x‖ ≤ ‖x‖) (Ω : H) (ζ : ℂ)
    (O S : H →L[ℂ] H) (hsplit : ∀x, U x=O x+S x)
    (r ε : ℝ) (hr : 0 ≤ r)
    (hS : ∀x, ‖S x‖ ≤ r*‖x‖)
    (hO₀ : ‖O Ω-ζ • A Ω‖ ≤ ε)
    (hO₁ : ‖O (A.symm (P (A Ω)))-ζ • A (A.symm (P (A Ω)))‖ ≤ ε) :
    ‖U.symm (P (U Ω))-A.symm (P (A Ω))‖ ≤ 2*ε+2*r*‖Ω‖ := by
  have hv : ‖A.symm (P (A Ω))‖ ≤ ‖Ω‖ := by
    rw [A.symm.norm_map]
    exact (hP _).trans_eq (A.norm_map _)
  have hb (x : H) : ‖U x-ζ • A x‖ ≤ ‖O x-ζ • A x‖+r*‖x‖ := by
    rw [hsplit]
    have he : O x+S x-ζ • A x=(O x-ζ • A x)+S x := by abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl (hS x))
  have h := insertion_from_forward U A P hP Ω ζ
  have h0 := hb Ω
  have h1 := hb (A.symm (P (A Ω)))
  have hh := mul_le_mul_of_nonneg_left hv hr
  linarith

 

theorem selective_flip_bound (V : H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x, ‖Z x‖ ≤ ‖x‖) (hanti : ∀x, Z (F x)=-F (Z x)) (o s : H) :
    ‖V.symm (Z (V (o+s)))-(Z o-Z s)‖ ≤
      ‖V o-o‖+‖V s-F s‖+‖V (Z o)-Z o‖+‖V (Z s)-F (Z s)‖ := by
  rw [← V.norm_map (V.symm (Z (V (o+s)))-(Z o-Z s)),map_sub,V.apply_symm_apply]
  have he : Z (V (o+s))-V (Z o-Z s) =
      Z (V o-o)+Z (V s-F s)-(V (Z o)-Z o)+(V (Z s)-F (Z s)) := by
    simp only [map_add,map_sub,hanti]
    abel
  rw [he]
  have h1 := norm_add_le (Z (V o-o)+Z (V s-F s)-(V (Z o)-Z o))
    (V (Z s)-F (Z s))
  have h2 := norm_sub_le (Z (V o-o)+Z (V s-F s)) (V (Z o)-Z o)
  have h3 := norm_add_le (Z (V o-o)) (Z (V s-F s))
  have h4 := hZ (V o-o)
  have h5 := hZ (V s-F s)
  linarith

 

theorem actual_flip_change (U V : H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x, ‖Z x‖ ≤ ‖x‖) (hanti : ∀x, Z (F x)=-F (Z x))
    (Ω o s : H) (hx : U Ω=o+s) :
    ‖U.symm (V.symm (Z (V (U Ω))))-U.symm (Z (U Ω))+
      (2:ℂ) • U.symm (Z s)‖ ≤
      ‖V o-o‖+‖V s-F s‖+‖V (Z o)-Z o‖+‖V (Z s)-F (Z s)‖ := by
  have he : U.symm (V.symm (Z (V (U Ω))))-U.symm (Z (U Ω))+
      (2:ℂ) • U.symm (Z s) =
      U.symm (V.symm (Z (V (o+s)))-(Z o-Z s)) := by
    rw [hx]
    simp only [map_sub,map_add]
    module
  rw [he,U.symm.norm_map]
  exact selective_flip_bound V Z F hZ hanti o s

 

theorem special_transport_bound (V : H ≃ₗᵢ[ℂ] H) (Z F : H →L[ℂ] H)
    (hZ : ∀x, ‖Z x‖ ≤ ‖x‖) (hanti : ∀x, Z (F x)=-F (Z x)) (s : H) :
    ‖V.symm (Z (V s))+Z s‖ ≤ ‖V s-F s‖+‖V (Z s)-F (Z s)‖ := by
  rw [← V.norm_map (V.symm (Z (V s))+Z s),map_add,V.apply_symm_apply]
  have he : Z (V s)+V (Z s)=Z (V s-F s)+(V (Z s)-F (Z s)) := by
    rw [map_sub,hanti]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hZ _) le_rfl)

end ForwardControl

namespace PointedTree
open CoherentFock RootSpin

 
theorem abs_treeEnergy_le (n : ℕ) (d : Mode n) : |treeEnergy n d| ≤ ‖d‖^2 := by
  calc
    _ ≤ ‖⟪centeredMap (empty n) d,rootShift n d⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖centeredMap (empty n) d‖*‖rootShift n d‖ := norm_inner_le_norm _ _
    _ = _ := by simp [pow_two]

 

def ordinaryValue (w : List Gate) : ℝ := treeEnergy w.length (ordinary w w.length).insertion

theorem ordinary_energy_succ (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    treeEnergy (n+1) (ordinary w (n+1)).insertion=treeEnergy n (ordinary w n).insertion := by
  rw [← ordinary_insertion_empty w n hn,treeEnergy_empty]

theorem ordinary_energy_stable (w : List Gate) (n : ℕ) (hn : w.length ≤ n) :
    treeEnergy n (ordinary w n).insertion=ordinaryValue w := by
  induction n,hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [ordinary_energy_succ w n hn,ih]

theorem abs_ordinaryValue_le_one (w : List Gate) : |ordinaryValue w| ≤ 1 := by
  simpa only [ordinaryValue,EvenUnitary.norm_insertion,one_pow] using abs_treeEnergy_le w.length (ordinary w w.length).insertion

end PointedTree

namespace SpinOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
@[simp] theorem actEquiv_symm_apply (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ unitary _) (x : Double H) :
    (actEquiv A hA).symm x=act A.conjTranspose x := by
  apply (actEquiv A hA).injective
  rw [LinearIsometryEquiv.apply_symm_apply,actEquiv_apply]
  change x=(act A).comp (act A.conjTranspose) x
  rw [← act_mul]
  have h := (Unitary.mem_iff.mp hA).2
  change A*A.conjTranspose=1 at h
  rw [h,act_one]
  rfl
end SpinOperators

namespace CoherentFock
open RootSpin
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]

@[simp] theorem rootY_apply (x : SpinSpace E) (i : Fin 2) :
    SpinOperators.act Y x i=if i=0 then (-Complex.I) • x 1 else Complex.I • x 0 := by
  fin_cases i <;> simp [SpinOperators.act_apply,Y,Fin.sum_univ_two]

theorem WZ_rootY (d : E) :
    (WZ d).comp (SpinOperators.act Y)=(SpinOperators.act Y).comp (WZ (-d)) := by
  ext x i
  fin_cases i <;> simp [WZ_apply,Y]

@[simp] theorem WZ_same (d : E) (x : SpinSpace E) : WZ d (WZ d x)=WZ (d+d) x := by
  change (WZ d).comp (WZ d) x=_
  rw [WZ_mul]
  have hi : (⟪d,d⟫_ℂ).im=0 := inner_self_im (𝕜 := ℂ) d
  change Complex.exp ((-(⟪d,d⟫_ℂ).im:ℝ)*Complex.I) • WZ (d+d) x=WZ (d+d) x
  rw [hi]
  simp

 
theorem one_layer_insertion (d : E) (β : ℝ) (x : SpinSpace E) :
    WZ (-d) (SpinOperators.act (R β).conjTranspose
      (SpinOperators.act Z (SpinOperators.act (R β) (WZ d x))))=
      (Real.cos (2*β):ℂ) • SpinOperators.act Z x+
      (Real.sin (2*β):ℂ) • SpinOperators.act Y (WZ (d+d) x) := by
  change WZ (-d) ((SpinOperators.act (R β).conjTranspose).comp
    ((SpinOperators.act Z).comp (SpinOperators.act (R β))) (WZ d x))=_
  rw [← ContinuousLinearMap.comp_assoc,← SpinOperators.act_mul,← SpinOperators.act_mul,R_conjugate_Z]
  change WZ (-d) (SpinOperators.rep
    ((Real.cos (2*β):ℂ) • Z+(Real.sin (2*β):ℂ) • Y) (WZ d x))=_
  simp only [map_add,map_smul,SpinOperators.rep_apply,add_apply,smul_apply]
  congr 1
  · congr 1
    change (WZ (-d)).comp (SpinOperators.act Z) (WZ d x)=_
    rw [WZ_rootZ]
    change SpinOperators.act Z (WZ (-d) (WZ d x))=_
    rw [← costEquiv_symm_apply,← costEquiv_apply,LinearIsometryEquiv.symm_apply_apply]
  · congr 1
    change (WZ (-d)).comp (SpinOperators.act Y) (WZ d x)=_
    rw [WZ_rootY,neg_neg]
    exact congrArg (SpinOperators.act Y) (WZ_same d x)
end CoherentFock

namespace PointedTree
open CoherentFock RootSpin

 
def initialDirection (n : ℕ) : Mode n := (EvenUnitary.ident n).insertion

@[simp] theorem initialDirection_coe (n : ℕ) :
    (initialDirection n : Level n)=root n Z (vac n) := rfl

@[simp] theorem initialDirection_norm (n : ℕ) : ‖initialDirection n‖=1 :=
  EvenUnitary.norm_insertion _

@[simp] theorem initialDirection_empty (n : ℕ) :
    centeredMap (empty n) (initialDirection n)=initialDirection (n+1) :=
  (EvenUnitary.compatible_ident n).insertion

 

theorem ordinary_one_insertion (n : ℕ) (γ β : ℝ) :
    ((ordinary [.mixer β,.cost γ] (n+1)).insertion : Level (n+1))=
      (Real.cos (2*β):ℂ) • (initialDirection (n+1) : Level (n+1))+
      (Real.sin (2*β):ℂ) • SpinOperators.act Y
        (WZ ((-(2*γ):ℂ) • initialDirection n) (vac (n+1))) := by
  change (costEquiv ((-(γ:ℂ)) • initialDirection n)).symm
    ((SpinOperators.actEquiv (R β) (R_unitary β)).symm
      (SpinOperators.act Z (SpinOperators.act (R β)
        (costEquiv ((-(γ:ℂ)) • initialDirection n) (vac (n+1))))))=_
  rw [costEquiv_symm_apply,SpinOperators.actEquiv_symm_apply,costEquiv_apply,one_layer_insertion]
  have hd : (-(γ:ℂ)) • initialDirection n+(-(γ:ℂ)) • initialDirection n=
      (-(2*γ):ℂ) • initialDirection n := by module
  rw [hd]
  rfl

 
def initializationWord (γ δ β : ℝ) : List Gate :=
  [.mixer β,.cost (-γ),.mixer δ,.cost γ]

theorem initialization_op (n : ℕ) (γ δ β : ℝ) (x : Level (n+2)) :
    (ordinary (initializationWord γ δ β) (n+2)).op x=
      SpinOperators.act (R β)
        (WZ ((γ:ℂ) • (ordinary [.mixer δ,.cost γ] (n+1)).insertion)
          (SpinOperators.act (R δ) (WZ (-(γ:ℂ) • initialDirection (n+1)) x))) := by
  change SpinOperators.act (R β)
    (WZ ((-((-γ:ℝ):ℂ)) • (ordinary [.mixer δ,.cost γ] (n+1)).insertion)
      (SpinOperators.act (R δ) (WZ (-(γ:ℂ) • initialDirection (n+1)) x)))=_
  simp only [Complex.ofReal_neg,neg_neg]

end PointedTree

namespace CoherentFock
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
@[simp] theorem W_vacuum (d : E) : W d (coherent 0)=coherent d := by simp
@[simp] theorem kernel_zero_left (d : E) : kernel 0 d=(Real.exp (-‖d‖^2/2):ℂ) := by
  simp [kernel_eq,Complex.ofReal_exp]
end CoherentFock

namespace PointedTree
open CoherentFock RootSpin Complex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inv_sqrt_two_sq : (((Real.sqrt 2)⁻¹:ℝ):ℂ)^2=1/2 := by
  rw [← Complex.ofReal_pow,inv_pow,Real.sq_sqrt (by norm_num)]
  norm_num

def spinPair (x y : H) : SpinOperators.Double H :=
  WithLp.toLp 2 (fun i => if i=0 then x else y)

@[simp] theorem spinPair_zero (x y : H) : spinPair x y 0=x := by rfl
@[simp] theorem spinPair_one (x y : H) : spinPair x y 1=y := by rfl

theorem inner_spinPair (x y u v : H) :
    ⟪spinPair x y,spinPair u v⟫_ℂ=⟪x,u⟫_ℂ+⟪y,v⟫_ℂ := by
  rw [PiLp.inner_apply,Fin.sum_univ_two]
  rfl

def spinCoefficient : ℂ := (((Real.sqrt 2)⁻¹:ℝ):ℂ)
@[simp] theorem spinCoefficient_conj : conj spinCoefficient=spinCoefficient := by
  simp [spinCoefficient]
@[simp] theorem spinCoefficient_sq : spinCoefficient^2=1/2 := inv_sqrt_two_sq

theorem plusEmbedding_pair (x : H) :
    plusEmbedding x=spinPair (spinCoefficient • x) (spinCoefficient • x) := by
  ext i
  fin_cases i <;> rfl

theorem rootZ_vac_pair : SpinOperators.act Z (vacuum H)=
    spinPair (spinCoefficient • coherent (0:H)) (-(spinCoefficient • coherent (0:H))) := by
  ext i
  fin_cases i <;> simp [Z,spinPair,vacuum_apply,spinCoefficient]

theorem rootY_WZ_vac_pair (d : H) : SpinOperators.act Y (WZ d (vacuum H))=
    spinPair ((-I*spinCoefficient) • coherent (-d)) ((I*spinCoefficient) • coherent d) := by
  ext i
  fin_cases i <;> simp [Y,spinPair,WZ_apply,vacuum_apply,spinCoefficient,smul_smul]

theorem inner_rootZ_vac_creation (v : H) :
    ⟪SpinOperators.act Z (vacuum H),plusEmbedding (creationVacuum v)⟫_ℂ=0 := by
  rw [rootZ_vac_pair,plusEmbedding_pair,inner_spinPair,inner_neg_left]
  exact add_neg_cancel _

theorem inner_rootZ_vac_rootY_WZ (d : H) :
    ⟪SpinOperators.act Z (vacuum H),SpinOperators.act Y (WZ d (vacuum H))⟫_ℂ=
      -I*(Real.exp (-‖d‖^2/2):ℂ) := by
  rw [rootZ_vac_pair,rootY_WZ_vac_pair,inner_spinPair]
  simp only [inner_neg_left,inner_smul_left,inner_smul_right,spinCoefficient_conj,
    inner_coherent,kernel_zero_left,norm_neg]
  linear_combination -2*I*(Real.exp (-‖d‖^2/2):ℂ)*spinCoefficient_sq

theorem inner_rootY_WZ_creation (d v : H) :
    ⟪SpinOperators.act Y (WZ d (vacuum H)),plusEmbedding (creationVacuum v)⟫_ℂ=
      -(Real.exp (-‖d‖^2/2):ℂ)*⟪d,v⟫_ℂ := by
  rw [rootY_WZ_vac_pair,plusEmbedding_pair,inner_spinPair]
  simp only [creationVacuum,inner_smul_left,inner_smul_right,
    inner_coherent_oneParticle,inner_neg_left,norm_neg,map_neg,map_mul,Complex.conj_I,
    spinCoefficient_conj]
  linear_combination -2*(Real.exp (-‖d‖^2/2):ℂ)*⟪d,v⟫_ℂ*spinCoefficient_sq +
    2*spinCoefficient^2*(Real.exp (-‖d‖^2/2):ℂ)*⟪d,v⟫_ℂ*Complex.I_sq

end PointedTree

namespace PointedTree
open CoherentFock RootSpin Complex

 
def highDirection (n : ℕ) (γ : ℝ) : Mode (n+1) :=
  (ordinary [.mixer (Real.pi/4),.cost γ] (n+1)).insertion

@[simp] theorem highDirection_coe (n : ℕ) (γ : ℝ) :
    (highDirection n γ : Level (n+1))=
      SpinOperators.act Y (WZ ((-2*γ:ℝ) • initialDirection n) (vac (n+1))) := by
  unfold highDirection
  rw [ordinary_one_insertion]
  have hpi : 2*(Real.pi/4)=Real.pi/2 := by ring
  simp only [hpi,Real.cos_pi_div_two,Real.sin_pi_div_two,Complex.ofReal_zero,
    Complex.ofReal_one,zero_smul,one_smul,zero_add]
  have hd : (-(2*γ):ℂ) • initialDirection n = (-2*γ:ℝ) • initialDirection n := by
    rw [← Complex.coe_smul]
    apply congrArg (fun z : ℂ => z • initialDirection n)
    push_cast
    ring
  rw [hd]

@[simp] theorem highDirection_norm (n : ℕ) (γ : ℝ) : ‖highDirection n γ‖=1 :=
  EvenUnitary.norm_insertion _

@[simp] theorem highDirection_empty (n : ℕ) (γ : ℝ) :
    centeredMap (empty (n+1)) (highDirection n γ)=highDirection (n+1) γ := by
  apply Subtype.ext
  rw [centeredMap_coe,highDirection_coe,highDirection_coe]
  change (empty (n+1)).toLinearIsometry (root (n+1) Y _) = root (n+2) Y _
  rw [root_empty,cost_empty,empty_vac]
  have hd : centeredMap (empty n) ((-2*γ:ℝ) • initialDirection n)=
      (-2*γ:ℝ) • initialDirection (n+1) := by
    calc
      _ = (-2*γ:ℝ) • centeredMap (empty n) (initialDirection n) :=
        (centeredMap (empty n)).map_smul_of_tower _ _
      _ = _ := by rw [initialDirection_empty]
  rw [hd]

theorem initial_inner_highDirection (n : ℕ) (γ : ℝ) :
    ⟪initialDirection (n+1),highDirection n γ⟫_ℂ=
      -I*(Real.exp (-2*γ^2):ℂ) := by
  change ⟪(initialDirection (n+1):Level (n+1)),(highDirection n γ:Level (n+1))⟫_ℂ=_
  rw [initialDirection_coe,highDirection_coe]
  change ⟪SpinOperators.act Z (vacuum (Mode n)),SpinOperators.act Y (WZ _ (vacuum (Mode n)))⟫_ℂ=_
  rw [inner_rootZ_vac_rootY_WZ]
  have hn : ‖(-2*γ:ℝ) • initialDirection n‖^2=4*γ^2 := by
    rw [norm_smul,initialDirection_norm,mul_one,Real.norm_eq_abs,sq_abs]
    ring
  rw [hn]
  congr 3
  ring

end PointedTree

namespace PointedTree
open CoherentFock RootSpin Complex

theorem ordinary_one_mode (n : ℕ) (γ β : ℝ) :
    (ordinary [.mixer β,.cost γ] (n+1)).insertion=
      (Real.cos (2*β):ℂ) • initialDirection (n+1)+
        (Real.sin (2*β):ℂ) • highDirection n γ := by
  apply Subtype.ext
  rw [ordinary_one_insertion]
  change _ = (Real.cos (2*β):ℂ) • (initialDirection (n+1):Level (n+1))+
    (Real.sin (2*β):ℂ) • (highDirection n γ:Level (n+1))
  rw [highDirection_coe]
  have hd : (-(2*γ):ℂ) • initialDirection n=(-2*γ:ℝ) • initialDirection n := by
    rw [← Complex.coe_smul]
    apply congrArg (fun z : ℂ => z • initialDirection n)
    push_cast
    ring
  rw [hd]

theorem inner_highDirection_creation (n : ℕ) (γ : ℝ) (v : Mode n) :
    ⟪(highDirection n γ:Level (n+1)),plusEmbedding (creationVacuum v)⟫_ℂ=
      (2*γ*Real.exp (-2*γ^2):ℂ)*⟪initialDirection n,v⟫_ℂ := by
  rw [highDirection_coe]
  change ⟪SpinOperators.act Y (WZ ((-2*γ:ℝ) • initialDirection n)
    (vacuum (Mode n))),plusEmbedding (creationVacuum v)⟫_ℂ=_
  rw [inner_rootY_WZ_creation]
  have hi : ⟪(-2*γ:ℝ) • initialDirection n,v⟫_ℂ=
      ((-2*γ:ℝ):ℂ)*⟪initialDirection n,v⟫_ℂ := by
    rw [← Complex.coe_smul,inner_smul_left,Complex.conj_ofReal]
  rw [hi]
  have hn : ‖(-2*γ:ℝ) • initialDirection n‖^2=4*γ^2 := by
    rw [norm_smul,initialDirection_norm,mul_one,Real.norm_eq_abs,sq_abs]
    ring
  rw [hn,show -(4*γ^2)/2= -2*γ^2 by ring]
  push_cast
  ring

theorem inner_initial_rootShift (n : ℕ) (v : Mode n) :
    ⟪initialDirection (n+1),rootShift n v⟫_ℂ=0 := by
  change ⟪(initialDirection (n+1):Level (n+1)),(rootShift n v:Level (n+1))⟫_ℂ=0
  rw [initialDirection_coe,rootShift_coe]
  exact inner_rootZ_vac_creation v

theorem inner_highDirection_rootShift (n : ℕ) (γ : ℝ) (v : Mode n) :
    ⟪highDirection n γ,rootShift n v⟫_ℂ=
      (2*γ*Real.exp (-2*γ^2):ℂ)*⟪initialDirection n,v⟫_ℂ :=
  inner_highDirection_creation n γ v

@[simp] theorem inner_initialDirection_self (n : ℕ) :
    ⟪initialDirection n,initialDirection n⟫_ℂ=1 := by
  rw [inner_self_eq_norm_sq_to_K,initialDirection_norm]
  norm_num

 

theorem treeEnergy_one (n : ℕ) (γ β : ℝ) :
    treeEnergy (n+1) (ordinary [.mixer β,.cost γ] (n+1)).insertion=
      γ*Real.sin (4*β)*Real.exp (-2*γ^2) := by
  rw [ordinary_one_mode]
  unfold treeEnergy
  rw [map_add,map_smul,map_smul,initialDirection_empty,highDirection_empty,
    inner_add_left,inner_smul_left,inner_smul_left,inner_initial_rootShift,
    inner_highDirection_rootShift,inner_add_right,inner_smul_right,inner_smul_right,
    inner_initialDirection_self,initial_inner_highDirection]
  simp only [Complex.conj_ofReal,mul_zero,zero_add]
  have hs : Real.sin (4*β)=2*Real.sin (2*β)*Real.cos (2*β) := by
    rw [show 4*β=2*(2*β) by ring]
    exact Real.sin_two_mul (2*β)
  rw [hs]
  simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.one_re,
    Complex.neg_re,Complex.I_re,Complex.ofReal_im,Complex.add_im,Complex.mul_im,
    Complex.neg_im,Complex.I_im,Complex.one_im,Complex.re_ofNat,Complex.im_ofNat]
  ring

theorem ordinaryValue_one (γ β : ℝ) :
    ordinaryValue [.mixer β,.cost γ]=γ*Real.sin (4*β)*Real.exp (-2*γ^2) := by
  exact treeEnergy_one 1 γ β

end PointedTree

open Filter Topology

namespace SeedInitialization

def amplitude (t : ℝ) : ℝ := t⁻¹
def delta (t : ℝ) : ℝ := Real.arcsin (amplitude t)
def gamma (b t : ℝ) : ℝ := b*t

theorem amplitude_pos {t : ℝ} (ht : 1 ≤ t) : 0 < amplitude t :=
  inv_pos.mpr (lt_of_lt_of_le zero_lt_one ht)
theorem amplitude_le_one {t : ℝ} (ht : 1 ≤ t) : amplitude t ≤ 1 := by
  exact inv_le_one_of_one_le₀ ht

theorem sin_delta {t : ℝ} (ht : 1 ≤ t) : Real.sin (delta t)=amplitude t := by
  exact Real.sin_arcsin (by linarith [amplitude_pos ht]) (amplitude_le_one ht)

theorem cos_delta (t : ℝ) : Real.cos (delta t)=Real.sqrt (1-(amplitude t)^2) :=
  Real.cos_arcsin _

theorem cos_two_delta {t : ℝ} (ht : 1 ≤ t) :
    Real.cos (2*delta t)=1-2*(amplitude t)^2 := by
  rw [Real.cos_two_mul',sin_delta ht]
  have h := Real.sin_sq_add_cos_sq (delta t)
  rw [sin_delta ht] at h
  linarith

theorem sin_two_delta {t : ℝ} (ht : 1 ≤ t) :
    Real.sin (2*delta t)=2*amplitude t*Real.sqrt (1-(amplitude t)^2) := by
  rw [Real.sin_two_mul,sin_delta ht,cos_delta]

theorem gamma_cos_error {t : ℝ} (ht : 1 ≤ t) (b : ℝ) :
    gamma b t*(Real.cos (2*delta t)-1)= -2*b*amplitude t := by
  rw [cos_two_delta ht]
  unfold gamma amplitude
  field_simp
  ring

theorem gamma_sin {t : ℝ} (ht : 1 ≤ t) (b : ℝ) :
    gamma b t*Real.sin (2*delta t)=2*b*Real.sqrt (1-(amplitude t)^2) := by
  rw [sin_two_delta ht]
  unfold gamma amplitude
  have hz : t≠0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  field_simp

theorem tendsto_amplitude : Tendsto amplitude atTop (𝓝 0) := tendsto_inv_atTop_zero

theorem tendsto_delta : Tendsto delta atTop (𝓝 0) := by
  change Tendsto (fun t => Real.arcsin (amplitude t)) atTop (𝓝 0)
  simpa [delta,Function.comp_def] using Real.continuous_arcsin.continuousAt.tendsto.comp tendsto_amplitude

theorem tendsto_cos_delta : Tendsto (fun t => Real.cos (delta t)) atTop (𝓝 1) := by
  simpa only [Function.comp_def,Real.cos_zero,Real.sin_zero,mul_zero] using Real.continuous_cos.continuousAt.tendsto.comp tendsto_delta

theorem tendsto_cos_two_delta : Tendsto (fun t => Real.cos (2*delta t)) atTop (𝓝 1) := by
  simpa only [Function.comp_def,Real.cos_zero,Real.sin_zero,mul_zero] using Real.continuous_cos.continuousAt.tendsto.comp (tendsto_delta.const_mul 2)

theorem tendsto_sin_two_delta : Tendsto (fun t => Real.sin (2*delta t)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Real.cos_zero,Real.sin_zero,mul_zero] using Real.continuous_sin.continuousAt.tendsto.comp (tendsto_delta.const_mul 2)

theorem tendsto_gamma_cos_error (b : ℝ) :
    Tendsto (fun t => gamma b t*(Real.cos (2*delta t)-1)) atTop (𝓝 0) := by
  apply Tendsto.congr' (f₁ := fun t => -2*b*amplitude t)
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    exact (gamma_cos_error ht b).symm
  · simpa using tendsto_amplitude.const_mul (-2*b)

theorem tendsto_gamma_sin (b : ℝ) :
    Tendsto (fun t => gamma b t*Real.sin (2*delta t)) atTop (𝓝 (2*b)) := by
  apply Tendsto.congr' (f₁ := fun t => 2*b*Real.cos (delta t))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    rw [gamma_sin ht,cos_delta]
  · simpa using tendsto_cos_delta.const_mul (2*b)

theorem tendsto_gamma (b : ℝ) (hb : 0 < b) : Tendsto (gamma b) atTop atTop :=
  tendsto_id.const_mul_atTop hb

theorem tendsto_gamma_sq_exp (b : ℝ) (hb : 0 < b) :
    Tendsto (fun t => (gamma b t)^2*Real.exp (-2*(gamma b t)^2)) atTop (𝓝 0) := by
  have hx := ((tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp (tendsto_gamma b hb)).const_mul_atTop
    (by norm_num : (0:ℝ)<2)
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hx
  convert! h.div_const 2 using 1
  · funext t
    simp only [Function.comp_def,pow_one]
    rw [show -(2*(gamma b t)^2)= -2*(gamma b t)^2 by ring]
    ring
  · norm_num

def phaseAngle (b t : ℝ) : ℝ :=
  (gamma b t)^2 * Real.sin (2*delta t) * Real.exp (-2*(gamma b t)^2)

theorem tendsto_phaseAngle (b : ℝ) (hb : 0 < b) :
    Tendsto (phaseAngle b) atTop (𝓝 0) := by
  convert! (tendsto_gamma_sq_exp b hb).mul tendsto_sin_two_delta using 1
  · funext t
    unfold phaseAngle
    ring
  · norm_num

end SeedInitialization

namespace UnitarySplit
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inverse (U O S : H ≃ₗᵢ[ℂ] H) (a b : ℂ)
    (h : ∀ x, U x=a • O x+b • S x) (y : H) :
    U.symm y=star a • O.symm y+star b • S.symm y := by
  apply ext_inner_left ℂ
  intro x
  have hU : ⟪x,U.symm y⟫_ℂ=⟪U x,y⟫_ℂ := by
    rw [← U.inner_map_map x (U.symm y),U.apply_symm_apply]
  have hO : ⟪x,O.symm y⟫_ℂ=⟪O x,y⟫_ℂ := by
    rw [← O.inner_map_map x (O.symm y),O.apply_symm_apply]
  have hS : ⟪x,S.symm y⟫_ℂ=⟪S x,y⟫_ℂ := by
    rw [← S.inner_map_map x (S.symm y),S.apply_symm_apply]
  rw [hU,h,inner_add_left,inner_smul_left,inner_smul_left,
    inner_add_right,inner_smul_right,inner_smul_right,hO,hS]
  rfl
end UnitarySplit

namespace SeedInitialization
open CoherentFock RootSpin Complex PointedTree
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def initialMap (γ δ β : ℝ) (v e : E) : SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E :=
  (costEquiv ((-γ) • e)).trans ((SpinOperators.actEquiv (R δ) (R_unitary δ)).trans
    ((costEquiv (γ • v)).trans (SpinOperators.actEquiv (R β) (R_unitary β))))

def ordinaryMap (γ β : ℝ) (v e : E) : SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E :=
  (costEquiv (γ • (v-e))).trans (SpinOperators.actEquiv (R β) (R_unitary β))

def specialMap (γ β : ℝ) (v e : E) : SpinSpace E ≃ₗᵢ[ℂ] SpinSpace E :=
  (costEquiv ((-γ) • (v+e))).trans ((SpinOperators.actEquiv X X_unitary).trans
    (SpinOperators.actEquiv (R β) (R_unitary β)))

def ordinaryCoefficient (γ δ : ℝ) (v e : E) : ℂ :=
  (Real.cos δ:ℂ)*phase (γ • v) ((-γ) • e)
def specialCoefficient (γ δ : ℝ) (v e : E) : ℂ :=
  (-I*(Real.sin δ:ℂ))*phase ((-γ) • v) ((-γ) • e)
def specialPhase (γ : ℝ) (v e : E) : ℂ :=
  -I*phase ((-γ) • v) ((-γ) • e)

@[simp] theorem initialMap_apply (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    initialMap γ δ β v e x=SpinOperators.act (R β)
      (WZ (γ • v) (SpinOperators.act (R δ) (WZ ((-γ) • e) x))) := rfl
@[simp] theorem ordinaryMap_apply (γ β : ℝ) (v e : E) (x : SpinSpace E) :
    ordinaryMap γ β v e x=SpinOperators.act (R β) (WZ (γ • (v-e)) x) := rfl
@[simp] theorem specialMap_apply (γ β : ℝ) (v e : E) (x : SpinSpace E) :
    specialMap γ β v e x=SpinOperators.act (R β)
      (SpinOperators.act X (WZ ((-γ) • (v+e)) x)) := rfl

 
theorem exact_split (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    initialMap γ δ β v e x=
      ordinaryCoefficient γ δ v e • ordinaryMap γ β v e x+
      specialCoefficient γ δ v e • specialMap γ β v e x := by
  rw [initialMap_apply,ordinaryMap_apply,specialMap_apply]
  have h := congrArg (fun A : SpinSpace E →L[ℂ] SpinSpace E => A x)
    (CoherentFock.initialization_split γ δ v e)
  change WZ (γ • v) (SpinOperators.act (R δ) (WZ ((-γ) • e) x))=_ at h
  rw [h]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,map_add,map_smul]
  rfl

@[simp] theorem norm_specialPhase (γ : ℝ) (v e : E) : ‖specialPhase γ v e‖=1 := by
  simp [specialPhase]

@[simp] theorem norm_special_component (γ δ β : ℝ) (v e : E) (x : SpinSpace E) :
    ‖specialCoefficient γ δ v e • specialMap γ β v e x‖=|Real.sin δ| * ‖x‖ := by
  rw [norm_smul,LinearIsometryEquiv.norm_map]
  simp only [specialCoefficient,norm_mul,norm_neg,Complex.norm_I,Complex.norm_real,
    norm_phase,one_mul,mul_one,Real.norm_eq_abs]

 

def address (γ δ : ℝ) (v e : E) : SpinSpace E :=
  (initialMap γ δ (Real.pi/4) v e).symm
    (SpinOperators.act Z (specialPhase γ v e • specialMap γ (Real.pi/4) v e (vacuum E)))

@[simp] theorem norm_address (γ δ : ℝ) (v e : E) : ‖address γ δ v e‖=1 := by
  unfold address
  rw [LinearIsometryEquiv.norm_map,SpinOperators.norm_act Z_unitary,
    norm_smul,norm_specialPhase,LinearIsometryEquiv.norm_map,norm_vacuum]
  norm_num

theorem address_exact_normalization (γ δ : ℝ) (v e : E) :
    (Real.sin δ:ℂ) • address γ δ v e=
      (initialMap γ δ (Real.pi/4) v e).symm
        (SpinOperators.act Z (specialCoefficient γ δ v e •
          specialMap γ (Real.pi/4) v e (vacuum E))) := by
  unfold address
  rw [← map_smul,← map_smul,smul_smul]
  congr 3
  unfold specialCoefficient specialPhase
  ring

end SeedInitialization

namespace RootSpin
@[simp] theorem Y_mul_X : Y*X=(-Complex.I) • Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y,X,Z,Matrix.mul_apply,Fin.sum_univ_two]

theorem R_quarter_conjugate_Z : (R (Real.pi/4)).conjTranspose*Z*R (Real.pi/4)=Y := by
  rw [R_conjugate_Z,show 2*(Real.pi/4)=Real.pi/2 by ring]
  simp only [Real.cos_pi_div_two,Real.sin_pi_div_two,Complex.ofReal_zero,
    Complex.ofReal_one,zero_smul,one_smul,zero_add]
end RootSpin

end

end OAI
