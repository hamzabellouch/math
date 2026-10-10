import Mathlib
import OAI.Algebra.FiniteTensor.BoxCoefficients

namespace OAI

/-! Scalar finite equations reconstructing every squarefree component and primitive. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {A σ τ : Type*} [CommRing A] {m : ℕ}

 
def assembleBox (f : Box m → MvPowerSeries σ A) : MvPowerSeries σ (Parameters A m) :=
  ∑ q, MvPowerSeries.C (boxMonomial A m q) *
    MvPowerSeries.map (algebraMap A (Parameters A m)) (f q)

@[simp] theorem assembleBox_boxSeries (f : MvPowerSeries σ (Parameters A m)) :
    assembleBox (boxSeries A m · f)=f := sum_boxSeries A m f

 theorem boxCoeff_mul_algebraMap (q : Box m) (x : Parameters A m) (a : A) :
    boxCoeff A m q (x*algebraMap A (Parameters A m) a)=boxCoeff A m q x*a := by
  rw [mul_comm,←Algebra.smul_def,map_smul,smul_eq_mul,mul_comm]

@[simp] theorem boxSeries_assembleBox (q : Box m) (f : Box m → MvPowerSeries σ A) :
    boxSeries A m q (assembleBox f)=f q := by
  classical
  ext d
  simp only [coeff_boxSeries,assembleBox,map_sum,MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_map,boxCoeff_mul_algebraMap,boxCoeff_boxMonomial,
    ite_mul,one_mul,zero_mul]
  simp

 theorem boxSeries_ext (f g : MvPowerSeries σ (Parameters A m))
    (h : ∀ q,boxSeries A m q f=boxSeries A m q g) : f=g := by
  rw [←assembleBox_boxSeries f,←assembleBox_boxSeries g]
  congr 1
  funext q
  exact h q

@[simp] theorem boxSeries_zero (q : Box m) :
    boxSeries A m q (0 : MvPowerSeries σ (Parameters A m))=0 := by
  ext d
  simp only [coeff_boxSeries,map_zero]

@[simp] theorem boxSeries_add (q : Box m) (f g : MvPowerSeries σ (Parameters A m)) :
    boxSeries A m q (f+g)=boxSeries A m q f+boxSeries A m q g := by
  ext d
  simp only [coeff_boxSeries,map_add]

@[simp] theorem boxSeries_sub (q : Box m) (f g : MvPowerSeries σ (Parameters A m)) :
    boxSeries A m q (f-g)=boxSeries A m q f-boxSeries A m q g := by
  ext d
  simp only [coeff_boxSeries,map_sub]

 theorem subst_assembleBox (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (f : Box m → MvPowerSeries σ A) :
    MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap A (Parameters A m)) (a i))
      (assembleBox f) = assembleBox (fun q=>MvPowerSeries.subst a (f q)) := by
  let hm := ha.map (algebraMap A (Parameters A m))
  rw [assembleBox,←MvPowerSeries.substAlgHom_apply hm,map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul,MvPowerSeries.substAlgHom_apply,MvPowerSeries.subst_C,
    MvPowerSeries.substAlgHom_apply,←MvPowerSeries.map_subst ha]

 

theorem boxSeries_subst (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (q : Box m) (f : MvPowerSeries σ (Parameters A m)) :
    boxSeries A m q (MvPowerSeries.subst
      (fun i=>MvPowerSeries.map (algebraMap A (Parameters A m)) (a i)) f)=
      MvPowerSeries.subst a (boxSeries A m q f) := by
  conv_lhs => rw [←assembleBox_boxSeries f,subst_assembleBox a ha,boxSeries_assembleBox]

 

def centerSeries (f : MvPowerSeries σ A) : MvPowerSeries σ A :=
  f-MvPowerSeries.C (MvPowerSeries.constantCoeff f)

@[simp] theorem centerSeries_zero (f : MvPowerSeries σ A) :
    MvPowerSeries.constantCoeff (centerSeries f)=0 := by
  simp [centerSeries]

 theorem centerFamily_hasSubst [Finite σ] (f : σ → MvPowerSeries τ A) :
    MvPowerSeries.HasSubst (fun i=>centerSeries (f i)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _=>centerSeries_zero _)

 def affineUnknown (i : σ) (c : A) : MvPowerSeries σ A :=
  MvPowerSeries.X i+MvPowerSeries.C c

 theorem subst_affineUnknown (a : σ → MvPowerSeries τ A) (ha : MvPowerSeries.HasSubst a)
    (i : σ) (c : A) :
    MvPowerSeries.subst a (affineUnknown i c)=a i+MvPowerSeries.C c := by
  simp only [affineUnknown,MvPowerSeries.subst_add ha,MvPowerSeries.subst_X ha,
    MvPowerSeries.subst_C]

 theorem subst_center_affine [Finite σ] (f : σ → MvPowerSeries τ A) (i : σ) :
    MvPowerSeries.subst (fun j=>centerSeries (f j))
      (affineUnknown i (MvPowerSeries.constantCoeff (f i)))=f i := by
  rw [subst_affineUnknown _ (centerFamily_hasSubst f)]
  simp only [centerSeries,sub_add_cancel]

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {K : Type*} [Field K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}

abbrev LeftUnknown (V : Type*) (m : ℕ) := (V × Box m) ⊕ (Triple m × V × Box m)
abbrev RightUnknown (V : Type*) (m : ℕ) := V ⊕ (Triple m × V)
abbrev LeftEquation (m : ℕ) := Box m ⊕ (Triple m × Box m)
abbrev RightEquation (m : ℕ) := Unit ⊕ Triple m

variable (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
  (W : TensorPrimitives K (fun i=>Fin (n i)) m M)

 

def leftOriginal : LeftUnknown ((i : Fin l) × Fin (n i)) m → MvPowerSeries (Fin d) K :=
  Sum.elim (fun vq=>boxSeries K m vq.2 (M.H vq.1))
    (fun tvq=>boxSeries K m tvq.2.2 (W.left tvq.1 tvq.2.1))

def rightOriginal : RightUnknown ((i : Fin l) × Fin (n i)) m → MvPowerSeries (Fin c) K :=
  Sum.elim M.G (fun tv=>W.right tv.1 tv.2)

def universalLeftH (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries (LeftUnknown ((i : Fin l) × Fin (n i)) m) (Parameters K m) :=
  assembleBox (fun q=>affineUnknown (.inl (v,q))
    (MvPowerSeries.constantCoeff (boxSeries K m q (M.H v))))

def universalLeftP (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries (LeftUnknown ((i : Fin l) × Fin (n i)) m) (Parameters K m) :=
  assembleBox (fun q=>affineUnknown (.inr (t,v,q))
    (MvPowerSeries.constantCoeff (boxSeries K m q (W.left t v))))

def universalRightG (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries (RightUnknown ((i : Fin l) × Fin (n i)) m) K :=
  affineUnknown (.inl v) (MvPowerSeries.constantCoeff (M.G v))

def universalRightP (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries (RightUnknown ((i : Fin l) × Fin (n i)) m) K :=
  affineUnknown (.inr (t,v)) (MvPowerSeries.constantCoeff (W.right t v))

 theorem constantCoeff_universalLeftH (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.constantCoeff (universalLeftH M v)=MvPowerSeries.constantCoeff (M.H v) := by
  calc
    _ = MvPowerSeries.constantCoeff (assembleBox (fun q=>boxSeries K m q (M.H v))) := by
      simp only [universalLeftH,assembleBox,map_sum,map_mul,MvPowerSeries.constantCoeff_C,
        MvPowerSeries.constantCoeff_map,affineUnknown,map_add,MvPowerSeries.constantCoeff_X,map_zero,
        zero_add]
    _ = _ := by rw [assembleBox_boxSeries]

 theorem hasSubst_universalLeftH : MvPowerSeries.HasSubst (universalLeftH M) := by
  apply hasSubst_parameters K m
  intro v
  rw [constantCoeff_universalLeftH]
  exact M.H_zero v

 theorem hasSubst_universalRightG : MvPowerSeries.HasSubst (universalRightG M) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro v
  simp only [universalRightG,affineUnknown,map_add,MvPowerSeries.constantCoeff_X,
    MvPowerSeries.constantCoeff_C,zero_add,M.G_zero]

 

def universalLeftEquation : LeftEquation m →
    MvPowerSeries (LeftUnknown ((i : Fin l) × Fin (n i)) m) K :=
  Sum.elim (fun q=>boxSeries K m q (MvPowerSeries.subst (universalLeftH M)
    (deformed K (fun i=>Fin (n i)) m M.F active M.b)))
    (fun tq=>boxSeries K m tq.2 ((∑ v,universalLeftP M W tq.1 v *
      MvPowerSeries.subst (universalLeftH M) (MvPowerSeries.pderiv v
        (deformed K (fun i=>Fin (n i)) m M.F active M.b))) -
      MvPowerSeries.C (parameter K m tq.1.val.1 * parameter K m tq.1.val.2.1 *
        parameter K m tq.1.val.2.2)))

def universalRightEquation : RightEquation m →
    MvPowerSeries (RightUnknown ((i : Fin l) × Fin (n i)) m) K :=
  Sum.elim (fun _=>MvPowerSeries.subst (universalRightG M) (potential K (fun i=>Fin (n i)) M.F))
    (fun t=>(∑ v,universalRightP M W t v * MvPowerSeries.subst (universalRightG M)
      (MvPowerSeries.pderiv v (potential K (fun i=>Fin (n i)) M.F))) -
      MvPowerSeries.subst (universalRightG M)
        (perturbation K (fun i=>Fin (n i)) m active M.b t.val.1 *
          perturbation K (fun i=>Fin (n i)) m active M.b t.val.2.1 *
          perturbation K (fun i=>Fin (n i)) m active M.b t.val.2.2))

 theorem eval_universalLeftH (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m))
      (centerSeries (leftOriginal M W i))) (universalLeftH M v)=M.H v := by
  rw [universalLeftH,subst_assembleBox _ (centerFamily_hasSubst _)]
  convert assembleBox_boxSeries (M.H v) using 1
  congr 1
  funext q
  exact subst_center_affine (leftOriginal M W) (.inl (v,q))

 theorem eval_universalLeftP (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m))
      (centerSeries (leftOriginal M W i))) (universalLeftP M W t v)=W.left t v := by
  rw [universalLeftP,subst_assembleBox _ (centerFamily_hasSubst _)]
  convert assembleBox_boxSeries (W.left t v) using 1
  congr 1
  funext q
  exact subst_center_affine (leftOriginal M W) (.inr (t,v,q))

 theorem eval_universalRightG (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.subst (fun i=>centerSeries (rightOriginal M W i))
      (universalRightG M v)=M.G v :=
  subst_center_affine (rightOriginal M W) (.inl v)

 theorem eval_universalRightP (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.subst (fun i=>centerSeries (rightOriginal M W i))
      (universalRightP M W t v)=W.right t v :=
  subst_center_affine (rightOriginal M W) (.inr (t,v))

 theorem original_solves_left (j : LeftEquation m) :
    MvPowerSeries.subst (fun i=>centerSeries (leftOriginal M W i))
      (universalLeftEquation M W j)=0 := by
  let a := fun i=>centerSeries (leftOriginal M W i)
  have ha := centerFamily_hasSubst (leftOriginal M W)
  have hma := ha.map (algebraMap K (Parameters K m))
  have hcomp (f : MvPowerSeries ((i : Fin l) × Fin (n i)) (Parameters K m)) :
      MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m)) (a i))
        (MvPowerSeries.subst (universalLeftH M) f)=MvPowerSeries.subst M.H f := by
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_universalLeftH M) hma]
    simp only [eval_universalLeftH]
  rcases j with q|tq
  · change MvPowerSeries.subst a (boxSeries K m q _)=0
    rw [←boxSeries_subst a ha,hcomp,M.left_vanishing,boxSeries_zero]
  · change MvPowerSeries.subst a (boxSeries K m tq.2 _)=0
    rw [←boxSeries_subst a ha,MvPowerSeries.subst_sub hma,
      ←MvPowerSeries.substAlgHom_apply hma,map_sum]
    simp only [map_mul,MvPowerSeries.substAlgHom_apply,eval_universalLeftP]
    dsimp only [a] at hcomp
    simp only [hcomp,MvPowerSeries.subst_mul hma,MvPowerSeries.subst_C,W.left_eq,map_mul,sub_self,boxSeries_zero]

 theorem original_solves_right (j : RightEquation m) :
    MvPowerSeries.subst (fun i=>centerSeries (rightOriginal M W i))
      (universalRightEquation M W j)=0 := by
  let a := fun i=>centerSeries (rightOriginal M W i)
  have ha := centerFamily_hasSubst (rightOriginal M W)
  have hcomp (f : MvPowerSeries ((i : Fin l) × Fin (n i)) K) :
      MvPowerSeries.subst a (MvPowerSeries.subst (universalRightG M) f)=
        MvPowerSeries.subst M.G f := by
    rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_universalRightG M) ha]
    simp only [eval_universalRightG]
  rcases j with u|t
  · exact (hcomp _).trans M.right_vanishing
  · change MvPowerSeries.subst a ((∑ v,_) - _)=0
    rw [MvPowerSeries.subst_sub ha,←MvPowerSeries.substAlgHom_apply ha,map_sum]
    simp only [map_mul,MvPowerSeries.substAlgHom_apply,eval_universalRightP]
    dsimp only [a] at hcomp
    simp only [hcomp,W.right_eq,sub_self]

end
end PD4Tensor.Spreading
end

end OAI
