import Mathlib
import OAI.Algebra.FiniteTensor.AlgebraicDescent
import OAI.Algebra.FiniteTensor.JetSystems

namespace OAI

/-! Exact tensor models reconstructed from jet solutions and their algebraicity. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
variable {K : Type*} [Field K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}
variable (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
  (W : TensorPrimitives K (fun i=>Fin (n i)) m M)

 

structure JetSolution where
  left : LeftUnknown ((i : Fin l) × Fin (n i)) m → MvPowerSeries (Fin d) K
  right : RightUnknown ((i : Fin l) × Fin (n i)) m → MvPowerSeries (Fin c) K
  left_zero : ∀ i,MvPowerSeries.constantCoeff (left i)=0
  right_zero : ∀ i,MvPowerSeries.constantCoeff (right i)=0
  left_jet : ∀ i j,MvPowerSeries.coeff (Finsupp.single j 1) (left i)=
    MvPowerSeries.coeff (Finsupp.single j 1) (centerSeries (leftOriginal M W i))
  right_jet : ∀ i j,MvPowerSeries.coeff (Finsupp.single j 1) (right i)=
    MvPowerSeries.coeff (Finsupp.single j 1) (centerSeries (rightOriginal M W i))
  left_solve : ∀ j,MvPowerSeries.subst left (universalLeftEquation M W j)=0
  right_solve : ∀ j,MvPowerSeries.subst right (universalRightEquation M W j)=0

def originalJetSolution : JetSolution M W where
  left := fun i=>centerSeries (leftOriginal M W i)
  right := fun i=>centerSeries (rightOriginal M W i)
  left_zero := fun _=>centerSeries_zero _
  right_zero := fun _=>centerSeries_zero _
  left_jet := fun _ _=>rfl
  right_jet := fun _ _=>rfl
  left_solve := original_solves_left M W
  right_solve := original_solves_right M W

variable {M W}
variable (s : JetSolution M W)

def JetSolution.H (v : (i : Fin l) × Fin (n i)) : MvPowerSeries (Fin d) (Parameters K m) :=
  MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m)) (s.left i))
    (universalLeftH M v)

def JetSolution.G (v : (i : Fin l) × Fin (n i)) : MvPowerSeries (Fin c) K :=
  MvPowerSeries.subst s.right (universalRightG M v)

def JetSolution.L (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries (Fin d) (Parameters K m) :=
  MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m)) (s.left i))
    (universalLeftP M W t v)

def JetSolution.R (t : Triple m) (v : (i : Fin l) × Fin (n i)) : MvPowerSeries (Fin c) K :=
  MvPowerSeries.subst s.right (universalRightP M W t v)

theorem JetSolution.left_hasSubst : MvPowerSeries.HasSubst s.left :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero s.left_zero

theorem JetSolution.right_hasSubst : MvPowerSeries.HasSubst s.right :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero s.right_zero

theorem JetSolution.H_box (v : (i : Fin l) × Fin (n i)) (q : Box m) :
    boxSeries K m q (s.H v)=s.left (.inl (v,q))+
      MvPowerSeries.C (MvPowerSeries.constantCoeff (boxSeries K m q (M.H v))) := by
  rw [JetSolution.H,universalLeftH,subst_assembleBox _ s.left_hasSubst,
    boxSeries_assembleBox,subst_affineUnknown _ s.left_hasSubst]

theorem JetSolution.L_box (t : Triple m) (v : (i : Fin l) × Fin (n i)) (q : Box m) :
    boxSeries K m q (s.L t v)=s.left (.inr (t,v,q))+
      MvPowerSeries.C (MvPowerSeries.constantCoeff (boxSeries K m q (W.left t v))) := by
  rw [JetSolution.L,universalLeftP,subst_assembleBox _ s.left_hasSubst,
    boxSeries_assembleBox,subst_affineUnknown _ s.left_hasSubst]

theorem JetSolution.G_eq (v : (i : Fin l) × Fin (n i)) :
    s.G v=s.right (.inl v)+MvPowerSeries.C (MvPowerSeries.constantCoeff (M.G v)) := by
  rw [JetSolution.G,universalRightG,subst_affineUnknown _ s.right_hasSubst]

theorem JetSolution.R_eq (t : Triple m) (v : (i : Fin l) × Fin (n i)) :
    s.R t v=s.right (.inr (t,v))+MvPowerSeries.C (MvPowerSeries.constantCoeff (W.right t v)) := by
  rw [JetSolution.R,universalRightP,subst_affineUnknown _ s.right_hasSubst]

theorem JetSolution.H_constant (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.constantCoeff (s.H v)=MvPowerSeries.constantCoeff (M.H v) := by
  apply parameters_ext K m
  intro q
  change MvPowerSeries.constantCoeff (boxSeries K m q (s.H v))=_
  rw [s.H_box,map_add,s.left_zero,zero_add,MvPowerSeries.constantCoeff_C]
  rfl

theorem JetSolution.H_first (v : (i : Fin l) × Fin (n i)) (j : Fin d) :
    MvPowerSeries.coeff (Finsupp.single j 1) (s.H v)=
      MvPowerSeries.coeff (Finsupp.single j 1) (M.H v) := by
  apply parameters_ext K m
  intro q
  have hj : Finsupp.single j 1 ≠ (0 : Fin d →₀ ℕ) := by simp
  change MvPowerSeries.coeff (Finsupp.single j 1) (boxSeries K m q (s.H v))=_
  rw [s.H_box,map_add,MvPowerSeries.coeff_C_of_ne_zero hj,add_zero,s.left_jet]
  simp only [centerSeries,leftOriginal,Sum.elim_inl,map_sub,
    MvPowerSeries.coeff_C_of_ne_zero hj,sub_zero,coeff_boxSeries]

theorem JetSolution.G_constant (v : (i : Fin l) × Fin (n i)) :
    MvPowerSeries.constantCoeff (s.G v)=0 := by
  rw [s.G_eq,map_add,s.right_zero,MvPowerSeries.constantCoeff_C,M.G_zero,add_zero]

theorem JetSolution.G_first (v : (i : Fin l) × Fin (n i)) (j : Fin c) :
    MvPowerSeries.coeff (Finsupp.single j 1) (s.G v)=
      MvPowerSeries.coeff (Finsupp.single j 1) (M.G v) := by
  have hj : Finsupp.single j 1 ≠ (0 : Fin c →₀ ℕ) := by simp
  rw [s.G_eq,map_add,MvPowerSeries.coeff_C_of_ne_zero hj,add_zero,s.right_jet]
  simp only [centerSeries,rightOriginal,Sum.elim_inl,map_sub,
    MvPowerSeries.coeff_C_of_ne_zero hj,sub_zero]

theorem JetSolution.comp_left (f : MvPowerSeries ((i : Fin l) × Fin (n i)) (Parameters K m)) :
    MvPowerSeries.subst (fun i=>MvPowerSeries.map (algebraMap K (Parameters K m)) (s.left i))
      (MvPowerSeries.subst (universalLeftH M) f)=MvPowerSeries.subst s.H f := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_universalLeftH M)
    (s.left_hasSubst.map (algebraMap K (Parameters K m)))]
  rfl

theorem JetSolution.comp_right (f : MvPowerSeries ((i : Fin l) × Fin (n i)) K) :
    MvPowerSeries.subst s.right (MvPowerSeries.subst (universalRightG M) f)=
      MvPowerSeries.subst s.G f := by
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_universalRightG M) s.right_hasSubst]
  rfl

theorem JetSolution.left_vanishing :
    MvPowerSeries.subst s.H (deformed K (fun i=>Fin (n i)) m M.F active M.b)=0 := by
  apply boxSeries_ext (A:=K) (m:=m)
  intro q
  have h := s.left_solve (.inl q)
  change MvPowerSeries.subst s.left (boxSeries K m q _)=0 at h
  rw [←boxSeries_subst _ s.left_hasSubst,s.comp_left] at h
  simpa only [boxSeries_zero] using h

theorem JetSolution.right_vanishing :
    MvPowerSeries.subst s.G (potential K (fun i=>Fin (n i)) M.F)=0 := by
  have h := s.right_solve (.inl ())
  change MvPowerSeries.subst s.right (MvPowerSeries.subst (universalRightG M) _)=0 at h
  rwa [s.comp_right] at h

theorem JetSolution.left_identity (t : Triple m) :
    (∑ v,s.L t v*MvPowerSeries.subst s.H
      (MvPowerSeries.pderiv v (deformed K (fun i=>Fin (n i)) m M.F active M.b)))=
    MvPowerSeries.C (parameter K m t.val.1*parameter K m t.val.2.1*parameter K m t.val.2.2) := by
  apply sub_eq_zero.mp
  apply boxSeries_ext (A:=K) (m:=m)
  intro q
  have h := s.left_solve (.inr (t,q))
  change MvPowerSeries.subst s.left (boxSeries K m q ((∑ v,_) - _))=0 at h
  have ha := s.left_hasSubst.map (algebraMap K (Parameters K m))
  rw [←boxSeries_subst _ s.left_hasSubst,MvPowerSeries.subst_sub ha,
    ←MvPowerSeries.substAlgHom_apply ha,map_sum] at h
  simp only [map_mul,MvPowerSeries.substAlgHom_apply,s.comp_left,
    MvPowerSeries.subst_mul ha,MvPowerSeries.subst_C] at h
  simpa only [map_mul,boxSeries_zero,JetSolution.L] using h

theorem JetSolution.right_identity (t : Triple m) :
    (∑ v,s.R t v*MvPowerSeries.subst s.G
      (MvPowerSeries.pderiv v (potential K (fun i=>Fin (n i)) M.F)))=
    MvPowerSeries.subst s.G (perturbation K (fun i=>Fin (n i)) m active M.b t.val.1*
      perturbation K (fun i=>Fin (n i)) m active M.b t.val.2.1*
      perturbation K (fun i=>Fin (n i)) m active M.b t.val.2.2) := by
  apply sub_eq_zero.mp
  have h := s.right_solve (.inr t)
  change MvPowerSeries.subst s.right ((∑ v,_) - _)=0 at h
  rw [MvPowerSeries.subst_sub s.right_hasSubst,
    ←MvPowerSeries.substAlgHom_apply s.right_hasSubst,map_sum] at h
  simpa only [map_mul,MvPowerSeries.substAlgHom_apply,s.comp_right,JetSolution.R] using h

 

def JetSolution.model : TensorModel K (fun i=>Fin (n i)) m d c e active where
  F := M.F
  b := M.b
  F_zero := M.F_zero
  b_zero := M.b_zero
  H := s.H
  G := s.G
  H_zero := fun v=>by rw [s.H_constant]; exact M.H_zero v
  G_zero := s.G_constant
  tangent_unit := by
    have heq : tangent K (fun i=>Fin (n i)) m e s.H s.G=
        tangent K (fun i=>Fin (n i)) m e M.H M.G := by
      ext i j
      simp only [tangent,s.H_first,s.G_first]
    rw [heq]
    exact M.tangent_unit
  left_vanishing := s.left_vanishing
  right_vanishing := s.right_vanishing
  left_triple := fun i j k hij hik hjk=>
    Ideal.mem_span_range_iff_exists_fun.mpr ⟨s.L ⟨(i,j,k),hij,hik,hjk⟩,
      s.left_identity ⟨(i,j,k),hij,hik,hjk⟩⟩
  right_triple := fun i j k hij hik hjk=>
    Ideal.mem_span_range_iff_exists_fun.mpr ⟨s.R ⟨(i,j,k),hij,hik,hjk⟩,
      s.right_identity ⟨(i,j,k),hij,hik,hjk⟩⟩

def JetSolution.primitives : TensorPrimitives K (fun i=>Fin (n i)) m s.model where
  left := s.L
  right := s.R
  left_eq := s.left_identity
  right_eq := s.right_identity

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
variable {K : Type*} [Field K] {l m d c : ℕ} {n : Fin l → ℕ}
  {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}
variable {M : TensorModel K (fun i=>Fin (n i)) m d c e active}
  {W : TensorPrimitives K (fun i=>Fin (n i)) m M}

 

structure JetSolution.Algebraic (s : JetSolution M W) : Prop where
  left : ∀ i,IsAlgebraic (MvPolynomial (Fin d) K) (s.left i)
  right : ∀ i,IsAlgebraic (MvPolynomial (Fin c) K) (s.right i)

 theorem constant_series_algebraic {σ : Type*} (a : K) :
    IsAlgebraic (MvPolynomial σ K) (MvPowerSeries.C (σ:=σ) a) := by
  simpa only [MvPowerSeries.algebraMap_apply',MvPowerSeries.map_id,
    Algebra.algebraMap_self,RingHom.id_apply,MvPolynomial.coe_C] using
    (isAlgebraic_algebraMap (R:=MvPolynomial σ K) (A:=MvPowerSeries σ K) (MvPolynomial.C a))

 theorem JetSolution.algebraicData (s : JetSolution M W) (hs : s.Algebraic)
    (hF : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) :
    AlgebraicData s.model s.primitives where
  F := hF
  b := hb
  H := fun v q=>by
    change IsAlgebraic _ (boxSeries K m q (s.H v))
    rw [s.H_box]
    exact (hs.left _).add (constant_series_algebraic _)
  G := fun v=>by
    change IsAlgebraic _ (s.G v)
    rw [s.G_eq]
    exact (hs.right _).add (constant_series_algebraic _)
  left := fun t v q=>by
    change IsAlgebraic _ (boxSeries K m q (s.L t v))
    rw [s.L_box]
    exact (hs.left _).add (constant_series_algebraic _)
  right := fun t v=>by
    change IsAlgebraic _ (s.R t v)
    rw [s.R_eq]
    exact (hs.right _).add (constant_series_algebraic _)

 

variable [CharZero K]

theorem no_algebraic_jet_solution (hm : 5 ≤ m)
    (hF : ∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i))
    (hb : ∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i))
    (s : JetSolution M W) : ¬s.Algebraic := fun hs=>
  no_algebraic_tensor_model hm s.model s.primitives (s.algebraicData hs hF hb)

 

def TensorAlgebraicApproximation : Prop :=
  ∀ {K : Type} [Field K] [CharZero K] {l m d c : ℕ} {n : Fin l → ℕ}
    {e : ((i : Fin l) × Fin (n i)) ≃ Fin d ⊕ Fin c} {active : Fin m ↪ Fin l}
    (M : TensorModel K (fun i=>Fin (n i)) m d c e active)
    (W : TensorPrimitives K (fun i=>Fin (n i)) m M),
    (∀ i,IsAlgebraic (MvPolynomial (Fin (n i)) K) (M.F i)) →
    (∀ i,IsAlgebraic (MvPolynomial (Fin (n (active i))) K) (M.b i)) →
    ∃ s : JetSolution M W,s.Algebraic

end
end PD4Tensor.Spreading
end

end OAI
