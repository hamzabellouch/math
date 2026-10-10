import OAI.Algebra.Drinfeld.Pentagon

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace RationalDescent
open scoped TensorProduct
variable {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E]

theorem factor_of_kernel (f : V →ₗ[K] E) (l : V →ₗ[K] K) (h : f.ker≤l.ker) :
    ∃ g : E →ₗ[K] K,g.comp f=l := by
  let r : f.range →ₗ[K] K := ((f.ker).liftQ l h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,hg⟩ := r.exists_extend
  refine ⟨g,?_⟩
  ext v
  have hh := LinearMap.congr_fun hg (f.rangeRestrict v)
  change g (f v)=r (f.rangeRestrict v) at hh
  change g (f v)=l v
  rw [hh]
  simp only [r,LinearMap.comp_apply,LinearEquiv.coe_coe]
  exact congrArg (f.ker.liftQ l h) (f.quotKerEquivRange.symm_apply_apply (f.ker.mkQ v))

theorem nonvanishing {S : Type*} [AddCommGroup S] [Module K S]
    (f : V →ₗ[K] E) (l : V →ₗ[K] K)
    (u : S ⊗[K] V) (hu : f.lTensor S u=0) (hl : l.lTensor S u≠0) :
    ∃ v : V,f v=0 ∧ l v≠0 := by
  by_contra hn
  have hk : f.ker≤l.ker := by
    intro v hv
    by_contra hv'
    exact hn ⟨v,hv,hv'⟩
  obtain ⟨g,hg⟩ := factor_of_kernel f l hk
  apply hl
  rw [←hg,LinearMap.lTensor_comp,LinearMap.comp_apply,hu,map_zero]

end RationalDescent

namespace RationalScalar

section
open scoped TensorProduct
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {M N : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
abbrev T (M : Type*) [AddCommGroup M] [Module ℚ M] := ℝ ⊗[ℚ] M
 def one : M →ₗ⁅ℚ⁆ T M where
  toLinearMap := TensorProduct.mk ℚ ℝ M 1
  map_lie' := by
    intro a b
    change 1 ⊗ₜ[ℚ] ⁅a,b⁆=⁅(1:ℝ) ⊗ₜ[ℚ] a,(1:ℝ) ⊗ₜ[ℚ] b⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul,one_mul]
 def base (f : M →ₗ⁅ℚ⁆ N) : T M →ₗ⁅ℝ⁆ T N where
  toLinearMap := f.toLinearMap.baseChange ℝ
  map_lie' := by
    intro a b
    change (f.toLinearMap.baseChange ℝ) ⁅a,b⁆=⁅(f.toLinearMap.baseChange ℝ) a,(f.toLinearMap.baseChange ℝ) b⁆
    induction a using TensorProduct.inductionOn with

    | tmul s a =>
      induction b using TensorProduct.inductionOn with

      | tmul t b =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,LinearMap.baseChange_tmul]
        change (s*t) ⊗ₜ[ℚ] f ⁅a,b⁆=(s*t) ⊗ₜ[ℚ] ⁅f a,f b⁆
        rw [LieHom.map_lie]
      | add a b ha hb => simp only [lie_add,map_add,ha,hb]
    | add a b ha hb => simp only [add_lie,map_add,ha,hb]
 @[simp] theorem base_tmul (f : M →ₗ⁅ℚ⁆ N) (s : ℝ) (p : M) : base f (s ⊗ₜ[ℚ] p)=s ⊗ₜ[ℚ] f p := rfl
variable {α : Type*}
 def free : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ T (FreeLieAlgebra ℚ α) :=
  FreeLieAlgebra.lift ℝ (fun a => 1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a)
 @[simp] theorem free_of (a : α) : free (FreeLieAlgebra.of ℝ a)=1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a := FreeLieAlgebra.lift_of_apply _ _
 theorem free_tree (t : UniversalEmbedding.Tree α) : free (t.eval : FreeLieAlgebra ℝ α)=1 ⊗ₜ[ℚ] (t.eval : FreeLieAlgebra ℚ α) := by
  induction t with
  | leaf a => exact free_of a
  | node t u ht hu => simp only [Tree.eval,LieHom.map_lie,ht,hu,LieAlgebra.ExtendScalars.bracket_tmul,one_mul]
 theorem cast_tree {S : Type*} [CommRing S] (t : UniversalEmbedding.Tree α) :
    IntegralBaseChange.lie (t.eval : FreeLieAlgebra ℤ α)=(t.eval : FreeLieAlgebra S α) := by
  induction t with
  | leaf a => exact IntegralBaseChange.lie_of a
  | node t u ht hu => simp only [Tree.eval,LieHom.map_lie,ht,hu]
 theorem tree_coefficient (t : UniversalEmbedding.Tree α) (w : FreeMonoid α) :
    ((embed (t.eval : FreeLieAlgebra ℚ α)).coeff w:ℝ)=(embed (t.eval : FreeLieAlgebra ℝ α)).coeff w := by
  rw [←cast_tree (S:=ℚ) t,←cast_tree (S:=ℝ) t,IntegralBaseChange.embed_lie,IntegralBaseChange.embed_lie,
    IntegralBaseChange.words_coeff,IntegralBaseChange.words_coeff]
  simp
 def coefficient (w : FreeMonoid α) : FreeLieAlgebra ℚ α →ₗ[ℚ] ℚ :=
  (Finsupp.lapply w).comp ((MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp embed.toLinearMap)
 def realCoefficient (w : FreeMonoid α) : T (FreeLieAlgebra ℚ α) →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    ((Algebra.linearMap ℚ ℝ).comp (coefficient w)))
 @[simp] theorem realCoefficient_tmul (w : FreeMonoid α) (s : ℝ) (p : FreeLieAlgebra ℚ α) :
    realCoefficient w (s ⊗ₜ[ℚ] p)=s*(coefficient w p:ℝ) := rfl
 theorem coefficient_free {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈RealDeligneDrinfeld.weightPiece wt n) (w : FreeMonoid α) :
    realCoefficient w (free p)=(embed p).coeff w := by
  rw [RealDeligneDrinfeld.WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,_ht,rfl⟩ := hp
    rw [free_tree,realCoefficient_tmul,one_mul]
    exact tree_coefficient t w
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,MonoidAlgebra.coeff_add,Finsupp.add_apply]
  | smul s p _ hp => simp only [map_smul,hp,MonoidAlgebra.coeff_smul,Finsupp.smul_apply]
 theorem realCoefficient_tensor (w : FreeMonoid α) (u : T (FreeLieAlgebra ℚ α)) :
    realCoefficient w u=TensorProduct.rid ℚ ℝ ((coefficient w).lTensor ℝ u) := by
  induction u using TensorProduct.inductionOn with

  | tmul s p =>
    simp only [realCoefficient_tmul,LinearMap.lTensor_tmul,TensorProduct.rid_tmul]
    change s*(coefficient w p:ℝ)=(coefficient w p:ℝ)*s
    exact mul_comm _ _
  | add a b ha hb => simp only [map_add,ha,hb]
end

open scoped TensorProduct
 def realT4 : RealDeligneDrinfeld.T4 →ₗ⁅ℝ⁆ T T4 :=
  RealDeligneDrinfeld.T4Universal.lift (fun i j => one (t i j))
    (fun i j => congrArg one (t_comm i j)) (fun i => by rw [t_self,map_zero])
    (fun i j k l hij hik hil hjk hjl hkl => by rw [←LieHom.map_lie,t_disjoint i j k l hij hik hil hjk hjl hkl,map_zero])
    (fun i j k hij hik hjk => by rw [←map_add,←LieHom.map_lie,t_three i j k hij hik hjk,map_zero])
 @[simp] theorem realT4_t (i j : Fin 4) : realT4 (RealDeligneDrinfeld.t i j)=one (t i j) :=
  RealDeligneDrinfeld.T4Universal.lift_t _ _ _ _ _ _ _
 theorem eval_natural {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {P : Type*} [LieRing P] [LieAlgebra ℝ P] (g : P →ₗ⁅ℝ⁆ T M)
    (a b : M) (a' b' : P) (ha : g a'=one a) (hb : g b'=one b) (p : RealDeligneDrinfeld.L) :
    base (eval a b) (free p)=g (RealDeligneDrinfeld.eval a' b' p) := by
  have hh : (base (eval a b)).comp free=g.comp (RealDeligneDrinfeld.eval a' b') := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp only [LieHom.comp_apply,free_of,base_tmul,eval,RealDeligneDrinfeld.eval,FreeLieAlgebra.lift_of_apply,Bool.false_eq_true,ite_false,ite_true] <;> first | exact ha.symm | exact hb.symm
  exact DFunLike.congr_fun hh p
 def antiMap : L →ₗ[ℚ] L := LinearMap.id+(eval y x).toLinearMap
 def cyclicMap : L →ₗ[ℚ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap
 def pentagonMap : L →ₗ[ℚ] T4 :=
  (eval (t 0 1) (t 1 2+t 1 3)).toLinearMap+(eval (t 0 2+t 1 2) (t 2 3)).toLinearMap-
  ((eval (t 1 2) (t 2 3)).toLinearMap+(eval (t 0 1+t 0 2) (t 1 3+t 2 3)).toLinearMap+(eval (t 0 1) (t 1 2)).toLinearMap)
 theorem tensor_add {A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (f g : A →ₗ[ℚ] B) (u : T A) : (f+g).lTensor ℝ u=f.lTensor ℝ u+g.lTensor ℝ u := by
  induction u using TensorProduct.inductionOn with

  | tmul s p => simp
  | add a b ha hb => simp only [map_add,ha,hb]; abel
 theorem tensor_sub {A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (f g : A →ₗ[ℚ] B) (u : T A) : (f-g).lTensor ℝ u=f.lTensor ℝ u-g.lTensor ℝ u := by
  induction u using TensorProduct.inductionOn with

  | tmul s p => simp
  | add a b ha hb => simp only [map_add,ha,hb]; abel
 theorem tensor_id (u : T L) : (LinearMap.id : L →ₗ[ℚ] L).lTensor ℝ u=u := by simp
 theorem eval_tensor {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) (u : T L) :
    (eval a b).toLinearMap.lTensor ℝ u=base (eval a b) u := rfl
 @[simp] theorem free_x : free RealDeligneDrinfeld.x=one x := free_of false
 @[simp] theorem free_y : free RealDeligneDrinfeld.y=one y := free_of true
 theorem equations {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.W) :
    antiMap.lTensor ℝ (free p)=0 ∧ cyclicMap.lTensor ℝ (free p)=0 ∧ pentagonMap.lTensor ℝ (free p)=0 := by
  rcases hp with ⟨h1,h2,h3⟩
  constructor
  · rw [antiMap,tensor_add,tensor_id,eval_tensor,eval_natural free y x _ _ free_y free_x,←map_add,h1,map_zero]
  constructor
  · have hz : free (-RealDeligneDrinfeld.x-RealDeligneDrinfeld.y)=one (-x-y) := by simp
    rw [cyclicMap,tensor_add,tensor_add,tensor_id,eval_tensor,eval_tensor,
      eval_natural free y (-x-y) _ _ free_y hz,eval_natural free (-x-y) x _ _ hz free_x,←map_add,←map_add,h2,map_zero]
  · rw [pentagonMap,tensor_sub,tensor_add,tensor_add,tensor_add]
    simp only [eval_tensor]
    have hsum (i j k l : Fin 4) : realT4 (RealDeligneDrinfeld.t i j+RealDeligneDrinfeld.t k l)=one (t i j+t k l) := by simp only [map_add,realT4_t]
    rw [eval_natural realT4 _ _ _ _ (realT4_t 0 1) (hsum 1 2 1 3),
      eval_natural realT4 _ _ _ _ (hsum 0 2 1 2) (realT4_t 2 3),
      eval_natural realT4 _ _ _ _ (realT4_t 1 2) (realT4_t 2 3),
      eval_natural realT4 _ _ _ _ (hsum 0 1 0 2) (hsum 1 3 2 3),
      eval_natural realT4 _ _ _ _ (realT4_t 0 1) (realT4_t 1 2)]
    rw [←map_add,←map_add,←map_add,h3,sub_self]

 theorem homogeneous_tensor {n : ℕ} {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.Ln n) :
    (Ln n).mkQ.lTensor ℝ (free p)=0 := by
  change p∈RealDeligneDrinfeld.weightPiece (fun _ => 1) n at hp
  rw [RealDeligneDrinfeld.WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    have hm : (t.eval : L)∈Ln n := by
      change t.eval∈weightPiece (fun _ => 1) n
      rw [LieGrading.weightPiece_eq]
      exact Submodule.subset_span ⟨t,ht,rfl⟩
    rw [free_tree,LinearMap.lTensor_tmul]
    have hz : (Ln n).mkQ (t.eval : L)=0 := (Submodule.Quotient.mk_eq_zero _).mpr hm
    rw [hz,TensorProduct.tmul_zero]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul s p _ hp =>
    rw [map_smul]
    change ((Ln n).mkQ.baseChange ℝ) (s • free p)=0
    rw [map_smul]
    change s • ((Ln n).mkQ.lTensor ℝ (free p))=0
    rw [hp,smul_zero]
 theorem tensor_prod {A B C : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [AddCommGroup C] [Module ℚ C] (f : A →ₗ[ℚ] B) (g : A →ₗ[ℚ] C) (u : T A)
    (hf : f.lTensor ℝ u=0) (hg : g.lTensor ℝ u=0) : (f.prod g).lTensor ℝ u=0 := by
  have hh : TensorProduct.prodRight ℚ ℝ ℝ B C ((f.prod g).lTensor ℝ u)=(f.lTensor ℝ u,g.lTensor ℝ u) := by
    clear hf hg
    induction u using TensorProduct.inductionOn with

    | tmul s a => simp
    | add a b ha hb => simp only [map_add,ha,hb,Prod.mk_add_mk]
  apply (TensorProduct.prodRight ℚ ℝ ℝ B C).injective
  rw [hh,hf,hg,map_zero]; rfl
 def system (n : ℕ) : L →ₗ[ℚ] (L ⧸ Ln n) × L × L × T4 :=
  (Ln n).mkQ.prod (antiMap.prod (cyclicMap.prod pentagonMap))
 theorem descend {n : ℕ} {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.W)
    (hpn : p∈RealDeligneDrinfeld.Ln n) (w : FreeMonoid Bool)
    (hc : (AssociativeElimination.embed p).coeff w≠0) :
    ∃ q : L,q∈Wn n ∧ (AssociativeElimination.embed q).coeff w≠0 := by
  have hs : (system n).lTensor ℝ (free p)=0 := by
    obtain ⟨h1,h2,h3⟩ := equations hp
    exact tensor_prod _ _ _ (homogeneous_tensor hpn) (tensor_prod _ _ _ h1 (tensor_prod _ _ _ h2 h3))
  have hn : (coefficient w).lTensor ℝ (free p)≠0 := by
    intro he
    apply hc
    rw [←coefficient_free hpn w,realCoefficient_tensor,he,map_zero]
  obtain ⟨q,hq,hc⟩ := RationalDescent.nonvanishing (system n) (coefficient w) (free p) hs hn
  have hh : (Ln n).mkQ q=0 ∧ antiMap q=0 ∧ cyclicMap q=0 ∧ pentagonMap q=0 := by
    change ((Ln n).mkQ q,antiMap q,cyclicMap q,pentagonMap q)=(0,0,0,0) at hq
    simpa only [Prod.mk.injEq] using hq
  refine ⟨q,⟨⟨hh.2.1,hh.2.2.1,?_⟩,(Submodule.Quotient.mk_eq_zero _).mp hh.1⟩,hc⟩
  exact sub_eq_zero.mp hh.2.2.2
end RationalScalar

namespace BraidSix
variable {M : Type*} [LieRing M]

def total (a b c d e f : M) : M := a+b+c+d+e+f

def matrix (a b c d e f : M) : Fin 4 → Fin 4 → M :=
  ![![0,a,d,f],![a,0,b,e],![d,b,0,c],![f,e,c,0]]

structure Relations (a b c d e f : M) : Prop where
  central : ∀ u∈({a,b,c,d,e,f}:Set M),⁅u,total a b c d e f⁆=0
  ac : ⁅a,c⁆=0
  de : ⁅d,e⁆=0
  aK : ⁅a,a+b+d⁆=0
  bK : ⁅b,a+b+d⁆=0
  bL : ⁅b,b+c+e⁆=0
  cL : ⁅c,b+c+e⁆=0

variable {a b c d e f : M}

theorem bf (h : Relations a b c d e f) : ⁅b,f⁆=0 := by
  calc
    _=⁅b,total a b c d e f⁆-⁅b,a+b+d⁆-⁅b,b+c+e⁆ := by
      simp only [total,lie_add,lie_self]
      abel
    _=0 := by rw [h.central b (by simp),h.bK,h.bL]; abel

theorem dK (h : Relations a b c d e f) : ⁅d,a+b+d⁆=0 := by
  have hh := lie_self (a+b+d)
  rw [add_lie,add_lie,h.aK,h.bK] at hh
  simpa only [zero_add] using hh

theorem eL (h : Relations a b c d e f) : ⁅e,b+c+e⁆=0 := by
  have hh := lie_self (b+c+e)
  rw [add_lie,add_lie,h.bL,h.cL] at hh
  simpa only [zero_add] using hh

theorem aM (h : Relations a b c d e f) : ⁅a,a+e+f⁆=0 := by
  calc
    _=⁅a,total a b c d e f⁆-⁅a,a+b+d⁆-⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central a (by simp),h.aK,h.ac]; abel

theorem eM (h : Relations a b c d e f) : ⁅e,a+e+f⁆=0 := by
  calc
    _=⁅e,total a b c d e f⁆-⁅e,b+c+e⁆+⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew d e]
      abel
    _=0 := by rw [h.central e (by simp),eL h,h.de]; abel

theorem fM (h : Relations a b c d e f) : ⁅f,a+e+f⁆=0 := by
  have hh := lie_self (a+e+f)
  rw [add_lie,add_lie,aM h,eM h] at hh
  simpa only [zero_add] using hh

theorem dP (h : Relations a b c d e f) : ⁅d,d+c+f⁆=0 := by
  calc
    _=⁅d,total a b c d e f⁆-⁅d,a+b+d⁆-⁅d,e⁆ := by
      simp only [total,lie_add,lie_self]; abel
    _=0 := by rw [h.central d (by simp),dK h,h.de]; abel

theorem cP (h : Relations a b c d e f) : ⁅c,d+c+f⁆=0 := by
  calc
    _=⁅c,total a b c d e f⁆-⁅c,b+c+e⁆+⁅a,c⁆ := by
      simp only [total,lie_add,lie_self]
      rw [←lie_skew a c]
      abel
    _=0 := by rw [h.central c (by simp),h.cL,h.ac]; abel

theorem fP (h : Relations a b c d e f) : ⁅f,d+c+f⁆=0 := by
  have hh := lie_self (d+c+f)
  rw [add_lie,add_lie,dP h,cP h] at hh
  simpa only [zero_add] using hh

theorem matrix_self (i : Fin 4) : matrix a b c d e f i i=0 := by
  fin_cases i <;> rfl

theorem matrix_symm (i j : Fin 4) : matrix a b c d e f i j=matrix a b c d e f j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem matrix_disjoint_0 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (0:Fin 4)≠k) (hil : (0:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_1 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (1:Fin 4)≠k) (hil : (1:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_2 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (2:Fin 4)≠k) (hil : (2:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint_3 (h : Relations a b c d e f) (j k l : Fin 4)
    (hik : (3:Fin 4)≠k) (hil : (3:Fin 4)≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f k l⁆=0 := by
  have hac := h.ac
  have hde := h.de
  have hbf := bf h
  have hca := commute_symm h.ac
  have hed := commute_symm h.de
  have hfb := commute_symm (bf h)
  fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [matrix]

theorem matrix_disjoint (h : Relations a b c d e f) (i j k l : Fin 4)
    (hik : i≠k) (hil : i≠l) (hjk : j≠k) (hjl : j≠l) :
    ⁅matrix a b c d e f i j,matrix a b c d e f k l⁆=0 := by
  fin_cases i
  · exact matrix_disjoint_0 h j k l hik hil hjk hjl
  · exact matrix_disjoint_1 h j k l hik hil hjk hjl
  · exact matrix_disjoint_2 h j k l hik hil hjk hjl
  · exact matrix_disjoint_3 h j k l hik hil hjk hjl

theorem matrix_three_0 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (0:Fin 4)≠j) (hik : (0:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 0 j,matrix a b c d e f 0 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_1 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (1:Fin 4)≠j) (hik : (1:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 1 j,matrix a b c d e f 1 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_2 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (2:Fin 4)≠j) (hik : (2:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 2 j,matrix a b c d e f 2 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three_3 (h : Relations a b c d e f) (j k : Fin 4)
    (hij : (3:Fin 4)≠j) (hik : (3:Fin 4)≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f 3 j,matrix a b c d e f 3 k+matrix a b c d e f j k⁆=0 := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using dK h
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using h.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using h.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eL h
  have ha' : ⁅a,e+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using aM h
  have he' : ⁅e,a+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using eM h
  have hf : ⁅f,a+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fM h
  have hd' : ⁅d,c+f⁆=0 := by simpa only [lie_add,lie_self,zero_add] using dP h
  have hc' : ⁅c,d+f⁆=0 := by simpa only [lie_add,lie_self,add_zero] using cP h
  have hf' : ⁅f,d+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using fP h
  fin_cases j <;> fin_cases k <;>
    simp_all [matrix,add_comm]

theorem matrix_three (h : Relations a b c d e f) (i j k : Fin 4)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    ⁅matrix a b c d e f i j,matrix a b c d e f i k+matrix a b c d e f j k⁆=0 := by
  fin_cases i
  · exact matrix_three_0 h j k hij hik hjk
  · exact matrix_three_1 h j k hij hik hjk
  · exact matrix_three_2 h j k hij hik hjk
  · exact matrix_three_3 h j k hij hik hjk

end BraidSix

namespace T4Basic
open BraidSix

def a : T4 := t 0 1
def b : T4 := t 1 2
def c : T4 := t 2 3
def d : T4 := t 0 2
def e : T4 := t 1 3
def f : T4 := t 0 3

 theorem induction {P : T4 → Prop} (hz : P 0) (ht : ∀ i j,P (t i j))
    (ha : ∀ p q,P p → P q → P (p+q)) (hs : ∀ (r : ℚ) p,P p → P (r • p))
    (hl : ∀ p q,P p → P q → P ⁅p,q⁆) (p : T4) : P p := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    induction p using freeLie_induction with
    | h0 => exact hz
    | hg ij =>
      have hh : (FreeLieAlgebra.of ℚ ij : BraidFree)=chord ij.val.1 ij.val.2 := by
        simp only [chord,dite_eq_left ij.property]
      rw [hh]
      exact ht _ _
    | ha p q hp hq => exact ha _ _ hp hq
    | hs r p hp => exact hs r _ hp
    | hl p q hp hq => exact hl _ _ hp hq

 theorem hom_ext {M : Type*} [LieRing M] [LieAlgebra ℚ M] {F G : T4 →ₗ⁅ℚ⁆ M}
    (h : ∀ i j,F (t i j)=G (t i j)) : F=G := by
  apply LieHom.ext
  intro p
  induction p using induction with
  | hz => simp
  | ht i j => exact h i j
  | ha p q hp hq => simp only [map_add,hp,hq]
  | hs r p hp => simp only [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq]

 theorem matrix_t (i j : Fin 4) : matrix a b c d e f i j=t i j := by
  fin_cases i <;> fin_cases j <;> rfl

 theorem central_a : ⁅a,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 1 2 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 1 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 1,t 0 2+t 1 2⁆+⁅t 0 1,t 0 3+t 1 3⁆+⁅t 0 1,t 2 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_b : ⁅b,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 2 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 2,t 1 0+t 2 0⁆+⁅t 1 2,t 1 3+t 2 3⁆+⁅t 1 2,t 0 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 2 0]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_c : ⁅c,total a b c d e f⁆=0 := by
  have h₁ := t_three 2 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 2 3 1 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 2 3,t 2 0+t 3 0⁆+⁅t 2 3,t 2 1+t 3 1⁆+⁅t 2 3,t 0 1⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 0,t_comm 2 1,t_comm 3 0,t_comm 3 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_d : ⁅d,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 2 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 2 3 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 2,t 0 1+t 2 1⁆+⁅t 0 2,t 0 3+t 2 3⁆+⁅t 0 2,t 1 3⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 2 1]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_e : ⁅e,total a b c d e f⁆=0 := by
  have h₁ := t_three 1 3 0 (by decide) (by decide) (by decide)
  have h₂ := t_three 1 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 1 3,t 1 0+t 3 0⁆+⁅t 1 3,t 1 2+t 3 2⁆+⁅t 1 3,t 0 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 1 0,t_comm 3 0,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central_f : ⁅f,total a b c d e f⁆=0 := by
  have h₁ := t_three 0 3 1 (by decide) (by decide) (by decide)
  have h₂ := t_three 0 3 2 (by decide) (by decide) (by decide)
  have h₃ := t_disjoint 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  calc
    _=⁅t 0 3,t 0 1+t 3 1⁆+⁅t 0 3,t 0 2+t 3 2⁆+⁅t 0 3,t 1 2⁆ := by
      simp only [a,b,c,d,e,f,total,lie_add,lie_self,t_comm 3 1,t_comm 3 2]
      abel
    _=0 := by rw [h₁,h₂,h₃]; simp

 theorem central (p : T4) : ⁅total a b c d e f,p⁆=0 := by
  induction p using induction with
  | hz => exact lie_zero _
  | ht i j =>
    rw [←matrix_t i j]
    have ha := commute_symm central_a
    have hb := commute_symm central_b
    have hc := commute_symm central_c
    have hd := commute_symm central_d
    have he := commute_symm central_e
    have hf := commute_symm central_f
    fin_cases i <;> fin_cases j <;> simp_all [matrix]
  | ha p q hp hq => rw [lie_add,hp,hq,add_zero]
  | hs r p hp => rw [lie_smul,hp,smul_zero]
  | hl p q hp hq => rw [leibniz_lie,hp,hq,zero_lie,lie_zero,add_zero]

 theorem relations : Relations a b c d e f := by
  constructor
  · intro u _; exact commute_symm (central u)
  · exact t_disjoint 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact t_disjoint 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · have h := t_three 0 1 2 (by decide) (by decide) (by decide)
    change ⁅t 0 1,t 0 1+t 1 2+t 0 2⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 1 2 0 (by decide) (by decide) (by decide)
    simpa only [a,b,d,lie_add,lie_self,add_zero,t_comm 1 0,t_comm 2 0] using h
  · have h := t_three 1 2 3 (by decide) (by decide) (by decide)
    change ⁅t 1 2,t 1 2+t 2 3+t 1 3⁆=0
    simp only [lie_add,lie_self] at h ⊢
    rw [add_comm] at h
    simpa only [zero_add] using h
  · have h := t_three 2 3 1 (by decide) (by decide) (by decide)
    simpa only [b,c,e,lie_add,lie_self,add_zero,t_comm 2 1,t_comm 3 1] using h

end T4Basic

namespace TangentBraid
open FreeDerivations BraidSix
variable {R M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]

structure Data (a b c d e f A B C D E H I J P Q : M) : Prop where
  base : BraidSix.Relations a b c d e f
  central : ∀ u : M,⁅total a b c d e f,u⁆=0
  aD : ⁅a,D⁆=0
  bB : ⁅b,B⁆=0
  cE : ⁅c,E⁆=0
  KA : ⁅a+b+d,A⁆=0
  LC : ⁅b+c+e,C⁆=0
  special_d : ⁅b,A⁆+⁅d,A+H⁆=0
  special_e : ⁅c,C⁆+⁅e,C+I⁆=0
  cyclic : C+I=J
  pentagon : D+E=A+B+C
  permuted : P+Q= -H+B+J
  dP : ⁅d,P⁆=0
  eQ : ⁅e,Q⁆=0

variable {a b c d e f A B C D E H I J P Q : M}

 theorem crossing {a b h k p q : M} (hab : ⁅a,b⁆=0)
    (hk : k-h=p+q) (hap : ⁅a,p⁆=0) (hbq : ⁅b,q⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,k⁆⁆=0 := by
  calc
    _=⁅a,⁅b,k-h⁆⁆ := by
      rw [lie_sub,lie_sub,leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
      abel
    _=0 := by
      rw [hk,lie_add,lie_add,hbq,lie_zero,add_zero,leibniz_lie,hab,hap,zero_lie,lie_zero,add_zero]

 theorem inner_pair {a b h : M} (hab : ⁅a,b⁆=0) :
    ⁅⁅a,h⁆,b⁆+⁅a,⁅b,h⁆⁆=0 := by
  rw [leibniz_lie a b h,hab,zero_lie,zero_add,←lie_skew b ⁅a,h⁆]
  abel

 theorem commute_lie {a b h : M} (ha : ⁅a,h⁆=0) (hb : ⁅b,h⁆=0) : ⁅⁅a,b⁆,h⁆=0 := by
  rw [lie_lie,ha,hb,lie_zero,lie_zero,sub_self]

 def va : M := 0
 def vb (b A : M) : M := ⁅b,A⁆
 def vc (c D : M) : M := ⁅c,D⁆
 def vd (b A : M) : M := -⁅b,A⁆
 def ve (b e A D E : M) : M := ⁅b+e,D+E⁆-⁅b,A⁆
 def vf (b c e A D E : M) : M := -vc c D-ve b e A D E

 theorem vd_tangent (h : Data a b c d e f A B C D E H I J P Q) : vd b A=⁅d,A+H⁆ := by
  exact neg_eq_of_add_eq_zero_right h.special_d

 theorem bC (h : Data a b c d e f A B C D E H I J P Q) : ⁅b,C⁆=⁅e,I⁆ := by
  apply sub_eq_zero.mp
  calc
    _=⁅b+c+e,C⁆-(⁅c,C⁆+⁅e,C+I⁆) := by simp only [add_lie,lie_add]; abel
    _=0 := by rw [h.LC,h.special_e,sub_self]

 theorem ve_tangent (h : Data a b c d e f A B C D E H I J P Q) :
    ve b e A D E=⁅e,A+B+C+I⁆ := by
  rw [ve,h.pentagon]
  simp only [add_lie,lie_add]
  rw [h.bB,bC h]
  abel

 theorem gauge_difference (h : Data a b c d e f A B C D E H I J P Q) :
    (A+B+C+I)-(A+H)=P+Q := by
  rw [h.permuted,←h.cyclic]
  abel

 theorem crossing_de (h : Data a b c d e f A B C D E H I J P Q) :
    ⁅vd b A,e⁆+⁅d,ve b e A D E⁆=0 := by
  rw [vd_tangent h,ve_tangent h]
  exact crossing h.base.de (gauge_difference h) h.dP h.eQ

 theorem velocity_K : (0:M)+vb b A+vd b A=0 := by simp only [vb,vd,zero_add,add_neg_cancel]
 theorem velocity_L (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A+vc c D+ve b e A D E=⁅b+c+e,A+B⁆ := by
  calc
    _=⁅b+c+e,D+E⁆ := by simp only [vb,vc,ve,add_lie,lie_add,h.cE]; abel
    _=⁅b+c+e,A+B⁆ := by rw [h.pentagon,lie_add,h.LC,add_zero]

 theorem velocity_b (h : Data a b c d e f A B C D E H I J P Q) :
    vb b A=⁅b,A+B⁆ := by simp only [vb,lie_add,h.bB,add_zero]
 theorem velocity_c (h : Data a b c d e f A B C D E H I J P Q) :
    vc c D=⁅c,A+B⁆+⁅c,C⁆ := by
  have hh := congrArg (fun u => ⁅c,u⁆) h.pentagon
  simpa only [vc,lie_add,h.cE,add_zero] using hh

 theorem velocity_total :
    total (0:M) (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)=0 := by
  simp only [total,vb,vc,vd,vf]
  abel

 def ja (a : M) : Jet R M := ⟨a,0⟩
 def jb (b A : M) : Jet R M := ⟨b,vb b A⟩
 def jc (c D : M) : Jet R M := ⟨c,vc c D⟩
 def jd (d b A : M) : Jet R M := ⟨d,vd b A⟩
 def je (e b A D E : M) : Jet R M := ⟨e,ve b e A D E⟩
 def jf (f b c e A D E : M) : Jet R M := ⟨f,vf b c e A D E⟩

 theorem relations (h : Data a b c d e f A B C D E H I J P Q) :
    BraidSix.Relations (ja (R:=R) a) (jb b A) (jc c D) (jd d b A)
      (je e b A D E) (jf f b c e A D E) := by
  constructor
  · intro u _
    apply Jet.ext
    · change ⁅u.base,total a b c d e f⁆=0
      exact commute_symm (h.central u.base)
    · change ⁅u.velocity,total a b c d e f⁆+⁅u.base,
        total 0 (vb b A) (vc c D) (vd b A) (ve b e A D E) (vf b c e A D E)⁆=0
      rw [velocity_total,lie_zero,add_zero]
      exact commute_symm (h.central u.velocity)
  · apply Jet.ext
    · exact h.base.ac
    · change ⁅(0:M),c⁆+⁅a,⁅c,D⁆⁆=0
      rw [zero_lie,zero_add,leibniz_lie,h.base.ac,h.aD,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.de
    · exact crossing_de h
  · apply Jet.ext
    · exact h.base.aK
    · change ⁅(0:M),a+b+d⁆+⁅a,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,zero_lie,lie_zero,add_zero]
  · apply Jet.ext
    · exact h.base.bK
    · change ⁅⁅b,A⁆,a+b+d⁆+⁅b,(0:M)+vb b A+vd b A⁆=0
      rw [velocity_K,lie_zero,add_zero]
      exact commute_lie h.base.bK (commute_symm h.KA)
  · apply Jet.ext
    · exact h.base.bL
    · change ⁅vb b A,b+c+e⁆+⁅b,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_b h]
      exact inner_pair h.base.bL
  · apply Jet.ext
    · exact h.base.cL
    · change ⁅vc c D,b+c+e⁆+⁅c,vb b A+vc c D+ve b e A D E⁆=0
      rw [velocity_L h,velocity_c h,add_lie]
      have hz := commute_lie h.base.cL (commute_symm h.LC)
      rw [hz,add_zero]
      exact inner_pair h.base.cL

end TangentBraid

namespace TriangleSolutions
variable {M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
variable (u v w : M) (hu : ⁅u,u+v+w⁆=0) (hv : ⁅v,u+v+w⁆=0)

omit [LieAlgebra ℚ M] in
include hu hv in
theorem third : ⁅w,u+v+w⁆=0 := by
  have h := lie_self (u+v+w)
  rw [add_lie,add_lie,hu,hv,zero_add,zero_add] at h
  exact h

include hqn hn hu hv in
theorem shift_u : eval u w q=eval u (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift u (-u-v) (u+v+w) hu hneg hqn (by omega)

include hqn hn hu hv in
theorem shift_v : eval v w q=eval v (-u-v) q := by
  have hsum : w=(-u-v)+(u+v+w) := by abel
  have hneg : ⁅-u-v,u+v+w⁆=0 := by rw [sub_lie,neg_lie,hu,hv,neg_zero,sub_zero]
  conv_lhs => rw [hsum]
  exact eval_central_shift v (-u-v) (u+v+w) hv hneg hqn (by omega)

include hq hqn hn hu hv in
theorem cyclic : eval u v q+eval v w q=eval u w q := by
  have h := solution_three hq u v
  rw [solution_swap hq (-u-v) u,←shift_u hqn hn u v w hu hv,
    ←shift_v hqn hn u v w hu hv] at h
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)

include hq hqn hn hu hv in
theorem special : ⁅v,eval u v q⁆+⁅w,eval u v q+eval v w q⁆=0 := by
  have h := Differentiation.special_identity hq hqn hn v u
  have hc : -v-u= -u-v := by abel
  rw [hc,←shift_u hqn hn u v w hu hv] at h
  have hk : ⁅u+v+w,eval u w q⁆=0 :=
    eval_commutes u w (u+v+w) (commute_symm hu) (commute_symm (third u v w hu hv)) q
  have he : ⁅-u-v,eval u w q⁆=⁅w,eval u w q⁆ := by
    have hh : -u-v=w-(u+v+w) := by abel
    rw [hh,sub_lie,hk,sub_zero]
  rw [he] at h
  rw [cyclic hq hqn hn u v w hu hv]
  exact h

end TriangleSolutions

namespace T4SolutionData
open T4Basic

def A (q : L) : T4 := eval a b q
def B (q : L) : T4 := eval (a+d) (e+c) q
def C (q : L) : T4 := eval b c q
def D (q : L) : T4 := eval (d+b) c q
def E (q : L) : T4 := eval a (b+e) q
def H (q : L) : T4 := eval b d q
def I (q : L) : T4 := eval c e q
def J (q : L) : T4 := eval b e q
def P (q : L) : T4 := eval (a+b) e q
def Q (q : L) : T4 := eval d (b+c) q

 theorem pentagon {q : L} (hq : q∈W) : D q+E q=A q+B q+C q := by
  calc
    _=E q+D q := add_comm _ _
    _=C q+B q+A q := hq.2.2
    _=_ := by abel

 theorem permuted {q : L} (hq : q∈W) : P q+Q q= -H q+B q+J q := by
  have hh := congrArg (t4Rename (Equiv.swap (1:Fin 4) 2)) hq.2.2
  simp only [map_add,map_eval,t4Rename_t] at hh
  change eval d (b+c) q+eval (a+b) e q=eval b e q+eval (d+a) (c+e) q+eval d b q at hh
  rw [add_comm d a,add_comm c e,solution_swap hq d b] at hh
  calc
    _=Q q+P q := add_comm _ _
    _=J q+B q+(-H q) := hh
    _=_ := by abel

 theorem data {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    TangentBraid.Data a b c d e f (A q) (B q) (C q) (D q) (E q)
      (H q) (I q) (J q) (P q) (Q q) := by
  have ha : ⁅a,b+d⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.aK
  have hb : ⁅b,a+d⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.bK
  have hd : ⁅d,a+b⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.dK relations
  have hb' : ⁅b,c+e⁆=0 := by simpa only [lie_add,lie_self,zero_add] using relations.bL
  have hc : ⁅c,b+e⁆=0 := by simpa only [lie_add,lie_self,add_zero] using relations.cL
  have he : ⁅e,b+c⁆=0 := by simpa only [lie_add,lie_self,add_zero] using BraidSix.eL relations
  constructor
  · exact relations
  · exact central
  · exact eval_commutes (d+b) c a (by rwa [add_comm]) relations.ac q
  · exact eval_commutes (a+d) (e+c) b hb (by rwa [add_comm]) q
  · exact eval_commutes a (b+e) c (commute_symm relations.ac) hc q
  · exact eval_commutes a b (a+b+d) (commute_symm relations.aK) (commute_symm relations.bK) q
  · exact eval_commutes b c (b+c+e) (commute_symm relations.bL) (commute_symm relations.cL) q
  · exact TriangleSolutions.special hq hqn hn a b d relations.aK relations.bK
  · exact TriangleSolutions.special hq hqn hn b c e relations.bL relations.cL
  · exact TriangleSolutions.cyclic hq hqn hn b c e relations.bL relations.cL
  · exact pentagon hq
  · exact permuted hq
  · exact eval_commutes (a+b) e d hd relations.de q
  · exact eval_commutes d (b+c) e (commute_symm relations.de) he q

end T4SolutionData

namespace T4Derivation
open T4Basic T4SolutionData FreeDerivations TangentBraid
variable {n : ℕ} {q : L}

def jets (q : L) : Fin 4 → Fin 4 → Jet ℚ T4 :=
  BraidSix.matrix (ja a) (jb b (A q)) (jc c (T4SolutionData.D q)) (jd d b (A q))
    (je e b (A q) (T4SolutionData.D q) (E q)) (jf f b c e (A q) (T4SolutionData.D q) (E q))

@[simp] theorem jets_base (q : L) (i j : Fin 4) : (jets q i j).base=t i j := by
  rw [←matrix_t i j]
  fin_cases i <;> fin_cases j <;> rfl

def lift (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : T4 →ₗ⁅ℚ⁆ Jet ℚ T4 :=
  T4Universal.lift (jets q) BraidSix.matrix_symm BraidSix.matrix_self
    (fun i j k l _ hik hil hjk hjl _ =>
      BraidSix.matrix_disjoint (TangentBraid.relations (data hq hqn hn)) i j k l hik hil hjk hjl)
    (BraidSix.matrix_three (TangentBraid.relations (data hq hqn hn)))

@[simp] theorem lift_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    lift hq hqn hn (t i j)=jets q i j := T4Universal.lift_t _ _ _ _ _ _ _

@[simp] theorem lift_base (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : T4) :
    (lift hq hqn hn p).base=p := by
  have he : Jet.baseHom.comp (lift hq hqn hn)=LieHom.id := by
    apply T4Basic.hom_ext
    intro i j
    change (lift hq hqn hn (t i j)).base=t i j
    rw [lift_t,jets_base]
  exact LieHom.congr_fun he p

def derivation (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : LieDerivation ℚ T4 T4 where
  toFun p := (lift hq hqn hn p).velocity
  map_add' p r := by change (lift hq hqn hn (p+r)).velocity=_; rw [map_add]; rfl
  map_smul' s p := by change (lift hq hqn hn (s • p)).velocity=_; rw [map_smul]; rfl
  leibniz' p r := by
    change (lift hq hqn hn ⁅p,r⁆).velocity=⁅p,(lift hq hqn hn r).velocity⁆-⁅r,(lift hq hqn hn p).velocity⁆
    rw [LieHom.map_lie,Jet.velocity_lie,lift_base,lift_base,sub_eq_add_neg,lie_skew,add_comm]

@[simp] theorem derivation_t (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (i j : Fin 4) :
    derivation hq hqn hn (t i j)=(jets q i j).velocity := by
  change (lift hq hqn hn (t i j)).velocity=_
  rw [lift_t]

@[simp] theorem derivation_a (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn a=0 := by
  exact derivation_t hq hqn hn 0 1
@[simp] theorem derivation_b (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn b=⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 2
@[simp] theorem derivation_c (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn c=⁅c,T4SolutionData.D q⁆ := by
  exact derivation_t hq hqn hn 2 3
@[simp] theorem derivation_d (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : derivation hq hqn hn d= -⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 0 2
@[simp] theorem derivation_e (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn e=⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆ := by
  exact derivation_t hq hqn hn 1 3
@[simp] theorem derivation_f (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) :
    derivation hq hqn hn f= -⁅c,T4SolutionData.D q⁆-(⁅b+e,T4SolutionData.D q+E q⁆-⁅b,A q⁆) := by
  exact derivation_t hq hqn hn 0 3

end T4Derivation

end DeligneDrinfeld

end

end OAI
