import OAI.Analysis.C0Absorption.Space

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

section Sparse
variable {A : Type*} [Fintype A]

def sparseC0 (j : A → ℕ) (x : A → ℝ) : C0 :=
  cfunOfTendsto (Function.extend j x 0) (by
    apply tendsto_congr' (show Function.extend j x 0 =ᶠ[cofinite] fun _ => 0 from ?_) |>.mpr
      tendsto_const_nhds
    filter_upwards [(Set.finite_range j).compl_mem_cofinite] with k hk
    exact Function.extend_apply' _ _ _ hk)

@[simp] theorem sparseC0_apply (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) (a : A) :
    sparseC0 j x (j a)=x a := hj.extend_apply _ _ a

theorem sparseC0_outside (j : A → ℕ) (x : A → ℝ) (k : ℕ) (hk : k∉Set.range j) :
    sparseC0 j x k=0 := Function.extend_apply' _ _ _ hk

theorem sparseC0_norm_le (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖≤‖x‖ := by
  apply cfun_norm_le _ (norm_nonneg x)
  intro k
  by_cases hk : k∈Set.range j
  · obtain ⟨a,rfl⟩ := hk
    rw [sparseC0_apply j hj]
    exact norm_le_pi_norm x a
  · rw [sparseC0_outside j x k hk,abs_zero]
    exact norm_nonneg x

def sparseC0L (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := sparseC0 j
      map_add' := by
        intro x y
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.add_apply,add_zero]
      map_smul' := by
        intro c x
        ext k
        by_cases hk : k∈Set.range j
        · obtain ⟨a,rfl⟩ := hk
          simp only [sparseC0_apply j hj,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply]
        · simp only [sparseC0_outside j _ k hk,ZeroAtInftyContinuousMap.smul_apply,smul_zero] }
    1 (fun x => by
      change ‖sparseC0 j x‖≤1*‖x‖
      simpa only [one_mul] using sparseC0_norm_le j hj x)

theorem sparseC0_norm (j : A → ℕ) (hj : Function.Injective j) (x : A → ℝ) : ‖sparseC0 j x‖=‖x‖ := by
  apply le_antisymm (sparseC0_norm_le j hj x)
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  rw [← sparseC0_apply j hj x a]
  exact cfun_norm_apply_le _ _

def sparseC0Isometry (j : A → ℕ) (hj : Function.Injective j) : (A → ℝ) →ₗᵢ[ℝ] C0 where
  toLinearMap := (sparseC0L j hj).toLinearMap
  norm_map' := sparseC0_norm j hj

end Sparse

abbrev FLevel (N : ℕ) := Fin (N+1) × Fin (N+1)
abbrev FLabel (N : ℕ) := (lev : FLevel N) × Block (lev.1.val,lev.2.val)
abbrev FCoord (N : ℕ) := Sum (Fin (N+1)) (FLabel N)
abbrev FInput (N : ℕ) := FCoord N → ℝ

def fLabel {N : ℕ} (γ : FLabel N) : Label := blockLabel (γ.1.1.val,γ.1.2.val) γ.2

theorem fLabel_injective (N : ℕ) : Function.Injective (@fLabel N) := by
  rintro ⟨⟨i,n⟩,b⟩ ⟨⟨i',n'⟩,b'⟩ he
  have hl := congrArg Label.level he
  change (i.val,n.val)=(i'.val,n'.val) at hl
  have hi : i=i' := Fin.ext (Prod.mk.inj hl).1
  have hn : n=n' := Fin.ext (Prod.mk.inj hl).2
  subst i'; subst n'
  have hb : b=b' := blockLabel_injective _ he
  subst b'
  rfl

def fCoord {N : ℕ} : FCoord N → ℕ := Sum.elim (fun i => rowIndex i.val) (fun γ => labelIndex (fLabel γ))

theorem fCoord_injective (N : ℕ) : Function.Injective (@fCoord N) := by
  rintro (i|γ) (j|δ) he
  · exact congrArg Sum.inl (Fin.ext (rowIndex_injective he))
  · exact (rowIndex_ne_labelIndex i.val (fLabel δ) he).elim
  · exact (rowIndex_ne_labelIndex j.val (fLabel γ) he.symm).elim
  · exact congrArg Sum.inr (fLabel_injective N (labelIndex_injective he))

def finiteEmbed (N : ℕ) : FInput N →ₗᵢ[ℝ] C0 := sparseC0Isometry fCoord (fCoord_injective N)

@[simp] theorem finiteEmbed_apply {N : ℕ} (x : FInput N) (a : FCoord N) :
    finiteEmbed N x (fCoord a)=x a := sparseC0_apply _ (fCoord_injective N) x a

@[simp] theorem finiteEmbed_row {N : ℕ} (x : FInput N) (i : Fin (N+1)) :
    finiteEmbed N x (rowIndex i.val)=x (.inl i) := finiteEmbed_apply x (.inl i)

@[simp] theorem finiteEmbed_block {N : ℕ} (x : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))=x (.inr ⟨l,b⟩) := finiteEmbed_apply x (.inr ⟨l,b⟩)

theorem finiteEmbed_row_outside {N : ℕ} (x : FInput N) (i : ℕ) (hi : N < i) : finiteEmbed N x (rowIndex i)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl a => have he := rowIndex_injective ha; have := a.isLt; omega
  | inr γ => exact rowIndex_ne_labelIndex i (fLabel γ) ha.symm

theorem finiteEmbed_block_outside {N : ℕ} (x : FInput N) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : finiteEmbed N x (labelIndex γ)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl i => exact rowIndex_ne_labelIndex i.val γ ha
  | inr δ =>
    have he := congrArg Label.level (labelIndex_injective ha)
    change (δ.1.1.val,δ.1.2.val)=γ.level at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    have := δ.1.1.isLt
    have := δ.1.2.isLt
    omega

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

def finiteRow (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  ∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*x (.inr ⟨l,b⟩)

theorem finiteRow_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finiteRow W l x=rowScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rw [rowScalar_apply]
  simp only [finiteRow,blockInput,finiteEmbed_block]

theorem finiteRow_bound (W : FrozenWeights) (l : FLevel N) (x : FInput N) : |finiteRow W l x|≤2*‖x‖ := by
  unfold finiteRow
  exact (abs_finite_dot_le _ _ (fun b => norm_le_pi_norm x (.inr ⟨l,b⟩))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound _) (norm_nonneg x))

def finPred (n : Fin (N+1)) : Fin (N+1) := ⟨n.val-1,(Nat.sub_le _ _).trans_lt n.isLt⟩

def finitePrev (W : FrozenWeights) (l : FLevel N) (x : FInput N) : ℝ :=
  if l.2.val=0 then x (.inl l.1) else finiteRow W (l.1,finPred l.2) x

theorem finitePrev_eq (W : FrozenWeights) (l : FLevel N) (x : FInput N) :
    finitePrev W l x=previousScalar W (l.1.val,l.2.val) (finiteEmbed N x) := by
  rcases l with ⟨i,⟨n,hn⟩⟩
  cases n with
  | zero => simp only [finitePrev,↓reduceIte,previousScalar,c0Eval_apply,finiteEmbed_row]
  | succ n =>
    simp only [finitePrev,Nat.succ_ne_zero,↓reduceIte,finiteRow_eq,finPred,Nat.add_sub_cancel,previousScalar]

def finiteFrozenFunction (W : FrozenWeights) (x : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,Fin.last N) x
  | .inr ⟨l,b⟩ => x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)

@[simp] theorem finiteFrozen_row (W : FrozenWeights) (x : FInput N) (i : Fin (N+1)) :
    finiteFrozenFunction W x (.inl i)=finiteRow W (i,Fin.last N) x := rfl

@[simp] theorem finiteFrozen_block (W : FrozenWeights) (x : FInput N) (γ : FLabel N) :
    finiteFrozenFunction W x (.inr γ)=frozenShift W (finiteEmbed N x) (fLabel γ) := by
  rcases γ with ⟨l,b⟩
  rw [frozenShift_apply,frozenCorrection_apply]
  change x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)=
    finiteEmbed N x (labelIndex (blockLabel (l.1.val,l.2.val) b))+W.vector (l.1.val,l.2.val) b*
      (previousScalar W (l.1.val,l.2.val) (finiteEmbed N x)-rowScalar W (l.1.val,l.2.val) (finiteEmbed N x))
  rw [finiteEmbed_block,finitePrev_eq,finiteRow_eq]

theorem finiteFrozen_bound (W : FrozenWeights) (x : FInput N) : ‖finiteFrozenFunction W x‖≤5*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg x))).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x|≤_
    exact (finiteRow_bound W _ x).trans (by nlinarith [norm_nonneg x])
  · rw [finiteFrozen_block]
    exact (cfun_norm_apply_le _ _).trans ((frozenShift_bound W (finiteEmbed N x)).trans_eq (by rw [LinearIsometry.norm_map]))

def finiteFrozen (N : ℕ) (W : FrozenWeights) : FInput N →L[ℝ] FInput N :=
  LinearMap.mkContinuous
    { toFun := finiteFrozenFunction W
      map_add' := by
        intro x y
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_add,Pi.add_apply]
        | inr γ => simp only [finiteFrozen_block,map_add,ZeroAtInftyContinuousMap.add_apply,Pi.add_apply]
      map_smul' := by
        intro c x
        funext a
        cases a with
        | inl i => simp only [finiteFrozen_row,finiteRow_eq,map_smul,Pi.smul_apply,RingHom.id_apply]
        | inr γ => simp only [finiteFrozen_block,map_smul,ZeroAtInftyContinuousMap.smul_apply,Pi.smul_apply,RingHom.id_apply] }
    5 (finiteFrozen_bound W)

def finiteNext (W : FrozenWeights) (l : FLevel N) (y : FInput N) : ℝ :=
  if h : l.2.val<N then finiteRow W (l.1,⟨l.2.val+1,by omega⟩) y else y (.inl l.1)

theorem finiteNext_bound (W : FrozenWeights) (l : FLevel N) (y : FInput N) : |finiteNext W l y|≤2*‖y‖ := by
  unfold finiteNext
  split_ifs
  · exact finiteRow_bound W _ y
  · exact (norm_le_pi_norm y (.inl l.1)).trans (by nlinarith [norm_nonneg y])

def finiteInverseFunction (W : FrozenWeights) (y : FInput N) : FInput N := fun a =>
  match a with
  | .inl i => finiteRow W (i,0) y
  | .inr ⟨l,b⟩ => y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)

@[simp] theorem finiteInverse_row (W : FrozenWeights) (y : FInput N) (i : Fin (N+1)) :
    finiteInverseFunction W y (.inl i)=finiteRow W (i,0) y := rfl

@[simp] theorem finiteInverse_block (W : FrozenWeights) (y : FInput N) (l : FLevel N) (b : Block (l.1.val,l.2.val)) :
    finiteInverseFunction W y (.inr ⟨l,b⟩)=y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y) := rfl

theorem finiteInverse_bound (W : FrozenWeights) (y : FInput N) : ‖finiteInverseFunction W y‖≤5*‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg y))).mpr
  rintro (i|⟨l,b⟩)
  · exact (finiteRow_bound W _ y).trans (by nlinarith [norm_nonneg y])
  · change |y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤_
    apply (abs_sub _ _).trans
    have hp : |W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|finiteRow W l y|+|finiteNext W l y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [finiteRow_bound W l y,finiteNext_bound W l y]
    have hy : |y (.inr ⟨l,b⟩)|≤‖y‖ := norm_le_pi_norm y _
    linarith

theorem finiteRow_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finiteRow W l (finiteInverseFunction W y)=finiteNext W l y := by
  unfold finiteRow
  simp only [finiteInverse_block]
  rw [finite_row_cancel _ _ _ (W.pairing _)]
  change finiteRow W l y-(finiteRow W l y-finiteNext W l y)=_
  ring

theorem finitePrev_inverse (W : FrozenWeights) (y : FInput N) (l : FLevel N) :
    finitePrev W l (finiteInverseFunction W y)=finiteRow W l y := by
  unfold finitePrev
  split_ifs with hn
  · have he : l.2=0 := Fin.ext hn
    rcases l with ⟨i,n⟩
    dsimp at he
    subst n
    rfl
  · rw [finiteRow_inverse]
    have hp : (finPred l.2).val<N := by have := l.2.isLt; dsimp [finPred]; omega
    simp only [finiteNext,hp,↓reduceDIte]
    congr 2
    apply Fin.ext
    dsimp [finPred]
    omega

theorem finiteFrozen_inverse (W : FrozenWeights) (y : FInput N) : finiteFrozen N W (finiteInverseFunction W y)=y := by
  funext a
  cases a with
  | inl i =>
    change finiteRow W (i,Fin.last N) (finiteInverseFunction W y)=_
    rw [finiteRow_inverse]
    simp only [finiteNext,Fin.val_last,lt_self_iff_false,↓reduceDIte]
  | inr γ =>
    rcases γ with ⟨l,b⟩
    change finiteInverseFunction W y (.inr ⟨l,b⟩)+_=_
    rw [finiteInverse_block,finitePrev_inverse,finiteRow_inverse]
    ring

theorem finiteRow_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteRow W l (finiteFrozen N W x)=finitePrev W l x := by
  unfold finiteRow
  change (∑ b : Block (l.1.val,l.2.val), W.row (l.1.val,l.2.val) b*
    (x (.inr ⟨l,b⟩)+W.vector (l.1.val,l.2.val) b*(finitePrev W l x-finiteRow W l x)))=_
  rw [finite_row_shift _ _ _ (W.pairing _)]
  change finiteRow W l x+(finitePrev W l x-finiteRow W l x)=_
  ring

theorem finiteNext_frozen (W : FrozenWeights) (x : FInput N) (l : FLevel N) :
    finiteNext W l (finiteFrozen N W x)=finiteRow W l x := by
  unfold finiteNext
  split_ifs with hn
  · rw [finiteRow_frozen]
    simp only [finitePrev,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
    congr 2
  · have he : l.2=Fin.last N := Fin.ext (by have := l.2.isLt; simp only [Fin.val_last]; omega)
    change finiteRow W (l.1,Fin.last N) x=finiteRow W l x
    rw [← he]

theorem finiteInverse_frozen (W : FrozenWeights) (x : FInput N) : finiteInverseFunction W (finiteFrozen N W x)=x := by
  funext a
  cases a with
  | inl i =>
    rw [finiteInverse_row,finiteRow_frozen]
    rfl
  | inr γ =>
    rcases γ with ⟨l,b⟩
    rw [finiteInverse_block,finiteRow_frozen,finiteNext_frozen]
    change x (.inr ⟨l,b⟩)+_ - _=x (.inr ⟨l,b⟩)
    ring

def finiteEquiv (N : ℕ) (W : FrozenWeights) : FInput N ≃L[ℝ] FInput N :=
  ContinuousLinearEquiv.ofBijective (finiteFrozen N W)
    (LinearMap.ker_eq_bot.mpr (fun x y h => by
      change finiteFrozen N W x=finiteFrozen N W y at h
      simpa only [finiteInverse_frozen] using congrArg (finiteInverseFunction W) h))
    (LinearMap.range_eq_top.mpr (fun y => ⟨finiteInverseFunction W y,finiteFrozen_inverse W y⟩))

theorem finiteEquiv_symm_apply (N : ℕ) (W : FrozenWeights) (y : FInput N) :
    (finiteEquiv N W).symm y=finiteInverseFunction W y := by
  apply (finiteEquiv N W).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (finiteFrozen_inverse W y).symm

theorem finiteFrozen_lower (W : FrozenWeights) (x : FInput N) : ‖x‖≤5*‖finiteFrozen N W x‖ := by
  simpa only [finiteInverse_frozen] using finiteInverse_bound W (finiteFrozen N W x)

theorem finiteEquiv_symm_norm (N : ℕ) (W : FrozenWeights) : ‖((finiteEquiv N W).symm : FInput N →L[ℝ] FInput N)‖≤5 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [ContinuousLinearEquiv.coe_coe,finiteEquiv_symm_apply]
  exact finiteInverse_bound W y

end
end C0Absorption

end OAI
