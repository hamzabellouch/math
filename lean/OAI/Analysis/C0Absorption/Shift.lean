import OAI.Analysis.C0Absorption.LocalInverse

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def frozenShift (W : FrozenWeights) : C0 →L[ℝ] BlockC0 := inputBlocks+frozenCorrectionL W

@[simp] theorem frozenShift_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenShift W x γ=x (labelIndex γ)+frozenCorrection W γ x := rfl

theorem frozenShift_bound (W : FrozenWeights) (x : C0) : ‖frozenShift W x‖≤5*‖x‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg x))
  intro γ
  rw [frozenShift_apply]
  exact (abs_add_le _ _).trans (by linarith [c0_norm_apply_le x (labelIndex γ),frozenCorrection_bound W γ x])

def blockInclusion : BlockC0 →L[ℝ] C0 :=
  inputCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ C0 BlockC0)

@[simp] theorem blockInclusion_apply (y : BlockC0) (γ : Label) : blockInclusion y (labelIndex γ)=y γ :=
  joinInputs_block (0,y) γ

def outputScalar (W : FrozenWeights) (lev : Level) : BlockC0 →L[ℝ] ℝ :=
  (rowScalar W lev).comp blockInclusion

@[simp] theorem outputScalar_apply (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    outputScalar W lev y=∑ b : Block lev,W.row lev b*y (blockLabel lev b) := by
  simp only [outputScalar,ContinuousLinearMap.comp_apply,rowScalar_apply,blockInput,blockInclusion_apply]

theorem outputScalar_bound (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    |outputScalar W lev y|≤2*‖y‖ := by
  rw [outputScalar_apply]
  exact (abs_finite_dot_le _ _ (fun b => cfun_norm_apply_le y (blockLabel lev b))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound lev) (norm_nonneg y))

theorem outputScalar_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (fun lev => outputScalar W lev y) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun lev => rowScalar_local W lev (blockInclusion y)) _
  simpa only [mul_zero] using (localRadius_tendsto (blockInclusion y)).const_mul 2

def firstLevel (i : ℕ) : Level := (i,0)

theorem firstLevel_injective : Function.Injective firstLevel := fun _ _ h => congrArg Prod.fst h

theorem levelSuccessor_injective : Function.Injective levelSuccessor := by
  rintro ⟨i,n⟩ ⟨j,m⟩ h
  simp only [levelSuccessor,Prod.mk.injEq,Nat.add_right_cancel_iff] at h
  exact Prod.ext h.1 h.2

def inverseRows (W : FrozenWeights) (y : BlockC0) : C0 :=
  cfunOfTendsto (fun i => outputScalar W (i,0) y)
    ((outputScalar_tendsto W y).comp firstLevel_injective.tendsto_cofinite)

def inverseBlockFunction (W : FrozenWeights) (y : BlockC0) (γ : Label) : ℝ :=
  y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)

theorem inverseBlockFunction_tendsto (W : FrozenWeights) (y : BlockC0) :
    Tendsto (inverseBlockFunction W y) cofinite (nhds 0) := by
  have hb : Tendsto (fun γ : Label => outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)
      cofinite (nhds 0) := by
    simpa only [sub_zero,Function.comp_def] using ((outputScalar_tendsto W y).comp labelLevel_tendsto).sub
      ((outputScalar_tendsto W y).comp (levelSuccessor_injective.tendsto_cofinite.comp labelLevel_tendsto))
  have hm : Tendsto (fun γ : Label => W.vector γ.level ⟨γ.band,γ.tag⟩*
      (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0) := by
    have hbound (γ : Label) : ‖W.vector γ.level ⟨γ.band,γ.tag⟩*
        (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)‖≤
        |outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y| := by
      simpa only [Real.norm_eq_abs,abs_mul,one_mul] using
        mul_le_mul_of_nonneg_right (W.vector_bound γ.level ⟨γ.band,γ.tag⟩)
          (abs_nonneg (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y))
    exact squeeze_zero_norm hbound (by simpa only [abs_zero] using hb.abs)
  change Tendsto (fun γ : Label => y γ-W.vector γ.level ⟨γ.band,γ.tag⟩*
    (outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)) cofinite (nhds 0)
  simpa only [sub_zero] using (cfun_tendsto y).sub hm

def inverseBlocks (W : FrozenWeights) (y : BlockC0) : BlockC0 :=
  cfunOfTendsto (inverseBlockFunction W y) (inverseBlockFunction_tendsto W y)

def frozenInverse (W : FrozenWeights) (y : BlockC0) : C0 := joinInputs (inverseRows W y,inverseBlocks W y)

@[simp] theorem frozenInverse_row (W : FrozenWeights) (y : BlockC0) (i : ℕ) :
    frozenInverse W y (rowIndex i)=outputScalar W (i,0) y := joinInputs_row _ i

@[simp] theorem frozenInverse_block (W : FrozenWeights) (y : BlockC0) (γ : Label) :
    frozenInverse W y (labelIndex γ)=inverseBlockFunction W y γ := joinInputs_block _ γ

theorem frozenInverse_bound (W : FrozenWeights) (y : BlockC0) : ‖frozenInverse W y‖≤5*‖y‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg y))
  intro k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    have hb := outputScalar_bound W (i,0) y
    change |frozenInverse W y (rowIndex i)|≤_
    rw [frozenInverse_row]
    nlinarith [norm_nonneg y]
  | inr γ =>
    change |frozenInverse W y (labelIndex γ)|≤_
    rw [frozenInverse_block,inverseBlockFunction]
    apply (abs_sub _ _).trans
    have hp : |W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|outputScalar W γ.level y|+|outputScalar W (levelSuccessor γ.level) y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [outputScalar_bound W γ.level y,outputScalar_bound W (levelSuccessor γ.level) y]
    linarith [cfun_norm_apply_le y γ]

def frozenInverseL (W : FrozenWeights) : BlockC0 →L[ℝ] C0 :=
  LinearMap.mkContinuous
    { toFun := frozenInverse W
      map_add' := by
        intro y z
        ext k
        obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
        cases a with
        | inl i =>
          change frozenInverse W (y+z) (rowIndex i)=frozenInverse W y (rowIndex i)+frozenInverse W z (rowIndex i)
          simp only [frozenInverse_row,map_add]
        | inr γ =>
          change frozenInverse W (y+z) (labelIndex γ)=frozenInverse W y (labelIndex γ)+frozenInverse W z (labelIndex γ)
          simp only [frozenInverse_block,inverseBlockFunction,ZeroAtInftyContinuousMap.add_apply,map_add]
          ring
      map_smul' := by
        intro c y
        ext k
        obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
        cases a with
        | inl i =>
          change frozenInverse W (c • y) (rowIndex i)=c • frozenInverse W y (rowIndex i)
          simp only [frozenInverse_row,map_smul]
        | inr γ =>
          change frozenInverse W (c • y) (labelIndex γ)=c • frozenInverse W y (labelIndex γ)
          simp only [frozenInverse_block,inverseBlockFunction,ZeroAtInftyContinuousMap.smul_apply,map_smul,smul_eq_mul]
          ring }
    5 (frozenInverse_bound W)

theorem finite_row_cancel {A : Type*} [Fintype A] (w v y : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(y a-v a*b))=(∑ a,w a*y a)-b := by
  simp only [mul_sub,← mul_assoc,Finset.sum_sub_distrib,← Finset.sum_mul,h,one_mul]

theorem finite_row_shift {A : Type*} [Fintype A] (w v x : A → ℝ) (h : (∑ a,w a*v a)=1) (b : ℝ) :
    (∑ a,w a*(x a+v a*b))=(∑ a,w a*x a)+b := by
  simp only [mul_add,← mul_assoc,Finset.sum_add_distrib,← Finset.sum_mul,h,one_mul]

theorem rowScalar_frozenInverse (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    rowScalar W lev (frozenInverse W y)=outputScalar W (levelSuccessor lev) y := by
  rw [rowScalar_apply]
  simp only [blockInput,frozenInverse_block,inverseBlockFunction,blockLabel]
  rw [finite_row_cancel _ _ _ (W.pairing lev)]
  have hs := outputScalar_apply W lev y
  simp only [blockLabel] at hs
  rw [← hs]
  ring

theorem previousScalar_frozenInverse (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    previousScalar W lev (frozenInverse W y)=outputScalar W lev y := by
  rcases lev with ⟨i,n⟩
  cases n with
  | zero => exact frozenInverse_row W y i
  | succ n => exact rowScalar_frozenInverse W (i,n) y

theorem frozenShift_frozenInverse (W : FrozenWeights) (y : BlockC0) : frozenShift W (frozenInverse W y)=y := by
  ext γ
  rw [frozenShift_apply,frozenInverse_block,inverseBlockFunction,frozenCorrection_apply,
    previousScalar_frozenInverse,rowScalar_frozenInverse]
  ring

theorem outputScalar_frozenShift (W : FrozenWeights) (lev : Level) (x : C0) :
    outputScalar W lev (frozenShift W x)=previousScalar W lev x := by
  rw [outputScalar_apply]
  simp only [frozenShift_apply,frozenCorrection_apply,blockLabel]
  rw [finite_row_shift _ _ _ (W.pairing lev)]
  rw [rowScalar_apply W lev x]
  simp only [blockInput,blockLabel]
  ring

theorem frozenInverse_frozenShift (W : FrozenWeights) (x : C0) : frozenInverse W (frozenShift W x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    change frozenInverse W (frozenShift W x) (rowIndex i)=_
    rw [frozenInverse_row,outputScalar_frozenShift]
    rfl
  | inr γ =>
    change frozenInverse W (frozenShift W x) (labelIndex γ)=_
    rw [frozenInverse_block,inverseBlockFunction,frozenShift_apply,outputScalar_frozenShift,outputScalar_frozenShift,frozenCorrection_apply]
    have he : previousScalar W (levelSuccessor γ.level)=rowScalar W γ.level := by
      rcases γ.level with ⟨i,n⟩
      rfl
    rw [he]
    change x (labelIndex γ)+_ - _=x (labelIndex γ)
    ring

def frozenEquiv (W : FrozenWeights) : C0 ≃L[ℝ] BlockC0 where
  toFun := frozenShift W
  invFun := frozenInverse W
  left_inv := frozenInverse_frozenShift W
  right_inv := frozenShift_frozenInverse W
  map_add' := map_add (frozenShift W)
  map_smul' := map_smul (frozenShift W)
  continuous_toFun := (frozenShift W).continuous
  continuous_invFun := (frozenInverseL W).continuous

theorem frozenShift_lower (W : FrozenWeights) (x : C0) : ‖x‖≤5*‖frozenShift W x‖ := by
  simpa only [frozenInverse_frozenShift] using frozenInverse_bound W (frozenShift W x)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

def recomputedShift (x : C0) : BlockC0 := frozenShift (stateWeights (normalizedBall x)) x

@[simp] theorem recomputedShift_zero : recomputedShift 0=0 := map_zero _

theorem WeightError.smul {W V : FrozenWeights} {x : C0} {q : ℝ} (h : WeightError W V x q) (a : ℝ) :
    WeightError W V (a • x) (|a| *q) := by
  constructor
  · intro lev b
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.vector lev b) (abs_nonneg a)
  · intro lev
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.row lev) (abs_nonneg a)

theorem WeightError.mono {W V : FrozenWeights} {x : C0} {q r : ℝ} (h : WeightError W V x q) (hr : q≤r) :
    WeightError W V x r := ⟨fun lev b => (h.vector lev b).trans hr,fun lev => (h.row lev).trans hr⟩

theorem normalized_error_left (x y : C0) : WeightError (stateWeights (normalizedBall x))
    (mixedWeights (normalizedBall x) (normalizedBall y)) x (2*eta*dist x y) := by
  have hh := (mixed_left_error (normalizedBall x) (normalizedBall y)).smul ‖x‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg x)] at hh
  apply hh.mono
  calc
    _ = eta*(‖x‖ * dist (normalize x) (normalize y)) := by rw [Subtype.dist_eq]; ring
    _ ≤ eta*(2*dist x y) := mul_le_mul_of_nonneg_left (normalization_bound x y) eta_pos.le
    _ = _ := by ring

theorem normalized_error_right (x y : C0) : WeightError (stateWeights (normalizedBall y))
    (mixedWeights (normalizedBall x) (normalizedBall y)) y (2*eta*dist x y) := by
  have hh := (mixed_right_error (normalizedBall x) (normalizedBall y)).smul ‖y‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg y)] at hh
  apply hh.mono
  calc
    _ = eta*(‖y‖ * dist (normalize y) (normalize x)) := by rw [Subtype.dist_eq,dist_comm]; ring
    _ ≤ eta*(2*dist y x) := mul_le_mul_of_nonneg_left (normalization_bound y x) eta_pos.le
    _ = _ := by rw [dist_comm]; ring

theorem shift_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) : ‖frozenShift W x-frozenShift V x‖≤6*q := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) hq)
  intro γ
  change |frozenShift W x γ-frozenShift V x γ|≤_
  rw [frozenShift_apply,frozenShift_apply,add_sub_add_left_eq_sub]
  exact correction_weight_error hq h γ

theorem recomputed_mixed_left (x y : C0) :
    ‖recomputedShift x-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) x‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_left x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_right (x y : C0) :
    ‖recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) y‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_right x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_approx (x y : C0) :
    ‖recomputedShift x-recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  have he : recomputedShift x-recomputedShift y-frozenShift W (x-y)=
      (recomputedShift x-frozenShift W x)-(recomputedShift y-frozenShift W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [recomputed_mixed_left x y,recomputed_mixed_right x y])

theorem recomputed_global_bounds (x y : C0) :
    (1/5-24*eta)*dist x y≤dist (recomputedShift x) (recomputedShift y) ∧
    dist (recomputedShift x) (recomputedShift y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  let a := recomputedShift x-recomputedShift y
  let b := frozenShift W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := recomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by simpa only [dist_eq_norm] using frozenShift_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using frozenShift_lower W (x-y)
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  rw [dist_eq_norm (recomputedShift x) (recomputedShift y)]
  change (1/5-24*eta)*dist x y≤‖a‖ ∧ ‖a‖≤(5+24*eta)*dist x y
  constructor <;> nlinarith

theorem recomputed_lipschitz : LipschitzWith (628/125) recomputedShift := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (recomputed_global_bounds x y).2
  norm_num [eta] at hh ⊢
  exact hh

theorem recomputed_antilipschitz : AntilipschitzWith (125/22) recomputedShift := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := (recomputed_global_bounds x y).1
  norm_num [eta] at h ⊢
  nlinarith

end
end C0Absorption

end OAI
