import OAI.MathematicalPhysics.NavierStokes.ShearFlows.FieldExpressions
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Localization

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set Filter
open scoped Topology BigOperators ContDiff
namespace ShearFlows

namespace RationalBox

def centerQ {n : ℕ} (R : RationalBox n) (j : Fin n) : ℚ := (R.lower j + R.upper j)/2

theorem centerQ_cast {n : ℕ} (R : RationalBox n) (j : Fin n) :
    (R.centerQ j : ℝ) = R.center j := by simp [centerQ,center]
end RationalBox

namespace PeriodicExpr

def cutoff (L a b c d : ℚ) : PeriodicExpr := ⟨L,a,d,ProfileExpr.cutoff a b c d⟩
def potential (L a b c d p : ℚ) : PeriodicExpr := ⟨L,a,d,ProfileExpr.potential a b c d p⟩
def mask (L a b c d p : ℚ) : PeriodicExpr := (potential L a b c d p).diff

theorem cutoff_valid {L a b c d : ℚ} (hL : 0<L) (hab : a<b) (hcd : c<d) :
    (cutoff L a b c d).Valid := by
  refine ⟨hL, ?_⟩
  dsimp [cutoff]
  rw [ProfileExpr.val_cutoff]
  exact (closedCutoff_support (by exact_mod_cast hab) (by exact_mod_cast hcd)).trans Ioo_subset_Icc_self

theorem potential_valid {L a b c d p : ℚ} (hL : 0<L) (hab : a<b) (hcd : c<d) :
    (potential L a b c d p).Valid := by
  refine ⟨hL, ?_⟩
  dsimp [potential]
  rw [ProfileExpr.val_potential]
  exact maskPotential_support (by exact_mod_cast hab) (by exact_mod_cast hcd) _

theorem mask_valid {L a b c d p : ℚ} (hL : 0<L) (hab : a<b) (hcd : c<d) :
    (mask L a b c d p).Valid := valid_diff (potential_valid hL hab hcd)

theorem cutoff_val (L a b c d : ℚ) :
    (cutoff L a b c d).val = circleCutoff L a b c d := by
  simp only [val,cutoff,ProfileExpr.val_cutoff,circleCutoff]

theorem potential_val (L a b c d p : ℚ) :
    (potential L a b c d p).val = periodize L (fun x => (x-(p : ℝ))*closedCutoff a b c d x) := by
  simp only [val,potential,ProfileExpr.val_potential]

theorem mask_val {L a b c d p : ℚ} (hL : 0<L) (hab : a<b) (hcd : c<d) :
    (mask L a b c d p).val = circleMask L a b c d p := by
  rw [mask, val_diff (potential_valid hL hab hcd), potential_val]
  rfl

def pulse (j : Fin 7) : PeriodicExpr :=
  ⟨1,stageStart j,stageFinish j,(ProfileExpr.ramp (stageStart j) (stageFinish j)).diff⟩

theorem pulse_valid (j : Fin 7) : (pulse j).Valid := by
  refine ⟨by norm_num [pulse], ?_⟩
  dsimp [pulse]
  rw [ProfileExpr.val_diff,ProfileExpr.val_ramp]
  exact (smoothPulse_support (by exact_mod_cast (stage_intervals j).2.1)).trans Ioo_subset_Icc_self

theorem pulse_val (j : Fin 7) : (pulse j).val = periodPulse j := by
  simp only [pulse,val,ProfileExpr.val_diff,ProfileExpr.val_ramp,periodPulse,smoothPulse,Rat.cast_one]

end PeriodicExpr

namespace FieldExpr

def planeMask (L : ℚ) (R : RationalBox 2) (r : ℚ) : FieldExpr :=
  letI := neZeroTwo
  letI := neZeroFour
  .mul (.atom 1 (PeriodicExpr.mask L (R.lower 0-2*r) (R.lower 0-r)
    (R.upper 0+r) (R.upper 0+2*r) (R.centerQ 0)))
  (.atom 2 (PeriodicExpr.cutoff L (R.lower 1-2*r) (R.lower 1-r)
    (R.upper 1+r) (R.upper 1+2*r)))

theorem planeMask_valid {L r : ℚ} (hL : 0<L) (hr : 0<r) (R : RationalBox 2) :
    (planeMask L R r).Valid :=
  ⟨PeriodicExpr.mask_valid hL (by linarith) (by linarith),
    PeriodicExpr.cutoff_valid hL (by linarith) (by linarith)⟩

theorem planeMask_val {L r : ℚ} (hL : 0<L) (hr : 0<r) (R : RationalBox 2) (y : SpaceTime) :
    (planeMask L R r).val y = planarMask L R r (horizontal y.2) := by
  simp only [planeMask,val,PeriodicExpr.mask_val hL (by linarith : R.lower 0-2*r<R.lower 0-r)
    (by linarith : R.upper 0+r<R.upper 0+2*r),PeriodicExpr.cutoff_val]
  change circleMask _ _ _ _ _ _ (y.2 0) * circleCutoff _ _ _ _ _ (y.2 1) = _
  simp [planarMask,RationalBox.centerQ_cast,horizontal]

end FieldExpr

namespace Input

def heightExpr (d : Input) (i : Fin d.instructions.length) : FieldExpr :=
  .atom 3 (PeriodicExpr.mask d.period (d.privateHeight i-2*d.heightRadius)
    (d.privateHeight i-d.heightRadius) (d.privateHeight i+d.heightRadius)
    (d.privateHeight i+2*d.heightRadius) (d.privateHeight i))

def horizontalExpr (d : Input) (i : Fin d.instructions.length) (j : Fin 2) : FieldExpr :=
  .atom j.castSucc.succ (PeriodicExpr.potential d.period
    (d.horizontalBox.lower j-2*d.horizontalRadius) (d.horizontalBox.lower j-d.horizontalRadius)
    (d.horizontalBox.upper j+d.horizontalRadius) (d.horizontalBox.upper j+2*d.horizontalRadius)
    ((d.sources i).centerQ j))

def sourceExpr (d : Input) (i : Fin d.instructions.length) : FieldExpr :=
  FieldExpr.planeMask d.period (d.sources i) d.sourceRadius

def targetExpr (d : Input) (i : Fin d.instructions.length) : FieldExpr :=
  FieldExpr.planeMask d.period (d.targets i) d.targetRadius

end Input

theorem heightExpr_valid {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    (d.heightExpr i).Valid := by
  have hr : 0<d.heightRadius := div_pos (heightSpacing_pos hd) (by norm_num)
  exact PeriodicExpr.mask_valid hd.period_pos (by linarith) (by linarith)

theorem heightExpr_val {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) (y : SpaceTime) :
    (d.heightExpr i).val y = d.heightMask i (y.2 2) := by
  have hr : 0<d.heightRadius := div_pos (heightSpacing_pos hd) (by norm_num)
  simp only [Input.heightExpr,FieldExpr.val,PeriodicExpr.mask_val hd.period_pos
    (by linarith : d.privateHeight i-2*d.heightRadius<d.privateHeight i-d.heightRadius)
    (by linarith : d.privateHeight i+d.heightRadius<d.privateHeight i+2*d.heightRadius)]
  change circleMask _ _ _ _ _ _ (y.2 2) = _
  simp [Input.heightMask]

theorem horizontalExpr_valid {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) (j : Fin 2) :
    (d.horizontalExpr i j).Valid := by
  have hr := horizontalRadius_pos hd
  exact PeriodicExpr.potential_valid hd.period_pos (by linarith) (by linarith)

theorem horizontalExpr_val (d : Input) (i : Fin d.instructions.length) (j : Fin 2) (y : SpaceTime) :
    (d.horizontalExpr i j).val y = d.horizontalProfile i j (y.2 j.castSucc) := by
  simp only [Input.horizontalExpr,FieldExpr.val,PeriodicExpr.potential_val,
    RationalBox.centerQ_cast,Input.horizontalProfile]
  congr 1
  push_cast
  rfl

theorem sourceExpr_valid {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    (d.sourceExpr i).Valid := FieldExpr.planeMask_valid hd.period_pos (sourceRadius_pos hd) _

theorem targetExpr_valid {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) :
    (d.targetExpr i).Valid := FieldExpr.planeMask_valid hd.period_pos (targetRadius_pos hd) _

theorem sourceExpr_val {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) (y : SpaceTime) :
    (d.sourceExpr i).val y = d.sourceMask i (horizontal y.2) :=
  FieldExpr.planeMask_val hd.period_pos (sourceRadius_pos hd) _ _

theorem targetExpr_val {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) (y : SpaceTime) :
    (d.targetExpr i).val y = d.targetMask i (horizontal y.2) :=
  FieldExpr.planeMask_val hd.period_pos (targetRadius_pos hd) _ _

namespace FieldExpr

def along (e : FieldExpr) (j : Fin 3) : VelocityExpr := fun k => if k = j then e else .const 0

theorem along_valid {e : FieldExpr} (he : e.Valid) (j : Fin 3) : (e.along j).Valid := by
  intro k
  dsimp [along]
  split_ifs
  · exact he
  · trivial

theorem along_val (e : FieldExpr) (j : Fin 3) (y : SpaceTime) :
    (e.along j).val y = e.val y • basis j := by
  ext k
  dsimp [along,VelocityExpr.val]
  split_ifs with h
  · subst k; simp [basis]
  · simp [val,basis,Pi.single_eq_of_ne h]

theorem sum_ofFn_val {n : ℕ} (e : Fin n → FieldExpr) (y : SpaceTime) :
    (sum (List.ofFn e)).val y = ∑ i, (e i).val y := by
  rw [val_sum,List.map_ofFn,List.sum_ofFn]
  rfl

theorem sum_ofFn_valid {n : ℕ} (e : Fin n → FieldExpr) (he : ∀ i, (e i).Valid) :
    (sum (List.ofFn e)).Valid := by
  apply valid_sum
  intro f hf
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
  exact he i

end FieldExpr

namespace Input

def branchExpr (d : Input) (i : Fin d.instructions.length) : Fin 7 → VelocityExpr :=
  letI := neZeroTwo
  letI := neZeroThree
  ![(FieldExpr.mul (.const (d.privateHeight i-d.codingHeight)) (d.sourceExpr i)).along 2,
    (FieldExpr.mul (.mul (.const (-(d.instructions.get i).factor)) (d.heightExpr i))
      (d.horizontalExpr i 0)).along 1,
    (FieldExpr.mul (.mul (.const ((d.instructions.get i).factor⁻¹-1)) (d.heightExpr i))
      (d.horizontalExpr i 1)).along 0,
    (FieldExpr.mul (d.heightExpr i) (d.horizontalExpr i 0)).along 1,
    (FieldExpr.mul (.mul (.const ((d.instructions.get i).factor-1)) (d.heightExpr i))
      (d.horizontalExpr i 1)).along 0,
    (fun k => .mul (d.heightExpr i) (.const
      (![ (d.targets i).centerQ 0-(d.sources i).centerQ 0,
          (d.targets i).centerQ 1-(d.sources i).centerQ 1, 0] k))),
    (FieldExpr.mul (.const (d.codingHeight-d.privateHeight i)) (d.targetExpr i)).along 2]

def spatialExpr (d : Input) (j : Fin 7) : VelocityExpr :=
  fun k => FieldExpr.sum (List.ofFn (fun i => d.branchExpr i j k))

def velocityExpr (d : Input) : VelocityExpr := fun k =>
  FieldExpr.sum (List.ofFn (fun j => .mul (.atom 0 (PeriodicExpr.pulse j)) (d.spatialExpr j k)))

end Input

theorem branchExpr_valid {d : Input} (hd : ValidInput d) (i : Fin d.instructions.length) (j : Fin 7) :
    (d.branchExpr i j).Valid := by
  have hs := sourceExpr_valid hd i
  have ht := targetExpr_valid hd i
  have hz := heightExpr_valid hd i
  have hx := horizontalExpr_valid hd i 0
  have hy := horizontalExpr_valid hd i 1
  fin_cases j <;> dsimp [Input.branchExpr]
  · apply FieldExpr.along_valid; exact ⟨trivial,hs⟩
  · apply FieldExpr.along_valid; exact ⟨⟨trivial,hz⟩,hx⟩
  · apply FieldExpr.along_valid; exact ⟨⟨trivial,hz⟩,hy⟩
  · apply FieldExpr.along_valid; exact ⟨hz,hx⟩
  · apply FieldExpr.along_valid; exact ⟨⟨trivial,hz⟩,hy⟩
  · intro k; exact ⟨hz,trivial⟩
  · apply FieldExpr.along_valid; exact ⟨trivial,ht⟩

theorem spatialExpr_valid {d : Input} (hd : ValidInput d) (j : Fin 7) :
    (d.spatialExpr j).Valid := fun k => FieldExpr.sum_ofFn_valid _ (fun i => branchExpr_valid hd i j k)

theorem velocityExpr_valid {d : Input} (hd : ValidInput d) : d.velocityExpr.Valid := by
  intro k
  apply FieldExpr.sum_ofFn_valid
  intro j
  exact ⟨PeriodicExpr.pulse_valid j, spatialExpr_valid hd j k⟩

theorem spatialExpr_val {d : Input} (hd : ValidInput d) (j : Fin 7) (y : SpaceTime) :
    (d.spatialExpr j).val y = d.spatialFields j y.2 := by
  ext k
  change (FieldExpr.sum _).val y = _
  rw [FieldExpr.sum_ofFn_val]
  fin_cases j <;> simp only [Input.spatialFields,sevenFields]
  all_goals
    simp only [Matrix.cons_val, Fin.reduceFinMk, Fin.isValue, Fin.zero_eta,
      transverseSum,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    fin_cases k <;>
      simp [Input.branchExpr, FieldExpr.along, FieldExpr.val, sourceExpr_val hd,
        targetExpr_val hd,heightExpr_val hd, horizontalExpr_val,
        selectTwo, horizontal, basis, atHeight, RationalBox.centerQ_cast]
  all_goals
    left
    congr 1
    ext k
    fin_cases k <;> rfl

theorem velocityExpr_val {d : Input} (hd : ValidInput d) : d.velocityExpr.val = d.realizingVelocity := by
  funext y k
  change (FieldExpr.sum _).val y = _
  rw [FieldExpr.sum_ofFn_val]
  simp only [FieldExpr.val,PeriodicExpr.pulse_val]
  change (∑ j, periodPulse j y.1 * (d.spatialExpr j).val y k) = _
  simp only [Input.realizingVelocity,pulsedSum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [spatialExpr_val hd]

end ShearFlows

end

end OAI
