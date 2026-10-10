import OAI.Dynamics.StandardMap.TorusIntegral

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def torusStep (k : ℝ) : Equiv.Perm Torus where
  toFun := recurrenceMap k
  invFun z := (z.2,2 • z.2+kick k z.2-z.1)
  left_inv := by intro z; ext <;> simp [recurrenceMap]
  right_inv := by intro z; ext <;> simp [recurrenceMap]
@[simp] lemma torusStep_apply (k : ℝ) (z : Torus) : torusStep k z=recurrenceMap k z := rfl
@[simp] lemma torusStep_symm_apply (k : ℝ) (z : Torus) :
    (torusStep k).symm z=(z.2,2 • z.2+kick k z.2-z.1) := rfl
lemma continuous_torusStep (k : ℝ) : Continuous (torusStep k) :=
  (((continuous_fst.nsmul 2).add ((continuous_kick k).comp continuous_fst)).sub continuous_snd).prodMk continuous_fst
lemma continuous_torusStep_symm (k : ℝ) : Continuous (torusStep k).symm :=
  continuous_snd.prodMk (((continuous_snd.nsmul 2).add ((continuous_kick k).comp continuous_snd)).sub continuous_fst)
lemma measurePreserving_recurrenceCoordinates : MeasurePreserving recurrenceCoordinates area area := by
  unfold area
  apply (MeasurePreserving.id (volume : Measure Circle)).skew_product
  · exact measurable_fst.sub measurable_snd
  · exact Eventually.of_forall fun x => (Measure.measurePreserving_sub_left (volume : Measure Circle) x).map_eq
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
noncomputable def torusStep_measurableEquiv (k : ℝ) : MeasurableEquiv Torus Torus where
  toEquiv := torusStep k
  measurable_toFun := (continuous_torusStep k).measurable
  measurable_invFun := (continuous_torusStep_symm k).measurable
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
noncomputable def torusIter (k : ℝ) (i : ℤ) : Torus → Torus := ((torusStep k)^i : Equiv.Perm Torus)
lemma torusIter_add (k : ℝ) (i j : ℤ) (z : Torus) :
    torusIter k (i+j) z=torusIter k i (torusIter k j z) := by
  simp only [torusIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
@[simp] lemma torusIter_zero (k : ℝ) (z : Torus) : torusIter k 0 z=z := by simp [torusIter]
lemma continuous_torusIter (k : ℝ) (i : ℤ) : Continuous (torusIter k i) := by
  cases i with
  | ofNat n =>
      change Continuous (torusIter k (n : ℤ))
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (continuous_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (continuous_torusStep_symm k).iterate (n+1)
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
lemma coe_phi (k x : ℝ) : (phi k x : Circle)=2 • (x : Circle)+kick k (x : Circle) := by
  simp only [phi,kick,sine_coe,AddCircle.coe_add]
  rw [two_mul,two_smul,AddCircle.coe_add]
lemma liftProjection_step (k : ℝ) (z : ℝ × ℝ) :
    liftProjection (liftStep k z)=torusStep k (liftProjection z) := by
  apply Prod.ext
  · change ((phi k z.1-z.2 : ℝ) : Circle)=_
    rw [AddCircle.coe_sub,coe_phi]
    rfl
  · rfl
lemma liftProjection_step_symm (k : ℝ) (z : ℝ × ℝ) :
    liftProjection ((liftStep k).symm z)=(torusStep k).symm (liftProjection z) := by
  apply (torusStep k).injective
  rw [Equiv.apply_symm_apply,← liftProjection_step,Equiv.apply_symm_apply]
lemma liftProjection_iter (k : ℝ) (i : ℤ) (z : ℝ × ℝ) :
    liftProjection (liftIter k i z)=torusIter k i (liftProjection z) := by
  have hf : Function.Semiconj liftProjection (liftStep k) (torusStep k) := liftProjection_step k
  have hb : Function.Semiconj liftProjection (liftStep k).symm (torusStep k).symm := liftProjection_step_symm k
  cases i with
  | ofNat n =>
      change liftProjection (liftIter k (n : ℤ) z)=torusIter k (n : ℤ) (liftProjection z)
      simpa only [liftIter,torusIter,zpow_natCast,Equiv.Perm.coe_pow] using hf.iterate_right n z
  | negSucc n => simpa only [liftIter,torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using hb.iterate_right (n+1) z
lemma liftProjection_surjective : Function.Surjective liftProjection := by
  intro z
  obtain ⟨x,hx⟩ := Quotient.mk_surjective z.1
  obtain ⟨y,hy⟩ := Quotient.mk_surjective z.2
  exact ⟨(x,y),Prod.ext hx hy⟩
end StandardMapEntropy

end OAI
