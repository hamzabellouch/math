import OAI.Dynamics.StandardMap.FourPoint

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
noncomputable def transferStepEquiv (v : ℝ) : ℂ ≃L[ℝ] ℂ :=
  { toLinearEquiv :=
      { toLinearMap := (transferStep v).toLinearMap
        invFun := transferStepInv v
        left_inv := transferStepInv_inv v
        right_inv := transferStep_inv v }
    continuous_toFun := (transferStep v).continuous
    continuous_invFun := (transferStepInv v).continuous }
@[simp] lemma transferStepEquiv_apply (v : ℝ) (u : ℂ) : transferStepEquiv v u=transferStep v u := rfl
@[simp] lemma transferStepEquiv_symm_apply (v : ℝ) (u : ℂ) : (transferStepEquiv v).symm u=transferStepInv v u := rfl
noncomputable def positivePrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℕ → (ℂ ≃L[ℝ] ℂ)
  | 0 => ContinuousLinearEquiv.refl ℝ ℂ
  | n+1 => (positivePrefix G n).trans (G (n:ℤ))
noncomputable def negativePrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℕ → (ℂ ≃L[ℝ] ℂ)
  | 0 => ContinuousLinearEquiv.refl ℝ ℂ
  | n+1 => (negativePrefix G n).trans (G (-((n:ℤ)+1))).symm
noncomputable def integerPrefix (G : ℤ → (ℂ ≃L[ℝ] ℂ)) : ℤ → (ℂ ≃L[ℝ] ℂ)
  | .ofNat n => positivePrefix G n
  | .negSucc n => negativePrefix G (n+1)
@[simp] lemma integerPrefix_nat (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (n : ℕ) : integerPrefix G (n:ℤ)=positivePrefix G n := rfl
@[simp] lemma integerPrefix_neg_nat (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (n : ℕ) : integerPrefix G (-(n:ℤ))=negativePrefix G n := by
  cases n <;> rfl
lemma integerPrefix_step (G : ℤ → (ℂ ≃L[ℝ] ℂ)) (i : ℤ) (u : ℂ) :
    integerPrefix G (i+1) u=G i (integerPrefix G i u) := by
  cases i with
  | ofNat n => rfl
  | negSucc n =>
    change integerPrefix G (-((n:ℤ)+1)+1) u=G (-((n:ℤ)+1)) (negativePrefix G (n+1) u)
    rw [show -((n:ℤ)+1)+1=-(n:ℤ) by ring,integerPrefix_neg_nat]
    simp only [negativePrefix,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.apply_symm_apply]
lemma equiv_area_symm (A : ℂ ≃L[ℝ] ℂ) (hA : PlaneAreaPreserving A.toContinuousLinearMap) :
    PlaneAreaPreserving A.symm.toContinuousLinearMap := by
  intro u v
  have h := hA (A.symm u) (A.symm v)
  simpa using h.symm
lemma equiv_area_trans (A B : ℂ ≃L[ℝ] ℂ)
    (hA : PlaneAreaPreserving A.toContinuousLinearMap) (hB : PlaneAreaPreserving B.toContinuousLinearMap) :
    PlaneAreaPreserving (A.trans B).toContinuousLinearMap := by
  intro u v
  exact (hB (A u) (A v)).trans (hA u v)
lemma integerPrefix_area (G : ℤ → (ℂ ≃L[ℝ] ℂ))
    (hG : ∀ i, PlaneAreaPreserving (G i).toContinuousLinearMap) (i : ℤ) :
    PlaneAreaPreserving (integerPrefix G i).toContinuousLinearMap := by
  have hp : ∀ n, PlaneAreaPreserving (positivePrefix G n).toContinuousLinearMap := by
    intro n
    induction n with
    | zero => exact fun _ _ => rfl
    | succ n ih => exact equiv_area_trans _ _ ih (hG _)
  have hm : ∀ n, PlaneAreaPreserving (negativePrefix G n).toContinuousLinearMap := by
    intro n
    induction n with
    | zero => exact fun _ _ => rfl
    | succ n ih => exact equiv_area_trans _ _ ih (equiv_area_symm _ (hG _))
  cases i with
  | ofNat n => exact hp n
  | negSucc n => exact hm (n+1)
noncomputable def torusPrefix (k : ℝ) (z : Torus) (i : ℤ) : ℂ ≃L[ℝ] ℂ :=
  integerPrefix (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1)) i
noncomputable def torusTransfer (k : ℝ) (z : Torus) (i j : ℤ) : ℂ ≃L[ℝ] ℂ :=
  (torusPrefix k z i).symm.trans (torusPrefix k z j)
lemma torusTransfer_apply (k : ℝ) (z : Torus) (i j : ℤ) (u : ℂ) :
    torusTransfer k z i j u=torusPrefix k z j ((torusPrefix k z i).symm u) := rfl
lemma torusTransfer_comp (k : ℝ) (z : Torus) (i j l : ℤ) (u : ℂ) :
    torusTransfer k z j l (torusTransfer k z i j u)=torusTransfer k z i l u := by
  simp only [torusTransfer_apply,ContinuousLinearEquiv.symm_apply_apply]
lemma torusTransfer_self (k : ℝ) (z : Torus) (i : ℤ) :
    (torusTransfer k z i i).toContinuousLinearMap=ContinuousLinearMap.id ℝ ℂ := by
  ext u
  exact ContinuousLinearEquiv.apply_symm_apply _ _
lemma torusTransfer_area (k : ℝ) (z : Torus) (i j : ℤ) :
    PlaneAreaPreserving (torusTransfer k z i j).toContinuousLinearMap := by
  apply equiv_area_trans
  · apply equiv_area_symm
    exact integerPrefix_area (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1))
      (fun a => transferStep_area _) i
  · exact integerPrefix_area (fun a => transferStepEquiv (torusPotential k (torusIter k a z).1))
      (fun a => transferStep_area _) j
lemma torusTransfer_forward (k : ℝ) (z : Torus) (a : ℤ) (n : ℕ) :
    (torusTransfer k z a (a+(n:ℤ))).toContinuousLinearMap=torusSegmentTransfer k z a n := by
  induction n with
  | zero => simpa only [Nat.cast_zero,add_zero,torusSegmentTransfer,transferProduct] using torusTransfer_self k z a
  | succ n ih =>
    ext u
    change torusPrefix k z (a+((n+1:ℕ):ℤ)) ((torusPrefix k z a).symm u)=_
    rw [show a+((n+1:ℕ):ℤ)=(a+(n:ℤ))+1 by omega]
    change integerPrefix _ ((a+(n:ℤ))+1) _=_
    rw [integerPrefix_step]
    change transferStep (torusPotential k (torusIter k (a+(n:ℤ)) z).1)
      ((torusTransfer k z a (a+(n:ℤ))).toContinuousLinearMap u)=_
    rw [ih]
    simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_apply,torusSegmentCoefficient]
    congr 1
    exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
end StandardMapEntropy

end OAI
