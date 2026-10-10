import Mathlib.Data.List.FinRange
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion
open Construction

def sourceSampleEquiv {S T : PrimeSource} (h : S=T) : S.Sample ≃ T.Sample :=
  Equiv.cast (congrArg PrimeSource.Sample h)

@[simp] theorem sourceSampleEquiv_val {S T : PrimeSource} (h : S=T) (x : S.Sample) :
    (sourceSampleEquiv h x).val=x.val := by cases h; rfl

@[simp] theorem sourceSampleEquiv_mass {S T : PrimeSource} (h : S=T) (x : S.Sample) :
    T.law.mass (sourceSampleEquiv h x)=S.law.mass x := by cases h; rfl

def sourceAssignmentPermutation (sources : SourceFamily) (T : List SourceSlot)
    (σ : Equiv.Perm (Fin T.length))
    (hσ : ∀ i, sources T[σ i].origin = sources T[i].origin) :
    SourceAssignment sources T ≃ SourceAssignment sources T where
  toFun x i := sourceSampleEquiv (hσ i) (x (σ i))
  invFun x i := sourceSampleEquiv (by simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm i)).symm)
    (x (σ.symm i))
  left_inv x := by
    funext i
    apply Subtype.ext
    simp only [sourceSampleEquiv_val]
    exact congrArg (fun j => (x j).val) (σ.apply_symm_apply i)
  right_inv x := by
    funext i
    apply Subtype.ext
    simp only [sourceSampleEquiv_val]
    exact congrArg (fun j => (x j).val) (σ.symm_apply_apply i)

@[simp] theorem sourceAssignmentPermutation_val (sources : SourceFamily) (T : List SourceSlot)
    (σ : Equiv.Perm (Fin T.length)) (hσ) (x : SourceAssignment sources T) (i) :
    (sourceAssignmentPermutation sources T σ hσ x i).val = (x (σ i)).val :=
  sourceSampleEquiv_val (hσ i) (x (σ i))

theorem sourceAssignmentPermutation_mass (sources : SourceFamily) (T : List SourceSlot)
    (σ : Equiv.Perm (Fin T.length)) (hσ) (x : SourceAssignment sources T) :
    (assignmentPrior sources T).mass (sourceAssignmentPermutation sources T σ hσ x) =
      (assignmentPrior sources T).mass x := by
  change (∏ i : Fin T.length, (sources T[i].origin).law.mass
    (sourceSampleEquiv (hσ i) (x (σ i)))) = ∏ i, (sources T[i].origin).law.mass (x i)
  simp only [sourceSampleEquiv_mass]
  exact Equiv.prod_comp σ (fun i => (sources T[i].origin).law.mass (x i))

theorem sourceAssignmentPermutation_values (sources : SourceFamily) (T : List SourceSlot)
    (σ : Equiv.Perm (Fin T.length)) (hσ) (x : SourceAssignment sources T) :
    ((assignedSlots sources T (sourceAssignmentPermutation sources T σ hσ x)).map SmallSlot.value).Perm
      ((assignedSlots sources T x).map SmallSlot.value) := by
  simpa only [assignedSlots,Template.sample,List.map_ofFn,sourceAssignmentPermutation_val,Function.comp_def]
    using σ.ofFn_comp_perm (fun i => (x i).val)

theorem regularTransform_values_perm (g giant : (p : ℕ) → ZMod p → ℂ)
    (outside : List ℕ) {a b : State} (hf : a.frequency=b.frequency)
    (hp : a.giantPlus=b.giantPlus) (hm : a.giantMinus=b.giantMinus)
    (hs : (a.small.map SmallSlot.value).Perm (b.small.map SmallSlot.value)) :
    regularTransform g giant outside a = regularTransform g giant outside b := by
  have hprod : a.product=b.product := by
    simp only [State.product,State.values,List.prod_cons]
    rw [hp,hm,hs.prod_eq]
  simp only [regularTransform]
  rw [hf,hp,hm,hprod]
  have h := hs.map (fun q => g q (modFraction q b.frequency (outsideProduct outside*(b.product/q))))
  simpa only [List.map_map,Function.comp_def] using congrArg
    (fun z => giant b.giantPlus (modFraction b.giantPlus b.frequency (outsideProduct outside*(b.product/b.giantPlus))) *
      giant b.giantMinus (modFraction b.giantMinus b.frequency (outsideProduct outside*(b.product/b.giantMinus))) * z)
    h.prod_eq

theorem regularTransform_sourceAssignmentPermutation (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (σ : Equiv.Perm (Fin T.length)) (hσ)
    (g giantTransform : (p : ℕ) → ZMod p → ℂ) (outside : List ℕ)
    (p q : giant.Sample) (x : SourceAssignment sources T) (s : ℤ) :
    regularTransform g giantTransform outside
      (outerState sources T giant (p,q,sourceAssignmentPermutation sources T σ hσ x) s) =
    regularTransform g giantTransform outside (outerState sources T giant (p,q,x) s) :=
  regularTransform_values_perm g giantTransform outside rfl rfl rfl
    (sourceAssignmentPermutation_values sources T σ hσ x)

end Ostmann.Conclusion

end

end OAI
