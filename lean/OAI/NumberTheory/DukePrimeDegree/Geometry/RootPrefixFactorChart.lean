import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFactorTransversal

namespace OAI

/-! # Actual one-root transversals inside every remaining-group chart -/

noncomputable section
open Matrix Set
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

namespace RootPrefixCoordinates
variable {n : ℕ} (s : InitialRootStep n) {T : Type*} [TopologicalSpace T]
  (C : RootPrefixCoordinates n s.processed T) (g : G n)

abbrev FactorTransverse :=
  (UpperRootTransverse n × T) × positiveRootGeneratedGroup (s.remaining.erase s.root)

def factorBase (z : FactorTransverse s (T := T)) : G n :=
  g * (z.1.1.val * (C.base z.1.2 * z.2.val))

def factorParam (z : FactorTransverse s (T := T) × ℝ) : G n :=
  C.factorBase s g z.1 * Matrix.SpecialLinearGroup.transvection s.distinct z.2

theorem factorParam_isOpenEmbedding : Topology.IsOpenEmbedding (C.factorParam s g) := by
  have herase : ∀ a b c : Fin n, (a,b) ∈ s.remaining.erase s.root →
      (b,c) ∈ s.remaining.erase s.root → (a,c) ∈ s.remaining.erase s.root := by
    dsimp only [InitialRootStep.remaining]
    rw [initialRemaining_erase]
    exact initialRemaining_roots_closed _ (initialRootPattern_insert_min s.initial s.root
      s.mem_remaining s.least)
  let F := positiveRootRightFactorHomeomorph s.remaining s.remaining_positive s.remaining_closed
    s.distinct s.mem_remaining herase
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n × T) _ ℝ).trans
    (((Homeomorph.refl (UpperRootTransverse n × T)).prodCongr F).trans
      (Homeomorph.prodAssoc (UpperRootTransverse n) T _))
  have H := (Homeomorph.mulLeft g).isOpenEmbedding.comp (C.groupParam_isOpenEmbedding.comp E.isOpenEmbedding)
  convert H using 1
  funext z
  change C.factorBase s g z.1 * Matrix.SpecialLinearGroup.transvection s.distinct z.2 =
    g * C.groupParam (z.1.1.1,(z.1.1.2,F (z.1.2,z.2)))
  rw [C.groupParam_eq_mul]
  change (g * (z.1.1.1.val * (C.base z.1.1.2 * z.1.2.val))) *
    Matrix.SpecialLinearGroup.transvection s.distinct z.2 =
      g * (z.1.1.1.val * (C.base z.1.1.2 *
        (z.1.2.val * Matrix.SpecialLinearGroup.transvection s.distinct z.2)))
  simp only [mul_assoc]

lemma continuous_factorBase : Continuous (C.factorBase s g) := by
  have H := (C.factorParam_isOpenEmbedding s g).continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : FactorTransverse s (T := T) => (0:ℝ))))
  simpa only [Function.comp_def, id_eq, factorParam, Matrix.SpecialLinearGroup.transvection_coeff_zero,
    mul_one] using H

def factorPivotDomain (k : Fin n) : Set (FactorTransverse s (T := T)) :=
  {z | (C.factorBase s g z).val k s.root.1 ≠ 0}

lemma factorPivotDomain_open (k : Fin n) : IsOpen (C.factorPivotDomain s g k) :=
  (rootPivot_isOpen s.root.1 k).preimage (C.continuous_factorBase s g)

def factorPivot (k : Fin n) (z : C.factorPivotDomain s g k) : RootPivot s.root.1 k :=
  ⟨C.factorBase s g z.val,z.prop⟩

def factorSlice (k : Fin n) (z : C.factorPivotDomain s g k) : RootSlice s.root.1 s.root.2 k :=
  rootSliceRepresentative s.distinct (C.factorPivot s g k z)

theorem factorSlice_isOpenEmbedding (k : Fin n) :
    Topology.IsOpenEmbedding (C.factorSlice s g k) := by
  have hf : Continuous (C.factorPivot s g k) :=
    ((C.continuous_factorBase s g).comp continuous_subtype_val).subtype_mk _
  apply root_transversal_isOpenEmbedding s.distinct _ hf
  let f := fun z : C.factorPivotDomain s g k × ℝ =>
    rootPivotTranslate s.distinct (C.factorPivot s g k z.1) z.2
  have H := (C.factorParam_isOpenEmbedding s g).comp
    ((C.factorPivotDomain_open s g k).isOpenEmbedding_subtypeVal.prodMap
      (Topology.IsOpenEmbedding.id (X := ℝ)))
  exact Topology.IsOpenEmbedding.of_comp f (rootPivot_isOpen s.root.1 k).isOpenEmbedding_subtypeVal H

lemma factorSlice_param (k : Fin n) (z : C.factorPivotDomain s g k) (t : ℝ) :
    rootQuotientParametrization s.distinct (C.factorSlice s g k z,t) =
      Quotient.mk _ (C.factorBase s g z.val * Matrix.SpecialLinearGroup.transvection s.distinct
        (t - rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) := by
  change Quotient.mk _ ((C.factorBase s g z.val *
    Matrix.SpecialLinearGroup.transvection s.distinct
      (-rootParameter s.root.1 s.root.2 k (C.factorBase s g z.val))) *
      Matrix.SpecialLinearGroup.transvection s.distinct t) = _
  rw [mul_assoc, ← Matrix.SpecialLinearGroup.transvection_add]
  congr 3
  ring

end RootPrefixCoordinates
end DukePrimeDegree

end

end OAI
