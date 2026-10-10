import OAI.NumberTheory.DukePrimeDegree.Entropy.WeylEntropy
import OAI.NumberTheory.DukePrimeDegree.Geometry.RootAtomicTransversal

namespace OAI

/-! # Coordinate permutations transport atomic intrinsic root leaves -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

lemma reindex_transvection {n : ℕ} (e : Equiv.Perm (Fin n))
    {i j : Fin n} (hij : i ≠ j) (t : ℝ) :
    reindexSpecialLinear ℝ e (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t := by
  apply Subtype.ext
  ext a b
  change ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single i j t) (e.symm a) (e.symm b) =
    ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.single (e i) (e j) t) a b
  simp only [Matrix.add_apply,Matrix.one_apply,Matrix.single_apply,
    e.symm.injective.eq_iff,e.eq_symm_apply]

/-- Only the geometric characterization of an atomic leaf is needed;
there is no assumed covariance formula for arbitrary intrinsic leaves. -/
theorem atomic_root_reindex (d : ℕ) (e : Equiv.Perm (Fin (d+1)))
    {i j : Fin (d+1)} (hij : i ≠ j)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hatom : ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x=Measure.dirac 0) :
    ∀ᵐ x ∂μ.map (quotientReindex e),
      intrinsicRootLeaf (e.injective.ne hij) (μ.map (quotientReindex e)) x=Measure.dirac 0 := by
  let E := (quotientReindexHomeomorph e).toMeasurableEquiv
  obtain ⟨N,hN,hN0,htrans⟩ := exists_nullset_atomic_root_transversal d hij μ hA hatom
  have hfree : ∀ᵐ y ∂μ.map E, ∀ t : ℝ,
      rightAction y (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t)=y → t=0 := by
    rw [←E.map_ae μ]
    change ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction (E x) (Matrix.SpecialLinearGroup.transvection (e.injective.ne hij) t)=E x → t=0
    filter_upwards [(ae_root_stabilizer_trivial d μ hA).mono
      (fun x hx => hx i j hij)] with x hx
    intro t ht
    apply hx t
    apply E.injective
    change quotientReindex e (rightAction x _) = quotientReindex e x
    rw [quotientReindex_rightAction,reindex_transvection]
    exact ht
  have hN' : (μ.map E) (E '' N)=0 := by
    rw [E.map_apply,E.injective.preimage_image,hN0]
  apply intrinsicRootLeaf_dirac_of_nullset_transversal (e.injective.ne hij) (μ.map E)
    hfree (E '' N) hN'
  intro y hy t ht
  obtain ⟨x,rfl⟩ := E.surjective y
  apply htrans x
  · exact fun hx => hy ⟨x,hx,rfl⟩
  · intro hx
    apply ht
    refine ⟨rightAction x (Matrix.SpecialLinearGroup.transvection hij t),hx,?_⟩
    exact (quotientReindex_rightAction e x _).trans
      (congrArg (rightAction (quotientReindex e x)) (reindex_transvection e hij t))

end DukePrimeDegree

end

end OAI
