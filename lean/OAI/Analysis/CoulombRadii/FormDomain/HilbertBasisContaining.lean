import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.OrbitalHilbertBasis

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

lemma exists_hilbertBasis_containing {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (v : E) (hv : ‖v‖ = 1) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (i : w), b i = v ∧ ⇑b = Subtype.val := by
  have ho : Orthonormal ℂ ((↑) : ({v} : Set E) → E) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : E) = v := Set.mem_singleton_iff.mp i.property
    have hj : (j : E) = v := Set.mem_singleton_iff.mp j.property
    have he : i = j := Subtype.ext (hi.trans hj.symm)
    simp [he, hj, inner_self_eq_norm_sq_to_K, hv]
  obtain ⟨w, b, hw, hb⟩ := ho.exists_hilbertBasis_extension
  exact ⟨w, b, ⟨v, hw (Set.mem_singleton v)⟩, congrFun hb _, hb⟩

lemma scalarCoefficient_contract {A ι : Type*} [MeasurableSpace A]
    {μ : Measure A} [SigmaFinite μ] {n : ℕ}
    (f : (Fin (n+1) → A) → ℂ) (hf : MemLp f 2 (Measure.pi fun _ => μ))
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ) (a : ι) (b : Fin n → ι) :
    scalarCoefficient (μ := μ) f v (Fin.cons a b) =
      scalarCoefficient (μ := μ)
        (fiberContract (μ := μ) (v a) (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1))) v b := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).trans
    (MeasurableEquiv.prodComm : A × (Fin n → A) ≃ᵐ (Fin n → A) × A)
  have he : MeasurePreserving e (Measure.pi fun _ => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    (measurePreserving_piFinSuccAbove (fun _ => μ) 0).trans (Measure.measurePreserving_swap)
  have hcons : ∀ z : (Fin n → A) × A, e.symm z = Fin.cons z.2 z.1 := by
    intro z
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
    · simp [e, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]
  have hf' : MemLp (fun z : (Fin n → A) × A => f (Fin.cons z.2 z.1)) 2
      ((Measure.pi fun _ : Fin n => μ).prod μ) := by
    simpa only [Function.comp_def, hcons] using hf.comp_measurePreserving (he.symm e)
  unfold scalarCoefficient
  rw [← (he.symm e).integral_comp']
  simp only [hcons]
  have hprod (z : (Fin n → A) × A) :
      (∏ i : Fin (n+1), v ((Fin.cons a b : Fin (n+1) → ι) i)
        ((Fin.cons z.2 z.1 : Fin (n+1) → A) i)) =
        (∏ i : Fin n, v (b i) (z.1 i)) * v a z.2 := by
    rw [Fin.prod_univ_succ]
    simp [mul_comm]
  simp only [hprod]
  exact integral_tensorPair (scalarTensor_memLp v hv b) (hv a) hf'

end Coulomb

end
end

end OAI
