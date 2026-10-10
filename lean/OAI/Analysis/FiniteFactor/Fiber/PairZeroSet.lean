import OAI.Analysis.FiniteFactor.Fiber.Diagonal
import OAI.Analysis.FiniteFactor.CrossedProduct.FiberSeparable

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The actual bounded operator whose vanishing is the pair identity. -/
def fiberPairResidual {X : Type*}
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1) (z : X × X) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  (1 - P z.2) * fiberDiagonal (d z) (hd z) * P z.1

theorem fiberPairResidual_eq_zero_iff {X : Type*}
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1) (z : X × X) :
    fiberPairResidual P d hd z = 0 ↔
      ∀ k : ℤ, fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0 := by
  constructor
  · intro h k; rw [h]; rfl
  · intro h
    apply fiberOperator_ext
    intro k n
    rw [h n]
    rfl

theorem fiberPairResidual_continuousOn {X : Type*} [TopologicalSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) (v : SourceFiberHilbert) :
    ContinuousOn (fun z => fiberPairResidual P d hd z v) (Q ×ˢ Q) := by
  have hPs (w : SourceFiberHilbert) := fiberField_continuousOn P Q C hC hP w
  have hx (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.1 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hy (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.2 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hD (w : SourceFiberHilbert) := fiberDiagonal_continuousOn d hd (Q ×ˢ Q) hdc w
  have hv := fiberField_continuousOn_apply (fun z => fiberDiagonal (d z) (hd z))
    (Q ×ˢ Q) 1 (fun z _ => fiberDiagonal_norm _ _) hD (fun z => P z.1 v) (hx v)
  have hpv := fiberField_continuousOn_apply (fun z : X × X => P z.2)
    (Q ×ˢ Q) C (fun z hz => hC z.2 hz.2) hy _ hv
  exact hv.sub hpv

theorem fiberPairResidual_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => fiberPairResidual P d hd z v) := by
  have hv := fiberField_stronglyMeasurable_apply (fun z => fiberDiagonal (d z) (hd z))
    (fun w => fiberDiagonal_stronglyMeasurable d hd hdm w)
    (fun z => P z.1 v) ((hP v).comp_measurable measurable_fst)
  have hpv := fiberField_stronglyMeasurable_apply (fun z : X × X => P z.2)
    (fun w => (hP w).comp_measurable measurable_snd) _ hv
  exact hv.sub hpv

theorem fiberPairZeroSet_measurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) :
    MeasurableSet {z | fiberPairResidual P d hd z = 0} := by
  borelize (↥SourceFiberHilbert)
  simp_rw [fiberPairResidual_eq_zero_iff, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => measurableSet_eq_fun
    (fiberPairResidual_stronglyMeasurable P d hd hP hdm _).measurable measurable_const)

theorem fiberPairZeroSet_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (hQ : IsCompact Q) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) :
    IsCompact ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) := by
  have he : ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) =
      ⋂ k : ℤ, ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      fiberPairResidual_eq_zero_iff]
    constructor
    · rintro ⟨hz,h⟩ k; exact ⟨hz,h k⟩
    · intro h; exact ⟨(h 0).1,fun k => (h k).2⟩
  apply (hQ.prod hQ).of_isClosed_subset _ Set.inter_subset_left
  rw [he]
  apply isClosed_iInter
  intro k
  exact (fiberPairResidual_continuousOn P d hd Q C hC hP hdc _).preimage_isClosed_of_isClosed
    (hQ.prod hQ).isClosed isClosed_singleton

end
end FiniteFactor

end OAI
