import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalFiberRecoding

namespace OAI

/-! # Finite predecessor words control clipped countable words -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

theorem conditionalSigmaEntropy_le_of_fiber_refinement
    {Y S α β : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace S] [MeasurableEq S]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [Nonempty α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Fintype β]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (F : Y → S) (hF : Measurable F)
    (P : Y → α) (hP : Measurable P) (B : Y → β) (hB : Measurable B)
    (href : ∀ x y, F x=F y → B x=B y → P x=P y) :
    conditionalSigmaEntropy μ P (MeasurableSpace.comap F inferInstance) ≤
      conditionalSigmaEntropy μ B (MeasurableSpace.comap F inferInstance) := by
  classical
  let f : S → β → α := fun s b =>
    if h : ∃ x, F x=s ∧ B x=b then P h.choose else Classical.choice inferInstance
  apply conditionalSigmaEntropy_le_fiber_recoding μ F hF P hP B hB f
  intro x
  have hx : ∃ y, F y=F x ∧ B y=B x := ⟨x,rfl,rfl⟩
  dsimp only [f]
  rw [dite_eq_left hx]
  exact href x hx.choose hx.choose_spec.1.symm hx.choose_spec.2.symm

theorem predecessor_clippedWord_conditionalEntropy_le
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (T : Y → Y) (hT : Measurable T) (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin M) (hB : Measurable B)
    (decode : ℕ → Fin M → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N L : ℕ) :
    conditionalSigmaEntropy μ (orbitName T (heightClip Q L) N)
      (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) ≤
      conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) := by
  have hPN : Measurable (orbitName T (heightClip Q L) N) :=
    measurable_pi_iff.mpr fun i => (heightClip_measurable hQ L).comp (hT.iterate i.val)
  have hBN : Measurable (orbitName T B N) :=
    measurable_pi_iff.mpr fun i => hB.comp (hT.iterate i.val)
  apply conditionalSigmaEntropy_le_of_fiber_refinement μ (Q ∘ T^[N])
    (hQ.comp (hT.iterate N)) _ hPN _ hBN
  intro x y hterm hword
  have heq := predecessor_word_recovers T Q B decode hdecode hterm
    (fun k hk => congrFun hword ⟨k,hk⟩)
  funext i
  change heightClip Q L (T^[i.val] x)=heightClip Q L (T^[i.val] y)
  apply Fin.ext
  change min (Q (T^[i.val] x)) L=min (Q (T^[i.val] y)) L
  rw [heq i.val i.isLt.le]

end DukePrimeDegree

end

end OAI
