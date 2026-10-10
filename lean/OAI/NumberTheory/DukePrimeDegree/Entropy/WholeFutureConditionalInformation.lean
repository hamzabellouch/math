import OAI.NumberTheory.DukePrimeDegree.Entropy.SelfConditionalKernel
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalInformation
import OAI.NumberTheory.DukePrimeDegree.Entropy.RemainingFutureInformation
import OAI.NumberTheory.DukePrimeDegree.Geometry.NormalizedRestrictionLimit

namespace OAI

/-! # Actual conditional information of the whole-future root kernel -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem selfConstant_kernel_conditionalInformation
    {Y α : Type*} [MeasurableSpace Y] [Countable α]
    (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : Kernel Y Y) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (P : Y → α) (hP : ∀ a, MeasurableSet {y | P y=a}) :
    conditionalInformation μ P (MeasurableSpace.comap κ inferInstance) =ᵐ[μ]
      fun x => -Real.log ((κ x).real {y | P y=P x}) := by
  filter_upwards [ae_all_iff.mpr (fun a =>
    selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hP a))] with x hx
  exact congrArg (-Real.log ·) (hx (P x)).symm

namespace EliminationChain

lemma remainingFutureAtom_present_inter_one
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (x : X n) :
    {u | Q (rightAction x (c.word u))=Q x} ∩ c.remainingFutureAtom ell hell Q 1 x =
      c.remainingFutureAtom ell hell Q 0 x := by
  ext u
  constructor
  · rintro ⟨hzero,hpos⟩ k
    cases k with
    | zero => simpa only [Set.mem_ofPred_eq,Nat.zero_add,Function.iterate_zero,Function.id_def] using hzero
    | succ k => simpa only [Nat.add_zero,Nat.succ_eq_add_one] using hpos k
  · intro h
    refine ⟨?_,c.remainingFutureAtom_zero_subset_one ell hell Q x h⟩
    simpa only [Set.mem_ofPred_eq,Nat.zero_add,Function.iterate_zero,Function.id_def] using h 0

theorem wholeFuture_conditionalInformation
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u))) :
    conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) =ᵐ[μ]
      fun x => -Real.log
        (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
          c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 1 x)).toReal := by
  have H := selfConstant_kernel_conditionalInformation μ κ hstat hself Q
    (fun a => hQ (measurableSet_singleton a))
  filter_upwards [H,hversion] with x hx hv
  rw [hx,hv]
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hA : MeasurableSet {y : X (d+1) | Q y=Q x} := hQ (measurableSet_singleton _)
  apply congrArg (-Real.log ·)
  rw [Measure.real,Measure.map_apply hF hA]
  change ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
      (c.remainingFutureAtom ell hell Q 1 x)).restrict
      (c.remainingFutureAtom ell hell Q 1 x)).real
      {u | Q (rightAction x (c.word u))=Q x} = _
  rw [normalized_restriction_real _ _ {u | Q (rightAction x (c.word u))=Q x} (hA.preimage hF),
    c.remainingFutureAtom_present_inter_one ell hell Q x,ENNReal.toReal_div]
  rfl

theorem wholeFuture_conditionalInformation_integrable_integral
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (hversion : ∀ᵐ x ∂μ, κ x=
      ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
        (c.remainingFutureAtom ell hell Q 1 x)).restrict
        (c.remainingFutureAtom ell hell Q 1 x)).map
        (fun u => rightAction x (c.word u)))
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1) :
    Integrable (conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance)) μ ∧
      (∫ x, conditionalInformation μ Q (MeasurableSpace.comap κ inferInstance) x ∂μ) =
        ∑ p : ↥(allPositiveRoots (d+1) \ P),
          (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  have he := c.wholeFuture_conditionalInformation d hP hf μ ell hell Q hQ κ hstat hself hversion
  have H := c.remainingFutureInformation_integrable_integral d hP hf μ hA ell hell Q hQ hmass
  exact ⟨H.1.congr he.symm,(integral_congr_ae he).trans H.2⟩

end EliminationChain
end DukePrimeDegree

end

end OAI
