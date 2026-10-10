import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureKernelCovariance
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureConditionalInformation

namespace OAI

/-! # Information of finite words against delayed future kernels -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets
namespace EliminationChain

lemma remainingFutureAtom_word_inter
    {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    (c : EliminationChain P D) (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (N : ℕ) (x : X n) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} ∩
      c.remainingFutureAtom ell hell Q N x = c.remainingFutureAtom ell hell Q 0 x := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  ext u
  constructor
  · rintro ⟨hword,hfuture⟩ k
    by_cases hk : k<N
    · exact congrFun hword ⟨k,hk⟩
    · have hkN : N≤k := Nat.le_of_not_gt hk
      have h := hfuture (k-N)
      simpa only [Nat.sub_add_cancel hkN,Nat.add_zero] using h
  · intro h
    refine ⟨?_,?_⟩
    · funext k
      exact h k.val
    · intro k
      exact h (k+N)

theorem futureBlock_conditionalProbability
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (N : ℕ)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q N x) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    (fun x => (μ[({y | orbitName T Q N y=orbitName T Q N x}.indicator
      (fun _ => (1 : ℝ))) | MeasurableSpace.comap κ inferInstance]) x) =ᵐ[μ]
      fun x => (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
          c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q N x)).toReal := by
  let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
  have hT : Measurable T := (continuous_rightAction _).measurable
  have hword := orbitName_measurable_fiber hT (fun a => hQ (measurableSet_singleton a)) N
  have H := ae_all_iff.mpr (fun a =>
    selfConstant_kernel_ae_eq_condExp μ κ hstat hself (hword a))
  filter_upwards [H,hversion] with x hx hv
  rw [←hx (orbitName T Q N x),hv]
  have hF : Measurable (fun u => rightAction x (c.word u)) :=
    ((continuous_rightAction_uncurry (d+1)).comp
      (continuous_const.prodMk (c.word_isEmbedding_remaining hf).continuous)).measurable
  have hA : MeasurableSet {y | orbitName T Q N y=orbitName T Q N x} := hword _
  rw [ambientFutureMeasure,Measure.real,Measure.map_apply hF hA]
  change ((anchorNormalize (c.remainingTimeProduct hP hf μ x)
      (c.remainingFutureAtom ell hell Q N x)).restrict
      (c.remainingFutureAtom ell hell Q N x)).real
      {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} = _
  rw [normalized_restriction_real _ _
      {u | orbitName T Q N (rightAction x (c.word u))=orbitName T Q N x} (hA.preimage hF),
    c.remainingFutureAtom_word_inter ell hell Q N x,ENNReal.toReal_div]
  rfl

theorem futureBlock_conditionalInformation
    (d : ℕ) {P : Finset (Fin (d+1) × Fin (d+1))} {D : Finset (Fin (d+1))}
    (c : EliminationChain P D) (hP : InitialRootPattern P)
    (hf : c.finalEntries=allPositiveRoots (d+1))
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (ell : Fin (d+1) → ℝ) (hell : ∑ k, ell k=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (κ : Kernel (X (d+1)) (X (d+1))) [IsMarkovKernel κ]
    (hstat : μ.bind κ=μ)
    (hself : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, κ y=κ x)
    (N : ℕ)
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q N x) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    conditionalInformation μ (orbitName T Q N) (MeasurableSpace.comap κ inferInstance) =ᵐ[μ]
      fun x => -Real.log
        (c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) /
          c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q N x)).toReal := by
  filter_upwards [c.futureBlock_conditionalProbability d hP hf μ ell hell Q hQ κ
    hstat hself N hversion] with x hx
  exact congrArg (-Real.log ·) hx

end EliminationChain

theorem delayedFuture_conditionalInformation_integrable_integral
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
    (hversion : ∀ᵐ x ∂μ, κ x=c.ambientFutureMeasure hP hf μ ell hell Q 1 x)
    (hmass : ∀ᵐ x ∂μ,
      0 < c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ∧
      c.remainingTimeProduct hP hf μ x (c.remainingFutureAtom ell hell Q 0 x) ≤ 1)
    (N : ℕ) :
    let T := fun y => rightAction y (diagonalOneParameter ell hell (-1))
    let K := delayedFutureKernel κ (diagonalOneParameter ell hell (-1)) N
    Integrable (conditionalInformation μ (orbitName T Q (N+1))
      (MeasurableSpace.comap K inferInstance)) μ ∧
      (∫ x, conditionalInformation μ (orbitName T Q (N+1))
        (MeasurableSpace.comap K inferInstance) x ∂μ) = (N+1 : ℝ) *
        ∑ p : ↥(allPositiveRoots (d+1) \ P),
          (ell p.val.2-ell p.val.1) * canonicalRootCoefficient d μ p.val.1 p.val.2 := by
  have hK := delayedFutureKernel_spec d c hP hf μ hA ell hell Q κ hstat hself hversion N
  have he := c.futureBlock_conditionalInformation d hP hf μ ell hell Q hQ _
    hK.1 hK.2.1 (N+1) hK.2.2
  have H := c.futureBlockInformation_integrable_integral d hP hf μ hA ell hell Q hQ hmass (N+1)
  refine ⟨H.1.congr he.symm,?_⟩
  exact (integral_congr_ae he).trans (by simpa only [Nat.cast_add,Nat.cast_one] using H.2)

end DukePrimeDegree

end

end OAI
