import OAI.NumberTheory.DukePrimeDegree.Entropy.PredecessorWholeFutureSigma

namespace OAI

/-! # Exact predecessor-word entropy conditioned on the whole terminal future -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets

def fullFutureObservation {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ)
    (y : Y) : ℕ → ℕ := fun k => Q (T^[r+k] y)

lemma fullFutureObservation_measurable {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {Q : Y → ℕ} (hQ : Measurable Q) (r : ℕ) :
    Measurable (fullFutureObservation T Q r) :=
  measurable_pi_iff.mpr fun k => hQ.comp (hT.iterate (r+k))

lemma fullFutureSigma_eq_comap {Y : Type*} (T : Y → Y) (Q : Y → ℕ) (r : ℕ) :
    fullFutureSigma T Q r=
      MeasurableSpace.comap (fullFutureObservation T Q r) inferInstance :=
  (MeasurableSpace.comap_process_pi (fun k y => Q (T^[r+k] y))).symm

lemma orbitName_eq_iff_last_initial {Y α : Type*} (T : Y → Y) (B : Y → α)
    (N : ℕ) (x y : Y) :
    orbitName T B (N+1) x=orbitName T B (N+1) y ↔
      B (T^[N] x)=B (T^[N] y) ∧ orbitName T B N x=orbitName T B N y := by
  constructor
  · intro h
    exact ⟨congrFun h (Fin.last N),funext fun i => congrFun h i.castSucc⟩
  · rintro ⟨hl,hw⟩
    funext i
    by_cases hi : i.val<N
    · exact congrFun hw ⟨i.val,hi⟩
    · have he : i.val=N := by omega
      change B (T^[i.val] x)=B (T^[i.val] y)
      simpa only [he] using hl

theorem predecessor_word_wholeFuture_increment
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B (N+1)) (fullFutureSigma T Q (N+1)) =
      conditionalSigmaEntropy μ B (fullFutureSigma T Q 1) +
        conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) := by
  let P := B ∘ T^[N]
  let W := orbitName T B N
  have hP : Measurable P := hB.comp (hT.measurable.iterate N)
  have hW : Measurable W := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have hV : Measurable (orbitName T B (N+1)) := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have he : conditionalSigmaEntropy μ (orbitName T B (N+1))
        (fullFutureSigma T Q (N+1)) =
      conditionalSigmaEntropy μ (fun y => (P y,W y))
        (fullFutureSigma T Q (N+1)) := by
    rw [fullFutureSigma_eq_comap]
    have hF := fullFutureObservation_measurable hT.measurable hQ (N+1)
    apply le_antisymm
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ _ hF _ hV _ (hP.prodMk hW)
      intro x y _ hxy
      exact (orbitName_eq_iff_last_initial T B N x y).mpr (Prod.mk.inj hxy)
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ _ hF _ (hP.prodMk hW) _ hV
      intro x y _ hxy
      exact Prod.ext
        ((orbitName_eq_iff_last_initial T B N x y).mp hxy).1
        ((orbitName_eq_iff_last_initial T B N x y).mp hxy).2
  rw [he,conditionalSigmaEntropy_chain_fullFuture μ hT.measurable Q hQ P
    (fun b => hP (measurableSet_singleton b)) W
    (fun w => hW (measurableSet_singleton w)) N]
  rw [conditionalSigmaEntropy_comp_preserving_fullFuture μ hT Q hQ B
    (fun b => hB (measurableSet_singleton b)) N,
    ←fullFutureSigma_predecessor_at T Q B href decode hdecode N]

theorem predecessor_word_wholeFuture_entropy
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B N) (fullFutureSigma T Q N) =
      (N : ℝ)*conditionalSigmaEntropy μ B (fullFutureSigma T Q 1) := by
  induction N with
  | zero =>
      rw [fullFutureSigma_eq_comap,conditionalSigmaEntropy_comap_eq_integral μ _
        (fullFutureObservation_measurable hT.measurable hQ 0) _
        (orbitName_measurable_fiber hT.measurable
          (fun b => hB (measurableSet_singleton b)) 0)]
      simp only [observationEntropy_unique,integral_zero,Nat.cast_zero,zero_mul]
  | succ N ih =>
      rw [predecessor_word_wholeFuture_increment μ hT Q hQ B hB href decode hdecode N,ih]
      push_cast
      ring

end DukePrimeDegree

end

end OAI
