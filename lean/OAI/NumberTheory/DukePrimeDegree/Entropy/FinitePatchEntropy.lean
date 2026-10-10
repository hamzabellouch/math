import OAI.NumberTheory.DukePrimeDegree.Entropy.FinitePatchNames
import OAI.NumberTheory.DukePrimeDegree.Entropy.WholeFutureEntropyCriterion

namespace OAI

/-! # Terminal patch errors have their actual stationary measure cost -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

theorem finite_patch_name_entropy_bound {n p k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (E : Fin p → Set (X n)) (hE : ∀ i, MeasurableSet (E i))
    (hpair : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i,
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 x =
      fullFutureObservation
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q 0 y →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    (B : Set (X n)) (hB : MeasurableSet B) (R : X n → Fin k)
    {r : ℝ} (hr : 0 < r)
    (hrobust : ∀ z y, y ∉ B → quotientLogDistance z y < r → P y=R z)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ M : ℕ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (fullFutureSigma
          (fun z => rightAction z (diagonalOneParameter ell hell (-1))) Q N) ≤
      Real.log M+(N : ℝ)*rareLabelCost k δ (μ.real B+μ.real (⋃ i, E i)ᶜ) := by
  classical
  let x₀ : X n := Quotient.mk _ (1 : G n)
  let : Nonempty (Fin k) := ⟨P x₀⟩
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let U := ⋃ i, E i
  have hU : MeasurableSet U := MeasurableSet.iUnion hE
  obtain ⟨M,hM⟩ := finite_patch_terminal_names ell hell Q hQ E hE hpair hr
  refine ⟨M,?_⟩
  intro N
  let F := fullFutureObservation T Q N
  have hF : Measurable F := fullFutureObservation_measurable hT.measurable hQ N
  choose c v hc hclose using hM N
  let refs (s : ℕ → ℕ) (i : Fin M) (j : Fin N) := R (v s i j)
  let bad (j : Fin N) := (T^[j.val]) ⁻¹' B ∪ (T^[N]) ⁻¹' Uᶜ
  have hbad (j : Fin N) : MeasurableSet (bad j) :=
    (hB.preimage (hT.measurable.iterate j.val)).union
      (hU.compl.preimage (hT.measurable.iterate N))
  have he : ∀ᵐ s ∂μ.map F, ∀ j : Fin N,
      ∀ᵐ y ∂condDistrib id F μ s,
        orbitName T P N y j ≠ refs s (c s y) j → y ∈ bad j := by
    filter_upwards [ae_condDistrib_self_fiber μ F hF] with s hs
    intro j
    filter_upwards [hs] with y hy
    intro hne
    by_contra hnot
    have hyB : T^[j.val] y ∉ B := fun h => hnot (Or.inl h)
    have hyU : T^[N] y ∈ U := by
      by_contra h
      exact hnot (Or.inr h)
    apply hne
    exact hrobust _ _ hyB (hclose s y hy hyU j)
  have H := conditionalSigmaEntropy_comap_le_reference_bad_sets μ F hF N M
    (orbitName T P N) (measurable_pi_iff.mpr fun j =>
      hP.comp (hT.measurable.iterate j.val)) c hc refs bad hbad he hδ hδ1
  have hb (j : Fin N) : μ.real (bad j) ≤ μ.real B+μ.real Uᶜ := by
    have hh := measureReal_union_le (μ := μ) ((T^[j.val]) ⁻¹' B) ((T^[N]) ⁻¹' Uᶜ)
    rw [(hT.iterate j.val).measureReal_preimage hB.nullMeasurableSet,
      (hT.iterate N).measureReal_preimage hU.compl.nullMeasurableSet] at hh
    exact hh
  have hsum : (∑ j : Fin N, μ.real (bad j)) ≤ N*(μ.real B+μ.real Uᶜ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hslope : 0 ≤ Real.log (k:ℝ)-Real.log δ := by
    have hkNat : 0 < k := by
      simpa only [Fintype.card_fin] using (Fintype.card_pos (α := Fin k))
    have hk : 1 ≤ (k:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hkNat)
    linarith [Real.log_nonneg hk,Real.log_neg hδ hδ1]
  rw [fullFutureSigma_eq_comap]
  have hm := mul_le_mul_of_nonneg_right hsum hslope
  simp only [Fintype.card_fin] at H
  dsimp only [rareLabelCost]
  change conditionalSigmaEntropy μ (orbitName T P N)
    (MeasurableSpace.comap F inferInstance) ≤ _
  nlinarith

end DukePrimeDegree

end

end OAI
