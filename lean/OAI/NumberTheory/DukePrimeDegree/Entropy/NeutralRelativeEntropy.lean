import OAI.NumberTheory.DukePrimeDegree.Entropy.BilateralConditionalSupport
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalMapEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.RobustFiniteObservations

namespace OAI

/-! # Relative entropy of finite names over the bilateral itinerary factor -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

theorem diagonal_negative_iterate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (j : ℕ) (x : X n) :
    (fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[j] x =
      rightAction x (diagonalOneParameter ell hell (-(j:ℝ))) := by
  rw [rightAction_iterate,diagonalOneParameter_neg,inv_pow,
    ←diagonalOneParameter_nat,←diagonalOneParameter_neg]

theorem bilateral_name_entropy_le_robust_error {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
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
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) ≤
        Real.log M+(N : ℝ)*rareLabelCost k δ (μ.real B) := by
  classical
  let x₀ : X n := Quotient.mk _ (1 : G n)
  let : Nonempty (Fin k) := ⟨P x₀⟩
  let F := bilateralNameObservation ell hell Q
  have hF : Measurable F := measurable_bilateralNameObservation ell hell Q hQ
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  obtain ⟨M,v,hcover⟩ := measurable_neutral_fiber_names ell hell Q hQ hlift hr
  choose c hc hclose using hcover
  let x (s : (ℕ → ℕ) × (ℕ → ℕ)) : X n :=
    if h : ∃ y, F y=s then h.choose else x₀
  have hsupport := ae_condDistrib_self_fiber μ F hF
  have hx : ∀ᵐ s ∂μ.map F, F (x s)=s := by
    filter_upwards [hsupport] with s hs
    have he : ∃ y, F y=s := hs.exists
    simpa only [x,dite_eq_left he] using he.choose_spec
  refine ⟨M,?_⟩
  intro N
  let refs (s : (ℕ → ℕ) × (ℕ → ℕ)) (i : Fin M) (j : Fin N) :=
    R (rightAction (rightAction (x s) (v i))
      (diagonalOneParameter ell hell (-(j.val:ℝ))))
  let bad (j : Fin N) := (T^[j.val]) ⁻¹' B
  have hbad (j : Fin N) : MeasurableSet (bad j) :=
    hB.preimage (hT.measurable.iterate j.val)
  have he : ∀ᵐ s ∂μ.map F, ∀ j : Fin N,
      ∀ᵐ y ∂condDistrib id F μ s,
        orbitName T P N y j ≠ refs s (c N (x s) y) j → y ∈ bad j := by
    filter_upwards [hsupport,hx] with s hs hxs
    intro j
    filter_upwards [hs] with y hy
    intro hne
    have hmem : y ∈ bilateralNameFiber ell hell Q (x s) :=
      (bilateralNameObservation_eq_iff ell hell Q (x s) y).mp (hy.trans hxs.symm)
    have hdist := hclose N (x s) y hmem j
    by_contra hnot
    apply hne
    exact hrobust _ _ hnot (by
      simpa only [T,diagonal_negative_iterate] using hdist)
  have H := conditionalSigmaEntropy_comap_le_reference_bad_sets μ F hF N M
    (orbitName T P N) (measurable_pi_iff.mpr fun j =>
      hP.comp (hT.measurable.iterate j.val))
    (fun s => c N (x s)) (fun s => hc N (x s)) refs bad hbad he hδ hδ1
  have hm (j : Fin N) : μ.real (bad j)=μ.real B :=
    (hT.iterate j.val).measureReal_preimage hB.nullMeasurableSet
  simpa only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    rareLabelCost,mul_add,mul_assoc,add_assoc] using H

/-- Conditioning on the actual bilateral itinerary leaves a sublinear
amount of information in every finite measurable observation. -/
theorem bilateral_name_entropy_sublinear {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ N : ℕ,
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) ≤
        Real.log M+(N : ℝ)*ε := by
  obtain ⟨δ,η,hδ,hδ1,hη,hcost⟩ := rareLabelCost_small k hε
  obtain ⟨B,r,R,hB,hsmall,hr,hrobust⟩ := exists_robust_finite_observation μ P hP
    (ENNReal.ofReal η) (by simp only [ne_eq,ENNReal.ofReal_eq_zero]; linarith)
  have hsmall' : μ.real B < η := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top μ B) ENNReal.ofReal_ne_top).mpr hsmall
    simpa only [Measure.real,ENNReal.toReal_ofReal hη.le] using h
  obtain ⟨M,hM⟩ := bilateral_name_entropy_le_robust_error ell hell Q hQ hlift
    μ hT P hP B hB R hr hrobust hδ hδ1
  refine ⟨M,fun N => (hM N).trans ?_⟩
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (hcost (μ.real B) measureReal_nonneg hsmall').le (Nat.cast_nonneg N))

theorem bilateral_name_relative_entropy_tendsto_zero {n k : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall n 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) μ μ)
    (P : X n → Fin k) (hP : Measurable P) :
    Tendsto (fun N : ℕ =>
      conditionalSigmaEntropy μ
        (orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P N)
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance) / N)
      atTop (𝓝 0) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := bilateralNameObservation ell hell Q
  let E (N : ℕ) := conditionalSigmaEntropy μ (orbitName T P N)
    (MeasurableSpace.comap F inferInstance)
  have hE (N : ℕ) : 0 ≤ E N := conditionalSigmaEntropy_comap_nonneg μ F
    (measurable_bilateralNameObservation ell hell Q hQ) (orbitName T P N)
    (orbitName_measurable_fiber hT.measurable
      (fun a => hP (measurableSet_singleton a)) N)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨M,hM⟩ := bilateral_name_entropy_sublinear ell hell Q hQ hlift
    μ hT P hP (show 0 < ε/2 by positivity)
  have hlim : Tendsto (fun N : ℕ => Real.log M/(N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (gt_mem_nhds (show 0 < ε/2 by positivity)),
    eventually_ge_atTop (1 : ℕ)] with N hlog hN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb : E N/(N : ℝ) ≤ Real.log M/(N : ℝ)+ε/2 := by
    apply (div_le_iff₀ hn).mpr
    have he : (Real.log M/(N : ℝ)+ε/2)*N = Real.log M+N*(ε/2) := by
      field_simp
    rw [he]
    exact hM N
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (div_nonneg (hE N) hn.le)]
  linarith

end DukePrimeDegree

end

end OAI
