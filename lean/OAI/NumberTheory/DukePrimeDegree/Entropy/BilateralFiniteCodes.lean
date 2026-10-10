import OAI.NumberTheory.DukePrimeDegree.Entropy.NeutralRelativeEntropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.ConditionalSigmaLimit
import OAI.NumberTheory.DukePrimeDegree.Entropy.FiniteBlockEntropy

namespace OAI

/-! # Finite codes exhausting the actual bilateral itinerary factor -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

def bilateralFiniteCode {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (m : ℕ) (x : X n) :
    (Fin m → Fin (m+1)) × (Fin m → Fin (m+1)) :=
  (fun i => heightClip Q m
      ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[i.val] x),
   fun i => heightClip Q m
      ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[i.val] x))

theorem bilateralFiniteCode_measurable {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q) (m : ℕ) :
    Measurable (bilateralFiniteCode ell hell Q m) := by
  have hT (t : ℝ) : Measurable (fun z : X n =>
      rightAction z (diagonalOneParameter ell hell t)) :=
    (continuous_rightAction _).measurable
  exact (measurable_pi_iff.mpr fun i : Fin m =>
    (heightClip_measurable hQ m).comp ((hT (-1)).iterate i.val)).prodMk
      (measurable_pi_iff.mpr fun i : Fin m =>
        (heightClip_measurable hQ m).comp ((hT 1).iterate i.val))

def truncateBilateralCode {m l : ℕ} (hml : m ≤ l)
    (v : (Fin l → Fin (l+1)) × (Fin l → Fin (l+1))) :
    (Fin m → Fin (m+1)) × (Fin m → Fin (m+1)) :=
  (fun i => ⟨min (v.1 ⟨i.val,lt_of_lt_of_le i.isLt hml⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩,
   fun i => ⟨min (v.2 ⟨i.val,lt_of_lt_of_le i.isLt hml⟩).val m,
      Nat.lt_succ_of_le (min_le_right _ _)⟩)

theorem truncate_bilateralFiniteCode {n m l : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (hml : m ≤ l) (x : X n) :
    truncateBilateralCode hml (bilateralFiniteCode ell hell Q l x) =
      bilateralFiniteCode ell hell Q m x := by
  apply Prod.ext <;> funext i <;> apply Fin.ext <;>
    simp only [truncateBilateralCode,bilateralFiniteCode,heightClip] <;> omega

theorem bilateralFiniteCode_sigma_monotone {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ) :
    Monotone (fun m => observationSigma (bilateralFiniteCode ell hell Q m)) := by
  intro m l hml
  have he : bilateralFiniteCode ell hell Q m =
      truncateBilateralCode hml ∘ bilateralFiniteCode ell hell Q l :=
    funext fun x => (truncate_bilateralFiniteCode ell hell Q hml x).symm
  change observationSigma (bilateralFiniteCode ell hell Q m) ≤
    observationSigma (bilateralFiniteCode ell hell Q l)
  rw [he]
  simpa only [Function.comp_def] using
    observationSigma_comp_le (bilateralFiniteCode ell hell Q l) (truncateBilateralCode hml)

theorem bilateralFiniteCode_sigma_generate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ) :
    (⨆ m, observationSigma (bilateralFiniteCode ell hell Q m)) =
      MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance := by
  let F := bilateralNameObservation ell hell Q
  apply le_antisymm
  · let : MeasurableSpace (X n) := MeasurableSpace.comap F inferInstance
    have hF : Measurable F := comap_measurable F
    apply iSup_le
    intro m
    have hl (i : Fin m) : Measurable (fun x => (F x).1 i.val) :=
      (measurable_pi_apply i.val).comp (measurable_fst.comp hF)
    have hr (i : Fin m) : Measurable (fun x => (F x).2 i.val) :=
      (measurable_pi_apply i.val).comp (measurable_snd.comp hF)
    have hC : Measurable (bilateralFiniteCode ell hell Q m) :=
      (measurable_pi_iff.mpr fun i => heightClip_measurable (hl i) m).prodMk
        (measurable_pi_iff.mpr fun i => heightClip_measurable (hr i) m)
    exact observationSigma_le _ (fun a => hC (measurableSet_singleton a))
  · let : MeasurableSpace (X n) :=
      ⨆ m, observationSigma (bilateralFiniteCode ell hell Q m)
    have hC (m : ℕ) : Measurable (bilateralFiniteCode ell hell Q m) := by
      apply measurable_to_countable'
      intro a
      exact (le_iSup (fun l => observationSigma (bilateralFiniteCode ell hell Q l)) m)
        _ ⟨{a},trivial,rfl⟩
    have hl (k : ℕ) : Measurable (fun x => (F x).1 k) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp [m]; omega
      have ha : a < m := by dsimp [m]; omega
      let g (x : X n) := ((bilateralFiniteCode ell hell Q m x).1 ⟨k,hk⟩).val
      have hg : Measurable g := (measurable_of_finite (fun v : Fin (m+1) => v.val)).comp
        ((measurable_pi_apply (⟨k,hk⟩ : Fin m)).comp (measurable_fst.comp (hC m)))
      have he : {x | (F x).1 k=a}={x | g x=a} := by
        ext x
        change Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)=a ↔
          min (Q ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[k] x)) m=a
        omega
      change MeasurableSet {x | (F x).1 k=a}
      rw [he]
      exact measurableSet_eq_fun hg measurable_const
    have hr (k : ℕ) : Measurable (fun x => (F x).2 k) := by
      apply measurable_to_countable'
      intro a
      let m := max (k+1) (a+1)
      have hk : k < m := by dsimp [m]; omega
      have ha : a < m := by dsimp [m]; omega
      let g (x : X n) := ((bilateralFiniteCode ell hell Q m x).2 ⟨k,hk⟩).val
      have hg : Measurable g := (measurable_of_finite (fun v : Fin (m+1) => v.val)).comp
        ((measurable_pi_apply (⟨k,hk⟩ : Fin m)).comp (measurable_snd.comp (hC m)))
      have he : {x | (F x).2 k=a}={x | g x=a} := by
        ext x
        change Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)=a ↔
          min (Q ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[k] x)) m=a
        omega
      change MeasurableSet {x | (F x).2 k=a}
      rw [he]
      exact measurableSet_eq_fun hg measurable_const
    exact ((measurable_pi_iff.mpr hl).prodMk (measurable_pi_iff.mpr hr)).comap_le

theorem conditional_bilateralFiniteCode_tendsto {n : ℕ} {α : Type*} [Fintype α]
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0)
    (Q : X n → ℕ) (hQ : Measurable Q)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    (P : X n → α) (hP : ∀ a, MeasurableSet {x | P x=a}) :
    Tendsto (fun m => conditionalObservationEntropy μ P (bilateralFiniteCode ell hell Q m))
      atTop (𝓝 (conditionalSigmaEntropy μ P
        (MeasurableSpace.comap (bilateralNameObservation ell hell Q) inferInstance))) := by
  have H := conditionalObservationEntropy_tendsto_sigma μ P hP
    (bilateralFiniteCode ell hell Q)
    (fun m a => bilateralFiniteCode_measurable ell hell Q hQ m (measurableSet_singleton a))
    (bilateralFiniteCode_sigma_monotone ell hell Q)
  rwa [bilateralFiniteCode_sigma_generate] at H

private theorem diagonal_positive_iterate {n : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (j : ℕ) (x : X n) :
    (fun z => rightAction z (diagonalOneParameter ell hell 1))^[j] x =
      rightAction x (diagonalOneParameter ell hell (j:ℝ)) := by
  rw [rightAction_iterate,←diagonalOneParameter_nat]

private theorem shifted_window_symbol {n m W : ℕ}
    (ell : Fin n → ℝ) (hell : ∑ i, ell i=0) (Q : X n → ℕ)
    (x : X n) (j : Fin W) :
    orbitName (fun z => rightAction z (diagonalOneParameter ell hell (-1)))
      (heightClip Q m) W (rightAction x (diagonalOneParameter ell hell (m:ℝ))) j =
      heightClip Q m (rightAction x
        (diagonalOneParameter ell hell ((m:ℝ)-(j.val:ℝ)))) := by
  change heightClip Q m
    ((fun z => rightAction z (diagonalOneParameter ell hell (-1)))^[j.val]
      (rightAction x (diagonalOneParameter ell hell (m:ℝ)))) = _
  rw [diagonal_negative_iterate,rightAction_mul,←diagonalOneParameter_add]
  rfl

/-- A bilateral finite code is a factor of a shifted finite orbit window,
so it has no more entropy than the clipped countable observation. -/
theorem bilateralFiniteCode_entropyRate_le (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (m : ℕ) :
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1)))
      (bilateralFiniteCode ell hell Q m) ≤
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let S := fun z => rightAction z (diagonalOneParameter ell hell (m:ℝ))
  have hp (t : ℝ) : MeasurePreserving
      (fun z => rightAction z (diagonalOneParameter ell hell t)) μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hcomm : Function.Commute S T := by
    intro x
    dsimp [S,T]
    rw [rightAction_mul,rightAction_mul,←diagonalOneParameter_add,
      ←diagonalOneParameter_add,
      show (-1:ℝ)+(m:ℝ)=(m:ℝ)+(-1) from add_comm _ _]
  let R := orbitName T (heightClip Q m) (2*m+1)
  have hR : Measurable R := measurable_pi_iff.mpr fun i =>
    (heightClip_measurable hQ m).comp ((hp (-1)).measurable.iterate i.val)
  have hfactor : ∀ x y, (R ∘ S) x=(R ∘ S) y →
      bilateralFiniteCode ell hell Q m x=bilateralFiniteCode ell hell Q m y := by
    intro x y hxy
    have hf (z : X (d+1)) (i : Fin m) :
        (R ∘ S) z ⟨m+i.val,by omega⟩ =
          (bilateralFiniteCode ell hell Q m z).1 i := by
      rw [show (R ∘ S) z ⟨m+i.val,by omega⟩ =
        orbitName T (heightClip Q m) (2*m+1) (S z) ⟨m+i.val,by omega⟩ from rfl]
      rw [shifted_window_symbol]
      change heightClip Q m (rightAction z
        (diagonalOneParameter ell hell ((m:ℝ)-((m+i.val:ℕ):ℝ)))) =
        heightClip Q m (T^[i.val] z)
      rw [diagonal_negative_iterate]
      congr 3
      push_cast
      ring
    have hb (z : X (d+1)) (i : Fin m) :
        (R ∘ S) z ⟨m-i.val,by omega⟩ =
          (bilateralFiniteCode ell hell Q m z).2 i := by
      change orbitName T (heightClip Q m) (2*m+1) (S z) ⟨m-i.val,by omega⟩ = _
      rw [shifted_window_symbol]
      change heightClip Q m (rightAction z
        (diagonalOneParameter ell hell ((m:ℝ)-((m-i.val:ℕ):ℝ)))) =
        heightClip Q m ((fun z => rightAction z (diagonalOneParameter ell hell 1))^[i.val] z)
      rw [diagonal_positive_iterate]
      congr 3
      rw [Nat.cast_sub (by omega : i.val ≤ m)]
      ring
    apply Prod.ext <;> funext i
    · exact (hf x i).symm.trans ((congrFun hxy ⟨m+i.val,by omega⟩).trans (hf y i))
    · exact (hb x i).symm.trans ((congrFun hxy ⟨m-i.val,by omega⟩).trans (hb y i))
  have H := observationEntropyRate_le_of_refines μ (hp (-1))
    (bilateralFiniteCode ell hell Q m) (R ∘ S)
    (fun a => bilateralFiniteCode_measurable ell hell Q hQ m (measurableSet_singleton a))
    (fun a => (hR.comp (hp m).measurable) (measurableSet_singleton a)) hfactor
  rw [observationEntropyRate_comp_commuting μ T S (hp m) hcomm R
    (fun a => hR (measurableSet_singleton a)) (hp (-1)).measurable] at H
  refine H.trans ?_
  simpa only [Function.iterate_one,Nat.cast_one,one_mul] using
    observationEntropyRate_sampled_window_le μ (hp (-1)) (heightClip Q m)
      (fun a => heightClip_measurable hQ m (measurableSet_singleton a))
      (q := 1) (by omega) (2*m+1)

/-- The small neutral fibers make a uniform entropy bound on all finite
clips of Q an entropy bound for every finite measurable observation. -/
theorem entropyRate_le_of_bilateral_heightClip_bounds (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (B : ℝ)
    (hbound : ∀ m, observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B)
    {k : ℕ} (P : X (d+1) → Fin k) (hP : Measurable P) :
    observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) P ≤ B := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let F := bilateralNameObservation ell hell Q
  have hT : MeasurePreserving T μ μ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    dsimp [T]
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hA _
  have hblock (N : ℕ) (hN : 0 < N) :
      observationEntropyRate μ T P ≤ B+
        conditionalSigmaEntropy μ (orbitName T P N)
          (MeasurableSpace.comap F inferInstance)/(N : ℝ) := by
    have hm (m : ℕ) : observationEntropyRate μ T P ≤ B+
        conditionalObservationEntropy μ (orbitName T P N)
          (bilateralFiniteCode ell hell Q m)/(N : ℝ) := by
      have H := observationEntropyRate_le_block_conditional μ hT P
        (bilateralFiniteCode ell hell Q m)
        (fun a => hP (measurableSet_singleton a))
        (fun a => bilateralFiniteCode_measurable ell hell Q hQ m
          (measurableSet_singleton a)) hN
      exact H.trans (add_le_add
        ((bilateralFiniteCode_entropyRate_le d ell hell Q hQ μ hA m).trans (hbound m)) le_rfl)
    have hlim := ((conditional_bilateralFiniteCode_tendsto ell hell Q hQ μ (orbitName T P N)
      (orbitName_measurable_fiber hT.measurable
        (fun a => hP (measurableSet_singleton a)) N)).div_const (N : ℝ)).const_add B
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hm)
  have hlim := (bilateral_name_relative_entropy_tendsto_zero ell hell Q hQ hlift
    μ hT P hP).const_add B
  have h := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact hblock N (by omega))
  simpa only [add_zero] using h

theorem measureEntropy_le_of_bilateral_heightClip_bounds (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t))
    (B : ℝ)
    (hbound : ∀ m, observationEntropyRate μ
      (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m) ≤ B) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) ≤
      ENNReal.ofReal B := by
  apply iSup_le
  intro k
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  exact ENNReal.ofReal_le_ofReal (entropyRate_le_of_bilateral_heightClip_bounds
    d ell hell Q hQ μ hA hlift B hbound P (by apply measurable_to_countable'; exact hP))

/-- For the constructed neutral-fiber observation, the full metric
entropy is the supremum of the entropy rates of its finite clips. -/
theorem measureEntropy_eq_iSup_heightClip_of_neutral_fibers (d : ℕ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i=0)
    (Q : X (d+1) → ℕ) (hQ : Measurable Q)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u))=μ)
    (hlift : ∀ x y, y ∈ bilateralNameFiber ell hell Q x →
      ∃ g ∈ matrixBall (d+1) 1, rightAction x g=y ∧
        ∀ t : ℝ, Commute g (diagonalOneParameter ell hell t)) :
    measureEntropy μ (fun z => rightAction z (diagonalOneParameter ell hell (-1))) =
      ⨆ m, ENNReal.ofReal (observationEntropyRate μ
        (fun z => rightAction z (diagonalOneParameter ell hell (-1))) (heightClip Q m)) := by
  let T := fun z => rightAction z (diagonalOneParameter ell hell (-1))
  let E := ⨆ m, ENNReal.ofReal (observationEntropyRate μ T (heightClip Q m))
  apply le_antisymm
  · change measureEntropy μ T ≤ E
    by_cases hE : E=∞
    · rw [hE]
      exact le_top
    have hbound (m : ℕ) : observationEntropyRate μ T (heightClip Q m) ≤ E.toReal :=
      (ENNReal.ofReal_le_iff_le_toReal hE).mp (le_iSup
        (fun m => ENNReal.ofReal (observationEntropyRate μ T (heightClip Q m))) m)
    exact (measureEntropy_le_of_bilateral_heightClip_bounds d ell hell Q hQ μ hA
      hlift E.toReal hbound).trans_eq (ENNReal.ofReal_toReal hE)
  · apply iSup_le
    intro m
    exact le_iSup_of_le (m+1) (le_iSup_of_le (heightClip Q m)
      (le_iSup_of_le (fun a => heightClip_measurable hQ m (measurableSet_singleton a)) le_rfl))

end DukePrimeDegree

end

end OAI
