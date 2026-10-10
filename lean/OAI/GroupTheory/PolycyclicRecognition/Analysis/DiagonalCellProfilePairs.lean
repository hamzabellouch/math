import OAI.GroupTheory.PolycyclicRecognition.Analysis.DiagonalProfileSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfilePairs

namespace OAI

/-! # The diagonal's two profiles retain subexponential relative Haar mass -/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- The concrete coordinate balls absorb every later compact path set. -/
theorem compact_eventually_subset_coordinate_balls
    {V : Type*} [PseudoMetricSpace V] (x : V) (C : Set V) (hC : IsCompact C) :
    ∀ᶠ n : ℕ in atTop, C ⊆ Metric.closedBall x ((n : ℝ) + 1) := by
  obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall x
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventually_ge_atTop r)] with n hn
  exact hr.trans (Metric.closedBall_subset_closedBall (by linarith))

theorem exists_diagonal_good_cell_profile_pairs
    {V W A : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace A]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : ℕ → Set V) (hK : ∀ j, IsCompact (K j))
    (hcover : ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, C ⊆ K j)
    (scale : ℕ → ℕ → ℝ) (hs : ∀ j, Tendsto (scale j) atTop atTop)
    (μ : Measure A) (Q : ℕ → ℕ → Set A)
    (hQ : ∀ j n, MeasurableSet (Q j n))
    (hQ0 : ∀ j n, μ (Q j n) ≠ 0) (hQfin : ∀ j n, μ (Q j n) ≠ ∞)
    (profile : ℕ → ℕ → A → S × S)
    (hp : ∀ j n, Measurable (profile j n)) (ν : ℕ → ProbabilityMeasure (S × S))
    (hν : ∀ j, Tendsto (fun n => ProbabilityMeasure.map (cellProbabilityMeasure μ (Q j n) (hQ0 j n) (hQfin j n)) (profile j n))
      atTop (𝓝 (ν j)))
    (f : ℕ → S × S) (g : S × S) (hf : ∀ j, f j ∈ (ν j : Measure (S × S)).support)
    (hfg : Tendsto f atTop (𝓝 g))
    (P : ℕ → ℕ → Prop) (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ (u n : ℕ → ℕ) (B : ℕ → Set A),
      Tendsto u atTop atTop ∧ (∀ j, P (u j) (n j)) ∧
      Tendsto (fun j => scale (u j) (n j)) atTop atTop ∧
      (∀ j, MeasurableSet (B j)) ∧
      (∀ j, B j ⊆ Q (u j) (n j)) ∧
      (∀ j, 0 < (μ (B j)).toReal) ∧
      HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
        (fun j => (μ (B j)).toReal / (μ (Q (u j) (n j))).toReal) ∧
      ∀ C : Set V, IsCompact C → ∀ᶠ j in atTop, ∀ a ∈ B j, ∀ z ∈ C,
        ‖(profile (u j) (n j) a).1.val z - g.1.val z‖ < 2 / ((j : ℝ) + 1) ∧
        ‖(profile (u j) (n j) a).2.val z - g.2.val z‖ < 2 / ((j : ℝ) + 1) := by
  let : ∀ j, CompactSpace (K j) := fun j => isCompact_iff_compactSpace.mp (hK j)
  let res : ∀ j, C(S, C(K j, W)) := fun j =>
    ⟨fun g => g.val.comp ⟨Subtype.val, continuous_subtype_val⟩,
      (ContinuousMap.continuous_precomp ⟨Subtype.val, continuous_subtype_val⟩).comp
        continuous_subtype_val⟩
  let observe : ∀ j, C(S × S, C(K j, W) × C(K j, W)) := fun j =>
    ⟨fun g => (res j g.1, res j g.2), ((res j).continuous.comp continuous_fst).prodMk
      ((res j).continuous.comp continuous_snd)⟩
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he j : 0 < e j := by dsimp [e]; positivity
  have hclose j : ∀ᶠ m in atTop, ‖observe j (f m) - observe j g‖ < e j := by
    have ht := (((observe j).continuous.tendsto g).comp hfg).sub
      (tendsto_const_nhds (x := observe j g))
    have htn : Tendsto (fun m => ‖observe j (f m) - observe j g‖) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, sub_self, norm_zero] using ht.norm
    exact htn.eventually (gt_mem_nhds (he j))
  have hu j : ∃ m, j ≤ m ∧ ‖observe j (f m) - observe j g‖ < e j :=
    ((eventually_ge_atTop j).and (hclose j)).exists
  choose u hule huc using hu
  have hut : Tendsto u atTop atTop := tendsto_atTop_mono hule tendsto_id
  let U : ℕ → Set (S × S) := fun j =>
    (observe j) ⁻¹' Metric.ball (observe j (f (u j))) (e j)
  have hU j : IsOpen (U j) := Metric.isOpen_ball.preimage (observe j).continuous
  have hfU j : f (u j) ∈ U j := by
    change dist (observe j (f (u j))) (observe j (f (u j))) < e j
    simpa only [dist_self] using he j
  obtain ⟨n, B, hn, hr, hB, hBpos, hmass, happ⟩ := exists_diagonal_supported_neighborhoods
    (fun j => scale (u j)) (fun j => hs (u j))
    (fun j n => cellProbabilityMeasure μ (Q (u j) n) (hQ0 (u j) n) (hQfin (u j) n)) (fun j => profile (u j)) (fun j => hp (u j))
    (fun j => ν (u j)) (fun j => hν (u j)) (fun j => f (u j)) (fun j => hf (u j))
    U hU hfU (fun j => P (u j)) (fun j => hP (u j))
  let Good := fun j => B j ∩ Q (u j) (n j)
  have hmassEq j :
      ((cellProbabilityMeasure μ (Q (u j) (n j)) (hQ0 (u j) (n j)) (hQfin (u j) (n j)) :
        Measure A) (B j)).toReal = (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal :=
    cellProbabilityMeasure_apply_toReal μ _ _ _ _ (hB j)
  have hGoodmass : HasSubexponentialLowerBoundSeq (fun j => scale (u j) (n j))
      (fun j => (μ (Good j)).toReal / (μ (Q (u j) (n j))).toReal) := by
    simpa only [hmassEq] using hmass
  have hGoodpos j : 0 < (μ (Good j)).toReal := by
    have h := hBpos j
    rw [hmassEq] at h
    exact (div_pos_iff.mp h).resolve_right (fun hn => (ENNReal.toReal_nonneg).not_gt hn.1) |>.1
  refine ⟨u, n, Good, hut, hn, hr, fun j => (hB j).inter (hQ (u j) (n j)),
    fun _ => inter_subset_right, hGoodpos, hGoodmass, ?_⟩
  intro C hC
  filter_upwards [hcover C hC] with j hj
  intro a ha z hz
  have hzK := hj hz
  have hab : ‖observe j (profile (u j) (n j) a) - observe j (f (u j))‖ < e j := by
    simpa only [U, mem_preimage, Metric.mem_ball, dist_eq_norm] using happ j a ha.1
  have htriangle := norm_add_le
    (observe j (profile (u j) (n j) a) - observe j (f (u j)))
    (observe j (f (u j)) - observe j g)
  rw [sub_add_sub_cancel] at htriangle
  have hb : ‖observe j (profile (u j) (n j) a) - observe j g‖ < 2 / ((j : ℝ) + 1) := by
    apply htriangle.trans_lt
    dsimp only [e] at hab huc
    rw [show (2 : ℝ) / ((j : ℝ) + 1) =
      1 / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) by ring]
    exact add_lt_add hab (huc j)
  have hfst : ‖res j (profile (u j) (n j) a).1 - res j g.1‖ ≤
      ‖observe j (profile (u j) (n j) a) - observe j g‖ := norm_fst_le (observe j (profile (u j) (n j) a) - observe j g)
  have hsnd : ‖res j (profile (u j) (n j) a).2 - res j g.2‖ ≤
      ‖observe j (profile (u j) (n j) a) - observe j g‖ := norm_snd_le (observe j (profile (u j) (n j) a) - observe j g)
  exact ⟨((res j (profile (u j) (n j) a).1 - res j g.1).norm_coe_le_norm ⟨z, hzK⟩).trans_lt
    (hfst.trans_lt hb), ((res j (profile (u j) (n j) a).2 - res j g.2).norm_coe_le_norm
      ⟨z, hzK⟩).trans_lt (hsnd.trans_lt hb)⟩

end PolycyclicRecognition

end

end OAI
