import OAI.Analysis.CircleDomains.Rigidity.TraceIntervalPayment

namespace OAI

/-! Countable open intervals convert local variation payment into a
measure bound for the entire image, without requiring image measurability. -/
open Set Function MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem open_line_image_measure_le (κ : Measure ℝ) [IsFiniteMeasure κ]
    {U : Set ℝ} (hU : IsOpen U) (v : ℝ → ℝ)
    (hpay : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → Icc x y ⊆ U →
      |v y-v x| ≤ κ.real (Icc x y)) : volume (v '' U) ≤ κ U := by
  classical
  let C : Set (Set ℝ) := {V | ∃ x ∈ U, V = connectedComponentIn U x}
  have hC (V : Set ℝ) (hV : V ∈ C) : IsOpen V ∧ IsConnected V ∧ V ⊆ U := by
    obtain ⟨x,hx,rfl⟩ := hV
    exact ⟨hU.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr hx,
      connectedComponentIn_subset U x⟩
  have hd : C.PairwiseDisjoint id := by
    rintro V ⟨x,hx,rfl⟩ W ⟨y,hy,rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro z hzx hzy
    exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)
  have hcount : C.Countable := hd.countable_of_nonempty_interior (fun V hV => by
    change (interior V).Nonempty
    rw [(hC V hV).1.interior_eq]
    exact (hC V hV).2.1.nonempty)
  let : Countable C := hcount.to_subtype
  have hpiece (V : C) : volume (v '' V.val) ≤ κ V.val := by
    apply (Real.volume_le_diam _).trans
    rw [← ofReal_measureReal]
    apply Metric.ediam_le
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [edist_dist,Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    have hfwd (a b : ℝ) (ha : a ∈ V.val) (hb : b ∈ V.val) (hab : a ≤ b) :
        |v b-v a| ≤ κ.real V.val := by
      have hI : Icc a b ⊆ V.val := (hC _ V.property).2.1.isPreconnected.ordConnected.out ha hb
      exact (hpay a ((hC _ V.property).2.2 ha) b ((hC _ V.property).2.2 hb)
        hab (hI.trans (hC _ V.property).2.2)).trans (measureReal_mono hI)
    rcases le_total x y with h | h
    · simpa only [abs_sub_comm] using hfwd x y hx hy h
    · exact hfwd y x hy hx h
  have hunion : (⋃ V : C, V.val) = U := by
    apply Subset.antisymm
    · exact iUnion_subset (fun V => (hC _ V.property).2.2)
    · intro x hx
      exact mem_iUnion.mpr ⟨⟨connectedComponentIn U x,x,hx,rfl⟩,mem_connectedComponentIn hx⟩
  have hdp : Pairwise (Disjoint on fun V : C => V.val) := by
    intro V W hne
    exact hd V.property W.property (fun he => hne (Subtype.ext he))
  calc
    volume (v '' U) = volume (⋃ V : C, v '' V.val) := by rw [← image_iUnion,hunion]
    _ ≤ ∑' V : C, volume (v '' V.val) := measure_iUnion_le _
    _ ≤ ∑' V : C, κ V.val := ENNReal.tsum_le_tsum hpiece
    _ = κ U := by rw [← measure_iUnion hdp (fun V => (hC _ V.property).1.measurableSet),hunion]

end CircleDomainRigidity

end

end OAI
