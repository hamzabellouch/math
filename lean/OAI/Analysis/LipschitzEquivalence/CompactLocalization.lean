import OAI.Analysis.LipschitzEquivalence.CompactLipschitz

namespace OAI

universe uM uI

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Fintype I]

theorem cutoff_nonzero_mem (z : M) {r : ℝ≥0} (hr : 0 < r) {x : M}
    (hx : cutoff z r x ≠ 0) : x ∈ Metric.ball z r := by
  by_contra hn
  apply hx
  exact cutoff_zero z hr (le_of_not_gt hn)

omit [Fintype I] in
theorem disjoint_cutoffs (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    ∀ x j k, cutoff (z j) r x ≠ 0 → cutoff (z k) r x ≠ 0 → j = k := by
  intro x j k hj hk
  by_contra hn
  exact Set.disjoint_left.mp (hdis hn) (cutoff_nonzero_mem _ hr hj) (cutoff_nonzero_mem _ hr hk)

theorem sum_cutoff_bounds (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    ∀ x, (∑ j,cutoff (z j) r x) ∈ Icc (0 : ℝ) 1 := by
  classical
  intro x
  refine ⟨Finset.sum_nonneg (fun j _ => cutoff_nonneg _ _ _),?_⟩
  by_cases hx : ∃ j, cutoff (z j) r x ≠ 0
  · obtain ⟨j,hj⟩ := hx
    have heq : ∑ k,cutoff (z k) r x = cutoff (z j) r x := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        by_contra hk'
        exact hkj (disjoint_cutoffs z hr hdis x k j hk' hj)
      · simp
    rw [heq]
    exact cutoff_le_one _ _ _
  · push Not at hx
    simp [hx]

def removed (d : M → ℝ) (z : I → M) (r : ℝ≥0) (x : M) : ℝ :=
  ∑ j, (d x-d (z j))*cutoff (z j) r x

def remainder (d : M → ℝ) (z : I → M) (r : ℝ≥0) : M → ℝ :=
  weightedRemainder d z (fun j => cutoff (z j) r)

theorem removed_lipschitz (d : M → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d)
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    LipschitzWith (6*L) (removed d z r) := by
  have hpart (j : I) : LipschitzWith (3*L) (fun x => (d x-d (z j))*cutoff (z j) r x) :=
    cutoff_product_lipschitz _ hr _ (lipschitz_sub_const _ hd _) (sub_self _)
  have ht := disjoint_sum_lipschitz _ hpart (by
    intro x j k hj hk
    apply disjoint_cutoffs z hr hdis x j k
    · exact (mul_ne_zero_iff.mp hj).2
    · exact (mul_ne_zero_iff.mp hk).2)
  have he : 2*(3*L) = 6*L := by ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [he,removed] using ht.dist_le_mul x y

theorem remainder_lipschitz (d : M → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d)
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r))) :
    LipschitzWith (7*L) (remainder d z r) := by
  have ht := hd.sub (removed_lipschitz d hd z hr hdis)
  have he : L+6*L = 7*L := by ring
  rw [he] at ht
  exact ht

theorem remainder_inner (d : M → ℝ) (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)))
    (j : I) {x : M} (hx : x ∈ Metric.ball (z j) ((r : ℝ)/2)) :
    remainder d z r x = d (z j) := by
  classical
  have hj : cutoff (z j) r x = 1 := cutoff_one _ hr hx.le
  have hk (k : I) (hkj : k ≠ j) : cutoff (z k) r x = 0 := by
    by_contra hn
    exact hkj (disjoint_cutoffs z hr hdis x k j hn (by rw [hj]; norm_num))
  have heq : ∑ k, (d x-d (z k))*cutoff (z k) r x = d x-d (z j) := by
    rw [Finset.sum_eq_single j]
    · rw [hj,mul_one]
    · intro k _ hkj
      rw [hk k hkj,mul_zero]
    · simp
  change d x - _ = _
  rw [heq]
  ring

theorem remainder_tendsto_zero (d : ℕ → M → ℝ)
    (hd : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0)) (z : I → M) (r : ℝ≥0) (x : M) :
    Tendsto (fun i => remainder (d i) z r x) atTop (𝓝 0) := by
  have ht := (hd x).sub (tendsto_finsetSum Finset.univ (fun j _ =>
    ((hd x).sub (hd (z j))).mul_const (cutoff (z j) r x)))
  simpa [remainder,weightedRemainder] using ht

theorem remainder_compact_lipschitz (d : ℕ → M → ℝ) {L : ℝ≥0}
    (hd : ∀ i, LipschitzWith L (d i))
    (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    (z : I → M) {r : ℝ≥0} (hr : 0 < r)
    (hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)))
    {η : ℝ≥0} (hη : 0 < η)
    (hgood : ∀ p, p ∉ Set.range z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
      ∀ᶠ i in atTop, LipschitzOnWith η (d i) O)
    {K : Set M} (hK : IsCompact K) :
    ∀ᶠ i in atTop, LipschitzOnWith (2*η) (remainder (d i) z r) K := by
  have hR := fun i => remainder_lipschitz (d i) (hd i) z hr hdis
  apply compact_eventual_lipschitz _ hK (by positivity)
  · intro ε hε
    exact uniform_zero_on_compact _ hR (remainder_tendsto_zero d hpoint z r) hK hε
  · intro p hp
    by_cases hpz : p ∈ Set.range z
    · obtain ⟨j,rfl⟩ := hpz
      refine ⟨Metric.ball (z j) ((r : ℝ)/2),Metric.isOpen_ball,
        Metric.mem_ball_self (by exact half_pos hr),?_⟩
      exact Filter.Eventually.of_forall (fun i => LipschitzOnWith.of_dist_le_mul (by
        intro x hx y hy
        rw [remainder_inner (d i) z hr hdis j hx.2,remainder_inner (d i) z hr hdis j hy.2,dist_self]
        positivity))
    · obtain ⟨O,hO,hpO,hOi⟩ := hgood p hpz
      let B : ℝ≥0 := 2/r
      let ε : ℝ≥0 := η/(2*Fintype.card I*B+1)
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hsmall := uniform_zero_on_compact d hd hpoint hK (show (0 : ℝ) < ε from hε)
      have hzsmall : ∀ᶠ i in atTop, ∀ j, |d i (z j)| ≤ (ε : ℝ) := by
        apply Filter.eventually_all.mpr
        intro j
        have ht := (hpoint (z j)).abs
        simp only [abs_zero] at ht
        exact (ht.eventually (eventually_lt_nhds (show (0 : ℝ) < ε from hε))).mono (fun _ hi => hi.le)
      refine ⟨O,hO,hpO,?_⟩
      filter_upwards [hOi,hsmall,hzsmall] with i hi hsi hzi
      apply (weightedRemainder_lipschitzOn (d i) z (fun j => cutoff (z j) r) hi
        (fun j => cutoff_lipschitz _ _) (sum_cutoff_bounds z hr hdis)
        (fun x hx => (hsi x hx).le) hzi).weaken
      have herr : 2*Fintype.card I*B*ε ≤ η := by
        dsimp [ε]
        have hden : 0 < 2*(Fintype.card I : ℝ≥0)*B+1 := by positivity
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith
      dsimp [B] at herr
      nlinarith
end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal ENNReal
variable {M : Type uM} {I : Type uI} [MetricSpace M] [Zero M] [Fintype I]

theorem test_normalized_sum (f : I → M → ℝ) {C D : ℝ≥0}
    (hf : ∀ j, LipschitzWith C (f j))
    (hs : LipschitzWith D (fun x => ∑ j,f j x)) (μ : FreeSpace.Space M) :
    test (normalized (fun x => ∑ j,f j x) hs) μ =
      ∑ j, test (normalized (f j) (hf j)) μ := by
  classical
  change μ.1 (normalized (fun x => ∑ j,f j x) hs) = ∑ j,μ.1 (normalized (f j) (hf j))
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  funext x
  have hev (s : Finset I) : (∑ j ∈ s,normalized (f j) (hf j)).1 x =
      ∑ j ∈ s,(f j x-f j 0) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs, Finset.sum_insert hjs]
      change (f j x-f j 0)+(∑ k ∈ s,normalized (f k) (hf k)).1 x = _
      rw [ih]
  rw [hev]
  change (∑ j,f j x)-(∑ j,f j 0) = ∑ j,(f j x-f j 0)
  exact (Finset.sum_sub_distrib (fun j => f j x) (fun j => f j 0)).symm

theorem removed_pairings_small {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (d : ℕ → M → ℝ) {L : ℝ≥0}
    (hd : ∀ i, LipschitzWith L (d i)) (z : I → M) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ≥0, ∀ hr : 0 < r, (r : ℝ) < δ →
      ∀ hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)),
      ∀ᶠ i in atTop,
        |test (normalized (removed (d i) z r) (removed_lipschitz (d i) (hd i) z hr hdis)) (μ i)| < ε := by
  classical
  let ε' : ℝ := ε / ((Fintype.card I : ℝ)+1)
  have hε' : 0 < ε' := div_pos hε (by positivity)
  choose δ hδ hsmall using fun j => cutoff_pairings_small (z j) hw d hd hε'
  have hex : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ j, d₀ ≤ δ j := by
    cases isEmpty_or_nonempty I with
    | inl hI => exact ⟨1,by norm_num,fun j => isEmptyElim j⟩
    | inr hI =>
      let D : ℝ := Finset.univ.inf' Finset.univ_nonempty δ
      refine ⟨D,?_,?_⟩
      · exact (Finset.lt_inf'_iff _).mpr (fun j _ => hδ j)
      · intro j
        exact Finset.inf'_le _ (Finset.mem_univ j)
  obtain ⟨δ₀,hδ₀,hδall⟩ := hex
  refine ⟨δ₀,hδ₀,?_⟩
  intro r hr hrad hdis
  have hall : ∀ᶠ i in atTop, ∀ j,
      |test (normalized (fun x => (d i x-d i (z j))*cutoff (z j) r x)
        (cutoff_product_lipschitz (z j) hr _ (lipschitz_sub_const _ (hd i) _) (sub_self _))) (μ i)| < ε' :=
    Filter.eventually_all.mpr (fun j => hsmall j r hr (hrad.trans_le (hδall j)))
  filter_upwards [hall] with i hi
  rw [show test (normalized (removed (d i) z r) (removed_lipschitz (d i) (hd i) z hr hdis)) (μ i) =
    ∑ j, test (normalized (fun x => (d i x-d i (z j))*cutoff (z j) r x)
      (cutoff_product_lipschitz (z j) hr _ (lipschitz_sub_const _ (hd i) _) (sub_self _))) (μ i) from
        test_normalized_sum _ _ _ _]
  calc
    _ ≤ ∑ j, |test (normalized (fun x => (d i x-d i (z j))*cutoff (z j) r x)
      (cutoff_product_lipschitz (z j) hr _ (lipschitz_sub_const _ (hd i) _) (sub_self _))) (μ i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : I, ε' := Finset.sum_le_sum (fun j _ => (hi j).le)
    _ < ε := by
      simp only [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]
      have hid : ε'*((Fintype.card I : ℝ)+1) = ε := by dsimp [ε']; field_simp
      nlinarith
end LipschitzCounterexample.LocalizedLinearization

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology LocalLipschitz
open scoped NNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem scalar_localization (hcompact : FreeSpace.HasCompactReduction (M := M))
    {μ : ℕ → FreeSpace.Space M} (hw : WeakSequences.WeakNull μ)
    (d : ℕ → M → ℝ) {L : ℝ≥0} (hd : ∀ i, LipschitzWith L (d i))
    (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    (hgood : ∀ η : ℝ≥0, 0 < η → ∃ Z : Set M, Z.Finite ∧
      ∀ p, p ∉ Z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
        ∀ᶠ i in atTop, LipschitzOnWith η (d i) O) :
    Tendsto (fun i => test (normalized (d i) (hd i)) (μ i)) atTop (𝓝 0) := by
  classical
  obtain ⟨C,hC⟩ := (show WeakSequences.WeakCauchy μ from fun f => (hw f).cauchySeq).bounded
  have hC0 : 0 ≤ C := (norm_nonneg (μ 0)).trans (hC 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  let τ : ℝ := min 1 (ε/(28*((L : ℝ)+1)))
  have hτ : 0 < τ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτerr : 7*(L : ℝ)*τ ≤ ε/4 := by
    have ht : τ ≤ ε/(28*((L : ℝ)+1)) := min_le_right _ _
    have he := (le_div_iff₀ (show 0 < 28*((L : ℝ)+1) by positivity)).mp ht
    nlinarith [mul_nonneg L.coe_nonneg hτ.le]
  obtain ⟨K,hK,hK0,hν⟩ := hcompact μ hw τ hτ
  choose ν hνK hνdist using hν
  have hνnorm (i : ℕ) : ‖ν i‖ ≤ C+1 := by
    have ht := norm_add_le (μ i) (ν i-μ i)
    rw [add_sub_cancel, norm_sub_rev] at ht
    linarith [hνdist i,hC i]
  let η : ℝ≥0 := ⟨ε/(8*(C+1)),(div_pos hε (by positivity)).le⟩
  have hη : 0 < η := div_pos hε (by positivity)
  have hηerr : 2*(η : ℝ)*(C+1) = ε/4 := by
    change 2*(ε/(8*(C+1)))*(C+1) = ε/4
    field_simp [ne_of_gt (show 0 < C+1 by positivity)]
    ring
  obtain ⟨Z,hZ,hgoodZ⟩ := hgood η hη
  let : Fintype Z := hZ.fintype
  let z : Z → M := Subtype.val
  obtain ⟨r₀,hr₀,hdis₀⟩ := LocalGeometry.exists_disjoint_balls z Subtype.val_injective
  obtain ⟨δ,hδ,hremoved⟩ := removed_pairings_small hw d hd z (show 0 < ε/4 by positivity)
  let r : ℝ≥0 := ⟨min r₀ δ / 2,(half_pos (lt_min hr₀ hδ)).le⟩
  have hr : 0 < r := half_pos (lt_min hr₀ hδ)
  have hr₀' : (r : ℝ) ≤ r₀ := (half_le_self (le_of_lt (lt_min hr₀ hδ))).trans (min_le_left _ _)
  have hrδ : (r : ℝ) < δ := (half_lt_self (lt_min hr₀ hδ)).trans_le (min_le_right _ _)
  have hdis : Pairwise (fun j k => Disjoint (Metric.ball (z j) (r : ℝ)) (Metric.ball (z k) r)) := by
    intro j k hjk
    exact (hdis₀ hjk).mono (Metric.ball_subset_ball hr₀') (Metric.ball_subset_ball hr₀')
  have hR := fun i => remainder_lipschitz (d i) (hd i) z hr hdis
  have hg := fun i => removed_lipschitz (d i) (hd i) z hr hdis
  have hsmallg := hremoved r hr hrδ hdis
  have hsmallR := remainder_compact_lipschitz d hd hpoint z hr hdis hη (by
    intro p hp
    apply hgoodZ p
    simpa only [z,Subtype.range_coe] using hp) hK
  have hevent : ∀ᶠ i in atTop, dist (test (normalized (d i) (hd i)) (μ i)) 0 < ε := by
    filter_upwards [hsmallg,hsmallR] with i hgi hRi
    have hsupp := FreeSpace.supported_pairing_le hK0 (remainder (d i) z r) (hR i) hRi (ν i) (hνK i)
    have herr : |test (normalized (remainder (d i) z r) (hR i)) (μ i-ν i)| ≤ 7*(L : ℝ)*τ := by
      have ht := (norm_test_apply_le (normalized (remainder (d i) z r) (hR i)) (μ i-ν i)).trans
        (mul_le_mul_of_nonneg_right (norm_normalized_le _ (hR i)) (norm_nonneg _))
      rw [Real.norm_eq_abs] at ht
      exact ht.trans (by simpa using mul_le_mul_of_nonneg_left (hνdist i).le (show 0 ≤ 7*(L : ℝ) by positivity))
    have hRv : |test (normalized (remainder (d i) z r) (hR i)) (μ i)| ≤ ε/2 := by
      have ht := abs_add_le (test (normalized (remainder (d i) z r) (hR i)) (ν i))
        (test (normalized (remainder (d i) z r) (hR i)) (μ i-ν i))
      rw [← map_add,add_sub_cancel] at ht
      have hm := mul_le_mul_of_nonneg_left (hνnorm i) (show 0 ≤ 2*(η : ℝ) by positivity)
      norm_num only [NNReal.coe_mul,NNReal.coe_ofNat] at hsupp
      linarith
    have hid : test (normalized (remainder (d i) z r) (hR i)) (μ i) =
        test (normalized (d i) (hd i)) (μ i)-test (normalized (removed (d i) z r) (hg i)) (μ i) :=
      test_normalized_sub (d i) (removed (d i) z r) (hd i) (hg i) (hR i) (μ i)
    have ht := abs_add_le (test (normalized (remainder (d i) z r) (hR i)) (μ i))
      (test (normalized (removed (d i) z r) (hg i)) (μ i))
    rw [Real.dist_eq,sub_zero]
    rw [hid,sub_add_cancel] at ht
    rw [hid] at hRv
    linarith
  exact Filter.eventually_atTop.mp hevent

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
