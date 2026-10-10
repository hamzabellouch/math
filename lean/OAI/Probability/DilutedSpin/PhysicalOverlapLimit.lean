import OAI.Probability.DilutedSpin.PatternComparison
import OAI.Probability.DilutedSpin.PhysicalOverlapAverage

namespace OAI

section
namespace DilutedSpinGlass.UniversalDictionary
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks PhysicalRoot PrescribedTree ConcreteReservoir
open ReducedTopology Filter Set
open scoped NNReal BigOperators Topology
noncomputable local instance physicalOverlapLimitDecidableEq (carrier : Type) :
    DecidableEq carrier := Classical.decEq carrier
variable {p L : ℕ}

noncomputable def physicalOverlapLimsup (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) : ℝ :=
  limsup (fun n => physicalOverlapAverage M C H (Ns n+1) L (us n) S η) atTop

lemma physicalOverlapLimsup_nonneg (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    0≤physicalOverlapLimsup M C H L Ns us S η :=
  unit_limsup_nonneg (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S η)
    (fun n => physicalOverlapAverage_le_one M C H (Ns n+1) L (us n) S η)

lemma physicalOverlapLimsup_le_one (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) (η : ℝ) :
    physicalOverlapLimsup M C H L Ns us S η≤1 :=
  unit_limsup_le_one (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S η)
    (fun n => physicalOverlapAverage_le_one M C H (Ns n+1) L (us n) S η)

lemma physicalOverlapLimsup_bound {M : Model p} {C H : ℝ}
    {Ns : ℕ → ℕ} {us : ℕ → Spec L×ℕ → ℝ} (h : FullShapeControl M C H L Ns us)
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) (hη1 : η≤1) (hlarge : 8<η*(L+1:ℕ)) :
    (η/8)*physicalOverlapLimsup M C H L Ns us S η≤
      Real.sqrt (physicalShapeLimsup M C H L Ns us S (η/8)) := by
  have he : Tendsto (fun n => DepthAverage.average (regularShapeDomain S (L+1) (η/8))
      (fun Q => |physicalMarkerDefect M C H (Ns n+1) L (us n) S Q|)) atTop (𝓝 0) := by
    apply DepthAverage.tendsto_average_zero
    intro Q
    simpa only [abs_zero] using (h.markerDefect S Q).abs
  apply limsup_sqrt_error_bound _ _ _ (by positivity)
    (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S η)
    (fun n => physicalShapeAverage_le_one M C H (Ns n+1) L (us n) S (η/8)) he
  intro n
  exact physicalOverlapAverage_le_marker M C H (Ns n+1) L (us n) S hη hη1 hlarge

lemma physicalOverlapLimsup_antitone (M : Model p) (C H : ℝ) (L : ℕ)
    (Ns : ℕ → ℕ) (us : ℕ → Spec L×ℕ → ℝ) (S : ReducedTopology) :
    Antitone (physicalOverlapLimsup M C H L Ns us S) := by
  intro η ε hηε
  have hab (n : ℕ) : physicalOverlapAverage M C H (Ns n+1) L (us n) S ε≤
      physicalOverlapAverage M C H (Ns n+1) L (us n) S η := by
    apply DepthAverage.average_domain_bound
    · intro q hq
      refine ⟨⟨?_,?_⟩,hq.2⟩
      · intro v
        have hv := hq.1.1 v
        constructor <;> linarith
      · intro v w hvw
        exact hηε.trans_lt (hq.1.2 v w hvw)
    · intro q _; rfl
    · exact physicalOverlapVariance_nonneg M C H (Ns n+1) L (us n) S
  exact limsup_le_limsup (Eventually.of_forall hab)
    (IsCoboundedUnder.of_frequently_ge
      ((Eventually.of_forall (fun n => physicalOverlapAverage_nonneg M C H (Ns n+1) L (us n) S ε)).frequently))
    (isBoundedUnder_of_eventually_le
      (Eventually.of_forall (fun n => physicalOverlapAverage_le_one M C H (Ns n+1) L (us n) S η)))

lemma eventually_large_overlap_grid {η : ℝ} (hη : 0<η) :
    ∀ᶠ L : ℕ in atTop, 8<η*((L+1:ℕ):ℝ) := by
  obtain ⟨n,hn⟩ := exists_nat_gt (8/η)
  filter_upwards [eventually_ge_atTop n] with L hL
  have hc : (n:ℝ)≤((L+1:ℕ):ℝ) := by exact_mod_cast (show n≤L+1 by omega)
  have hd := (div_lt_iff₀ hη).mp (hn.trans_le hc)
  simpa only [mul_comm] using hd

/-- All root, auxiliary and thermal randomness are concentrated. Branch depths
alone are averaged; the topology and model are arbitrary and unchanged. -/
theorem physicalOverlapLimsup_tendsto (M : Model p) (C H : ℝ)
    (Ns : ℕ → ℕ → ℕ) (us : (L : ℕ) → ℕ → Spec L×ℕ → ℝ)
    (hcontrol : ∀ L, FullShapeControl M C H L (Ns L) (us L))
    (S : ReducedTopology) {η : ℝ} (hη : 0<η) :
    Tendsto (fun L => physicalOverlapLimsup M C H L (Ns L) (us L) S η) atTop (𝓝 0) := by
  let ε := min η 1
  have hε : 0<ε := lt_min hη (by norm_num)
  have hε1 : ε≤1 := min_le_right _ _
  have hs := (physicalShapeLimsup_tendsto M C H Ns us (fun L => (hcontrol L).scheduled)
    S (by positivity : 0<ε/8)).sqrt.div_const (ε/8)
  have hs' : Tendsto (fun L => Real.sqrt (physicalShapeLimsup M C H L (Ns L) (us L) S (ε/8))/(ε/8))
      atTop (𝓝 0) := by simpa using hs
  apply squeeze_zero' (Eventually.of_forall (fun L => physicalOverlapLimsup_nonneg M C H L (Ns L) (us L) S η)) _ hs'
  filter_upwards [eventually_large_overlap_grid hε] with L hL
  apply (physicalOverlapLimsup_antitone M C H L (Ns L) (us L) S (min_le_left _ _)).trans
  apply (le_div_iff₀ (by positivity : 0<ε/8)).mpr
  rw [mul_comm]
  exact physicalOverlapLimsup_bound (hcontrol L) S hε hε1 hL

end DilutedSpinGlass.UniversalDictionary

end

end OAI
