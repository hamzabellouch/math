import Mathlib
import OAI.Probability.SLE.DiskHalfPlane
import OAI.Probability.SLE.StoppedMeasures

namespace OAI

/-! Chart Measurability for chordal SLE. -/

section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_killedChart_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (fun ω => if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0) := by
  exact measurable_stoppedValue
    (source_killedChart_progressive hm hc κ γ G F hw z) hτ

end
end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex TopologicalSpace Classical
open scoped Topology NNReal
namespace SLEExactGauge

lemma source_measurable_inverse_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (S : Ω → Set ℂ) (G F K : Ω → ℂ → ℂ) (H : Set ℂ)
    (hS : ∀ ω, IsOpen (S ω)) (hH : IsOpen H)
    (hG : ∀ ω, ContinuousOn (G ω) (S ω))
    (hF : ∀ ω, ContinuousOn (F ω) H)
    (hFH : ∀ ω, MapsTo (F ω) H (S ω))
    (hGF : ∀ ω z, z ∈ H → G ω (F ω z) = z)
    (hFG : ∀ ω z, z ∈ S ω → F ω (G ω z) = z)
    (hK : ∀ z, Measurable (fun ω => K ω z))
    (hKeq : ∀ ω z, K ω z = if z ∈ S ω then G ω z else 0)
    (hGH : ∀ ω z, z ∈ S ω → 0 < (G ω z).im)
    (w : Ω → ℂ) (hwm : Measurable w) (hw : ∀ ω, w ω ∈ H) :
    Measurable (fun ω => F ω (w ω)) := by
  classical
  let d := denseSeq ℂ
  let v (k : ℕ) (ω : Ω) (n : ℕ) : Prop :=
    0 < (K ω (d n)).im ∧ dist (K ω (d n)) (w ω) < 1/((k:ℝ)+1)
  have hv (k : ℕ) (ω : Ω) : ∃ n, v k ω n := by
    have hpos : 0 < 1/((k:ℝ)+1) := by positivity
    have hx : F ω (w ω) ∈ S ω := hFH ω (hw ω)
    have hct := (hG ω).continuousAt ((hS ω).mem_nhds hx)
    have hn : {z | dist (G ω z) (w ω) < 1/((k:ℝ)+1)} ∈ 𝓝 (F ω (w ω)) := by
      change G ω ⁻¹' Metric.ball (w ω) (1/((k:ℝ)+1)) ∈ 𝓝 (F ω (w ω))
      apply hct.preimage_mem_nhds
      rw [hGF ω _ (hw ω)]
      exact Metric.ball_mem_nhds (w ω) hpos
    obtain ⟨n,hn⟩ := (denseRange_denseSeq ℂ).mem_nhds (inter_mem ((hS ω).mem_nhds hx) hn)
    refine ⟨n,?_⟩
    dsimp [v,d]
    rw [hKeq,ite_eq_left hn.1]
    exact ⟨hGH ω _ hn.1,hn.2⟩
  have hvm (k n : ℕ) : MeasurableSet {ω | v k ω n} :=
    (measurableSet_lt measurable_const (Complex.measurable_im.comp (hK _))).inter
      (measurableSet_lt ((hK _).dist hwm) measurable_const)
  let j (k : ℕ) (ω : Ω) : ℕ := Nat.find (hv k ω)
  have hj (k : ℕ) : Measurable (j k) := measurable_find (hv k) (hvm k)
  have hjv (k : ℕ) (ω : Ω) : v k ω (j k ω) := Nat.find_spec (hv k ω)
  have hjS (k : ℕ) (ω : Ω) : d (j k ω) ∈ S ω := by
    by_contra hn
    have hh := (hjv k ω).1
    rw [hKeq,ite_eq_right hn] at hh
    norm_num at hh
  have hlim (ω : Ω) : Tendsto (fun k => K ω (d (j k ω))) atTop (𝓝 (w ω)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
    refine ⟨N,fun k hk => (hjv k ω).2.trans ?_⟩
    simpa only [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < 1/((k:ℝ)+1))]
      using hN k hk
  have hflim (ω : Ω) : Tendsto (fun k => d (j k ω)) atTop (𝓝 (F ω (w ω))) := by
    have hh := ((hF ω).continuousAt (hH.mem_nhds (hw ω))).tendsto.comp (hlim ω)
    convert hh using 1
    ext k
    simp only [Function.comp_apply,hKeq,ite_eq_left (hjS k ω),hFG ω _ (hjS k ω)]
  exact measurable_of_tendsto_metrizable (fun k => (measurable_of_countable d).comp (hj k)) (tendsto_pi_nhds.mpr hflim)
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal
namespace SLEExactGauge
lemma source_stopped_inverseChart_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (w : Ω → ℂ)
    (hwm : Measurable[hτ.measurableSpace] w) (hwH : ∀ ω, w ω ∈ upperHalfPlane) :
    Measurable[hτ.measurableSpace] (fun ω => F ω (τ ω) (w ω)) := by
  apply @source_measurable_inverse_chart Ω hτ.measurableSpace
    (fun ω => survivingDomain (γ ω) (τ ω)) (fun ω => G ω (τ ω))
    (fun ω => F ω (τ ω))
    (fun ω z => if z ∈ survivingDomain (γ ω) (τ ω) then G ω (τ ω) z else 0)
    upperHalfPlane
    (fun ω => isOpen_survivingDomain (hw ω).1 _) isOpen_upperHalfPlane
    (fun ω => ((hw ω).2.2.2.1 _).continuousOn)
    (fun ω => ((hw ω).2.2.2.2.1 _).continuousOn)
    (fun ω => (hw ω).2.2.2.2.2.2.1 _)
    (fun ω => (hw ω).2.2.2.2.2.2.2.2.1 _)
    (fun ω => (hw ω).2.2.2.2.2.2.2.1 _)
    (fun z => source_killedChart_stopped_measurable hm hc κ γ G F hw z τ hτ)
    (fun _ _ => rfl)
    (fun ω z hz => (hw ω).imag_positive _ z hz) w hwm hwH
end SLEExactGauge

end

section
open Set Filter MeasureTheory ProbabilityTheory Complex Classical TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
local instance : MeasurableSpace C(upperHalfPlane,ℂ) := borel _
local instance : BorelSpace C(upperHalfPlane,ℂ) := ⟨rfl⟩

lemma source_halfplane_cmap_measurable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → C(upperHalfPlane,ℂ))
    (hf : ∀ z, Measurable (fun ω => f ω z)) : Measurable f := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  let : PolishSpace upperHalfPlane := isOpen_upperHalfPlane.polishSpace
  let : Nonempty upperHalfPlane := ⟨⟨Complex.I,by simp [upperHalfPlane]⟩⟩
  have he : MeasurableEmbedding
      (fun F : C(upperHalfPlane,ℂ) => fun n => F (denseSeq upperHalfPlane n)) := by
    apply Continuous.measurableEmbedding
    · exact continuous_pi fun n => continuous_eval_const _
    · intro F G heq
      apply DFunLike.coe_injective
      exact (denseRange_denseSeq upperHalfPlane).equalizer F.continuous G.continuous heq
  exact he.measurable_comp_iff.mp (Measurable.of_eval (fun _ => hf _))

def sourceStoppedInversePath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0) (ω : Ω) : C(upperHalfPlane,ℂ) :=
  ⟨fun z => F ω (τ ω) (z + (Real.sqrt κ * B (τ ω) ω : ℝ)),
    ContinuousOn.comp_continuous ((hw ω).2.2.2.2.1 _).continuousOn
      (continuous_subtype_val.add continuous_const)
      (fun z => by simpa [upperHalfPlane] using z.2)⟩

lemma source_stopped_inversePath_measurable
    {Ω : Type*} [m : MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (sourceStoppedInversePath B κ γ G F hw τ) := by
  apply @source_halfplane_cmap_measurable Ω hτ.measurableSpace
  intro z
  have hB := measurable_stoppedValue
    ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc) hτ
  apply source_stopped_inverseChart_measurable B hm hc κ γ G F hw τ hτ
    (fun ω => z+(Real.sqrt κ * B (τ ω) ω : ℝ))
  · exact measurable_const.add (Complex.measurable_ofReal.comp (measurable_const.mul hB))
  · intro ω
    simpa [upperHalfPlane] using z.2
end
end SLEExactGauge

end

section
open Set Filter MeasureTheory Metric Bornology
open scoped Topology NNReal
namespace SLEExactGauge
 

def square (R : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ |z.im| ≤ R}

def upperExterior (R : ℝ) : Set ℂ := upperHalfPlane ∩ (square R)ᶜ

def lowerExterior (R : ℝ) : Set ℂ := {z | z.im ≤ 0} ∩ (square R)ᶜ

lemma square_isCompact (R : ℝ) : IsCompact (square R) := by
  have hc : IsClosed (square R) :=
    (isClosed_le Complex.continuous_re.abs continuous_const).inter
      (isClosed_le Complex.continuous_im.abs continuous_const)
  apply isCompact_of_isClosed_isBounded hc
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2*R,fun z hz => ?_⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith [hz.1,hz.2])

lemma bounded_subset_square {s : Set ℂ} (hs : Bornology.IsBounded s) :
    ∃ R > 0, s ⊆ square R := by
  obtain ⟨C,hC⟩ := hs.exists_norm_le
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro z hz
  exact ⟨(Complex.abs_re_le_norm z).trans ((hC z hz).trans (le_max_left _ _)),
    (Complex.abs_im_le_norm z).trans ((hC z hz).trans (le_max_left _ _))⟩

lemma upperExterior_eq (R : ℝ) (hR : 0 ≤ R) : upperExterior R =
    ({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∪ {z | R < z.im} ∪
    ({z : ℂ | R < z.re} ∩ {z | 0 < z.im}) := by
  ext z
  simp only [upperExterior,upperHalfPlane,square,mem_inter_iff,mem_ofPred_eq,
    mem_compl_iff,mem_union,abs_le]
  constructor
  · rintro ⟨hi,hs⟩
    by_cases hl : z.re < -R
    · exact Or.inl (Or.inl ⟨hl,hi⟩)
    by_cases hr : R < z.re
    · exact Or.inr ⟨hr,hi⟩
    exact Or.inl (Or.inr (by by_contra hn; exact hs ⟨⟨by linarith,by linarith⟩,
      ⟨by linarith,by linarith⟩⟩))
  · rintro ((⟨hl,hi⟩ | hi) | ⟨hr,hi⟩)
    · exact ⟨hi,fun hs => (not_lt_of_ge hs.1.1) hl⟩
    · exact ⟨by linarith,fun hs => (not_lt_of_ge hs.2.2) hi⟩
    · exact ⟨hi,fun hs => (not_lt_of_ge hs.1.2) hr⟩

lemma upperExterior_preconnected (R : ℝ) (hR : 0 ≤ R) : IsPreconnected (upperExterior R) := by
  rw [upperExterior_eq R hR]
  have hL := ((convex_halfSpace_re_lt (-R)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hU := (convex_halfSpace_im_gt R).isPreconnected
  have hV := ((convex_halfSpace_re_gt R).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hLU : (({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∩ {z | R < z.im}).Nonempty := by
    refine ⟨⟨-R-1,R+1⟩,?_,?_⟩ <;> simp only [mem_inter_iff,mem_ofPred_eq] <;> (try constructor) <;> linarith
  have hUV : ((({z : ℂ | z.re < -R} ∩ {z | 0 < z.im}) ∪ {z | R < z.im}) ∩
      ({z : ℂ | R < z.re} ∩ {z | 0 < z.im})).Nonempty := by
    refine ⟨⟨R+1,R+1⟩,Or.inr ?_,?_,?_⟩ <;> simp only [mem_ofPred_eq] <;> linarith
  exact (hL.union' hLU hU).union' hUV hV

lemma upperExterior_unbounded (R : ℝ) (hR : 0 ≤ R) : ¬ Bornology.IsBounded (upperExterior R) := by
  intro hb
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  let y : ℝ := max C R + 1
  have hyR : R < y := by dsimp [y]; linarith [le_max_right C R]
  have hyC : C < y := by dsimp [y]; linarith [le_max_left C R]
  have hy0 : 0 < y := by linarith
  have hm : (⟨0,y⟩ : ℂ) ∈ upperExterior R := by
    exact ⟨hy0,fun h => (not_le_of_gt hyR) ((le_abs_self y).trans h.2)⟩
  have hb' := hC _ hm
  have hn := Complex.abs_im_le_norm (⟨0,y⟩ : ℂ)
  change |y| ≤ ‖(⟨0,y⟩ : ℂ)‖ at hn
  rw [abs_of_pos hy0] at hn
  linarith

lemma upperExterior_subset_survivingDomain {γ : ℝ≥0 → ℂ} {T : ℝ≥0} {R : ℝ}
    (hR : 0 ≤ R) (hγ : γ '' Icc 0 T ⊆ square R) :
    upperExterior R ⊆ survivingDomain γ T := by
  intro z hz
  have hs : upperExterior R ⊆ upperHalfPlane \ (γ '' Icc 0 T) := by
    intro w hw
    exact ⟨hw.1,fun ht => hw.2 (hγ ht)⟩
  refine ⟨hs hz,?_⟩
  intro hb
  exact upperExterior_unbounded R hR (hb.subset
    ((upperExterior_preconnected R hR).subset_connectedComponentIn hz hs))

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

lemma source_live_compact_bridge (γ : C(ℝ≥0,ℂ)) (t : ℝ≥0) (z : ℂ)
    (hz : z ∈ survivingDomain γ t) :
    ∃ (R δ : ℝ) (K : Set ℂ), 0 < R ∧ 0 < δ ∧ IsCompact K ∧
      IsPreconnected K ∧ Metric.closedBall z δ ⊆ K ∧
      (⟨0,R+1⟩ : ℂ) ∈ K ∧ K ⊆ upperHalfPlane ∧
      MapsTo γ (Icc 0 t) (Metric.ball 0 R \ K) := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.image γ.continuous).isBounded.exists_norm_le
  let R := max M 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right M 0]
  have hnorm (s : ℝ≥0) (hs : s ∈ Icc 0 t) : ‖γ s‖ < R := by
    have hh := hM _ ⟨s,hs,rfl⟩
    dsimp [R]; linarith [le_max_left M 0]
  have htr : γ '' Icc 0 t ⊆ square R := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨(abs_re_le_norm _).trans (hnorm s hs).le,(abs_im_le_norm _).trans (hnorm s hs).le⟩
  let A : Set ℂ := upperHalfPlane \ γ '' Icc 0 t
  let C := connectedComponentIn A z
  have hA : IsOpen A := isOpen_upperHalfPlane.sdiff (isCompact_Icc.image γ.continuous).isClosed
  have hzC : z ∈ C := mem_connectedComponentIn hz.1
  have hCsub : C ⊆ A := connectedComponentIn_subset _ _
  have hnot : ¬ C ⊆ square R := fun hh => hz.2 ((square_isCompact R).isBounded.subset hh)
  obtain ⟨v,hv,hvR⟩ := Set.not_subset.mp hnot
  have hvE : v ∈ upperExterior R := ⟨(hCsub hv).1,hvR⟩
  have hEsub : upperExterior R ⊆ A := by
    intro w hw
    exact ⟨hw.1,fun ht => hw.2 (htr ht)⟩
  have hEC : upperExterior R ⊆ C := by
    have hc := (upperExterior_preconnected R hR.le).subset_connectedComponentIn hvE hEsub
    rwa [← connectedComponentIn_eq hv] at hc
  let p : ℂ := ⟨0,R+1⟩
  have hpE : p ∈ upperExterior R := by
    refine ⟨by change 0 < R+1; linarith,?_⟩
    intro hh
    have hhi : |R+1| ≤ R := hh.2
    linarith [le_abs_self (R+1)]
  have hpathc : IsPathConnected C := (hA.connectedComponentIn).isConnected_iff_isPathConnected.mp
    ⟨⟨z,hzC⟩,isPreconnected_connectedComponentIn⟩
  let η := (hpathc.joinedIn z hzC p (hEC hpE)).somePath
  have hη : range η ⊆ A := by
    rintro _ ⟨s,rfl⟩
    exact hCsub ((hpathc.joinedIn z hzC p (hEC hpE)).somePath_mem s)
  obtain ⟨ε,hε,hεsub⟩ := Metric.isOpen_iff.mp hA z hz.1
  let δ := ε/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hball : Metric.closedBall z δ ⊆ A := by
    apply subset_trans _ hεsub
    exact Metric.closedBall_subset_ball (by dsimp [δ]; linarith)
  let K := range η ∪ Metric.closedBall z δ
  have hKc : IsCompact K := (isCompact_range η.continuous).union (isCompact_closedBall z δ)
  have hKconn : IsPreconnected K :=
    (isConnected_range η.continuous).2.union z η.source_mem_range (Metric.mem_closedBall_self hδ.le)
      (convex_closedBall z δ).isPreconnected
  have hKsub : K ⊆ A := union_subset hη hball
  refine ⟨R,δ,K,hR,hδ,hKc,hKconn,subset_union_right,
    Or.inl η.target_mem_range,fun w hw => (hKsub hw).1,?_⟩
  intro s hs
  refine ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hnorm s hs,?_⟩
  intro hh
  exact (hKsub hh).2 ⟨s,hs,rfl⟩

 

lemma source_live_of_bridge {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {z : ℂ} {R : ℝ} {K : Set ℂ}
    (hR : 0 ≤ R) (hK : IsPreconnected K) (hz : z ∈ K)
    (hp : (⟨0,R+1⟩ : ℂ) ∈ K) (hKH : K ⊆ upperHalfPlane)
    (hγ : MapsTo γ (Icc 0 t) (Metric.ball 0 R \ K)) :
    z ∈ survivingDomain γ t := by
  have hnorm (s : ℝ≥0) (hs : s ∈ Icc 0 t) : ‖γ s‖ < R := by
    simpa only [Metric.mem_ball,dist_zero_right] using (hγ hs).1
  have htr : γ '' Icc 0 t ⊆ square R := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨(abs_re_le_norm _).trans (hnorm s hs).le,(abs_im_le_norm _).trans (hnorm s hs).le⟩
  have hpE : (⟨0,R+1⟩ : ℂ) ∈ upperExterior R := by
    refine ⟨by change 0 < R+1; linarith,?_⟩
    intro hh
    have hhi : |R+1| ≤ R := hh.2
    linarith [le_abs_self (R+1)]
  have hpS := upperExterior_subset_survivingDomain hR htr hpE
  have hKa : K ⊆ upperHalfPlane \ γ '' Icc 0 t := by
    intro w hw
    refine ⟨hKH hw,?_⟩
    rintro ⟨s,hs,rfl⟩
    exact (hγ hs).2 hw
  have hpC := hK.subset_connectedComponentIn hz hKa hp
  refine ⟨hKa hz,?_⟩
  rw [connectedComponentIn_eq hpC]
  exact hpS.2

noncomputable def sourceRescaledPath (p : C(ℝ≥0,ℂ) × ℝ≥0) : C(ℝ≥0,ℂ) :=
  ⟨fun s => p.1 (p.2*s),p.1.continuous.comp (continuous_const.mul continuous_id)⟩

lemma sourceRescaledPath_continuous : Continuous sourceRescaledPath := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp
    ((continuous_fst.fst).prodMk ((continuous_fst.snd).mul continuous_snd))

lemma sourceRescaledPath_mapsTo {p : C(ℝ≥0,ℂ) × ℝ≥0} {A : Set ℂ} :
    MapsTo (sourceRescaledPath p) (Icc 0 1) A ↔ MapsTo p.1 (Icc 0 p.2) A := by
  have he : (fun s : ℝ≥0 => p.2*s) '' Icc 0 1 = Icc 0 p.2 := by
    simpa using image_mul_left_Icc (show 0 ≤ p.2 from bot_le) (show (0 : ℝ≥0) ≤ 1 by norm_num)
  rw [← he]
  constructor
  · intro h v hv
    rcases hv with ⟨s,hs,rfl⟩
    exact h hs
  · intro h s hs
    exact h ⟨s,hs,rfl⟩

lemma source_survival_open :
    IsOpen {p : (C(ℝ≥0,ℂ) × ℝ≥0) × ℂ | p.2 ∈ survivingDomain p.1.1 p.1.2} := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro ⟨⟨γ,t⟩,z⟩ hz
  obtain ⟨R,δ,K,hR,hδ,hKc,hKconn,hball,hp,hKH,hγ⟩ := source_live_compact_bridge γ t z hz
  let W : Set (C(ℝ≥0,ℂ) × ℝ≥0) := {p | MapsTo p.1 (Icc 0 p.2) (Metric.ball 0 R \ K)}
  have hWo : IsOpen W := by
    have hh := (ContinuousMap.isOpen_setOfPred_mapsTo (K := Icc (0 : ℝ≥0) 1) (U := Metric.ball (0 : ℂ) R \ K) isCompact_Icc
      (Metric.isOpen_ball.sdiff hKc.isClosed)).preimage sourceRescaledPath_continuous
    convert hh using 1
    ext p
    exact sourceRescaledPath_mapsTo.symm
  refine ⟨W ×ˢ Metric.ball z δ,?_,hWo.prod Metric.isOpen_ball,⟨hγ,Metric.mem_ball_self hδ⟩⟩
  rintro ⟨⟨β,s⟩,w⟩ ⟨hβ,hw⟩
  exact source_live_of_bridge hR.le hKconn (hball (Metric.ball_subset_closedBall hw)) hp hKH hβ

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge
abbrev SourceDiskParameter := (C(upperHalfPlane,ℂ) × ℂ) × (ℂ × ℝ)

lemma source_physical_disk_kernel_open :
  IsOpen {p : SourceDiskParameter × C(ℝ≥0,ℂ) |
    ∃ t : ℝ≥0, p.1.1.2 ∈ survivingDomain p.2 t ∧
      ∃ h : p.2 t ∈ upperHalfPlane,
        p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩ - p.1.2.1‖} := by
  let : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace
  have ht (t : ℝ≥0) :
      IsOpen {p : SourceDiskParameter × C(ℝ≥0,ℂ) |
        p.1.1.2 ∈ survivingDomain p.2 t ∧
          ∃ h : p.2 t ∈ upperHalfPlane,
            p.1.2.2 < ‖p.1.1.1 ⟨p.2 t,h⟩ - p.1.2.1‖} := by
    let S : Set (SourceDiskParameter × C(ℝ≥0,ℂ)) := {p | p.2 t ∈ upperHalfPlane}
    have hS : IsOpen S := isOpen_upperHalfPlane.preimage
      ((continuous_eval_const t).comp continuous_snd)
    let Z : S → upperHalfPlane := fun p => ⟨p.1.2 t,p.2⟩
    have hZ : Continuous Z := Continuous.subtype_mk
      ((continuous_eval_const t).comp (continuous_snd.comp continuous_subtype_val)) _
    have hF : Continuous (fun p : S => p.1.1.1.1 (Z p)) :=
      continuous_eval.comp
        ((continuous_fst.fst.fst.comp continuous_subtype_val).prodMk hZ)
    have hLive : IsOpen {p : S | p.1.1.1.2 ∈ survivingDomain p.1.2 t} :=
      source_survival_open.preimage
        (((continuous_snd.comp continuous_subtype_val).prodMk continuous_const).prodMk
          (continuous_fst.fst.snd.comp continuous_subtype_val))
    have hExit : IsOpen {p : S | p.1.1.2.2 < ‖p.1.1.1.1 (Z p) - p.1.1.2.1‖} :=
      isOpen_lt (continuous_fst.snd.snd.comp continuous_subtype_val)
        ((hF.sub (continuous_fst.snd.fst.comp continuous_subtype_val)).norm)
    have hO := hS.isOpenMap_subtype_val _ (hLive.inter hExit)
    convert hO using 1
    ext p
    constructor
    · rintro ⟨hl,h,he⟩
      exact ⟨⟨p,h⟩,⟨hl,he⟩,rfl⟩
    · rintro ⟨q,⟨hl,he⟩,rfl⟩
      exact ⟨hl,q.2,he⟩
  simpa only [ofPred_exists] using isOpen_iUnion ht
end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma source_high_vertical_survives {γ : ℝ≥0 → ℂ} {t : ℝ≥0} {R : ℝ}
    (hR : 0 ≤ R) (hb : ∀ s ∈ Icc 0 t, ‖γ s‖ ≤ R) {y : ℝ} (hy : R < y) :
    (⟨0,y⟩ : ℂ) ∈ survivingDomain γ t := by
  let A : Set ℂ := {z | R < z.im}
  have hA : A ⊆ upperHalfPlane \ γ '' Icc 0 t := by
    intro z hz
    refine ⟨lt_of_le_of_lt hR hz, ?_⟩
    rintro ⟨s,hs,rfl⟩
    have hh := (le_abs_self (γ s).im).trans ((Complex.abs_im_le_norm _).trans (hb s hs))
    exact (not_lt_of_ge hh) hz
  refine ⟨hA hy, ?_⟩
  intro hbd
  obtain ⟨C,hC⟩ := (hbd.subset ((convex_halfSpace_im_gt R).isPreconnected.subset_connectedComponentIn hy hA)).exists_norm_le
  let v : ℝ := max C R + 1
  have hv : R < v := by dsimp [v]; linarith [le_max_right C R]
  have hvC : C < v := by dsimp [v]; linarith [le_max_left C R]
  have hh := hC (⟨0,v⟩ : ℂ) hv
  have hh' := Complex.abs_im_le_norm (⟨0,v⟩ : ℂ)
  change |v| ≤ _ at hh'
  linarith [le_abs_self v]

lemma IsCapacityTwoWitness.source_later_image_unbounded
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) :
    ¬ Bornology.IsBounded ((fun z => G T z - (U T : ℂ)) '' survivingDomain γ (T+t)) := by
  intro hbd
  obtain ⟨C,hC⟩ := hbd.exists_norm_le
  obtain ⟨R,hR⟩ := (isCompact_Icc.image h.1).isBounded.exists_norm_le
  have hb : ∀ s ∈ Icc 0 (T+t), ‖γ s‖ ≤ max R 0 := by
    intro s hs
    exact (hR _ ⟨s,hs,rfl⟩).trans (le_max_left _ _)
  have hlim := h.2.2.2.2.2.2.2.2.2.2.2.1 T
  have hnorm := hlim.norm
  have he : ∀ᶠ z in cocompact ℂ, z ∈ survivingDomain γ T →
      ‖z * (G T z - z)‖ < ‖(2 : ℂ)*(T : ℂ)‖ + 1 := by
    apply eventually_inf_principal.mp
    exact (tendsto_order.mp hnorm).2 _ (lt_add_one _)
  obtain ⟨K,hK,hKe⟩ := mem_cocompact.mp he
  obtain ⟨D,hD⟩ := hK.isBounded.exists_norm_le
  let A : ℝ := ‖(2 : ℂ)*(T : ℂ)‖ + 1
  let y : ℝ := max (max (max R 0) D) (max A (C + |U T|)) + 2
  have hyR : max R 0 < y := by dsimp [y]; linarith [le_max_left (max R 0) D,le_max_left (max (max R 0) D) (max A (C+|U T|))]
  have hyD : D < y := by dsimp [y]; linarith [le_max_right (max R 0) D,le_max_left (max (max R 0) D) (max A (C+|U T|))]
  have hyA : A < y := by dsimp [y]; linarith [le_max_left A (C+|U T|),le_max_right (max (max R 0) D) (max A (C+|U T|))]
  have hyC : C + |U T| + 1 < y := by dsimp [y]; linarith [le_max_right A (C+|U T|),le_max_right (max (max R 0) D) (max A (C+|U T|))]
  have hy0 : 0 < y := lt_of_le_of_lt (le_max_right R 0) hyR
  let z : ℂ := ⟨0,y⟩
  have hnz : ‖z‖ = y := by simp [z,Complex.norm_def,Real.sqrt_mul_self hy0.le]
  have hz : z ∈ survivingDomain γ (T+t) := source_high_vertical_survives (le_max_right R 0) hb hyR
  have hzt : z ∈ survivingDomain γ T := survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le)) hz
  have hzK : z ∈ Kᶜ := by intro h'; have := hD z h'; rw [hnz] at this; linarith
  have hsmall := hKe hzK hzt
  have hG : ‖G T z‖ ≤ C + |U T| := by
    calc
      ‖G T z‖ = ‖(G T z-(U T : ℂ))+(U T : ℂ)‖ := by rw [sub_add_cancel]
      _ ≤ ‖G T z-(U T : ℂ)‖+‖(U T : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |U T| := by gcongr; exact hC _ ⟨z,hz,rfl⟩; simp
  have htri := norm_sub_norm_le z (G T z)
  rw [hnz,norm_sub_rev] at htri
  rw [norm_mul,hnz] at hsmall
  change y*‖G T z-z‖ < A at hsmall
  have hpos : 0 < A := by dsimp [A]; positivity
  nlinarith

lemma IsCapacityTwoWitness.source_surviving_preconnected
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (t : ℝ≥0) :
    IsPreconnected (survivingDomain γ t) := by
  have he : F t '' upperHalfPlane = survivingDomain γ t := by
    apply Subset.antisymm
    · rintro _ ⟨w,hw,rfl⟩
      exact h.2.2.2.2.2.2.1 t hw
    · intro z hz
      exact ⟨G t z,h.2.2.2.2.2.1 t hz,h.2.2.2.2.2.2.2.1 t z hz⟩
  rw [← he]
  exact (convex_halfSpace_im_gt 0).isPreconnected.image _ (h.2.2.2.2.1 t).continuousOn

lemma source_stopped_live_transfer
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T t : ℝ≥0) (β : ℝ≥0 → ℂ)
    (hid : ∀ s ∈ Icc 0 t, β s ∈ upperHalfPlane →
      γ (T+s) = F T (β s + (U T : ℂ)))
    (z : ℂ) (hz : z ∈ survivingDomain γ (T+t)) :
    G T z - (U T : ℂ) ∈ survivingDomain β t := by
  let f : ℂ → ℂ := fun z => G T z - (U T : ℂ)
  let D := survivingDomain γ (T+t)
  have hsub : D ⊆ survivingDomain γ T :=
    survivingDomain_antitone γ (le_add_of_nonneg_right (show 0 ≤ t from bot_le))
  have hmap : f '' D ⊆ upperHalfPlane \ β '' Icc 0 t := by
    rintro w ⟨v,hv,rfl⟩
    have hvT := hsub hv
    have him : f v ∈ upperHalfPlane := by
      simpa only [f,upperHalfPlane,mem_ofPred_eq,sub_im,ofReal_im,sub_zero]
        using h.2.2.2.2.2.1 T hvT
    refine ⟨him,?_⟩
    rintro ⟨s,hs,he⟩
    have hβ : β s ∈ upperHalfPlane := he ▸ him
    have hv' : γ (T+s) = v := by
      rw [hid s hs hβ,he]
      simp only [f,sub_add_cancel,h.2.2.2.2.2.2.2.1 T v hvT]
    exact hv.1.2 ⟨T+s,⟨bot_le,by simpa only [add_comm] using add_le_add_left hs.2 T⟩,hv'⟩
  have hconn : IsPreconnected (f '' D) :=
    (h.source_surviving_preconnected (T+t)).image _
      (((h.2.2.2.1 T).continuousOn.mono hsub).sub continuousOn_const)
  have hmem : f z ∈ f '' D := ⟨z,hz,rfl⟩
  refine ⟨hmap hmem,?_⟩
  intro hb
  exact h.source_later_image_unbounded T t
    (hb.subset (hconn.subset_connectedComponentIn hmem hmap))

end SLEExactGauge

end

section
open Set Filter MeasureTheory Complex TopologicalSpace
open scoped Topology NNReal
namespace SLEExactGauge
noncomputable section
local instance : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩

def SourcePathInteriorDense (β : C(ℝ≥0,ℂ)) : Prop :=
  ∀ s t : ℝ≥0, s < t → ∃ u ∈ Ioo s t, 0 < (β u).im

lemma source_path_interior_dense_measurable :
    MeasurableSet {β : C(ℝ≥0,ℂ) | SourcePathInteriorDense β} := by
  have he : {β : C(ℝ≥0,ℂ) | SourcePathInteriorDense β} =
      ⋂ n : ℕ, ⋂ m : ℕ, {β | denseSeq ℝ≥0 n < denseSeq ℝ≥0 m →
        ∃ u ∈ Ioo (denseSeq ℝ≥0 n) (denseSeq ℝ≥0 m), 0 < (β u).im} := by
    ext β
    simp only [mem_iInter,mem_ofPred_eq]
    constructor
    · exact fun h _ _ => h _ _
    · intro h s t hst
      obtain ⟨a,ha⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hst)
      obtain ⟨b,hb⟩ := (denseRange_denseSeq ℝ≥0).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ha.2)
      obtain ⟨u,hu,hui⟩ := h a b hb.1
      exact ⟨u,⟨ha.1.trans hu.1,hu.2.trans hb.2⟩,hui⟩
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iInter
  intro m
  by_cases hnm : denseSeq ℝ≥0 n < denseSeq ℝ≥0 m
  · simp only [hnm,true_implies,ofPred_exists]
    apply IsOpen.measurableSet
    apply isOpen_iUnion
    intro u
    by_cases hu : u ∈ Ioo (denseSeq ℝ≥0 n) (denseSeq ℝ≥0 m)
    · simpa only [hu,true_and,Function.comp_apply] using isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_eval_const u))
    · simp [hu]
  · simp [hnm]
end
end SLEExactGauge

end

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsCapacityTwoWitness.radius_le_of_domain_subset
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (h : IsCapacityTwoWitness U γ G F)
    (s t : ℝ≥0) (hsub : survivingDomain γ s ⊆ survivingDomain γ t)
    (z : ℂ) (hz : z ∈ survivingDomain γ s) :
    fullRadius G s z ≤ fullRadius G t z := by
  have hγ := h.1
  have ht : z ∈ survivingDomain γ t := hsub hz
  have hgs := h.derivative_norm_positive hU s z hz
  have hgt := h.derivative_norm_positive hU t z ht
  have hys := h.imag_positive s z hz
  rcases h with ⟨_,h0,hupper,hG,hF,hGm,hFm,hinv,hinv',hinit,hode,hnorm,htip⟩
  have hfs := ((hF s).differentiableAt (isOpen_upperHalfPlane.mem_nhds (hGm s hz))).hasDerivAt
  have hgsd := ((hG s).differentiableAt ((isOpen_survivingDomain hγ s).mem_nhds hz)).hasDerivAt
  have hgtd := ((hG t).differentiableAt ((isOpen_survivingDomain hγ t).mem_nhds ht)).hasDerivAt
  have hinvder : deriv (F s) (G s z)*deriv (G s) z = 1 := by
    have he : (fun w => F s (G s w)) =ᶠ[𝓝 z] (fun w => w) := by
      filter_upwards [(isOpen_survivingDomain hγ s).mem_nhds hz] with w hw
      exact hinv s w hw
    exact ((hfs.comp z hgsd).congr_of_eventuallyEq he.symm).unique (hasDerivAt_id z)
  have hnp : ‖deriv (F s) (G s z)‖*‖deriv (G s) z‖ = 1 := by
    simpa only [norm_mul,norm_one] using congrArg norm hinvder
  let f : ℂ → ℂ := fun w => G t (F s (diskToHalfPlane (G s z) w))
  have hfd : DifferentiableOn ℂ f (Metric.ball 0 1) :=
    (hG t).comp ((hF s).comp (diskToHalfPlane_differentiable _) (diskToHalfPlane_maps hys))
      (fun w hw => hsub (hFm s (diskToHalfPlane_maps hys hw)))
  have hfm : MapsTo f (Metric.ball 0 1) upperHalfPlane :=
    fun w hw => hGm t (hsub (hFm s (diskToHalfPlane_maps hys hw)))
  have hf0 : f 0 = G t z := by simp only [f,diskToHalfPlane_zero,hinv s z hz]
  have hder : deriv f 0 = deriv (G t) z*deriv (F s) (G s z)*(G s z-star (G s z)) := by
    have hfs' : HasDerivAt (F s) (deriv (F s) (G s z)) (diskToHalfPlane (G s z) 0) := by
      simpa only [diskToHalfPlane_zero] using hfs
    have hgt' : HasDerivAt (G t) (deriv (G t) z) (F s (diskToHalfPlane (G s z) 0)) := by
      simpa only [diskToHalfPlane_zero,hinv s z hz] using hgtd
    have hh := hgt'.comp 0 (hfs'.comp 0 (diskToHalfPlane_deriv_zero (G s z)))
    simpa only [f,Function.comp_def,mul_assoc] using hh.deriv
  have hn : ‖deriv f 0‖ = ‖deriv (G t) z‖*fullRadius G s z := by
    rw [hder,norm_mul,norm_mul,norm_sub_conj_of_im_pos hys,fullRadius]
    have hi : ‖deriv (F s) (G s z)‖ = 1/‖deriv (G s) z‖ := (eq_div_iff hgs.ne').mpr hnp
    rw [hi]
    ring
  have hpos : 0 < ‖deriv f 0‖ := by
    rw [hn,fullRadius]
    positivity
  have hbound := radius_of_halfplane_map (by norm_num : (0:ℝ) < 1) hfd hfm
    (norm_pos_iff.mp hpos)
  rw [hf0,hn] at hbound
  have hy : 0 < (G t z).im := hGm t ht
  have hh := (le_div_iff₀ (show 0 < ‖deriv (G t) z‖*fullRadius G s z by rwa [← hn])).mp hbound
  change _ ≤ 2*(G t z).im/‖deriv (G t) z‖
  exact (le_div_iff₀ hgt).mpr (by nlinarith [hh])

end SLEExactGauge
namespace SLEExactGauge
 

end SLEExactGauge
end
end

end OAI
