import Mathlib
import OAI.Analysis.VlasovMaxwell.Maxwell.WaveGradient

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def positiveTimeCut (a t : ℝ) : ℝ := Real.smoothTransition ((t-a/4)/(a/4))
def positiveTimeExtend (a : ℝ) (F : ℝ × H → W) (p : ℝ × H) : W :=
  positiveTimeCut a p.1 • F p

def positiveTimeShift (a : ℝ) (F : ℝ × H → W) (p : ℝ × H) : W :=
  positiveTimeExtend a F (a+p.1,p.2)

lemma contDiff_positiveTimeCut (a : ℝ) : ContDiff ℝ ∞ (positiveTimeCut a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (a/4))
lemma positiveTimeCut_zero {a t : ℝ} (ha : 0<a) (ht : t≤a/4) : positiveTimeCut a t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
lemma positiveTimeCut_one {a t : ℝ} (ha : 0<a) (ht : a/2≤t) : positiveTimeCut a t=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0<a/4)).mpr
  linarith

lemma contDiff_positiveTimeExtend {a : ℝ} (ha : 0<a) {F : ℝ × H → W}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) : ContDiff ℝ ∞ (positiveTimeExtend a F) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0<p.1
  · exact ((contDiff_positiveTimeCut a).comp contDiff_fst).contDiffAt.smul (hF p hp)
  · have he : positiveTimeExtend a F =ᶠ[𝓝 p] (fun _ => 0) := by
      have hnh : {q : ℝ × H | q.1<a/4} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds (show p.1<a/4 by linarith)
      filter_upwards [hnh] with q hq
      simp only [positiveTimeExtend,positiveTimeCut_zero ha hq.le,zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

omit [NormedSpace ℝ H] in
lemma positiveTimeExtend_eventually_eq {a : ℝ} (ha : 0<a) (F : ℝ × H → W)
    {p : ℝ × H} (hp : a/2<p.1) : positiveTimeExtend a F =ᶠ[𝓝 p] F := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [positiveTimeExtend,positiveTimeCut_one ha hq.le,one_smul]

lemma contDiff_positiveTimeShift {a : ℝ} (ha : 0<a) {F : ℝ × H → W}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) : ContDiff ℝ ∞ (positiveTimeShift a F) :=
  (contDiff_positiveTimeExtend ha hF).comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma positiveTimeShift_eq {a t : ℝ} (ha : 0<a) (ht : 0≤t) (F : ℝ × H → W) (x : H) :
    positiveTimeShift a F (t,x)=F (a+t,x) := by
  change positiveTimeCut a (a+t) • F (a+t,x)=_
  rw [positiveTimeCut_one ha (by linarith),one_smul]

lemma fderiv_positiveTimeShift {a t : ℝ} (ha : 0<a) (ht : 0≤t) {F : ℝ × H → W} (x : H)
    (hF : DifferentiableAt ℝ F (a+t,x)) :
    fderiv ℝ (positiveTimeShift a F) (t,x)=fderiv ℝ F (a+t,x) := by
  have he := positiveTimeExtend_eventually_eq ha F (show a/2<(a+t,x).1 by dsimp; linarith)
  have hD : HasFDerivAt (fun p : ℝ × H => (a+p.1,p.2)) (ContinuousLinearMap.id ℝ (ℝ × H)) (t,x) := by
    simpa only [Prod.add_def,zero_add,id_eq] using
      (hasFDerivAt_id (𝕜:=ℝ) (t,x)).const_add (a,0)
  have hP : DifferentiableAt ℝ (positiveTimeExtend a F) (a+t,x) := hF.congr_of_eventuallyEq he
  have h := hP.hasFDerivAt.comp (t,x) hD
  change HasFDerivAt (positiveTimeShift a F) _ (t,x) at h
  rw [h.fderiv,he.fderiv_eq]
  simp

end PositiveExtension

lemma SmoothOnFiniteHorizons.field_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    {p : ℝ × Vec} (hp : 0<p.1) : ContDiffAt ℝ ∞ s.E p ∧ ContDiffAt ℝ ∞ s.B p := by
  have hT : 0≤p.1+1 := by linarith
  have hn : fieldSlab (p.1+1) ∈ 𝓝 p := by
    have hnh : {q : ℝ × Vec | q.1 ∈ Ioo 0 (p.1+1)} ∈ 𝓝 p :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨hp,by linarith⟩
    exact mem_of_superset hnh (fun q hq => ⟨hq.1.le,hq.2.le⟩)
  exact ⟨(hs _ hT).2.1.contDiffAt hn,(hs _ hT).2.2.contDiffAt hn⟩

lemma SmoothOnFiniteHorizons.particle_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    {p : ℝ × Phase} (hp : 0<p.1) : ContDiffAt ℝ ∞ s.f p := by
  have hT : 0≤p.1+1 := by linarith
  apply (hs _ hT).1.contDiffAt
  exact mem_of_superset ((isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds
    (show p.1 ∈ Ioo 0 (p.1+1) from ⟨hp,by linarith⟩)) (fun q hq => ⟨hq.1.le,hq.2.le⟩)

lemma SmoothOnFiniteHorizons.moments_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    (hc : CompactOnFiniteHorizons s) {p : ℝ × Vec} (hp : 0<p.1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Vec => rho (fun z => s.f (q.1,z)) q.2) p ∧
    ContDiffAt ℝ ∞ (fun q : ℝ × Vec => current (fun z => s.f (q.1,z)) q.2) p := by
  let U : Set (ℝ × Vec) := {q | q.1 ∈ Ioo 0 (p.1+1)}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hpU : p ∈ U := ⟨hp,by linarith⟩
  have hT : 0≤p.1+1 := by linarith
  obtain ⟨K,hK,hz⟩ := hc _ hT
  have hF : ContDiffOn ℝ ∞ (particleBySpacetime s.f) (U ×ˢ (univ : Set Vec)) := by
    intro z hz'
    apply (hs.particle_positive hz'.1.1).comp (f:=fun w : (ℝ × Vec) × Vec => (w.1.1,w.1.2,w.2)) z
      ((contDiff_reassociate).contDiffAt) |>.contDiffWithinAt
  have hzero : ∀ q ∈ U, ∀ v ∉ Prod.snd '' K, particleBySpacetime s.f (q,v)=0 := by
    intro q hq v hv
    by_contra hne
    exact hv ⟨(q.2,v),hz q.1 ⟨hq.1.le,hq.2.le⟩ (subset_tsupport _ hne),rfl⟩
  have hr := contDiffOn_integral_uniform_support hU (hK.image continuous_snd) hF hzero
  have hJ : ContDiffOn ℝ ∞ (fun z : (ℝ × Vec) × Vec => particleBySpacetime s.f z • velocity z.2)
      (U ×ˢ univ) := hF.smul ((contDiff_velocity.comp contDiff_snd).contDiffOn)
  have hzeroJ : ∀ q ∈ U, ∀ v ∉ Prod.snd '' K, particleBySpacetime s.f (q,v) • velocity v=0 := by
    intro q hq v hv
    rw [hzero q hq v hv,zero_smul]
  have hj := contDiffOn_integral_uniform_support hU (hK.image continuous_snd) hJ hzeroJ
  exact ⟨hr.contDiffAt (hU.mem_nhds hpU),hj.contDiffAt (hU.mem_nhds hpU)⟩

lemma spaceCurl_positiveTimeShift {a t : ℝ} (ha : 0<a) (ht : 0≤t) {F : Field}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) (x : Vec) :
    spaceCurl (positiveTimeShift a F) (t,x)=curl (fun y => F (a+t,y)) x := by
  rw [spaceCurl_slice ((contDiff_positiveTimeShift ha hF).differentiable (by simp))]
  congr 1
  funext y
  exact positiveTimeShift_eq ha ht F y

lemma classical_positiveTimeShift_maxwell {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a t : ℝ}
    (ha : 0<a) (ht : 0≤t) (x : Vec) :
    dirD (positiveTimeShift a s.E) (1,0) (t,x)=
      spaceCurl (positiveTimeShift a s.B) (t,x)-
        positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    dirD (positiveTimeShift a s.B) (1,0) (t,x) =
      -spaceCurl (positiveTimeShift a s.E) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.E (t,y)) x =
      positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.B (t,y)) x = 0 := by
  have hat : 0<a+t := by linarith
  have heq := hs.2.2.2.2.2.2.2.1 (a+t) hat.le
  have hE := field_differentiableAt_positive hs.2.1 hat x
  have hB := field_differentiableAt_positive hs.2.2.1 hat x
  have he := heq.2.1 x
  have hb := heq.2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hE] at he
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hB] at hb
  have hcE := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).1) x
  have hcB := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).2) x
  have hsE : (fun y => positiveTimeShift a s.E (t,y))=(fun y => s.E (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.E)
  have hsB : (fun y => positiveTimeShift a s.B (t,y))=(fun y => s.B (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.B)
  refine ⟨?_,?_,?_,?_⟩
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hE,hcB,positiveTimeShift_eq ha ht]
    exact (sub_eq_iff_eq_add.mp he).trans (by abel)
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hB,hcE]
    exact eq_neg_of_add_eq_zero_left hb
  · rw [hsE,positiveTimeShift_eq ha ht]
    exact heq.2.2.2.1 x
  · rw [hsB]
    exact heq.2.2.2.2 x

lemma classical_shifted_electric_potential_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (x : Vec) (i : Fin 3) :
    s.E (a+T,x) i =
      freeWave (fun y => s.E (a,y) i) (fun y => curl (fun z => s.B (a,z)) y i) (T,x) +
      electricPotentialComponent
        (positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2))
        (positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)) i (T,x) := by
  have hE := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).1)
  have hB := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).2)
  have hρ := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1)
  have hj := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)
  have hh := maxwell_electric_potential_representation hE hB hj hρ hT
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1 y).1)
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1.le y).2.1)
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1.le y).2.2.1) x i
  rw [positiveTimeShift_eq ha hT] at hh
  simpa only [positiveTimeShift_eq ha (le_refl 0),add_zero,
    spaceCurl_positiveTimeShift ha (le_refl 0) (fun p hp => (hm.field_positive hp).2)] using hh

lemma classical_shifted_magnetic_potential_representation {d : Datum} {s : Solution}
    (hs : Classical d s) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      magneticPotentialComponent
        (positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)) i (T,x) := by
  have hE := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).1)
  have hB := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).2)
  have hj := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)
  have hh := maxwell_magnetic_potential_representation hE hB hj hT
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1.le y).1)
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1 y).2.1)
    (fun r hr y => (classical_positiveTimeShift_maxwell hs hm ha hr.1.le y).2.2.2) x i
  rw [positiveTimeShift_eq ha hT] at hh
  simpa only [positiveTimeShift_eq ha (le_refl 0),add_zero,
    spaceCurl_positiveTimeShift ha (le_refl 0) (fun p hp => (hm.field_positive hp).1)] using hh

end RVM

end

end OAI
