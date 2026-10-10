import OAI.Probability.FKMaps.ExcursionGeometry
import OAI.Probability.FKMaps.TraceLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sum_differences_real {m : ℕ} (g : Fin (m+1) → ℝ) :
    (∑ i : Fin m,(g i.succ-g i.castSucc))=g (Fin.last m)-g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hh := ih (Fin.tail g)
    simp only [Fin.tail_def,Fin.succ_castSucc] at hh
    rw [hh]
    simp only [Fin.succ_last,Fin.castSucc_zero]
    ring

lemma remaining_differences {m : ℕ} (g : Fin (m+1) → ℝ) (i : Fin m) :
    remaining (fun j => g j.succ-g j.castSucc) (1-g (Fin.last m)) i=1-g i.succ := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    induction i using Fin.cases with
    | zero =>
      rw [remaining_zero]
      have hh := sum_differences_real (Fin.tail g)
      simp only [Fin.tail_def,Fin.succ_castSucc] at hh
      simp +unfoldPartialApp only [Fin.tail_def]
      rw [hh]
      simp only [Fin.succ_last]
      ring
    | succ i =>
      rw [remaining_succ]
      have hh := ih (Fin.tail g) i
      simpa only [Fin.tail_def,Fin.succ_castSucc,Fin.succ_last] using hh

lemma durationRatio_bridge {m : ℕ} (u : Fin (m+1) → unitInterval) :
    durationRatio (fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)) (1-(u (Fin.last m):ℝ))=
      fun i => Radial.bridgeRatio (u i.castSucc) (u i.succ) := by
  funext i
  rw [durationRatio,remaining_differences (fun j => (u j:ℝ)),Radial.bridgeRatio]
  congr 1
  ring

lemma durationVariance_bridge {m : ℕ} (u : Fin (m+1) → unitInterval) :
    durationVariance (fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)) (1-(u (Fin.last m):ℝ))=
      fun i => Radial.bridgeVariance (u i.castSucc) (u i.succ) := by
  funext i
  rw [durationVariance,remaining_differences (fun j => (u j:ℝ)),Radial.bridgeVariance]
  congr 1
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram

/-- Scheffé's argument in its nonnegative measure-theoretic form: pointwise
convergence of probability densities implies convergence of every bounded test. -/
lemma lintegral_min_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hgint : ∫⁻ x,g x ∂μ≠∞) :
    Tendsto (fun n => ∫⁻ x,min (f n x) (g x) ∂μ) atTop (𝓝 (∫⁻ x,g x ∂μ)) := by
  apply tendsto_lintegral_of_dominated_convergence g
  · exact fun n => (hf n).min hg
  · exact fun _ => Filter.Eventually.of_forall (fun _ => min_le_right _ _)
  · exact hgint
  · filter_upwards [hlim] with x hx
    simpa only [min_self] using hx.min (tendsto_const_nhds (x := g x))

lemma tendsto_withDensity {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (_hg : Measurable g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hp : ∀ n, IsProbabilityMeasure (μ.withDensity (f n)))
    (hpg : IsProbabilityMeasure (μ.withDensity g)) :
    Tendsto (fun n => (⟨μ.withDensity (f n),hp n⟩ : ProbabilityMeasure α)) atTop
      (@nhds (ProbabilityMeasure α) inferInstance ⟨μ.withDensity g,hpg⟩) := by
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro s hs
  simp only [ProbabilityMeasure.coe_mk,withDensity_apply _ hs.measurableSet]
  have he : ∀ᵐ x ∂μ.restrict s,g x=liminf (fun n => f n x) atTop := by
    filter_upwards [ae_restrict_of_ae hlim] with x hx
    exact hx.liminf_eq.symm
  rw [lintegral_congr_ae he]
  exact lintegral_liminf_le (fun n => hf n)

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma pathMass_trace_at_size {N : ℕ} (a R : ℕ) (xs : List (ℕ×ℕ))
    (h : traceSize R xs=N) :
    pathMass N (fun d => firstHit a d ∧ observed a xs d)=traceKilledWeight a R xs := by
  subst N
  exact pathMass_firstHit_observed a R xs

lemma excursion_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) :
    (excursionLaw n).real {d | ∀ i,pathSum d (evenGrid n (u i.succ))=(b i:ℤ)}=
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n) b := by
  have ht : traceSize (gridRemainder u n+1) (segments (gridDurations u n) b)=2*n+1 := by
    rw [traceSize_segments,← Nat.add_assoc,grid_total u hu h0]
  have hh := pathMass_trace_at_size 0 (gridRemainder u n+1) (segments (gridDurations u n) b) ht
  simp_rw [grid_observed u hu h0] at hh
  rw [excursionLaw_real,normalizedTrace,grid_total u hu h0]
  simp only [mem_ofPred_eq]
  rw [hh]

/-- Lattice mesh and actual sampled heights, not a reference density. -/
def mesh (n : ℕ) : ℝ := 2/Real.sqrt ((2*n+1:ℕ):ℝ)

def gridIndex {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (d : Path (2*n+1)) (i : Fin m) : ℕ :=
  (pathSum d (evenGrid n (u i.succ))).toNat/2

def gridSample {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (d : Path (2*n+1)) (i : Fin m) : ℝ := mesh n*(gridIndex u n d i:ℝ)

def histogramDensity {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :=
  Histogram.density (excursionLaw n) (gridSample u n) (mesh n)

lemma mesh_pos (n : ℕ) : 0< mesh n := div_pos (by norm_num) (Real.sqrt_pos.mpr (by positivity))

lemma odd_size_atTop : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by show n≤2*n+1; omega) tendsto_id

lemma mesh_tendsto_zero : Tendsto mesh atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp odd_size_atTop))

lemma index_eq_iff {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) (b : ℕ) :
    gridIndex u n d i=b↔pathSum d (evenGrid n (u i.succ))=(2*b:ℕ) := by
  have hk := evenGrid_le n (u i.succ).property.2
  have hpos : 0≤pathSum d (evenGrid n (u i.succ)) := by
    have h := hd.2 _ (by omega : evenGrid n (u i.succ)<2*n+1)
    simpa only [Int.natCast_zero,zero_add] using h
  have hp := pathSum_parity d (hk.trans (Nat.le_succ _))
  have he : Even (evenGrid n (u i.succ):ℤ) := by exact_mod_cast even_evenGrid n (u i.succ)
  have hb := hp.add he
  rw [sub_add_cancel] at hb
  obtain ⟨k,hk⟩ := hb
  have hnat := Int.toNat_of_nonneg hpos
  unfold gridIndex
  push_cast
  omega

lemma gridSample_eq {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) :
    gridSample u n d i=(pathSum d (evenGrid n (u i.succ)):ℝ)/Real.sqrt ((2*n+1:ℕ):ℝ) := by
  have he := (index_eq_iff u n hd i (gridIndex u n d i)).mp rfl
  rw [gridSample,mesh,he]
  push_cast
  ring

lemma gridIndex_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) :
    (excursionLaw n).real {d | gridIndex u n d=b}=
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n) (fun i => 2*b i) := by
  rw [← excursion_probability u hu h0]
  apply measureReal_congr
  filter_upwards [excursionLaw_ae n] with d hd
  apply propext
  rw [funext_iff]
  exact forall_congr' (fun i => index_eq_iff u n hd i (b i))

lemma histogramDensity_positive {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) {x : Fin m → ℝ} (hx : ∀ i,0≤x i) :
    histogramDensity u n x=ENNReal.ofReal ((Real.sqrt ((2*n+1:ℕ):ℝ)/2)^m*
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n)
        (fun i => 2*⌊x i/mesh n⌋₊)) := by
  simp +unfoldPartialApp only [histogramDensity,gridSample]
  rw [Histogram.density_lattice _ _ (mesh_pos n) hx]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ENNReal.ofReal ((excursionLaw n).real {d | gridIndex u n d=fun i => ⌊x i/mesh n⌋₊}) * _=_
  rw [gridIndex_probability u hu h0]
  simp only [Fintype.card_fin]
  have hp : 0≤normalizedTrace 0 (gridRemainder u n) (gridDurations u n) (fun i => 2*⌊x i/mesh n⌋₊) := by
    rw [← gridIndex_probability u hu h0 n (fun i => ⌊x i/mesh n⌋₊)]
    exact measureReal_nonneg
  rw [← ENNReal.ofReal_pow (mesh_pos n).le,← ENNReal.ofReal_inv_of_pos (pow_pos (mesh_pos n) _),
    ← ENNReal.ofReal_mul hp]
  congr 1
  rw [← inv_pow,mesh,inv_div]
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma gridRemainder_atTop {m : ℕ} (u : Fin (m+1) → unitInterval)
    (h1 : (u (Fin.last m):ℝ)<1) : Tendsto (gridRemainder u) atTop atTop := by
  have h : Tendsto (fun n => gridRemainder u n+1) atTop atTop := nat_atTop_of_ratio (sub_pos.mpr h1) odd_size_atTop (by
    simpa only [Nat.cast_add,Nat.cast_one] using gridRemainder_ratio u)
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 h (b+1)] with n hn
  omega

lemma histogramDensity_limit_pos {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    {x : Fin m → ℝ} (hx : ∀ i,0<x i) :
    Tendsto (fun n => histogramDensity u n x) atTop (𝓝 (Radial.bridgeDensity u x)) := by
  let s : Fin m → ℝ := fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)
  let r : ℝ := 1-(u (Fin.last m):ℝ)
  have hs (i : Fin m) : 0<s i := sub_pos.mpr (hu i.castSucc_lt_succ)
  have hr : 0<r := sub_pos.mpr (h1 _)
  have hd (i : Fin m) : Tendsto (fun n => gridDurations u n i) atTop atTop :=
    nat_atTop_of_ratio (hs i) odd_size_atTop (gridDurations_ratio u hu.monotone i)
  have hb (i : Fin m) : Tendsto (fun n => ((2*⌊x i/mesh n⌋₊:ℕ):ℝ)/
      Real.sqrt ((2*n+1:ℕ):ℝ)) atTop (𝓝 (x i)) := by
    have hh := Histogram.floor_mesh_tendsto mesh_pos mesh_tendsto_zero (hx i).le
    convert hh using 1
    funext n
    simp only [mesh,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hl := scaledTrace_limit_zero m hr hs hx (gridRemainder_atTop u (h1 _))
    odd_size_atTop hd (gridRemainder_ratio u) (gridDurations_ratio u hu.monotone)
    (gridRemainder_even u) (gridDurations_even u hu.monotone)
    (fun _ _ => even_two_mul _) hb
  simp only [s,r,durationRatio_bridge,durationVariance_bridge] at hl
  change Tendsto _ atTop (𝓝 (Radial.bridgeDensity u x)) at hl
  apply hl.congr'
  exact Filter.Eventually.of_forall (fun n => (histogramDensity_positive u hu.monotone h0 n (fun i => (hx i).le)).symm)

lemma chainDensity_zero {m : ℕ} (v : ℝ) (a t x : Fin m → ℝ)
    (hx : ∃ i,x i≤0) : Radial.chainDensity v a t x=0 := by
  induction m generalizing v with
  | zero => obtain ⟨i,_⟩ := hx; exact Fin.elim0 i
  | succ m ih =>
    obtain ⟨i,hi⟩ := hx
    induction i using Fin.cases with
    | zero =>
      rw [Radial.chainDensity,Radial.transition,indicator_of_notMem (show x 0 ∉ Ioi (0:ℝ) from not_lt.mpr hi),zero_mul]
    | succ i =>
      rw [Radial.chainDensity,ih _ (Fin.tail a) (Fin.tail t) (Fin.tail x) ⟨i,hi⟩,mul_zero]

lemma histogramDensity_limit_ae {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      Tendsto (fun n => histogramDensity u n x) atTop (𝓝 (Radial.bridgeDensity u x)) := by
  have hwall : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),∀ i,x i≠0 := by
    rw [volume_pi]
    exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ => volume) i 0)
  filter_upwards [hwall] with x hx
  by_cases hp : ∀ i,0<x i
  · exact histogramDensity_limit_pos u hu h0 h1 hp
  · obtain ⟨i,hi⟩ := not_forall.mp hp
    have hn : x i<0 := lt_of_le_of_ne (le_of_not_gt hi) (hx i)
    have hg : Radial.bridgeDensity u x=0 := chainDensity_zero _ _ _ _ ⟨i,hn.le⟩
    rw [hg]
    apply tendsto_const_nhds.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (Histogram.density_lattice_negative (excursionLaw n) (gridIndex u n)
      (mesh_pos n).le ⟨i,hn⟩).symm

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma aemeasurable_standardExcursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (u : unitInterval) : AEMeasurable (fun ω => standardExcursion B ω u) P := by
  apply Real.continuous_sqrt.measurable.comp_aemeasurable
  apply Finset.aemeasurable_fun_sum
  intro i _
  exact (((hB i).aemeasurable _).sub ((hB i).aemeasurable 1 |>.const_mul (u:ℝ))).pow_const 2

lemma standardExcursion_hasLaw {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω i => standardExcursion B ω (u i.succ)) (volume.withDensity (bridgeDensity u)) P := by
  have ha := AEMeasurable.of_eval (fun index : Fin m => aemeasurable_standardExcursion hB (u index.succ))
  refine ⟨ha,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map' hF.aemeasurable ha,lintegral_withDensity_eq_lintegral_mul _ (measurable_bridgeDensity u) hF]
  rw [lintegral_standardExcursion hB hI u hu h0 h1 F hF]
  apply lintegral_congr
  intro x
  exact mul_comm _ _

lemma bridgeDensity_probability {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    IsProbabilityMeasure (volume.withDensity (bridgeDensity u)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have ht (i : Fin m) : 0<bridgeVariance (u i.castSucc) (u i.succ) :=
    bridgeVariance_pos (hu i.castSucc_lt_succ) (h1 _)
  have hh := lintegral_chain m (0:Space)
    (fun i => bridgeRatio (u i.castSucc) (u i.succ))
    (fun i => bridgeVariance (u i.castSucc) (u i.succ)) ht
    (fun _ => 1) measurable_const
  simpa only [lintegral_const,measure_univ,mul_one,norm_zero,one_mul,bridgeDensity] using hh.symm

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

lemma pathSum_step {N k : ℕ} (d : Path N) (hk : k<N) :
    pathSum d (k+1)=pathSum d k+sign (d ⟨k,hk⟩) := by
  have he (i : Fin N) : (if i.val<k+1 then sign (d i) else 0)=
      (if i.val<k then sign (d i) else 0)+(if i=⟨k,hk⟩ then sign (d ⟨k,hk⟩) else 0) := by
    by_cases hi : i=⟨k,hk⟩
    · subst i; simp
    · have hne : i.val≠k := fun h => hi (Fin.ext h)
      by_cases hh : i.val<k <;> simp [hi,hh,show (i.val<k+1)↔(i.val<k) by omega]
  simp only [pathSum,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma abs_sign (s : Bool) : |(sign s:ℝ)|=1 := by cases s <;> norm_num [sign]

lemma pathSum_diff_le {N k j : ℕ} (d : Path N) (hj : j≤k) (hk : k≤N) :
    |(pathSum d k:ℝ)-(pathSum d j:ℝ)|≤(k:ℝ)-(j:ℝ) := by
  induction k generalizing j with
  | zero =>
    have : j=0 := by omega
    subst j
    simp
  | succ k ih =>
    by_cases he : j=k+1
    · subst j; simp
    · have hjk : j≤k := by omega
      have hh := ih hjk (by omega)
      rw [pathSum_step d (by omega)]
      push_cast
      calc
        |(pathSum d k:ℝ)+(sign (d ⟨k,by omega⟩):ℝ)-(pathSum d j:ℝ)| =
          |((pathSum d k:ℝ)-(pathSum d j:ℝ))+(sign (d ⟨k,by omega⟩):ℝ)| := by ring_nf
        _ ≤ |(pathSum d k:ℝ)-(pathSum d j:ℝ)|+|(sign (d ⟨k,by omega⟩):ℝ)| := abs_add_le _ _
        _ ≤ (k:ℝ)+1-j := by rw [abs_sign]; linarith

lemma pathSum_dist_le {N k j : ℕ} (d : Path N) (hk : k≤N) (hj : j≤N) :
    |(pathSum d k:ℝ)-(pathSum d j:ℝ)|≤|(k:ℝ)-(j:ℝ)| := by
  rcases le_total j k with h|h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))] using pathSum_diff_le d h hk
  · rw [abs_sub_comm,abs_sub_comm (k:ℝ)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))] using pathSum_diff_le d h hj

def simplePolygon {N : ℕ} (d : Path N) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (pathSum d i.val:ℝ)/Real.sqrt (N:ℝ))

def arrayPolygon {N : ℕ} (d : Fin N → ℕ) : C(unitInterval,ℝ) :=
  interpolation N (fun i => (arrayWalk d i.val:ℝ)/Real.sqrt (N:ℝ))

lemma arrayPolygon_binaryArray {N : ℕ} (d : Path N) :
    arrayPolygon (binaryArray d)=simplePolygon d := by
  simp only [arrayPolygon,simplePolygon,arrayWalk_binaryArray]

lemma arrayPolygon_code {N : ℕ} (d : Code N) :
    arrayPolygon (codeEmbedding N d)=walkPolygon binaryOffspring.sigma d.val := by
  simp only [arrayPolygon,walkPolygon,arrayWalk_codeEmbedding,binaryOffspring_sigma,one_mul]

lemma simplePolygon_grid_bound {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) :
    |simplePolygon d (u i.succ)-gridSample u n d i|≤3/Real.sqrt ((2*n+1:ℕ):ℝ) := by
  rw [gridSample_eq u n hd,simplePolygon]
  apply interpolation_sub_const_bound
  intro j hj
  have hs := hat_support hj
  have he := evenGrid_error n (u i.succ).property.1
  have hpos : 0<Real.sqrt ((2*n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [← sub_div,abs_div,abs_of_pos hpos]
  apply (div_le_div_iff_of_pos_right hpos).mpr
  have hh := pathSum_dist_le d (Nat.le_of_lt_succ j.isLt)
    ((evenGrid_le n (u i.succ).property.2).trans (Nat.le_succ _))
  apply hh.trans
  rw [abs_lt] at hs
  rw [abs_le]
  constructor <;> linarith

lemma code_simple_integral (n : ℕ) (F : C(unitInterval,ℝ) → ℝ) :
    (∫ c,F (walkPolygon binaryOffspring.sigma c.val) ∂binaryOffspring.codeLaw n)=
      ∫ d,F (simplePolygon d) ∂excursionLaw n := by
  have h := binary_code_integral n (fun a => F (arrayPolygon a))
  simpa only [arrayPolygon_code,arrayPolygon_binaryArray] using h

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma histogram_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :
    IsProbabilityMeasure (volume.withDensity (histogramDensity u n)) := by
  rw [show histogramDensity u n=Histogram.density (excursionLaw n) (gridSample u n) (mesh n) from rfl,
    ← Histogram.mixture_withDensity]
  exact Histogram.mixture_probability _ _ (mesh_pos n)

lemma histogram_converges {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    Tendsto (fun n => (⟨volume.withDensity (histogramDensity u n),histogram_probability u n⟩ :
      ProbabilityMeasure (Fin m → ℝ))) atTop
      (@nhds (ProbabilityMeasure (Fin m → ℝ)) inferInstance ⟨volume.withDensity (Radial.bridgeDensity u),Radial.bridgeDensity_probability u hu h1⟩) :=
  Histogram.tendsto_withDensity (fun _ => Histogram.measurable_density _ _ _)
    (Radial.measurable_bridgeDensity u) (histogramDensity_limit_ae u hu h0 h1)
    (histogram_probability u) (Radial.bridgeDensity_probability u hu h1)

lemma grid_integral_limit {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d,F (gridSample u n d) ∂excursionLaw n) atTop
      (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) := by
  have hm := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (histogram_converges u hu h0 h1) F
  change Tendsto (fun n => ∫ x,F x ∂volume.withDensity (histogramDensity u n)) atTop
    (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) at hm
  apply hm.congr_dist
  have he (n : ℕ) := Histogram.integral_mixture_close (excursionLaw n) (gridSample u n) (mesh_pos n) F hF
  simp_rw [Histogram.mixture_withDensity] at he
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => by
    simpa only [Real.dist_eq,histogramDensity] using he n)
    (by simpa only [mul_zero] using mesh_tendsto_zero.const_mul (L:ℝ))

def pathEvaluation {m : ℕ} (u : Fin (m+1) → unitInterval) (f : C(unitInterval,ℝ)) : Fin m → ℝ :=
  fun i => f (u i.succ)

lemma pathEvaluation_continuous {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Continuous (pathEvaluation u) := continuous_pi (fun i => continuous_eval_const (u i.succ))

lemma polygon_integral_close {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ d,F (simplePolygon d |> pathEvaluation u) ∂excursionLaw n)-
      (∫ d,F (gridSample u n d) ∂excursionLaw n)|≤(L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ)) := by
  rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ : Path (2*n+1),(L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ)) ∂excursionLaw n := by
      apply integral_mono_ae (Integrable.of_finite) (integrable_const _)
      filter_upwards [excursionLaw_ae n] with d hd
      apply (hF.dist_le_mul _ _).trans
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      exact simplePolygon_grid_bound u n hd i
    _ = _ := by simp

lemma polygon_integral_limit {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d,F (pathEvaluation u (simplePolygon d)) ∂excursionLaw n) atTop
      (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) := by
  apply (grid_integral_limit u hu h0 h1 F hF).congr_dist
  have hz : Tendsto (fun n => (L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (3:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp odd_size_atTop))
    simpa only [mul_zero,Function.comp_def] using h.const_mul (L:ℝ)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
  rw [dist_comm,Real.dist_eq]
  exact polygon_integral_close u n F hF

lemma vervaat_fdd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω => pathEvaluation u (vervaat (bridgePath B ω)))
      (volume.withDensity (Radial.bridgeDensity u)) P := by
  have hV := (binaryOffspring.codeWalk_converges hB).continuous_comp (pathEvaluation_continuous u)
  refine ⟨hV.aemeasurable_limit,?_⟩
  have ht : Tendsto (fun n => (⟨(binaryOffspring.codeLaw n).map
      (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val)),
      inferInstance⟩ : ProbabilityMeasure (Fin m → ℝ)))
      atTop (@nhds (ProbabilityMeasure (Fin m → ℝ)) inferInstance ⟨volume.withDensity (Radial.bridgeDensity u),Radial.bridgeDensity_probability u hu h1⟩) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    rintro F ⟨M,hM⟩ ⟨L,hL⟩
    let F' : BoundedContinuousFunction (Fin m → ℝ) ℝ := ⟨⟨F,hL.continuous⟩,⟨M,hM⟩⟩
    change Tendsto (fun n => ∫ x,F x ∂(binaryOffspring.codeLaw n).map
      (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val))) atTop (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u)))
    have he (n : ℕ) : (∫ x,F x ∂(binaryOffspring.codeLaw n).map
        (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val)))=
        ∫ d,F (pathEvaluation u (simplePolygon d)) ∂excursionLaw n := by
      rw [integral_map (measurable_of_countable _).aemeasurable hL.continuous.aestronglyMeasurable]
      exact code_simple_integral n (fun f => F (pathEvaluation u f))
    simp_rw [he]
    exact polygon_integral_limit u hu h0 h1 F' hL
  exact congrArg (fun μ : ProbabilityMeasure (Fin m → ℝ) => (μ : Measure (Fin m → ℝ)))
    (tendsto_nhds_unique hV.tendsto ht)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

/-- Strictly interior mesh, with the initial zero included only as a reference. -/
def interiorTimes (m : ℕ) (i : Fin (m+2)) : unitInterval :=
  gridPoint (m+2) i.castSucc

lemma interiorTimes_strictMono (m : ℕ) : StrictMono (interiorTimes m) := by
  intro i j hij
  change (i.val:ℝ)/(m+2:ℕ)<(j.val:ℝ)/(m+2:ℕ)
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (Nat.cast_lt.mpr hij)

lemma interiorTimes_zero (m : ℕ) : interiorTimes m 0=0 := by
  apply Subtype.ext
  simp [interiorTimes,gridPoint]

lemma interiorTimes_lt_one (m : ℕ) (i : Fin (m+2)) : (interiorTimes m i:ℝ)<1 := by
  change (i.val:ℝ)/(m+2:ℕ)<1
  exact (div_lt_one (by positivity)).mpr (Nat.cast_lt.mpr i.isLt)

def interiorIndex (m : ℕ) (j : Fin (m+3)) : Fin (m+1) := ⟨min (j.val-1) m,by omega⟩

def interiorReconstruct (m : ℕ) (x : Fin (m+1) → ℝ) : C(unitInterval,ℝ) :=
  interpolation (m+2) (fun j => x (interiorIndex m j))

lemma continuous_interiorReconstruct (m : ℕ) : Continuous (interiorReconstruct m) :=
  (continuous_interpolation _).comp (continuous_pi (fun _ => continuous_apply _))

lemma interiorIndex_bounds (m : ℕ) (j : Fin (m+3)) :
    (interiorIndex m j).val+1≤j.val+1 ∧ j.val≤(interiorIndex m j).val+2 := by
  simp only [interiorIndex]
  have hj := j.isLt
  omega

lemma interiorTime_dist (m : ℕ) (j : Fin (m+3)) :
    dist (interiorTimes m (interiorIndex m j).succ) (gridPoint (m+2) j)≤1/(m+2:ℕ) := by
  have h := interiorIndex_bounds m j
  change |(((interiorIndex m j).val+1:ℕ):ℝ)/(m+2:ℕ)-(j.val:ℝ)/(m+2:ℕ)|≤_
  rw [← sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(m+2:ℕ)),
    div_le_div_iff_of_pos_right (by positivity)]
  rw [abs_le]
  have h₁ : ((interiorIndex m j).val:ℝ)+1≤(j.val:ℝ)+1 := by exact_mod_cast h.1
  have h₂ : (j.val:ℝ)≤((interiorIndex m j).val:ℝ)+2 := by exact_mod_cast h.2
  push_cast
  constructor <;> linarith

lemma interiorReconstruct_tendsto (f : C(unitInterval,ℝ)) :
    Tendsto (fun m => interiorReconstruct m (fun i => f (interiorTimes m i.succ))) atTop (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε/2) (half_pos hε)
  have hz : Tendsto (fun m : ℕ => (2:ℝ)/(m+2:ℕ)) atTop (𝓝 (0:ℝ)) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hz.eventually (gt_mem_nhds hδ)] with m hm
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity : 0≤ε/2)).mpr
  intro t
  change |interiorReconstruct m _ t-f t|≤ε/2
  apply interpolation_sub_const_bound
  intro j hj
  have ht := hat_gridPoint_dist (by omega : 0 < m+2) j t hj
  have hh := interiorTime_dist m j
  have htriangle := dist_triangle (interiorTimes m (interiorIndex m j).succ) (gridPoint (m+2) j) t
  have he : (1:ℝ)/(m+2:ℕ)+1/(m+2:ℕ)=2/(m+2:ℕ) := by ring
  apply (hd (lt_of_le_of_lt htriangle ?_)).le
  have hsum := add_lt_add_of_le_of_lt hh ht
  rw [he] at hsum
  exact hsum.trans hm

lemma interior_integral_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P)
    (F : BoundedContinuousFunction C(unitInterval,ℝ) ℝ) :
    Tendsto (fun m => ∫ ω,F (interiorReconstruct m (fun i => X ω (interiorTimes m i.succ))) ∂P)
      atTop (𝓝 (∫ ω,F (X ω) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro m
    exact F.continuous.measurable.comp_aemeasurable
      ((continuous_interiorReconstruct m).measurable.comp_aemeasurable
        (AEMeasurable.of_eval (fun index =>
          (continuous_eval_const (interiorTimes m index.succ)).measurable.comp_aemeasurable hX)))
      |>.aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact ae_of_all _ (fun ω => F.norm_coe_le_norm _)
  · exact ae_of_all _ (fun ω => F.continuous.continuousAt.tendsto.comp (interiorReconstruct_tendsto (X ω)))

lemma identDistrib_of_interior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ m : ℕ,IdentDistrib (fun ω (i : Fin (m+1)) => X ω (interiorTimes m i.succ))
      (fun ω (i : Fin (m+1)) => Y ω (interiorTimes m i.succ)) P P) : IdentDistrib X Y P P := by
  refine ⟨hX,hY,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map hX F.continuous.aestronglyMeasurable,integral_map hY F.continuous.aestronglyMeasurable]
  apply tendsto_nhds_unique (interior_integral_limit hX F)
  apply (interior_integral_limit hY F).congr
  intro m
  exact ((h m).comp ((F.continuous.comp (continuous_interiorReconstruct m)).measurable)).integral_eq.symm

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
local instance : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
local instance : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩

lemma continuous_standardExcursion {Ω : Type} {B : Fin 3 → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : ∀ i,Continuous (B i · ω)) : Continuous (standardExcursion B ω) := by
  unfold standardExcursion
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  apply Continuous.sub
  · exact (hB i).comp (continuous_subtype_val.subtype_mk _)
  · exact continuous_subtype_val.mul continuous_const

lemma standardExcursion_ae_continuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,Continuous (standardExcursion B ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
  exact continuous_standardExcursion hω

def excursionPath {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω) : C(unitInterval,ℝ) :=
  ContinuousMap.mkD (standardExcursion B ω) 0

lemma excursionPath_ae_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,(excursionPath B ω : unitInterval → ℝ)=standardExcursion B ω := by
  filter_upwards [standardExcursion_ae_continuous hB] with ω hω
  funext t
  exact ContinuousMap.mkD_apply_of_continuous hω

lemma dense_eval_measurableEmbedding : MeasurableEmbedding (fun f : C(unitInterval,ℝ) =>
    fun n : ℕ => f (TopologicalSpace.denseSeq unitInterval n)) := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi (fun n => continuous_eval_const _)
  · intro f g he
    apply ContinuousMap.ext
    exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer f.continuous g.continuous he)

lemma excursionPath_aemeasurable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    AEMeasurable (excursionPath B) P := by
  apply dense_eval_measurableEmbedding.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro n
  apply (Radial.aemeasurable_standardExcursion (fun i => (hB i).toIsPreBrownianReal) _).congr
  filter_upwards [excursionPath_ae_eq hB] with ω hω
  exact (congrFun hω _).symm

/-- The law identification is proved from exact binary first-passage counts and
radial Gaussian densities, not assumed as Vervaat's theorem. -/
theorem vervaat_identDistrib_excursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    IdentDistrib (fun ω => vervaat (bridgePath W ω)) (excursionPath B) P P := by
  apply identDistrib_of_interior
    ((measurable_vervaat).comp_aemeasurable (bridgePath_aemeasurable hW)) (excursionPath_aemeasurable hB)
  intro m
  have hV := SimpleWalk.vervaat_fdd hW (interiorTimes m) (interiorTimes_strictMono m)
    (interiorTimes_zero m) (interiorTimes_lt_one m)
  have hE := Radial.standardExcursion_hasLaw (fun i => (hB i).toIsPreBrownianReal) hI
    (interiorTimes m) (interiorTimes_strictMono m) (interiorTimes_zero m) (interiorTimes_lt_one m)
  apply hV.identDistrib
  apply hE.congr
  filter_upwards [excursionPath_ae_eq hB] with ω hω
  exact funext (fun i => congrFun hω _)

lemma diagonalExcursion_eq {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    diagonalExcursion B ω=diagonalPath (excursionPath B ω) := by
  unfold diagonalExcursion diagonalPath excursionPath ContinuousMap.mkD
  split_ifs <;> rfl

/-- The exact full joint finite-variance tree-coding theorem with the frozen
standard normalized (three-independent-bridge norm) excursion. -/
theorem CriticalEvenOffspring.jointCodingStatement (p : CriticalEvenOffspring) : JointCodingStatement p := by
  intro Ω mΩ P hp B hB hI F
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure P := hp
  have hc := p.jointCode_vervaat_CLT (hB 0)
  have hi := (vervaat_identDistrib_excursion (hB 0) hB hI).comp (diagonalPath_lipschitz.continuous.measurable)
  have he := (hi.comp F.continuous.measurable).integral_eq
  have ht := integral_tendsto_of_tendstoInDistribution hc F.continuous (fun x => F.norm_coe_le_norm x)
  change Tendsto (fun n => ∫ d,F (jointCode p.sigma d) ∂p.codeLaw n) atTop
    (𝓝 (∫ ω,F (diagonalPath (vervaat (bridgePath (B 0) ω))) ∂P)) at ht
  simp only [Function.comp_def] at he
  rw [he] at ht
  simp_rw [p.code_integral] at ht
  simpa only [codeExpectation,jointBrownianExpectation,diagonalExcursion_eq] using ht

end FKCRT.TreeCoding
end

end OAI
