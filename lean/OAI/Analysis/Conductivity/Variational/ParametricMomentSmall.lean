import Mathlib
import OAI.Analysis.Conductivity.Walls.ParametricWallTensors
import OAI.Analysis.Conductivity.Variational.RegularVanishingFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology

lemma compact_supported_integral_tendsto_zero {P : Type*} [TopologicalSpace P]
    [FirstCountableTopology P] {f : P×Coord3 → ℝ} {p : P} {K : Set Coord3}
    (hK : IsCompact K) (hf : ∀ x,ContinuousAt f (p,x)) (hz : ∀ x,f (p,x)=0)
    (hc : ∀ᶠ q in 𝓝 p,Continuous (fun x => f (q,x)))
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K) :
    Tendsto (fun q => ∫ x,f (q,x)) (𝓝 p) (𝓝 0) := by
  have ht : ContinuousAt (fun q => ∫ x in K,f (q,x)) p := by
    apply continuousAt_of_dominated (bound:=fun _ => (1:ℝ))
      (hc.mono (fun q hh => hh.aestronglyMeasurable))
    · filter_upwards [compact_parametric_norm_small hK (fun x _ => hf x)
        (fun x _ => hz x) zero_lt_one] with q hq
      exact (ae_restrict_mem hK.measurableSet).mono (fun x hx => hq x hx)
    · exact integrableOn_const hK.measure_ne_top
    · apply Eventually.of_forall
      intro x
      have hg : ContinuousAt (fun q : P => (q,x)) p := continuousAt_id.prodMk continuousAt_const
      exact (hf x).comp (f:=fun q : P => (q,x)) hg
  have ht' : Tendsto (fun q => ∫ x in K,f (q,x)) (𝓝 p) (𝓝 0) := by
    simpa only [ContinuousAt,hz,integral_zero] using ht
  apply ht'.congr'
  filter_upwards [hs] with q hq
  exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun hh => hx (hq hh)))

lemma physicalSourceMoment_family_tendsto_zero {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    {u : P×Coord3 → Fin 2 → ℝ} (hu : Continuous u)
    {r : Fin 2 → P×Coord3 → ℝ} {p : P} {V : Set P}
    (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hz : ∀ j x,r j (p,x)=0) :
    Tendsto (fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x)))
      (𝓝 p) (𝓝 0) := by
  have hcont (j x) : ContinuousAt (r j) (p,x) :=
    ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hp,mem_univ x⟩)).continuousAt
  have hc : ∀ᶠ q in 𝓝 p,∀ j,Continuous (fun x => r j (q,x)) := by
    filter_upwards [hV.mem_nhds hp] with q hq j
    exact (hr j).continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨hq,mem_univ x⟩)
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · exact compact_supported_integral_tendsto_zero hK (hcont 0) (hz 0)
      (hc.mono (fun q hh => hh 0)) (hs.mono (fun q hh => hh 0))
  · exact compact_supported_integral_tendsto_zero hK (hcont 1) (hz 1)
      (hc.mono (fun q hh => hh 1)) (hs.mono (fun q hh => hh 1))
  · apply compact_supported_integral_tendsto_zero hK
      (f:=fun q => u q 1*r 0 q-u q 0*r 1 q)
    · intro x
      exact (((continuous_apply 1).comp hu).continuousAt.mul (hcont 0 x)).sub
        (((continuous_apply 0).comp hu).continuousAt.mul (hcont 1 x))
    · intro x; simp only [hz,mul_zero,sub_zero]
    · filter_upwards [hc] with q hq
      exact (((continuous_apply 1).comp (hu.comp (continuous_const.prodMk continuous_id))).mul (hq 0)).sub
        (((continuous_apply 0).comp (hu.comp (continuous_const.prodMk continuous_id))).mul (hq 1))
    · filter_upwards [hs] with q hq
      exact (tsupport_sub _ _).trans (union_subset
        (tsupport_mul_subset_right.trans (hq 0)) (tsupport_mul_subset_right.trans (hq 1)))

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem two_sided_vanishing_family_correction
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {U : Set Coord3} (hU : IsOpen U)
    (hcpos : IsPreconnected (U∩{x : Coord3 | 0<x 2}))
    (hcneg : IsPreconnected (U∩{x : Coord3 | x 2<0}))
    (hD : ∀ x∈U,x 2≠0 → Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {K : Set Coord3} (hK : IsCompact K) (hKU : K⊆U)
    {δ : ℝ} (hδ : 0<δ) {r : Fin 2 → P×Coord3 → ℝ}
    {V : Set P} (hV : IsOpen V) (hp : p∈V)
    (hr : ∀ j,ContDiffOn ℝ (↑(⊤:ℕ∞)) (r j) (V×ˢuniv))
    (hs : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => r j (q,x)) K)
    (hgap : ∀ᶠ q in 𝓝 p,∀ j x,x∈tsupport (fun y => r j (q,y)) → δ≤|x 2|)
    (hz : ∀ j x,r j (p,x)=0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p,
      physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))=0 →
      physicalSourceMoment (fun x => u (q,x))
        (fun j => wallPositiveCut δ (fun x => r j (q,x)))=0 →
      BoundedPhysicallyCorrectable (fun x => u (q,x)) U (fun j x => r j (q,x)) ε := by
  let rp : Fin 2 → P×Coord3 → ℝ := fun j q =>
    wallPositiveCut δ (fun x => r j (q.1,x)) q.2
  let rn : Fin 2 → P×Coord3 → ℝ := fun j q => r j q-rp j q
  have hrp (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rp j) (V×ˢuniv) :=
    ((Real.smoothTransition.contDiff.comp
      (((contDiff_apply ℝ ℝ (2:Fin 3)).comp contDiff_snd).div_const δ)).contDiffOn).mul (hr j)
  have hrn (j) : ContDiffOn ℝ (↑(⊤:ℕ∞)) (rn j) (V×ˢuniv) := (hr j).sub (hrp j)
  have hup : IsOpen (U∩{x : Coord3 | 0<x 2}) := hU.inter (isOpen_lt continuous_const (continuous_apply 2))
  have hun : IsOpen (U∩{x : Coord3 | x 2<0}) := hU.inter (isOpen_lt (continuous_apply 2) continuous_const)
  have hKp : IsCompact (K∩{x : Coord3 | δ≤x 2}) :=
    hK.inter_right (isClosed_le continuous_const (continuous_apply 2))
  have hKn : IsCompact (K∩{x : Coord3 | x 2≤ -δ}) :=
    hK.inter_right (isClosed_le (continuous_apply 2) continuous_const)
  have hsp : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => rp j (q,x)) (K∩{x : Coord3 | δ≤x 2}) := by
    filter_upwards [hs,hgap] with q hq hg
    intro j x hx
    have hh := wallPositiveCut_tsupport hδ (hg j) hx
    exact ⟨hq j hh.1,hh.2⟩
  have hsn : ∀ᶠ q in 𝓝 p,PairSupported (fun j x => rn j (q,x)) (K∩{x : Coord3 | x 2≤ -δ}) := by
    filter_upwards [hs,hgap] with q hq hg
    intro j x hx
    have hh := wallNegativeCut_tsupport hδ (hg j) hx
    exact ⟨hq j hh.1,hh.2⟩
  have hrpz (j x) : rp j (p,x)=0 := by simp [rp,wallPositiveCut,hz]
  have hrnz (j x) : rn j (p,x)=0 := by simp [rn,hz,hrpz]
  have hsolvep := regular_vanishing_family_correction_of_moment hu p hup hcpos
    (fun x hx => hD x hx.1 (ne_of_gt hx.2)) hKp
    (fun x hx => ⟨hKU hx.1,hδ.trans_le hx.2⟩) hV hp hrp hsp hrpz (by linarith : 0<ε/2)
  have hsolven := regular_vanishing_family_correction_of_moment hu p hun hcneg
    (fun x hx => hD x hx.1 (ne_of_lt hx.2)) hKn
    (fun x hx => ⟨hKU hx.1,lt_of_le_of_lt hx.2 (neg_neg_of_pos hδ)⟩)
    hV hp hrn hsn hrnz (by linarith : 0<ε/2)
  filter_upwards [hsolvep,hsolven,hs,hV.mem_nhds hp] with q solvep solven supp hq hm hmp
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun x => u (q,x)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hrq : CompactSmoothPair (fun j x => r j (q,x)) := by
    intro j
    refine ⟨?_,hK.of_isClosed_subset (isClosed_tsupport _) (supp j)⟩
    rw [contDiff_iff_contDiffAt]
    intro x
    exact ((hr j).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq,mem_univ x⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  have hmn : physicalSourceMoment (fun x => u (q,x)) (fun j x => rn j (q,x))=0 := by
    change physicalSourceMoment (fun x => u (q,x))
      ((fun j x => r j (q,x))-(fun j => wallPositiveCut δ (fun x => r j (q,x))))=0
    rw [physicalSourceMoment_sub huq.continuous hrq
      (fun index => ⟨wallPositiveCut_smooth (hrq index).1,(hrq index).2.mul_left⟩),hm,hmp,sub_self]
  have hh := ((solvep hmp).region_mono inter_subset_left).add huq
    ((solven hmn).region_mono inter_subset_left)
  have he : (fun j x => rp j (q,x))+(fun j x => rn j (q,x))=(fun j x => r j (q,x)) := by
    ext j x; simp only [Pi.add_apply,rn]; ring
  rw [he] at hh
  convert hh using 1
  ring

end ScalarConductivity

end
end

end OAI
