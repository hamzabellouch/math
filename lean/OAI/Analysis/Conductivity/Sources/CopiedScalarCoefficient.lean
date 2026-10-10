import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildJetScaling
import OAI.Analysis.Conductivity.Sources.WordGeometry
import OAI.Analysis.Conductivity.Variational.PhysicalOpenVoltage

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

def copiedScalarCoefficient (b : Coord3 → ℝ) (x : R3) : ℝ :=
  1+∑' ν : SourceWord,(sourceWordBlock ν).indicator
    (fun x => b (WithLp.ofLp ((sourceWordMap ν).symm x))-1) x

lemma copiedScalarCoefficient_on (b : Coord3 → ℝ) {ν : SourceWord} {x : R3}
    (hx : x∈sourceWordBlock ν) :
    copiedScalarCoefficient b x=b (WithLp.ofLp ((sourceWordMap ν).symm x)) := by
  rw [copiedScalarCoefficient,tsum_eq_single ν]
  · rw [indicator_of_mem hx]; ring
  · intro ω hω
    apply indicator_of_notMem
    exact fun h => hω (sourceWordBlock_unique h hx)

lemma copiedScalarCoefficient_outside (b : Coord3 → ℝ) {x : R3}
    (hx : ∀ ν : SourceWord,x∉sourceWordBlock ν) : copiedScalarCoefficient b x=1 := by
  simp only [copiedScalarCoefficient,indicator_of_notMem (hx _),tsum_zero,add_zero]

lemma copiedScalarCoefficient_measurable {b : Coord3 → ℝ} (hb : Measurable b) :
    Measurable (copiedScalarCoefficient b) := by
  apply measurable_const.add
  apply Measurable.tsum
  intro ν
  exact ((hb.comp ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).comp
    (sourceWordMap ν).symm.continuous).measurable).sub measurable_const).indicator
      (sourceWordBlock_isOpen ν).measurableSet

lemma copiedScalarCoefficient_bounds {b : Coord3 → ℝ} {c C : ℝ}
    (hb : ∀ y,b y∈Icc c C) (x : R3) :
    copiedScalarCoefficient b x∈Icc (min c 1) (max C 1) := by
  by_cases hx : ∃ ν : SourceWord,x∈sourceWordBlock ν
  · obtain ⟨ν,hν⟩ := hx
    rw [copiedScalarCoefficient_on b hν]
    exact ⟨(min_le_left _ _).trans (hb _).1,(hb _).2.trans (le_max_left _ _)⟩
  · rw [copiedScalarCoefficient_outside b (not_exists.mp hx)]
    exact ⟨min_le_right _ _,le_max_right _ _⟩

lemma copiedScalarCoefficient_one (b : Coord3 → ℝ) {x : R3}
    (hx : x∉closure sourceDomain) : copiedScalarCoefficient b x=1 := by
  apply copiedScalarCoefficient_outside
  intro ν hν
  exact hx (sourceWordCell_subset ν (sourceWordBlock_subset_cell ν hν))

lemma copiedScalarCoefficient_collar (b : Coord3 → ℝ) :
    EqualOneNearBoundary (copiedScalarCoefficient b) := by
  refine ⟨5/2,by norm_num,by norm_num,Eventually.of_forall ?_⟩
  intro x hx
  apply copiedScalarCoefficient_one
  intro hh
  have hn := sourceClosure_subset_ball hh
  simp only [Metric.mem_ball,dist_zero_right] at hn
  linarith

lemma copiedScalarCoefficient_root (b : Coord3 → ℝ) :
    ∀ᵐ y∂volume.restrict physicalOpenBlock,copiedScalarCoefficient b (WithLp.toLp 2 y)=b y := by
  filter_upwards [ae_restrict_mem (sourceOpenBlock_isOpen.preimage (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))).measurableSet] with y hy
  have hroot : WithLp.toLp 2 y∈sourceWordBlock [] := by
    rw [sourceWordBlock_root]
    exact hy
  exact copiedScalarCoefficient_on b hroot

lemma copiedScalarCoefficient_child (b : Coord3 → ℝ) (k : Fin 2) {x : R3}
    (hx : x∈closure sourceDomain) :
    copiedScalarCoefficient b (sourceChildEuclidean (actualChildSign k) x)=copiedScalarCoefficient b x := by
  by_cases h : ∃ ν : SourceWord,x∈sourceWordBlock ν
  · obtain ⟨ν,hν⟩ := h
    have hc := (sourceWordBlock_child_iff k hx (k::ν)).mpr ⟨ν,rfl,hν⟩
    rw [copiedScalarCoefficient_on b hc,copiedScalarCoefficient_on b hν]
    change b (WithLp.ofLp ((sourceWordMap ν).symm ((sourceChildEuclidean (actualChildSign k)).symm
      (sourceChildEuclidean (actualChildSign k) x))))=_
    rw [Homeomorph.symm_apply_apply]
  · rw [copiedScalarCoefficient_outside b (not_exists.mp h),copiedScalarCoefficient_outside b]
    intro ν hn
    obtain ⟨ω,hω,hxω⟩ := (sourceWordBlock_child_iff k hx ν).mp hn
    exact h ⟨ω,hxω⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
attribute [local instance] Classical.propDecidable

lemma sourceChildEuclidean_inverse_quasi (σ : ℝ) :
    Measure.QuasiMeasurePreserving (sourceChildEuclidean σ).symm volume volume := by
  refine ⟨(sourceChildEuclidean σ).symm.measurable,?_⟩
  rw [sourceChildEuclidean_inverse_map_volume]
  exact Measure.smul_absolutelyContinuous

lemma sourceChild_inverse_ballae (k : Fin 2) {p : R3 → Prop} (hp : ∀ᵐ x∂ballMeasure,p x) :
    ∀ᵐ x∂ballMeasure,(sourceChildEuclidean (actualChildSign k)).symm x∈ball →
      p ((sourceChildEuclidean (actualChildSign k)).symm x) := by
  exact ae_restrict_of_ae ((sourceChildEuclidean_inverse_quasi _).ae
    ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp hp))

def SourceSupported (u : H1) : Prop :=
  ∀ᵐ x∂ballMeasure,x∉closure sourceDomain → u.val x=0

lemma sourceSupported_iff (u : H1) : SourceSupported u ↔
    ∀ᵐ x∂ballMeasure,x∉closure sourceDomain → weakValue u x=0 ∧ weakGradient u x=0 := by
  constructor
  · intro hu
    filter_upwards [hu] with x hx hn
    change jetValue (u.val x)=0 ∧ jetGradient (u.val x)=0
    rw [hx hn]; exact ⟨map_zero _,map_zero _⟩
  · intro hu
    filter_upwards [hu] with x hx hn
    obtain ⟨hv,hg⟩ := hx hn
    rw [jetFiber_decomposition (u.val x)]
    change jetLiftValue (weakValue u x)+jetLiftGradient (weakGradient u x)=0
    rw [hv,hg,map_zero,map_zero,add_zero]

lemma SourceSupported.add {u v : H1} (hu : SourceSupported u) (hv : SourceSupported v) :
    SourceSupported (u+v) := by
  filter_upwards [hu,hv,Lp.coeFn_add u.val v.val] with x hx hy he hn
  change (u.val+v.val) x=0
  rw [he,Pi.add_apply,hx hn,hy hn,add_zero]

lemma SourceSupported.smul {u : H1} (hu : SourceSupported u) (r : ℝ) :
    SourceSupported (r • u) := by
  filter_upwards [hu,Lp.coeFn_smul r u.val] with x hx he hn
  change (r • u.val) x=0
  rw [he,Pi.smul_apply,hx hn,smul_zero]

lemma childH10Transport_support (k : Fin 2) (u : H10) (hu : SourceSupported u.val) :
    ∀ᵐ x∂ballMeasure,x∉sourceChildEuclidean (actualChildSign k) '' closure sourceDomain →
      (childH10Transport k u).val x=0 := by
  filter_upwards [childH10Transport_jet k u,sourceChild_inverse_ballae k hu] with x hx hs hn
  rw [hx]
  split_ifs with hb
  · have hi : (sourceChildEuclidean (actualChildSign k)).symm x∉closure sourceDomain := by
      intro h
      exact hn ⟨_,h,Homeomorph.apply_symm_apply _ x⟩
    have he := hs hb hi
    have hv := congrArg jetValue he
    have hg := congrArg jetGradient he
    change weakValue u.val ((sourceChildEuclidean (actualChildSign k)).symm x)=0 at hv
    change weakGradient u.val ((sourceChildEuclidean (actualChildSign k)).symm x)=0 at hg
    rw [hv,hg]
    ext i
    cases i using Fin.cases <;> simp
  · rfl

def childZeroTransport (k : Fin 2) : H10 →L[ℝ] H10 :=
  (childH10Transport k).codRestrict H10 (childH10Transport_mem_H10 k)

lemma SourceSupported.child (k : Fin 2) {u : H10} (hu : SourceSupported u.val) :
    SourceSupported (childZeroTransport k u).val := by
  filter_upwards [childH10Transport_support k u hu] with x hx hn
  exact hx (fun h => hn (subset_closure (source_child_closed_subset k h)))

lemma childH10Transport_bounded (k : Fin 2) (u : H10) {M : ℝ} (hM : 0≤M)
    (hu : ∀ᵐ x∂ballMeasure,|weakValue u.val x|≤M) :
    ∀ᵐ x∂ballMeasure,|weakValue (childH10Transport k u) x|≤M := by
  filter_upwards [childH10Transport_value k u,sourceChild_inverse_ballae k hu] with x hx hs
  rw [hx]
  split_ifs with hb
  · exact hs hb
  · simpa only [abs_zero] using hM

lemma copied_child_energy (b : Coord3 → ℝ) (k : Fin 2) (v : H10)
    (hv : SourceSupported v.val) (h : H1) :
    (∫ x,copiedScalarCoefficient b x*inner ℝ (weakGradient (childH10Transport k v) x) (weakGradient h x) ∂ballMeasure)=
      sourceScale*(∫ x,copiedScalarCoefficient b x*
        inner ℝ (weakGradient v.val x) (weakGradient (childH1Pullback k h) x) ∂ballMeasure) := by
  rw [child_energy_scaling]
  congr 1
  apply integral_congr_ae
  filter_upwards [(sourceSupported_iff v.val).mp hv] with x hx
  by_cases hd : x∈closure sourceDomain
  · rw [copiedScalarCoefficient_child b k hd]
  · rw [(hx hd).2,inner_zero_left,mul_zero,mul_zero]

end ScalarConductivity

end
end

end OAI
