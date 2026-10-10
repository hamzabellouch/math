import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

def crossBilinearCLM : Vec →L[ℝ] Vec →L[ℝ] Vec :=
  ({ toFun := crossCLM
     map_add' := by
       intro a b; ext c i; fin_cases i <;> simp [crossCLM,cross] <;> ring
     map_smul' := by
       intro r a; ext b i; fin_cases i <;> simp [crossCLM,cross] <;> ring } :
    Vec →ₗ[ℝ] Vec →L[ℝ] Vec).toContinuousLinearMap

lemma spatialJetRegular_lorentz {n : ℕ∞} {J : Set ℝ} {E B : Field}
    (hE : SpatialJetRegular n J E) (hB : SpatialJetRegular n J B) :
    SpatialJetRegular n J (lorentzField E B) := by
  have hv : SpatialJetRegular n J (fun p : ℝ × Phase => velocity p.2.2) :=
    spatialJetRegular_fixed (contDiff_velocity.comp contDiff_snd)
  have he := hE.precomp (ContinuousLinearMap.fst ℝ Vec Vec)
  have hb := hB.precomp (ContinuousLinearMap.fst ℝ Vec Vec)
  exact hv.prodMk (he.add (hv.bilinear hb crossBilinearCLM))

def slabParticleRHS (s : Solution) (p : ℝ × Phase) : ℝ :=
  -(fderiv ℝ (fun z => s.f (p.1,z)) p.2) (lorentzField s.E s.B p)
def slabElectricRHS (s : Solution) (p : ℝ × Vec) : Vec :=
  curlMap (fderiv ℝ (fun x => s.B (p.1,x)) p.2) - current (fun z => s.f (p.1,z)) p.2
def slabMagneticRHS (s : Solution) (p : ℝ × Vec) : Vec :=
  -curlMap (fderiv ℝ (fun x => s.E (p.1,x)) p.2)

lemma slabParticleRHS_regular {n : ℕ∞} {J : Set ℝ} {s : Solution}
    (hf : SpatialJetRegular n J s.f) (hE : SpatialJetRegular n J s.E) (hB : SpatialJetRegular n J s.B) :
    SpatialJetRegular n J (slabParticleRHS s) :=
  (hf.deriv.clm_apply (spatialJetRegular_lorentz hE hB)).neg

lemma slabMagneticRHS_regular {n : ℕ∞} {J : Set ℝ} {s : Solution}
    (hE : SpatialJetRegular n J s.E) : SpatialJetRegular n J (slabMagneticRHS s) :=
  (hE.deriv.clm curlMap).neg

lemma compact_particle_velocity_bound {T : ℝ} {s : Solution}
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    ∃ P : ℝ, 0<P ∧ ∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0 := by
  obtain ⟨K,hK,hKf⟩ := hc
  obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro t ht x v hv
  by_contra hf
  have hb := hC (x,v) (hKf t ht (subset_tsupport _ hf))
  have hn : ‖v‖≤‖(x,v)‖ := by
    change ‖v‖ ≤ max ‖x‖ ‖v‖
    exact le_max_right _ _
  exact (not_lt_of_ge (hn.trans (hb.trans (le_max_left _ _)))) hv

attribute [local instance] Measure.Subtype.measureSpace in
lemma spatialJetRegular_current {T : ℝ} (hT : 0<T) (n : ℕ) {s : Solution}
    (hf : SpatialJetRegular n (Icc 0 T) s.f)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    SpatialJetRegular n (Icc 0 T) (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2) := by
  obtain ⟨P,hP,hzero⟩ := compact_particle_velocity_bound hc
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ isClosed_closedBall.measurableSet.nullMeasurableSet]
    exact (isCompact_closedBall (0:Vec) P).measure_lt_top⟩
  have hv : SpatialJetRegular n (Icc 0 T) (fun p : ℝ × Phase => velocity p.2.2) :=
    spatialJetRegular_fixed (contDiff_velocity.comp contDiff_snd)
  have hG := hf.bilinear hv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec →L[ℝ] Vec)
  have hi := hG.integral_compact (μ:=(volume : Measure K)) continuous_subtype_val hT n
  apply hi.congr
  intro p hp
  change current (fun z => s.f (p.1,z)) p.2=∫ a : K, s.f (p.1,p.2,(a:Vec)) • velocity a
  rw [integral_subtype (show MeasurableSet K from isClosed_closedBall.measurableSet)
    (f:=fun v : Vec => s.f (p.1,p.2,v) • velocity v)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hv' : P<‖v‖ := by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv
  simp only [hzero p.1 hp p.2 v hv',zero_smul]

lemma slabElectricRHS_regular {T : ℝ} (hT : 0<T) (n : ℕ) {s : Solution}
    (hf : SpatialJetRegular n (Icc 0 T) s.f) (hB : SpatialJetRegular n (Icc 0 T) s.B)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    SpatialJetRegular n (Icc 0 T) (slabElectricRHS s) :=
  (hB.deriv.clm curlMap).sub (spatialJetRegular_current hT n hf hc)

end RVM
end

end OAI
