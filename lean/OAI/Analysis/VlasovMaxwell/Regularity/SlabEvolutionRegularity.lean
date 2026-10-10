import Mathlib
import OAI.Analysis.VlasovMaxwell.Continuation.SlabSmoothBootstrap
import OAI.Analysis.VlasovMaxwell.LocalPDE.SlabRHS
import OAI.Analysis.VlasovMaxwell.LocalPDE.StrongLocalExistence

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma differentiableWithinAt_slab_time {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × U → W} {T t : ℝ}
    (hF : ContDiffOn ℝ 1 F {p | p.1∈Icc 0 T}) (ht : t∈Icc 0 T) (x : U) :
    DifferentiableWithinAt ℝ (fun r => F (r,x)) (Icc 0 T) t := by
  exact (hF.differentiableOn (by norm_num) (t,x) ht).comp t
    ((differentiableAt_id.prodMk (differentiableAt_const x)).differentiableWithinAt)
    (fun r hr => hr)

lemma C1ClassicalPrefix.hasDerivWithinAt_particle {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hf : SpatiallySmoothSlab T s.f) {t : ℝ} (ht : t∈Icc 0 T) (z : Phase) :
    HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t := by
  have he := (heq t ht).1 z.1 z.2
  have hdiff := (hf.1 t ht).differentiable (by simp) z
  simp only [spatialPartial] at he
  rw [← clm_sum_basis,← clm_sum_basis,add_assoc,fderiv_phase_split hdiff] at he
  have hderiv := (differentiableWithinAt_slab_time hs.f_c1 ht z).hasDerivWithinAt
  have hv : derivWithin (fun r => s.f (r,z)) (Icc 0 T) t=slabParticleRHS s (t,z) := by
    change derivWithin (fun r => s.f (r,z)) (Icc 0 T) t =
      -(fderiv ℝ (fun w => s.f (t,w)) z) (lorentzField s.E s.B (t,z))
    exact eq_neg_of_add_eq_zero_left he
  rwa [hv] at hderiv

lemma C1ClassicalPrefix.hasDerivWithinAt_electric {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hB : SpatiallySmoothSlab T s.B) {t : ℝ} (ht : t∈Icc 0 T) (x : Vec) :
    HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t := by
  have he := (heq t ht).2.1 x
  rw [curl_eq_curlMap ((hB.1 t ht).differentiable (by simp))] at he
  have hderiv := (differentiableWithinAt_slab_time hs.E_c1 ht x).hasDerivWithinAt
  have hv : derivWithin (fun r => s.E (r,x)) (Icc 0 T) t=slabElectricRHS s (t,x) := by
    change _=curlMap (fderiv ℝ (fun y => s.B (t,y)) x)-current (fun z => s.f (t,z)) x
    rw [sub_eq_iff_eq_add] at he
    rw [he]; abel
  rwa [hv] at hderiv

lemma C1ClassicalPrefix.hasDerivWithinAt_magnetic {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hE : SpatiallySmoothSlab T s.E) {t : ℝ} (ht : t∈Icc 0 T) (x : Vec) :
    HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t := by
  have he := (heq t ht).2.2.1 x
  rw [curl_eq_curlMap ((hE.1 t ht).differentiable (by simp))] at he
  have hderiv := (differentiableWithinAt_slab_time hs.B_c1 ht x).hasDerivWithinAt
  have hv : derivWithin (fun r => s.B (r,x)) (Icc 0 T) t=slabMagneticRHS s (t,x) :=
    eq_neg_of_add_eq_zero_left he
  rwa [hv] at hderiv

lemma C1ClassicalPrefix.spatialJetRegular_all {d : Datum} {s : Solution} {T : ℝ}
    (hT : 0<T) (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (n : ℕ) : SpatialJetRegular n (Icc 0 T) s.f ∧
      SpatialJetRegular n (Icc 0 T) s.E ∧ SpatialJetRegular n (Icc 0 T) s.B := by
  induction n with
  | zero => exact ⟨hf.spatialJetRegular,hE.spatialJetRegular,hB.spatialJetRegular⟩
  | succ n ih =>
    refine ⟨spatialJetRegular_succ hT n ih.1 (slabParticleRHS_regular ih.1 ih.2.1 ih.2.2) ?_,
      spatialJetRegular_succ hT n ih.2.1 (slabElectricRHS_regular hT n ih.1 ih.2.2 hs.compact) ?_,
      spatialJetRegular_succ hT n ih.2.2 (slabMagneticRHS_regular ih.2.1) ?_⟩
    · exact fun t ht z => hs.hasDerivWithinAt_particle heq hf ht z
    · exact fun t ht x => hs.hasDerivWithinAt_electric heq hB ht x
    · exact fun t ht x => hs.hasDerivWithinAt_magnetic heq hE ht x

lemma C1ClassicalPrefix.smooth {d : Datum} {s : Solution} {T : ℝ}
    (hT : 0<T) (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B) :
    ContDiffOn ℝ ∞ s.f (particleSlab T) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧
      ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
  refine ⟨?_,?_,?_⟩ <;> rw [contDiffOn_infty]
  · exact fun n => (hs.spatialJetRegular_all hT heq hf hE hB n).1.regular
  · exact fun n => (hs.spatialJetRegular_all hT heq hf hE hB n).2.1.regular
  · exact fun n => (hs.spatialJetRegular_all hT heq hf hE hB n).2.2.regular

theorem exists_local_smooth_classical_prefix (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, C1ClassicalPrefix d s T ∧ SlabEquations s T ∧
      ContDiffOn ℝ ∞ s.f (particleSlab T) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧
      ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
  obtain ⟨T,hT,s,hs,heq,hf,hE,hB⟩ := exists_local_spatially_smooth_classical d hd
  exact ⟨T,hT,s,hs,heq,hs.smooth hT heq hf hE hB⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.toC1 {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) : C1ClassicalPrefix d s T :=
  ⟨hs.f_smooth.of_le (by simp),hs.E_smooth.of_le (by simp),hs.B_smooth.of_le (by simp),
    hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,hs.equations,hs.initial_f,hs.initial_E,hs.initial_B⟩

structure BoundedClassicalPrefix (d : Datum) (s : Solution) (T : ℝ) : Prop where
  classical : SmoothClassicalPrefix d s T
  closed_equations : SlabEquations s T
  f_jets : BoundedSpatiallySmoothSlab T s.f
  E_jets : BoundedSpatiallySmoothSlab T s.E
  B_jets : BoundedSpatiallySmoothSlab T s.B

lemma exists_bounded_classical_prefix (d : Datum) (hd : Admissible d) :
    ∃ T : ℝ, 0<T ∧ ∃ s : Solution, BoundedClassicalPrefix d s T := by
  obtain ⟨T,hT,s,hs,he,hf,hE,hB⟩ := exists_local_smooth_bounded_prefix d hd
  exact ⟨T,hT,s,hs,he,hf,hE,hB⟩

def pasteSolution (T : ℝ) (s a : Solution) : Solution :=
  ⟨timePaste T s.f a.f,timePaste T s.E a.E,timePaste T s.B a.B⟩

lemma slabRHS_congr {s a : Solution} {t r : ℝ}
    (hf : (fun z => s.f (t,z))=(fun z => a.f (r,z)))
    (hE : (fun x => s.E (t,x))=(fun x => a.E (r,x)))
    (hB : (fun x => s.B (t,x))=(fun x => a.B (r,x))) :
    (∀ z, slabParticleRHS s (t,z)=slabParticleRHS a (r,z)) ∧
    (∀ x, slabElectricRHS s (t,x)=slabElectricRHS a (r,x)) ∧
    (∀ x, slabMagneticRHS s (t,x)=slabMagneticRHS a (r,x)) := by
  have hEv := congrFun hE
  have hBv := congrFun hB
  refine ⟨?_,?_,?_⟩
  · intro z
    simp only [slabParticleRHS,lorentzField,hf,hEv,hBv]
  · intro x
    simp only [slabElectricRHS,hf,hB]
  · intro x
    simp only [slabMagneticRHS,hE]

lemma pasteSolution_rhs (T : ℝ) (s a : Solution) :
    slabParticleRHS (pasteSolution T s a)=timePaste T (slabParticleRHS s) (slabParticleRHS a) ∧
    slabElectricRHS (pasteSolution T s a)=timePaste T (slabElectricRHS s) (slabElectricRHS a) ∧
    slabMagneticRHS (pasteSolution T s a)=timePaste T (slabMagneticRHS s) (slabMagneticRHS a) := by
  have hh (t : ℝ) :
      (∀ z, slabParticleRHS (pasteSolution T s a) (t,z)=timePaste T (slabParticleRHS s) (slabParticleRHS a) (t,z)) ∧
      (∀ x, slabElectricRHS (pasteSolution T s a) (t,x)=timePaste T (slabElectricRHS s) (slabElectricRHS a) (t,x)) ∧
      (∀ x, slabMagneticRHS (pasteSolution T s a) (t,x)=timePaste T (slabMagneticRHS s) (slabMagneticRHS a) (t,x)) := by
    by_cases ht : t≤T
    · have he := slabRHS_congr (s:=pasteSolution T s a) (a:=s)
        (timePaste_left T s.f a.f ht) (timePaste_left T s.E a.E ht) (timePaste_left T s.B a.B ht)
      simpa only [timePaste,ht,ite_true] using he
    · have hf : (fun z => (pasteSolution T s a).f (t,z))=(fun z => a.f (t-T,z)) := by
        funext z; simp [pasteSolution,timePaste,ht]
      have hE : (fun x => (pasteSolution T s a).E (t,x))=(fun x => a.E (t-T,x)) := by
        funext x; simp [pasteSolution,timePaste,ht]
      have hB : (fun x => (pasteSolution T s a).B (t,x))=(fun x => a.B (t-T,x)) := by
        funext x; simp [pasteSolution,timePaste,ht]
      simpa only [timePaste,ht,ite_false] using slabRHS_congr hf hE hB
  exact ⟨funext fun p => (hh p.1).1 p.2,funext fun p => (hh p.1).2.1 p.2,
    funext fun p => (hh p.1).2.2 p.2⟩

lemma spatiallySmooth_time_derivatives_smooth {s : Solution} {T : ℝ} (hT : 0<T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K)
    (hft : ∀ t∈Icc 0 T, ∀ z, HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t)
    (hEt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t)
    (hBt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ s.f (particleSlab T) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧
      ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
  have hh (n : ℕ) : SpatialJetRegular n (Icc 0 T) s.f ∧
      SpatialJetRegular n (Icc 0 T) s.E ∧ SpatialJetRegular n (Icc 0 T) s.B := by
    induction n with
    | zero => exact ⟨hf.spatialJetRegular,hE.spatialJetRegular,hB.spatialJetRegular⟩
    | succ n ih =>
      exact ⟨spatialJetRegular_succ hT n ih.1 (slabParticleRHS_regular ih.1 ih.2.1 ih.2.2) hft,
        spatialJetRegular_succ hT n ih.2.1 (slabElectricRHS_regular hT n ih.1 ih.2.2 hc) hEt,
        spatialJetRegular_succ hT n ih.2.2 (slabMagneticRHS_regular ih.2.1) hBt⟩
  refine ⟨?_,?_,?_⟩ <;> rw [contDiffOn_infty]
  · exact fun n => (hh n).1.regular
  · exact fun n => (hh n).2.1.regular
  · exact fun n => (hh n).2.2.regular

lemma slabEquations_of_time_derivatives {s : Solution} {T : ℝ} (hT : 0<T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (hft : ∀ t∈Icc 0 T, ∀ z, HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t)
    (hEt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t)
    (hBt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t)
    (hgauss : ∀ t∈Icc 0 T, (∀ x, divergence (fun y => s.E (t,y)) x=rho (fun z => s.f (t,z)) x) ∧
      (∀ x, divergence (fun y => s.B (t,y)) x=0)) : SlabEquations s T := by
  intro t ht
  refine ⟨?_,?_,?_,(hgauss t ht).1,(hgauss t ht).2⟩
  · intro x v
    rw [(hft t ht (x,v)).derivWithin (uniqueDiffOn_Icc hT t ht)]
    simp only [spatialPartial]
    rw [←clm_sum_basis,←clm_sum_basis,add_assoc,fderiv_phase_split ((hf.1 t ht).differentiable (by simp) (x,v))]
    exact neg_add_cancel _
  · intro x
    rw [(hEt t ht x).derivWithin (uniqueDiffOn_Icc hT t ht),
      curl_eq_curlMap ((hB.1 t ht).differentiable (by simp))]
    dsimp only [slabElectricRHS]; abel
  · intro x
    rw [(hBt t ht x).derivWithin (uniqueDiffOn_Icc hT t ht),
      curl_eq_curlMap ((hE.1 t ht).differentiable (by simp))]
    exact neg_add_cancel _

lemma BoundedClassicalPrefix.paste {d : Datum} {s a : Solution} {T S : ℝ}
    (hT : 0<T) (hS : 0<S) (hs : BoundedClassicalPrefix d s T)
    (ha : BoundedClassicalPrefix (timeSliceDatum s T) a S) :
    BoundedClassicalPrefix d (pasteSolution T s a) (T+S) := by
  have hjf (z : Phase) : s.f (T,z)=a.f (0,z) := (ha.classical.initial_f z).symm
  have hjE (x : Vec) : s.E (T,x)=a.E (0,x) := (ha.classical.initial_E x).symm
  have hjB (x : Vec) : s.B (T,x)=a.B (0,x) := (ha.classical.initial_B x).symm
  have hf := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.f_jets ha.f_jets hjf
  have hE := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.E_jets ha.E_jets hjE
  have hB := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.B_jets ha.B_jets hjB
  have hjR := slabRHS_congr (funext hjf) (funext hjE) (funext hjB)
  have hR := pasteSolution_rhs T s a
  have hft (t : ℝ) (ht : t∈Icc 0 (T+S)) (z : Phase) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).f (r,z))
        (slabParticleRHS (pasteSolution T s a) (t,z)) (Icc 0 (T+S)) t := by
    rw [hR.1]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu w => hs.classical.toC1.hasDerivWithinAt_particle hs.closed_equations hs.f_jets.1 hu w)
      (fun u hu w => ha.classical.toC1.hasDerivWithinAt_particle ha.closed_equations ha.f_jets.1 hu w)
      hjf hjR.1 ht z
  have hEt (t : ℝ) (ht : t∈Icc 0 (T+S)) (x : Vec) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).E (r,x))
        (slabElectricRHS (pasteSolution T s a) (t,x)) (Icc 0 (T+S)) t := by
    rw [hR.2.1]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu y => hs.classical.toC1.hasDerivWithinAt_electric hs.closed_equations hs.B_jets.1 hu y)
      (fun u hu y => ha.classical.toC1.hasDerivWithinAt_electric ha.closed_equations ha.B_jets.1 hu y)
      hjE hjR.2.1 ht x
  have hBt (t : ℝ) (ht : t∈Icc 0 (T+S)) (x : Vec) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).B (r,x))
        (slabMagneticRHS (pasteSolution T s a) (t,x)) (Icc 0 (T+S)) t := by
    rw [hR.2.2]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu y => hs.classical.toC1.hasDerivWithinAt_magnetic hs.closed_equations hs.E_jets.1 hu y)
      (fun u hu y => ha.classical.toC1.hasDerivWithinAt_magnetic ha.closed_equations ha.E_jets.1 hu y)
      hjB hjR.2.2 ht x
  have hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 (T+S),
      tsupport (fun z => (pasteSolution T s a).f (t,z)) ⊆ K := by
    obtain ⟨K,hK,hKb⟩ := hs.classical.compact
    obtain ⟨L,hL,hLb⟩ := ha.classical.compact
    refine ⟨K∪L,hK.union hL,?_⟩
    intro t ht
    change tsupport (fun z => timePaste T s.f a.f (t,z)) ⊆ K∪L
    by_cases hh : t≤T
    · rw [timePaste_left T s.f a.f hh]
      exact (hKb t ⟨ht.1,hh⟩).trans subset_union_left
    · rw [timePaste_right T s.f a.f hjf (le_of_not_ge hh)]
      exact (hLb (t-T) ⟨by linarith,by linarith [ht.2]⟩).trans subset_union_right
  have heq : SlabEquations (pasteSolution T s a) (T+S) := by
    apply slabEquations_of_time_derivatives (add_pos hT hS) hf.1 hE.1 hB.1 hft hEt hBt
    intro t ht
    change (∀ x, divergence (fun y => timePaste T s.E a.E (t,y)) x=
      rho (fun z => timePaste T s.f a.f (t,z)) x) ∧
      (∀ x, divergence (fun y => timePaste T s.B a.B (t,y)) x=0)
    by_cases hh : t≤T
    · rw [timePaste_left T s.E a.E hh,timePaste_left T s.f a.f hh,timePaste_left T s.B a.B hh]
      exact ⟨(hs.closed_equations t ⟨ht.1,hh⟩).2.2.2.1,(hs.closed_equations t ⟨ht.1,hh⟩).2.2.2.2⟩
    · rw [timePaste_right T s.E a.E hjE (le_of_not_ge hh),timePaste_right T s.f a.f hjf (le_of_not_ge hh),
        timePaste_right T s.B a.B hjB (le_of_not_ge hh)]
      have hu : t-T∈Icc 0 S := ⟨by linarith,by linarith [ht.2]⟩
      exact ⟨(ha.closed_equations (t-T) hu).2.2.2.1,(ha.closed_equations (t-T) hu).2.2.2.2⟩
  obtain ⟨hfs,hEs,hBs⟩ := spatiallySmooth_time_derivatives_smooth (add_pos hT hS)
    hf.1 hE.1 hB.1 hc hft hEt hBt
  refine ⟨⟨hfs,hEs,hBs,?_,slabTimeContinuousL2_timePaste hT.le hS.le hs.classical.E_L2 ha.classical.E_L2 hjE,
    slabTimeContinuousL2_timePaste hT.le hS.le hs.classical.B_L2 ha.classical.B_L2 hjB,hc,heq.equationsBefore,?_,?_,?_⟩,
    heq,hf,hE,hB⟩
  · intro t ht z
    change 0≤timePaste T s.f a.f (t,z)
    by_cases hh : t≤T
    · rw [congrFun (timePaste_left T s.f a.f hh) z]
      exact hs.classical.nonnegative t ⟨ht.1,hh⟩ z
    · rw [congrFun (timePaste_right T s.f a.f hjf (le_of_not_ge hh)) z]
      exact ha.classical.nonnegative (t-T) ⟨by linarith,by linarith [ht.2]⟩ z
  · intro z; exact (congrFun (timePaste_left T s.f a.f hT.le) z).trans (hs.classical.initial_f z)
  · intro x; exact (congrFun (timePaste_left T s.E a.E hT.le) x).trans (hs.classical.initial_E x)
  · intro x; exact (congrFun (timePaste_left T s.B a.B hT.le) x).trans (hs.classical.initial_B x)

theorem BoundedClassicalPrefix.extend {d : Datum} {s : Solution} {T : ℝ}
    (hT : 0<T) (hs : BoundedClassicalPrefix d s T) :
    ∃ U : ℝ, T<U ∧ ∃ a : Solution, BoundedClassicalPrefix d a U ∧
      (∀ t∈Icc 0 T, (∀ z, a.f (t,z)=s.f (t,z)) ∧
        (∀ x, a.E (t,x)=s.E (t,x)) ∧ (∀ x, a.B (t,x)=s.B (t,x))) := by
  have hd := hs.classical.slice_admissible hs.closed_equations hs.E_jets hs.B_jets ⟨hT.le,le_rfl⟩
  obtain ⟨S,hS,a,ha⟩ := exists_bounded_classical_prefix (timeSliceDatum s T) hd
  refine ⟨T+S,by linarith,pasteSolution T s a,hs.paste hT hS ha,?_⟩
  intro t ht
  exact ⟨congrFun (timePaste_left T s.f a.f ht.2),congrFun (timePaste_left T s.E a.E ht.2),
    congrFun (timePaste_left T s.B a.B ht.2)⟩

end RVM

end

end OAI
