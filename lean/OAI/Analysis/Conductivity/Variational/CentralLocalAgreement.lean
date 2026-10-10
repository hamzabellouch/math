import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CentralNeighborhoodCompletion
import OAI.Analysis.Conductivity.Variational.WholeBallJetFormula
import OAI.Analysis.Conductivity.Sobolev.PhysicalProductJet

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)

lemma centralInteriorCompletion_smooth_ae (f : centralSmoothFunctions) :
    (centralInteriorCompletion s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support
      (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy))
      (centralSmoothElement s f)).val=ᵐ[ballMeasure]
        (fun x => piSmoothJet ((centralJoinPartition 0)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x)) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (centralInteriorComponentCLM_smooth_value s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (centralInteriorComponentCLM_smooth_gradient s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralInteriorComponentCLM s
    (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact i (centralEmbedL s f)),h₀,ae_all_iff.mpr h₁] with x hj hv hg
  change physicalFourJetCLM (fun i => centralInteriorComponentCLM s
    (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact i (centralEmbedL s f)) x=_
  rw [hj]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

lemma parentCompletionJoin_smooth_central {a : ℝ} (ha : a<0) (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support (centralSmoothElement s f)).val x=
      piSmoothJet ((centralJoinPartition 1)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := by
  filter_upwards [parentLocalJetCLM_smooth_ae s hs ha (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact centralJoinPartition_parent_support f] with x hx
  intro hy
  change parentLocalJetCLM s hs ha _ _ (centralEmbedL s f) x=_
  rw [hx]
  apply localJoinedJet_eq_piSmoothJet
  · exact mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ((centralPhysical_time_iff _).mp hy).1)
  · exact (centralJoinPartition_smooth 1).differentiable (by simp) _
  · exact ((central_smooth f).comp sourcePairCLE.contDiff).differentiable (by simp) _

lemma physicalChildCompletionJoin_smooth_central {a : ℝ} (ha : 0<a) (k : Fin 2)
    (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) (centralSmoothElement s f)).val x=
      piSmoothJet ((centralJoinPartition (centralChildPatch k))*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := by
  have hB : ∀ y∈tsupport (centralJoinChildCutoff k),WithLp.toLp 2 y∈ball := by
    intro y hy
    have hb := centralJoinChildCutoff_support k hy
    exact sourceBand_mem_ball ⟨le_trans (by norm_num [centralThickness]) hb.1,
      le_trans hb.2 (by norm_num)⟩
  have hw := ballWholePiJetCLM_localJoined_ae hB
    (childLocalJetCLM_smooth_ae s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_support k) f)
  filter_upwards [childTransportJetCLM_ae_of_ae k _ _ hw] with x hx
  intro hy
  change childTransportJetCLM k (childLocalJetCLM s hs ha k
    (centralJoinChildCutoff_smooth k) (centralJoinChildCutoff_compact k) (centralEmbedL s f)) x=_
  rw [hx]
  let y := (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)
  have ht : a*(sourceCollarTime y-(-centralThickness)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr (((centralPhysical_time_iff _).mp hy).2 k))
  have hq := ((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k))
  have he := localJoinedJet_eq_piSmoothJet
    (τ:=fun y => a*(sourceCollarTime y-(-centralThickness)))
    (χ:=centralJoinChildCutoff k)
    (q:=fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
    (p:=fun y =>
      (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re)
    ht ((centralJoinChildCutoff_smooth k).differentiable (by simp) y) (hq.differentiable (by simp) y)
  have he' := congrArg (fun z : JetFiber => (WithLp.toLp 2
    (Fin.cases (z 0) (fun j => sourceScale⁻¹*z (childAxis j).succ)) : JetFiber)) he
  exact he'.trans (sourceChild_piSmoothJet_cancel
    ((centralJoinPartition (centralChildPatch k))*(fun y => f (sourcePairCoordinates y)))
    ((centralJoinPartition_smooth _).mul ((central_smooth f).comp sourcePairCLE.contDiff))
    (actualChildSign k) (WithLp.ofLp x))

end

open Set MeasureTheory Filter Topology

lemma centralPhysical_ae_interior :
    ∀ᵐ y : Fin 3 → ℝ,y∈centralPhysical → y∈interior centralPhysical := by
  have hp := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hc (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hp,ae_all_iff.mpr hc] with y hp hc
  intro hy
  have ht := (centralPhysical_time_iff y).mp hy
  exact centralPhysical_mem_interior_of_strict (lt_of_le_of_ne ht.1 hp.symm)
    (fun k => lt_of_le_of_ne (ht.2 k) (hc k))

lemma centralPhysical_ball_ae_interior :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical → WithLp.ofLp x∈interior centralPhysical :=
  ae_restrict_of_ae ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae centralPhysical_ae_interior)

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

def centralNeighborhoodRawCLM : CentralAmbient s →L[ℝ] JetSpace :=
  centralInteriorJetCLM s (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact+
  parentLocalJetCLM s hs ha₀ (centralJoinPartition_smooth 1) centralJoinPartition_parent_compact+
  ((childTransportJetCLM 0).comp (childLocalJetCLM s hs (ha 0) 0
      (centralJoinChildCutoff_smooth 0) (centralJoinChildCutoff_compact 0))+
    (childTransportJetCLM 1).comp (childLocalJetCLM s hs (ha 1) 1
      (centralJoinChildCutoff_smooth 1) (centralJoinChildCutoff_compact 1)))

lemma centralNeighborhoodCompletion_val (u : centralEnergySpace s) :
    (centralNeighborhoodCompletion s hs ha₀ ha u).val=centralNeighborhoodRawCLM s hs ha₀ ha u.val := by
  simp only [centralNeighborhoodCompletion,Fin.sum_univ_two,centralNeighborhoodRawCLM,
    add_apply,ContinuousLinearMap.comp_apply,Submodule.coe_add]
  rfl

def centralFullJetCLM : CentralAmbient s →L[ℝ] JetSpace :=
  physicalFourJetCLM.comp (ContinuousLinearMap.pi (fun i =>
    centralPhysicalWholeCLM.comp (centralAmbientComponent s i)))

lemma centralFullJetCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralFullJetCLM s (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralPhysicalWholeCLM_smooth_ae f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)),
    ae_all_iff.mpr hi] with x hx hi
  intro hy
  simp only [Function.comp_apply] at hi
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)) x=_
  rw [hx]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [indicator_of_mem hy,piSmoothJet,PiLp.toLp_apply,Fin.cases_zero,
      centralJetField,Matrix.cons_val_zero] using hi 0
  · change centralPhysicalWholeCLM (centralSmoothJet f j.succ) (WithLp.ofLp x)=_
    rw [hi j.succ,indicator_of_mem hy,central_parent_partial]
    rfl

lemma centralNeighborhoodRawCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  let zi := centralInteriorJetCLM s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact (centralEmbedL s f)
  let zp := parentLocalJetCLM s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralEmbedL s f)
  let zc (k : Fin 2) := childTransportJetCLM k (childLocalJetCLM s hs (ha k) k
    (centralJoinChildCutoff_smooth k) (centralJoinChildCutoff_compact k) (centralEmbedL s f))
  filter_upwards [Lp.coeFn_add (zi+zp) (zc 0+zc 1),Lp.coeFn_add zi zp,Lp.coeFn_add (zc 0) (zc 1),
    centralInteriorCompletion_smooth_ae s f,parentCompletionJoin_smooth_central s hs ha₀ f,
    physicalChildCompletionJoin_smooth_central s hs (ha 0) 0 f,
    physicalChildCompletionJoin_smooth_central s hs (ha 1) 1 f,
    centralPhysical_ball_ae_interior] with x hz hip hcc hi hp hc₀ hc₁ hinter
  intro hy
  change (zi+zp+(zc 0+zc 1)) x=_
  rw [hz]
  change (zi+zp) x+(zc 0+zc 1) x=_
  rw [hip,hcc]
  change zi x+zp x+(zc 0 x+zc 1 x)=_
  change zi x=_ at hi
  have hp' : zp x=piSmoothJet ((centralJoinPartition 1)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hp hy
  have h₀ : zc 0 x=piSmoothJet ((centralJoinPartition 2)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hc₀ hy
  have h₁ : zc 1 x=piSmoothJet ((centralJoinPartition 3)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hc₁ hy
  rw [hi,hp',h₀,h₁]
  have he := piSmoothJet_partition (q:=fun y => f (sourcePairCoordinates y)) centralJoinPartition_smooth
    ((central_smooth f).comp sourcePairCLE.contDiff) (WithLp.ofLp x)
    (centralJoinPartition_sum hy) (centralJoinPartition_derivative_sum (hinter hy))
  simpa only [Fin.sum_univ_four,add_assoc] using he

end ScalarConductivity

end

end OAI
