import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ChildFullEndH1
import OAI.Analysis.Conductivity.Branching.ChildComplementPartition

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_zero_on (k : Fin 2) (u : H10) (D : Set (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=0 ∧ ∀ i,weakGradient u.val x i=0) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=0 ∧
      ∀ i,weakGradient (childH10Transport k u) x i=0 := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hf : f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=0 := by
    dsimp only [f]
    split_ifs with hb
    · have hh := hx hb hm
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh.1
      · exact hh.2 j
    · rfl
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=0
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=0
    rw [hf]
    rfl
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=0
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=0
    rw [hf]
    simp

lemma childH10Transport_add (k : Fin 2) (u v : H1) (hu : u∈H10) (hv : v∈H10) :
    childH10Transport k ⟨u+v,H10.add_mem hu hv⟩=
      childH10Transport k ⟨u,hu⟩+childH10Transport k ⟨v,hv⟩ := by
  apply Subtype.ext
  change childTransportJetCLM k (u.val+v.val)=
    childTransportJetCLM k u.val+childTransportJetCLM k v.val
  exact map_add (childTransportJetCLM k) u.val v.val

lemma physicalChildCompletionJoin_eq_transport (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (p : centralEnergySpace s) :
    physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p=
    childH10Transport k ⟨childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p,childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p⟩ := rfl

theorem physicalChildAttachedCorrection_exists (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,
        (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈
          sourceClosedCollarBand (-centralThickness) 0 →
        weakValue (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x=
          fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ
            ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
        ∀ i,weakGradient (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x i=sourceScale⁻¹*
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ
            ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis i)) := by
  obtain ⟨d,hd,hdzero,hde⟩ := childAttachedCorrection_exists s hs ha k κ p
  refine ⟨childH10Transport k ⟨d,hd⟩,childH10Transport_mem_H10 k _,?_,?_⟩
  · have hh := childH10Transport_zero_on k ⟨d,hd⟩
      {y | sourceCollarTime y≤-centralThickness} hdzero
    filter_upwards [hh] with x hx hc
    exact hx (((centralPhysical_time_iff (WithLp.ofLp x)).mp hc).2 k)
  · let u := childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p
    have hu : u∈H10 := childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p
    have hh := childH10Transport_local_jet k ⟨u+d,H10.add_mem hu hd⟩
      (D:=sourceClosedCollarBand (-centralThickness) 0)
      (fun y hy => sourceBand_mem_ball ⟨
        (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hy.1,
        hy.2.trans (by norm_num)⟩)
      (fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ)
      (fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ) hde
    have hsum : childH10Transport k ⟨u+d,H10.add_mem hu hd⟩=
        physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+childH10Transport k ⟨d,hd⟩ := by
      rw [childH10Transport_add k u d hu hd]
      exact congrArg (fun q : H1 => q+childH10Transport k ⟨d,hd⟩)
        (physicalChildCompletionJoin_eq_transport s hs ha k p).symm
    rw [hsum] at hh
    exact hh

end ScalarConductivity

end

end OAI
