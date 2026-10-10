import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalChildAttachedCorrection
import OAI.Analysis.Conductivity.Branching.JoinedPhysicalEnds

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem physicalChildAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))≤-centralThickness →
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
  obtain ⟨d,hd,hds,hdzero,hde⟩ := childAttachedCorrection_supported s hs ha k κ p
  refine ⟨childH10Transport k ⟨d,hd⟩,childH10Transport_mem_H10 k _,?_,?_⟩
  · have hh := childH10Transport_zero_on k ⟨d,hd⟩
      {y | sourceCollarTime y≤-centralThickness} hdzero
    exact hh
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



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

def physicalJet (v : ℝ) (g : Fin 3 → ℝ) : JetFiber := WithLp.toLp 2 (Fin.cases v g)

lemma weak_jet_eq_iff (u : H1) (x : R3) (v : ℝ) (g : Fin 3 → ℝ) :
    u.val x=physicalJet v g ↔ weakValue u x=v ∧ ∀ i,weakGradient u x i=g i := by
  constructor
  · intro h
    constructor
    · exact congrArg (fun z : JetFiber => z 0) h
    · intro i
      exact congrArg (fun z : JetFiber => z i.succ) h
  · rintro ⟨hv,hg⟩
    ext i
    exact Fin.cases hv hg i

lemma weak_jet_zero_iff (u : H1) (x : R3) :
    u.val x=0 ↔ weakValue u x=0 ∧ ∀ i,weakGradient u x i=0 := by
  have he : physicalJet 0 (fun _ => 0)=0 := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [←he,weak_jet_eq_iff]

def H1JetOn (u : H1) (D : Set (Fin 3 → ℝ)) (f : R3 → JetFiber) : Prop :=
  ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → u.val x=f x

lemma H1JetOn.mono {u : H1} {D E : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (h : H1JetOn u D f) (hED : E⊆D) : H1JetOn u E f := by
  filter_upwards [h] with x hx hy
  exact hx (hED hy)

lemma H1JetOn.add {u v : H1} {D : Set (Fin 3 → ℝ)} {f g : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D g) :
    H1JetOn (u+v) D (fun x => f x+g x) := by
  filter_upwards [hu,hv,H1_add_jet_ae u v] with x hx hy he hm
  rw [he,hx hm,hy hm]

lemma H1JetOn.add_zero {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D (fun _ => 0)) : H1JetOn (u+v) D f := by
  simpa only [_root_.add_zero] using hu.add hv

lemma H1JetOn.zero_add {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D (fun _ => 0)) (hv : H1JetOn v D f) : H1JetOn (u+v) D f := by
  simpa only [_root_.zero_add] using hu.add hv

lemma H1JetOn.of_weak {u : H1} {D : Set (Fin 3 → ℝ)} {v : R3 → ℝ}
    {g : R3 → Fin 3 → ℝ}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=v x ∧
      ∀ i,weakGradient u x i=g x i) : H1JetOn u D (fun x => physicalJet (v x) (g x)) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_eq_iff u x _ _).mpr (hx hm)

lemma H1JetOn.zero_of_weak {u : H1} {D : Set (Fin 3 → ℝ)}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=0 ∧
      ∀ i,weakGradient u x i=0) : H1JetOn u D (fun _ => 0) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_zero_iff u x).mpr (hx hm)

end ScalarConductivity
end

end OAI
