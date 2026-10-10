import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCompactTransporters
import Mathlib.Topology.Algebra.Group.DiscontinuousSubgroup

namespace OAI

/-! The actual Eisenstein and principal-group actions are properly
discontinuous. This supplies the topological quotient needed for global
cusp gluing from proved compact-chart transport bounds. -/
noncomputable section
open Set
open scoped MatrixGroups
namespace CubicFirstMoment

instance cubicThetaPoint_topology : TopologicalSpace CubicThetaPoint :=
  inferInstanceAs (TopologicalSpace {p : ℂ × ℝ // 0<p.2})

instance cubicThetaPoint_t2 : T2Space CubicThetaPoint :=
  inferInstanceAs (T2Space {p : ℂ × ℝ // 0<p.2})

instance cubicThetaPoint_secondCountable : SecondCountableTopology CubicThetaPoint :=
  inferInstanceAs (SecondCountableTopology {p : ℂ × ℝ // 0<p.2})

instance cubicThetaFullPointAction : MulAction SL(2,Eisenstein) CubicThetaPoint :=
  MulAction.compHom CubicThetaPoint cubicThetaFullComplex

lemma cubicThetaFullPointAction_apply (g : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    (g • p).val=cubicThetaMobius (cubicThetaFullComplex g) p.val := rfl

instance cubicThetaFullPointAction_continuous : ContinuousConstSMul SL(2,Eisenstein) CubicThetaPoint where
  continuous_const_smul g := by
    change Continuous (fun p : CubicThetaPoint =>
      (⟨cubicThetaMobius (cubicThetaFullComplex g) p.val,
        cubicThetaMobius_height_pos _ p.property⟩ : CubicThetaPoint))
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (cubicThetaMobius_continuousAt (cubicThetaFullComplex g) p.property).comp
      (x:=p) (f:=fun q : CubicThetaPoint => q.val) continuous_subtype_val.continuousAt

instance cubicThetaFullPointAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul SL(2,Eisenstein) CubicThetaPoint where
  finite_disjoint_inter_image := by
    intro K L hK hL
    have hK' := hK.image continuous_subtype_val
    have hL' := hL.image continuous_subtype_val
    have hKpos : ∀ p∈Subtype.val '' K, 0<p.2 := by
      rintro p ⟨q,_,rfl⟩
      exact q.property
    have hLpos : ∀ p∈Subtype.val '' L, 0<p.2 := by
      rintro p ⟨q,_,rfl⟩
      exact q.property
    apply (cubicThetaCompact_transporter_finite hK' hL' hKpos hLpos).subset
    rintro g ⟨q,⟨⟨p,hp,rfl⟩,hq⟩⟩
    refine ⟨p.val,⟨p,hp,rfl⟩,g • p,hq,?_⟩
    exact cubicThetaFullPointAction_apply g p

lemma cubicThetaPrincipalPointAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul cubicThetaPrincipalGroup CubicThetaPoint := inferInstance

end CubicFirstMoment

end

end OAI
