import Mathlib
import OAI.Analysis.WeakInfiniteness.AnnihilatorStates
import OAI.Analysis.WeakInfiniteness.CompressedStates

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter

open scoped Topology ComplexOrder InnerProductSpace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_annihilator_state_of_not_mem
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b) (hbI : b ∉ I) :
    ∃ f ∈ annihilatorStates (I : Set A),0 < f ⟨b,hb.isSelfAdjoint⟩ := by
  classical
  let : IsClosed (I : Set A) := hI
  let : CompleteSpace I := hI.isComplete.completeSpace_coe
  let := CStarAlgebra.spectralOrder I
  let := CStarAlgebra.spectralOrderedRing I
  let L := CStarAlgebra.approximateUnit I
  have hL := CStarAlgebra.increasingApproximateUnit I
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hI.isOpen_compl.mem_nhds hbI)
  have hdist : ∀ y ∈ I,δ ≤ ‖b-y‖ := by
    intro y hy
    by_contra! hn
    have hyb : y ∈ Metric.ball b δ := by
      rw [Metric.mem_ball,dist_eq_norm,norm_sub_rev]
      exact hn
    exact hball hyb hy
  have hb0 : b ≠ 0 := fun hz => hbI (hz ▸ I.zero_mem)
  let : Nontrivial A := nontrivial_of_ne _ _ hb0
  obtain ⟨f₀,hf₀,_⟩ := exists_norming_real_state b hb
  let Good : I → Prop := fun e => 0 ≤ (e : A) ∧ ‖(e : A)‖ ≤ 1
  have hgood : ∀ᶠ e in L,Good e := by
    filter_upwards [hL.eventually_nonneg,hL.eventually_norm] with e he hen
    have heq : (e : A)=star ((CFC.sqrt e : I) : A)*((CFC.sqrt e : I) : A) := by
      have hh : e=star (CFC.sqrt e)*CFC.sqrt e := by
        rw [(CFC.sqrt_nonneg e).star_eq,CFC.sqrt_mul_sqrt_self e he]
      exact congrArg (fun x : I => (x : A)) hh
    exact ⟨heq.symm ▸ star_mul_self_nonneg (((CFC.sqrt e : I) : A)),hen⟩
  have hex : ∀ e : I,∃ f ∈ realStateSpace A,Good e →
      δ ≤ f ⟨b,hb.isSelfAdjoint⟩ ∧ ∀ c : A,
        f ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩ ≤
          (‖b‖/δ)*‖c*(1-(e : A))‖^2 := by
    intro e
    by_cases he : Good e
    · have heone : (e : A) ≤ 1 := (CStarAlgebra.mem_Icc_iff_norm_le_one.mpr he).2
      have hgn : ‖1-(e : A)‖ ≤ 1 :=
        (CStarAlgebra.mem_Icc_iff_norm_le_one.mp
          ⟨sub_nonneg.mpr heone,sub_le_self _ he.1⟩).2
      have hresI : b-(1-(e : A))*b*(1-(e : A)) ∈ I := by
        have heq : b-(1-(e : A))*b*(1-(e : A))=
            (e : A)*b+b*(e : A)-(e : A)*b*(e : A) := by noncomm_ring
        rw [heq]
        exact I.sub_mem (I.add_mem (hIR e e.property b) (hIL e e.property b))
          (hIR (e*b) (hIR e e.property b) e)
      have hdb : δ ≤ ‖(1-(e : A))*b*(1-(e : A))‖ := by
        simpa only [sub_sub_cancel] using hdist _ hresI
      obtain ⟨f,hf,hfb,hfc⟩ := exists_compressed_real_state hb
        (by change star (1-(e:A))=1-(e:A); rw [star_sub,star_one,he.1.star_eq]) hgn hδ hdb
      exact ⟨f,hf,fun _ => ⟨hfb,hfc⟩⟩
    · exact ⟨f₀,hf₀,fun hh => (he hh).elim⟩
  choose f hf hfb using hex
  let C := {g ∈ realStateSpace A | δ ≤ g ⟨b,hb.isSelfAdjoint⟩}
  have hC : IsCompact C := (realStateSpace_isCompact A).inter_right
    (isClosed_le continuous_const (WeakDual.eval_continuous _))
  have hfC : ∀ᶠ e in L,f e ∈ C := by
    filter_upwards [hgood] with e he
    exact ⟨hf e,(hfb e he).1⟩
  obtain ⟨g,hg,hcluster⟩ := hC.exists_mapClusterPt (u := f) (f := L) (le_principal_iff.mpr hfC)
  refine ⟨g,⟨hg.1,?_⟩,hδ.trans_le hg.2⟩
  intro x hx a
  let c : A := x*a
  have hcI : c ∈ I := hIR x hx a
  let cI : I := ⟨c,hcI⟩
  have ht : Tendsto (fun e : I => c*(e : A)) L (𝓝 c) :=
    (continuous_subtype_val.tendsto cI).comp (hL.tendsto_mul_left cI)
  have hzero : Tendsto (fun e : I => (‖b‖/δ)*‖c*(1-(e : A))‖^2) L (𝓝 0) := by
    have hh := (((tendsto_const_nhds : Tendsto (fun _ : I => c) L (𝓝 c)).sub ht).norm.pow 2).const_mul (‖b‖/δ)
    simpa only [mul_sub,mul_one,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] using hh
  let q : selfAdjoint A := ⟨star c*c,(star_mul_self_nonneg c).isSelfAdjoint⟩
  have htq : Tendsto (fun e : I => f e q) L (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun e => realState_nonneg (hf e) (star_mul_self_nonneg c))) _ hzero
    filter_upwards [hgood] with e he
    exact (hfb e he).2 c
  have hcq : MapClusterPt (g q) L (fun e => f e q) :=
    hcluster.continuousAt_comp (WeakDual.eval_continuous q).continuousAt
  exact eq_of_nhds_neBot (hcq.clusterPt.mono htq)

end

end WeakPureInfiniteness
end

end OAI
