import Mathlib
import OAI.Analysis.Commutator.OrthogonalLinkFamily

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (e f : H →L[ℂ] H)

variable (S : Set (Link M e f)) (hS : OrthogonalLinks M e f S)

def finiteProjection (s : Finset S) : H →L[ℂ] H := ∑ v∈s,v.val.final

include hS

lemma family_cross {v w : S} (hne : v≠w) : star v.val.val*w.val.val=0 :=
  hS v.property w.property (fun h => hne (Subtype.ext h))

lemma family_final_cross {v w : S} (hne : v≠w) : v.val.final*w.val.final=0 := by
  change (v.val.val*star v.val.val)*(w.val.val*star w.val.val)=0
  calc
    _=v.val.val*(star v.val.val*w.val.val)*star w.val.val := by noncomm_ring
    _=0 := by rw [family_cross M e f S hS hne,mul_zero,zero_mul]

lemma finiteProjection_projection (s : Finset S) : IsStarProjection (finiteProjection M e f S s) := by
  classical
  constructor
  · change (∑ v∈s,v.val.final)*(∑ v∈s,v.val.final)=∑ v∈s,v.val.final
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem v hv]
    · exact v.val.final_projection.isIdempotentElem.eq
    · intro w hw hne
      exact family_final_cross M e f S hS hne.symm
  · change star (∑ v∈s,v.val.final)=∑ v∈s,v.val.final
    rw [star_sum]
    exact Finset.sum_congr rfl (fun v hv => v.val.final_projection.isSelfAdjoint.star_eq)

lemma finiteProjection_norm_le (s : Finset S) : ‖finiteProjection M e f S s‖≤1 :=
  (finiteProjection_projection M e f S hS s).norm_le _

omit hS in
lemma finiteProjection_mem (s : Finset S) : finiteProjection M e f S s∈M :=
  M.sum_mem (fun v _ => M.mul_mem v.val.mem (M.star_mem' v.val.mem))

lemma finiteProjection_mul_val (s : Finset S) {v : S} (hv : v∈s) :
    finiteProjection M e f S s*v.val.val=v.val.val := by
  classical
  rw [finiteProjection,Finset.sum_mul,Finset.sum_eq_single_of_mem v hv]
  · exact v.val.final_mul
  · intro w hw hne
    change (w.val.val*star w.val.val)*v.val.val=0
    rw [mul_assoc,family_cross M e f S hS hne,mul_zero]

omit hS in
lemma finiteProjection_target (s : Finset S) (hf : IsStarProjection f) :
    finiteProjection M e f S s*f=finiteProjection M e f S s := by
  rw [finiteProjection,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  exact (v.val.final_projection.le_iff_mul_eq_left hf).mp v.val.target_le

lemma finiteProjection_tendsto_generator (v : S) (x : H) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s (v.val.val x)) atTop
      (𝓝 (v.val.val x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop ({v}:Finset S)] with s hs
  exact (congrArg (fun T : H →L[ℂ] H => T x)
    (finiteProjection_mul_val M e f S hS s (hs (by simp)))).symm

lemma finiteProjection_tendsto_space {x : H} (hx : x∈familySpace M e f S) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s x) atTop (𝓝 x) := by
  have hspan : ∀ y∈Submodule.span ℂ {x : H | ∃ v∈S,∃ ξ : H,v.val ξ=x},
      Tendsto (fun s : Finset S => finiteProjection M e f S s y) atTop (𝓝 y) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v,hv,ξ,rfl⟩ := hy
      exact finiteProjection_tendsto_generator M e f S hS ⟨v,hv⟩ ξ
    | zero => simpa only [map_zero] using (tendsto_const_nhds (x:=(0:H)) (f:=atTop (α:=Finset S)))
    | add x y hx hy hxlim hylim =>
      simpa only [map_add] using hxlim.add hylim
    | smul c x hx hxlim =>
      simpa only [map_smul] using hxlim.const_smul c
  have hequi : Equicontinuous (fun s : Finset S => fun x : H => finiteProjection M e f S s x) :=
    (LipschitzWith.uniformEquicontinuous _ 1 (fun s =>
      ContinuousLinearMap.lipschitzWith_of_opNorm_le (finiteProjection_norm_le M e f S hS s))).equicontinuous
  exact (hequi x).tendsto_of_mem_closure
    (continuous_id.continuousAt.mono_left inf_le_left) hspan hx

theorem finiteProjection_tendsto (hf : IsStarProjection f)
    (hspan : (familySpace M e f S).starProjection=f) (x : H) :
    Tendsto (fun s : Finset S => finiteProjection M e f S s x) atTop (𝓝 (f x)) := by
  have hx : f x∈familySpace M e f S := by
    simpa only [hspan] using (familySpace M e f S).starProjection_apply_mem x
  have ht := finiteProjection_tendsto_space M e f S hS hx
  have he (s : Finset S) : finiteProjection M e f S s (f x)=finiteProjection M e f S s x :=
    congrArg (fun T : H →L[ℂ] H => T x) (finiteProjection_target M e f S s hf)
  simpa only [he] using ht

end Kadison.PartialIsometryOrder

end

end
end

end OAI
