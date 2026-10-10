import Mathlib
import OAI.Analysis.Commutator.PartialUnitaryOrder
import OAI.Analysis.Commutator.PartialIsometryMaximal
import OAI.Analysis.Commutator.NormalGNS
import OAI.Analysis.Commutator.ProjectionChains
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter ContinuousLinearMapWOT

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

namespace Kadison.FinitePatching

namespace PartialUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H)

def toLink (v : PartialUnitary M) : PartialIsometryOrder.Link M 1 1 where
  val := v.val
  mem := v.val.property
  triple := congrArg Subtype.val (show v.val*star v.val*v.val=v.val by
    rw [v.mul_star,v.support_mul])
  source_le := by
    have he : star (v.val : H →L[ℂ] H)*(v.val : H →L[ℂ] H)=v.support :=
      congrArg Subtype.val v.star_mul
    rw [he]
    exact (v.projection.map M.toStarSubalgebra.subtype).le_one
  target_le := by
    have he : (v.val : H →L[ℂ] H)*star (v.val : H →L[ℂ] H)=v.support :=
      congrArg Subtype.val v.mul_star
    rw [he]
    exact (v.projection.map M.toStarSubalgebra.subtype).le_one

lemma toLink_initial (v : PartialUnitary M) :
    (toLink M v).initial=(v.support : H →L[ℂ] H) := by
  change (star v.val*v.val : M).val=v.support.val
  exact congrArg Subtype.val v.star_mul

lemma toLink_mono : Monotone (toLink M) := by
  intro v w h
  apply (PartialIsometryOrder.Link.le_def _ _).mpr
  rw [toLink_initial,toLink_initial]
  constructor
  · exact h.1
  · change (w.val*v.support : M).val=v.val.val
    exact congrArg Subtype.val h.2

theorem chain_upper_with_L2_and_membership (τ : M →ₚ[ℂ] ℂ)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (c : Set (PartialUnitary M)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v : PartialUnitary M, (∀ w∈c,w ≤ v) ∧
      (∀ R : VonNeumannAlgebra H, (∀ w∈c,(w.val : H →L[ℂ] H)∈R) →
        (v.val : H →L[ℂ] H)∈R) ∧
      ∃ ω : Ultrafilter c, (ω : Filter c) ≤ atTop ∧
        Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) ∧
        Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)) (ω : Filter c) (𝓝 0) := by
  classical
  let : Nonempty c := hne.to_subtype
  let : IsDirectedOrder c := hc.directedOn.isDirectedOrder
  let ω : Ultrafilter c := Ultrafilter.of atTop
  have hω : (ω : Filter c) ≤ atTop := Ultrafilter.of_le _
  let P : c → H →L[ℂ] H := fun w => w.val.support
  obtain ⟨p,hp,hPp,hlim,hLeast⟩ := ProjectionChains.monotone_ultralimit ω hω P
    (fun w => w.val.projection.map M.toStarSubalgebra.subtype)
    (fun _ _ h => h.1)
  have hscalar : ∀ x y, Tendsto (fun w : c => inner ℂ (P w x) y) (ω : Filter c)
      (𝓝 (inner ℂ (p x) y)) := by
    intro x y
    have hh := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using hh.star
  have hpM : p∈M := WeakOperatorLimit.mem_vonNeumann hscalar M
    (Eventually.of_forall fun w => w.val.support.property)
  let ps : M := ⟨p,hpM⟩
  have hps : IsStarProjection ps := by
    constructor
    · exact Subtype.ext hp.isIdempotentElem.eq
    · exact Subtype.ext hp.isSelfAdjoint.star_eq
  have hcl : IsChain (·≤·) (toLink M '' c) :=
    hc.image_of_map_rel (·≤·) (·≤·) (toLink M) (fun _ _ h => toLink_mono M h)
  obtain ⟨U,hU⟩ := PartialIsometryOrder.chain_has_upper M
    (IsStarProjection.one _) (IsStarProjection.one _) (toLink M '' c) hcl
    (hne.image (toLink M))
  have hUw (w : c) : toLink M w.val ≤ U := hU ⟨w.val,w.property,rfl⟩
  have hUP (w : c) : U.val*P w=(w.val.val : H →L[ℂ] H) := by
    have hh := (PartialIsometryOrder.Link.le_def _ _).mp (hUw w) |>.2
    rw [toLink_initial] at hh
    exact hh
  have hpU : p ≤ U.initial := hLeast U.initial U.initial_projection (fun w => by
    have hh := (PartialIsometryOrder.Link.le_def _ _).mp (hUw w) |>.1
    simpa only [toLink_initial] using hh)
  have htarget (w : c) : U.val*P w*star U.val=P w := by
    have hleft : U.val*star (w.val.val : H →L[ℂ] H)=P w := by
      calc
        _=U.val*((P w)*star (w.val.val : H →L[ℂ] H)) := by
          rw [show P w*star (w.val.val : H →L[ℂ] H)=star (w.val.val : H →L[ℂ] H) from
            congrArg Subtype.val w.val.support_mul_star]
        _=P w := by
          rw [←mul_assoc,hUP]
          exact congrArg Subtype.val w.val.mul_star
    have hright : (w.val.val : H →L[ℂ] H)*star U.val=P w := by
      have hh := congrArg star hleft
      have hpw : star (P w)=P w :=
        (w.val.projection.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
      simpa only [StarMul.star_mul,star_star,hpw] using hh
    rw [hUP,hright]
  have hUpU : U.val*p*star U.val=p := by
    ext x
    apply ext_inner_right ℂ
    intro y
    have hl := hscalar (star U.val x) (star U.val y)
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
    have he : ∀ᶠ w : c in (ω : Filter c),
        inner ℂ (U.val (P w (star U.val x))) y=inner ℂ (P w x) y :=
      Eventually.of_forall fun w => congrArg (fun T : H →L[ℂ] H => inner ℂ (T x) y) (htarget w)
    exact tendsto_nhds_unique (hl.congr' he) (hscalar x y)
  let a : M := ⟨U.val*p,M.mul_mem U.mem hpM⟩
  have hpa : star a*a=ps := by
    apply Subtype.ext
    change star (U.val*p)*(U.val*p)=p
    rw [StarMul.star_mul,hp.isSelfAdjoint.star_eq]
    have he := (hp.le_iff_mul_eq_left U.initial_projection).mp hpU
    change p*(star U.val*U.val)=p at he
    calc
      _=(p*(star U.val*U.val))*p := by noncomm_ring
      _=p := by rw [he,hp.isIdempotentElem.eq]
  have hap : a*star a=ps := by
    apply Subtype.ext
    change (U.val*p)*star (U.val*p)=p
    rw [StarMul.star_mul,hp.isSelfAdjoint.star_eq]
    calc
      _=U.val*(p*p)*star U.val := by noncomm_ring
      _=p := by rw [hp.isIdempotentElem.eq,hUpU]
  have haP : a*ps=a := by
    apply Subtype.ext
    change (U.val*p)*p=U.val*p
    rw [mul_assoc,hp.isIdempotentElem.eq]
  have hPa : ps*a=a := by rw [←hap,mul_assoc,hpa,haP]
  let v : PartialUnitary M := ⟨a,ps,hps,hpa,hap,haP,hPa⟩
  have hupper (w : c) : w.val ≤ v := by
    refine ⟨hPp w,?_⟩
    apply Subtype.ext
    change (U.val*p)*P w=(w.val.val : H →L[ℂ] H)
    have hm : p*P w=P w :=
      ((w.val.projection.map M.toStarSubalgebra.subtype).le_iff_mul_eq_right hp).mp (hPp w)
    rw [mul_assoc,hm,hUP]
  have htrace : Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) := by
    exact (Complex.continuous_re.tendsto _).comp
      (NormalGNS.tendsto_trace M τ hnormal (fun w : c => w.val.support) ps 1
        (fun w => w.val.projection.norm_le _) (hps.norm_le _) hscalar)
  have hmember (R : VonNeumannAlgebra H) (hR : ∀ w∈c,(w.val : H →L[ℂ] H)∈R) :
      (v.val : H →L[ℂ] H)∈R := by
    apply WeakOperatorLimit.mem_vonNeumann (l:=(ω : Filter c))
      (T:=fun w : c => (w.val.val : H →L[ℂ] H)) _ R
      (Eventually.of_forall fun w => hR w.val w.property)
    intro x y
    have hl := hscalar x (star U.val y)
    simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hl
    simpa only [←mul_apply_eq_comp,hUP] using hl
  refine ⟨v,fun w hw => hupper ⟨w,hw⟩,hmember,ω,hω,htrace,?_⟩
  have hs : Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)^2)
      (ω : Filter c) (𝓝 0) := by
    have hh := (tendsto_const_nhds (x:=(τ v.support).re)).sub htrace
    simp only [sub_self] at hh
    exact hh.congr' (Eventually.of_forall fun w => (norm_sub_sq τ (hupper w)).symm)
  have hh := hs.sqrt
  simpa only [Real.sqrt_sq (TracialL2.norm_nonneg τ _),Real.sqrt_zero] using hh

theorem chain_upper_with_L2 (τ : M →ₚ[ℂ] ℂ)
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (c : Set (PartialUnitary M)) (hc : IsChain (·≤·) c) (hne : c.Nonempty) :
    ∃ v : PartialUnitary M, (∀ w∈c,w ≤ v) ∧
      ∃ ω : Ultrafilter c, (ω : Filter c) ≤ atTop ∧
        Tendsto (fun w : c => (τ w.val.support).re) (ω : Filter c) (𝓝 (τ v.support).re) ∧
        Tendsto (fun w : c => TracialL2.norm τ (v.val-w.val.val)) (ω : Filter c) (𝓝 0) := by
  obtain ⟨v,hv,_,hlim⟩ := chain_upper_with_L2_and_membership M τ hnormal c hc hne
  exact ⟨v,hv,hlim⟩

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
