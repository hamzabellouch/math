import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateExcisionNormUltrapower
import OAI.Analysis.JiangSu.CStarAlgebras.UnitalKernelCutoff

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : TracialState A => τ) U

 theorem pure_state_orthogonal_extension
    (hsimple : TopologicallySimple A) (hcmp : StrictComparison A)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hf : 0≤F) (hfn : ‖F‖≤1)
    (hcentral : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → TracialState A,2*t ≤ ((L s).functional (q F)).re)
    (φ : A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := A)).extremePoints ℝ)
    {m : ℕ} (r : Fin m → N) (hr : ∀ i,q (r i)=0) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      (∀ a : A,star z*ι a*z=φ a • E) ∧
      (∀ i a,star (r i)*ι a*z=0) ∧ (∀ i a,star z*ι a*r i=0) := by
  classical
  obtain ⟨d,hd,hdp,hdn,hdr,hdF,hdA⟩ := trace_kernel_cutoff_finite U hfree F r hr
  let G : N := (1-d)*F*(1-d)
  obtain ⟨hgp,hgn,hgF⟩ := CStarExcision.cutoff_preserves_bound hf hfn hdp hdn hdF
  have hqg : q G=q F := by simp only [G,map_mul,map_sub,normToTracial_one,hd,sub_zero,one_mul,mul_one]
  have hgc (a : A) : Commute G (ι a) :=
    (((Commute.one_left _).sub_left (hdA a)).mul_left (hcentral a)).mul_left
      ((Commute.one_left _).sub_left (hdA a))
  obtain ⟨z,hzn,hze,hgz,hza⟩ := pure_state_excision_of_trace_projection U hsimple hcmp hfree
    E G he hen hsmall hgp hgn (fun a => (hgc a).eq)
    (by rwa [hqg]) ht (fun s => by simpa only [hqg] using hlarge s) φ hφ1 hpure
  have hfz : F*z=z := CStarExcision.support_monotone
    ((norm_le_one_iff_of_nonneg F hf).mp hfn) hgF hgz
  have hgr (i : Fin m) : G*r i=0 := by
    simp only [G,mul_assoc,sub_mul,one_mul,hdr i,sub_self,mul_zero]
  have hrG (i : Fin m) : star (r i)*G=0 := by
    have hGstar : star G=G := hgp.star_eq
    simpa only [star_mul,hGstar,star_zero] using congrArg star (hgr i)
  have horth (i : Fin m) (a : A) : star (r i)*ι a*z=0 := by
    calc
      star (r i)*ι a*z=star (r i)*ι a*(G*z) := by rw [hgz]
      _=star (r i)*(ι a*G)*z := by noncomm_ring
      _=star (r i)*(G*ι a)*z := by rw [(hgc a).eq]
      _=(star (r i)*G)*ι a*z := by noncomm_ring
      _=0 := by rw [hrG,zero_mul,zero_mul]
  refine ⟨z,hzn,hze,hfz,hza,horth,?_⟩
  intro i a
  have hh := congrArg star (horth i (star a))
  simpa only [star_mul,map_star,star_star,star_zero,mul_assoc] using hh

end DirectComparison

end
end

section

noncomputable section
namespace CStarExcision
open NuclearNorm
open scoped ComplexOrder

variable {A B : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NonUnitalCStarAlgebra B]

 def stateRowElement (ρ : A →⋆ₙₐ[ℂ] B) (R : StateRow (A := A)) (z : B) : B :=
  assembled (fun i => ρ (R.left i)) z (fun i => ρ (R.right i))

 theorem stateRowElement_compress (ρ : A →⋆ₙₐ[ℂ] B) (R : StateRow (A := A))
    (φ : A →ₚ[ℂ] ℂ) (z E : B)
    (he : ∀ a, E*ρ a=ρ a*E) (hz : ∀ a,star z*ρ a*z=φ a • E) (a : selfAdjoint A) :
    star (stateRowElement ρ R z)*ρ (a:A)*stateRowElement ρ R z=
      ρ (R.map φ a : A)*E := by
  rw [stateRowElement,assembled_square,StateRow.map_apply]
  simp only [map_sum,map_smul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show star (ρ (R.left i))*ρ (a:A)*ρ (R.left j)=
    ρ (star (R.left i)*(a:A)*R.left j) by simp only [map_mul,map_star],hz]
  simp only [map_mul,map_star,mul_smul_comm,smul_mul_assoc,mul_assoc,he]

 omit [PartialOrder A] [StarOrderedRing A] in
 theorem stateRowElement_support (ρ : A →⋆ₙₐ[ℂ] B) (R : StateRow (A := A))
    (F z : B) (hF : ∀ a,F*ρ a=ρ a*F) (hz : F*z=z) :
    F*stateRowElement ρ R z=stateRowElement ρ R z := by
  simp only [stateRowElement,assembled,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    F*(ρ (R.left i)*z*ρ (R.right i))=(F*ρ (R.left i))*z*ρ (R.right i) := by noncomm_ring
    _=ρ (R.left i)*(F*z)*ρ (R.right i) := by rw [hF]; noncomm_ring
    _=ρ (R.left i)*z*ρ (R.right i) := by rw [hz]

 omit [PartialOrder A] [StarOrderedRing A] in
 theorem stateRowElement_cross (ρ : A →⋆ₙₐ[ℂ] B) (R : StateRow (A := A))
    (v z : B) (hz : ∀ a,star v*ρ a*z=0) (a : A) :
    star v*ρ a*stateRowElement ρ R z=0 := by
  simp only [stateRowElement,assembled,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro i _
  calc
    star v*ρ a*(ρ (R.left i)*z*ρ (R.right i))=
      (star v*ρ (a*R.left i)*z)*ρ (R.right i) := by rw [map_mul]; noncomm_ring
    _=0 := by rw [hz,zero_mul]

end CStarExcision

end
end

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology CStarAlgebra NuclearNorm CStarExcision
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => normToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : TracialState A => τ) U

 theorem nuclear_list_excision
    (hsimple : TopologicallySimple A) (hcmp : StrictComparison A)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → TracialState A,2*t ≤ ((L s).functional (q F)).re)
    (φ : A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (R : List (StateRow (A := A))) :
    ∃ v : N,q v=0 ∧ F*v=v ∧ ∀ a : selfAdjoint A,
      star v*ι (a:A)*v=ι (stateRowSum φ R a :A)*E := by
  classical
  induction R with
  | nil =>
    refine ⟨0,map_zero q,mul_zero F,?_⟩
    intro a
    simp [stateRowSum]
  | cons R S ih =>
    obtain ⟨v,hvq,hvF,hv⟩ := ih
    obtain ⟨z,_hzn,hze,hzF,hz,hvz,_hzv⟩ := pure_state_orthogonal_extension U hsimple hcmp hfree
      E F he hen hsmall hf hfn hfc hprojection ht hlarge φ hφ1 hpure
      (fun _ : Fin 1 => v) (fun _ => hvq)
    have hzq : q z=0 := by
      apply (CStarRing.star_mul_self_eq_zero_iff _).mp
      rw [←map_star,←map_mul,hze,hsmall]
    let w : N := stateRowElement ι R z
    have hwq : q w=0 := by
      simp only [w,stateRowElement,assembled,map_sum,map_mul,hzq,mul_zero,zero_mul,Finset.sum_const_zero]
    have hwF : F*w=w := stateRowElement_support ι R F z (fun a => (hfc a).eq) hzF
    have hw (a : selfAdjoint A) : star w*ι (a:A)*w=ι (R.map φ a : A)*E :=
      stateRowElement_compress ι R φ z E (fun a => (hec a).eq) hz a
    have hcross (a : A) : star v*ι a*w=0 :=
      stateRowElement_cross ι R v z (hvz 0) a
    have hcross' (a : selfAdjoint A) : star w*ι (a:A)*v=0 := by
      have hh := congrArg star (hcross (a:A))
      simpa only [star_mul,←map_star,a.property.star_eq,star_star,star_zero,mul_assoc] using hh
    refine ⟨w+v,by rw [map_add,hwq,hvq,add_zero],by rw [mul_add,hwF,hvF],?_⟩
    intro a
    calc
      star (w+v)*ι (a:A)*(w+v)=star w*ι (a:A)*w+star v*ι (a:A)*v := by
        simp only [star_add,add_mul,mul_add,hcross (a:A),hcross' a,add_zero,zero_add]
      _=ι (R.map φ a : A)*E+ι (stateRowSum φ S a : A)*E := by rw [hw,hv]
      _=ι (stateRowSum φ (R::S) a : A)*E := by
        change ι (R.map φ a : A)*E+ι (stateRowSum φ S a : A)*E =
          ι ((R.map φ a : A)+(stateRowSum φ S a : A))*E
        rw [map_add,add_mul]

end DirectComparison

end
end

end OAI
