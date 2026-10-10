import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearCommutingExtension
import OAI.Analysis.JiangSu.Nonunital.RelativeCommutation

namespace OAI

noncomputable section


namespace CStarConnectedLift
open scoped CStarAlgebra

variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]

def starMonoidHom (q : C →⋆ₐ[ℂ] D) : C →⋆* D where
  toFun := q
  map_one' := map_one q
  map_mul' := map_mul q
  map_star' := map_star q

theorem selfAdjoint_lift (q : C →⋆ₐ[ℂ] D) (hq : Function.Surjective q)
    (a : selfAdjoint D) : ∃ b : selfAdjoint C,q b=a := by
  obtain ⟨x,hx⟩ := hq a
  refine ⟨⟨(1/2:ℂ) • (x+star x),?_⟩,?_⟩
  · change star ((1/2:ℂ) • (x+star x))=(1/2:ℂ) • (x+star x)
    simp only [star_smul,star_add,star_star]
    norm_num
    rw [add_comm]
  · change q ((1/2:ℂ) • (x+star x))=a
    rw [map_smul,map_add,map_star,hx,a.prop.star_eq]
    module

lemma map_expUnitary (q : C →⋆ₐ[ℂ] D) (a : selfAdjoint C) :
    Unitary.map (starMonoidHom q) (selfAdjoint.expUnitary a)=
      selfAdjoint.expUnitary ⟨q a,a.prop.map q⟩ := by
  let : NormedAlgebra ℚ C := .restrictScalars ℚ ℂ C
  let : NormedAlgebra ℚ D := .restrictScalars ℚ ℂ D
  apply Subtype.ext
  change q (NormedSpace.exp (Complex.I • (a:C)))=NormedSpace.exp (Complex.I • q a)
  rw [NormedSpace.map_exp q (map_continuous q),map_smul]

theorem unitary_lift_of_joined (q : C →⋆ₐ[ℂ] D) (hq : Function.Surjective q)
    (u : unitary D) (hu : Joined 1 u) :
    ∃ v : unitary C,Unitary.map (starMonoidHom q) v=u := by
  have hp : u∈pathComponent (1:unitary D) := hu
  obtain ⟨l,hl⟩ := Unitary.mem_pathComponentOne_iff.mp hp
  have he (a : selfAdjoint D) : ∃ v : unitary C,
      Unitary.map (starMonoidHom q) v=selfAdjoint.expUnitary a := by
    obtain ⟨b,hb⟩ := selfAdjoint_lift q hq a
    refine ⟨selfAdjoint.expUnitary b,?_⟩
    rw [map_expUnitary]
    congr 1
    exact Subtype.ext hb
  have hs : ∃ v : unitary C,Unitary.map (starMonoidHom q) v=(l.map selfAdjoint.expUnitary).prod := by
    clear hl
    induction l with
    | nil => exact ⟨1,map_one _⟩
    | cons a l ih =>
      obtain ⟨v,hv⟩ := he a
      obtain ⟨w,hw⟩ := ih
      exact ⟨v*w,by simp only [map_mul,hv,hw,List.map_cons,List.prod_cons]⟩
  obtain ⟨v,hv⟩ := hs
  exact ⟨v,hv.trans hl⟩

end CStarConnectedLift


namespace CStarAbsorption
open scoped CStarAlgebra TensorProduct

variable {D T : Type*} [CStarAlgebra D] [CStarAlgebra T]

def ConnectedApproximateInnerHalfFlip (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) : Prop :=
  ∀ (F : Finset D) (ε : ℝ),0<ε → ∃ u : unitary T,Joined 1 u ∧
    ∀ d∈F,‖(u:T)*f (d ⊗ₜ[ℂ] 1)*star (u:T)-f (1 ⊗ₜ[ℂ] d)‖<ε

lemma continuous_unitaryMap {E N : Type*} [CStarAlgebra E] [CStarAlgebra N]
    (q : E →⋆ₐ[ℂ] N) : Continuous (Unitary.map (CStarConnectedLift.starMonoidHom q)) := by
  apply continuous_induced_rng.mpr
  exact (map_continuous q).comp continuous_subtype_val

end CStarAbsorption
namespace NonunitalRelative
open Pureness NonunitalGamma NormUltra NormUltra.QuotientAlgebra Filter CStarAbsorption
open scoped CStarAlgebra ENNReal TensorProduct

universe u
variable {D : Type u} [CStarAlgebra D] [Nontrivial D]
variable {A E T : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra E] [CStarAlgebra T]
variable [PartialOrder A] [StarOrderedRing A] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ)≤atTop)]
variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E) (hc : ∀ a d,Commute (j a) (κ d))
variable (hj : ∃ a : A,j a≠0) (φ : D →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U)
variable (hD : IsNuclear.{u,u} D) (hs : Pureness.TopologicallySimple D)
variable (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T) (hf : Function.Injective f) (hd : DenseRange f)
variable (hh : ConnectedApproximateInnerHalfFlip f)
local notation "NA" => QuotientAlgebra (fun _ : ℕ => A) U
local notation "NE" => QuotientAlgebra (fun _ : ℕ => E) U
local notation "C" => Centralizer U j
local notation "R" => RelativeQuotient U j

include hc hj φ hD hs hf hd hh in
 theorem relative_half_flip_lift (F : Finset D) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary C,∀ d∈F,∀ x : normCentralizer (A := A) U,
      centralSequenceQuotient U x=φ d →
      ‖RelativeCentral.quotientMap (inclusion U j)
        ((u:C)*centralMap U j x*star (u:C))-diagonal U j κ hc d‖<ε := by
  let : Nontrivial R := RelativeCentral.quotient_nontrivial (inclusion U j) (by
    obtain ⟨a,ha⟩ := hj
    refine ⟨a,?_⟩
    intro he
    apply ha
    have hi : Isometry (normInclusion (A := E) U) := normInclusion_isometry U
    change normInclusion U (j a)=0 at he
    exact hi.injective (by simpa only [map_zero] using he))
  let α : D →⋆ₐ[ℂ] R := (factor U j).comp φ
  let β : D →⋆ₐ[ℂ] R := diagonal U j κ hc
  have hβ : Function.Injective β := CurrentMain.simple_starAlgHom_injective (A := D) (D := R) hs β
  have hαβ : ∀ d e,Commute (α d) (β e) := fun d e => factor_commute_diagonal U j κ hc (φ d) e
  let θ := nuclearCommutingHom hD hs f hf hd α β hβ hαβ
  have hl (d : D) : θ (f (d ⊗ₜ[ℂ] 1))=α d := by
    rw [nuclearCommutingHom_tensor]
    simp only [commutingStarTensorHom_tmul,map_one,mul_one]
  have hr (d : D) : θ (f (1 ⊗ₜ[ℂ] d))=β d := by
    rw [nuclearCommutingHom_tensor]
    simp only [commutingStarTensorHom_tmul,map_one,one_mul]
  obtain ⟨v,hv,hve⟩ := hh F ε hε
  let w : unitary R := Unitary.map (CStarConnectedLift.starMonoidHom θ) v
  have hw : Joined 1 w := by
    have h := hv.map (continuous_unitaryMap θ)
    simpa only [map_one] using h
  let q := RelativeCentral.quotientMap (inclusion U j)
  obtain ⟨u,hu⟩ := CStarConnectedLift.unitary_lift_of_joined q
    ((RelativeCentral.annihilator (inclusion U j)).quotientMap_surjective) w hw
  have hu' : q (u:C)=θ (v:T) := congrArg Subtype.val hu
  refine ⟨u,?_⟩
  intro d hdF x hx
  have hx' : q (centralMap U j x)=α d := by
    change factor U j (centralSequenceQuotient U x)=factor U j (φ d)
    rw [hx]
  have hnorm := NonUnitalStarAlgHom.norm_apply_le θ
    ((v:T)*f (d ⊗ₜ[ℂ] 1)*star (v:T)-f (1 ⊗ₜ[ℂ] d))
  rw [map_sub,map_mul,map_mul,map_star,hl,hr] at hnorm
  change ‖q ((u:C)*centralMap U j x*star (u:C))-β d‖<ε
  rw [map_mul,map_mul,map_star,hu',hx']
  exact hnorm.trans_lt (hve d hdF)

end NonunitalRelative

end

end OAI
