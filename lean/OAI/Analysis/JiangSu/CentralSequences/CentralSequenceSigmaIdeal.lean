import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.NormCentralSequenceAlgebra

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology NormUltra
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

omit [PartialOrder A] [StarOrderedRing A] in
lemma normCentralizer_nonneg_iff (x : normCentralizer (A := A) U) :
    0≤x ↔ 0≤(x:N) := by
  constructor
  · exact map_nonneg (normCentralInclusion (A := A) U)
  · intro hx
    let r : normCentralizer (A := A) U := ⟨CFC.sqrt (x:N),fun a =>
      ((show Commute (x:N) (normInclusion U a) from x.property a).cfcₙ_nnreal NNReal.sqrt).eq⟩
    have hr : star r*r=x := by
      apply Subtype.ext
      change star (CFC.sqrt (x:N))*CFC.sqrt (x:N)=(x:N)
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ hx]
    rw [←hr]
    exact star_mul_self_nonneg r

variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable [TopologicalSpace.SeparableSpace A] [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "F" => CentralSequenceAlgebra (A := A) U
local notation "q" => centralSequenceQuotient (A := A) U

theorem centralSequence_trace_kernel_sigma_ideal
    (x w : ℕ → F) (hw : ∀ m, centralSequenceToTracial U (w m)=0) :
    ∃ d : F, centralSequenceToTracial U d=0 ∧ 0≤d ∧ d≤1 ∧
      (∀ m, d*w m=w m) ∧ (∀ m, x m*d=d*x m) := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  have hl : Function.Surjective q := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U)
  choose X hX using fun m => hl (x m)
  choose W hW using fun m => hl (w m)
  let z : ℕ → N := fun m => (Encodable.decode (α := ℕ⊕ℕ) m).elim 0
    (Sum.elim (fun j => normInclusion U (a j)) (fun j => (X j:N)))
  have hW0 (m : ℕ) : normToTracial U (W m:N)=0 := by
    change centralSequenceToTracial U (q (W m))=0
    rw [hW m,hw m]
  obtain ⟨d,hd,hdp,hdn,hdW,hdz⟩ := trace_kernel_sigma_ideal U Fact.out z (fun m => (W m:N)) hW0
  have hda (m : ℕ) : normInclusion U (a m)*d=d*normInclusion U (a m) := by
    simpa only [z,Encodable.encodek,Option.elim_some,Sum.elim_inl] using hdz (Encodable.encode (Sum.inl m : ℕ⊕ℕ))
  have hdX (m : ℕ) : (X m:N)*d=d*(X m:N) := by
    simpa only [z,Encodable.encodek,Option.elim_some,Sum.elim_inr] using hdz (Encodable.encode (Sum.inr m : ℕ⊕ℕ))
  have hdc : ∀ b : A, d*normInclusion U b=normInclusion U b*d := by
    have hi : Continuous (normInclusion (A := A) U) := by fun_prop
    have he := ha.equalizer (continuous_const.mul hi) (hi.mul continuous_const) (funext (fun m => (hda m).symm))
    exact fun b => congrFun he b
  let D : normCentralizer (A := A) U := ⟨d,hdc⟩
  have hDp : 0≤D := (normCentralizer_nonneg_iff U D).mpr hdp
  have hqn : ‖q D‖≤1 := (NonUnitalStarAlgHom.norm_apply_le q D).trans hdn
  refine ⟨q D,hd,map_nonneg q hDp,(CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_nonneg q hDp)).mp hqn,?_,?_⟩
  · intro m
    rw [←hW m,←map_mul]
    congr 1
    exact Subtype.ext (hdW m)
  · intro m
    rw [←hX m,←map_mul,←map_mul]
    congr 1
    exact Subtype.ext (hdX m)

end NonunitalGamma

end
end

end OAI
