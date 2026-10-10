import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CentralSequenceSigmaIdeal
import OAI.Analysis.JiangSu.Excision.FiniteIdentityExcision
import OAI.Analysis.JiangSu.CentralSequences.IdentitySaturation

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "q" => NonunitalGamma.normToTracial (A := A) U
local notation "ι" => NonunitalGamma.normInclusion (A := A) U
local notation "L" => familyLimitTrace (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U

 theorem comparison_property_SI_projection_large
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hec : ∀ a : A,Commute E (ι a))
    (hf : 0≤F) (hfn : ‖F‖≤1) (hfc : ∀ a : A,Commute F (ι a))
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (q F)).re) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      (∀ a : A,star z*ι a*z=ι a*E) ∧ (∀ a : A,Commute z (ι a)) := by
  apply NormUltra.nonunital_identity_excision_saturation U hfree E F hen
  intro m a ε hε
  exact finite_nuclear_identity_excision U hnuc hsimple hprojectionless hcone hcmp hfree
    E F he hen hsmall hec hf hfn hfc hprojection ht hlarge (I := Fin (m+1)) a hε

variable [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "Q" => centralSequenceToTracial (A := A) U
local notation "π" => centralSequenceQuotient (A := A) U

 theorem central_sequence_property_SI_projection_large
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (E F : Fω) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : Q E=0)
    (hf : 0≤F) (hfn : ‖F‖≤1) (hprojection : IsStarProjection (Q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (Q F)).re) :
    ∃ z : Fω,‖z‖≤1 ∧ star z*z=E ∧ F*z=z := by
  have hπ : Function.Surjective π := NonunitalClosedIdeal.QuotientAlgebra.mk_surjective (normAnnihilator U)
  obtain ⟨e,heq,hep,hen'⟩ := CStarLift.exists_positive_contraction π hπ he hen
  obtain ⟨f,hfq,hfp,hfn'⟩ := CStarLift.exists_positive_contraction π hπ hf hfn
  have hsmall' : q (e:N)=0 := by
    change Q (π e)=0
    rw [heq,hsmall]
  have hFq : q (f:N)=Q F := by
    change Q (π f)=Q F
    rw [hfq]
  obtain ⟨z,hzn,hze,hzf,_hzex,hzc⟩ := comparison_property_SI_projection_large U hnuc hsimple
    hprojectionless hcone hcmp Fact.out (e:N) (f:N)
    ((normCentralizer_nonneg_iff U e).mp hep) hen' hsmall' (fun a => e.property a)
    ((normCentralizer_nonneg_iff U f).mp hfp) hfn' (fun a => f.property a)
    (by simpa only [hFq] using hprojection) ht (by simpa only [hFq] using hlarge)
  let Z : normCentralizer (A := A) U := ⟨z,fun a => (hzc a).eq⟩
  have hZe : star Z*Z=e := Subtype.ext hze
  have hZf : f*Z=Z := Subtype.ext hzf
  refine ⟨π Z,(NonUnitalStarAlgHom.norm_apply_le π _).trans hzn,?_,?_⟩
  · rw [←map_star,←map_mul,hZe,heq]
  · rw [←hfq,←map_mul,hZf]

end NonunitalSI

end
end

end OAI
