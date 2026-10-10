import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.FamilyProjectionLiftTraces
import OAI.Analysis.JiangSu.Excision.PureStateSmallExcision

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "q" => normToTracial (A := A) U
local notation "L" => familyLimitTrace T U

 theorem pure_state_excision_of_trace_projection
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hf : 0≤F) (hfn : ‖F‖≤1)
    (hcentral : ∀ a : A,F*NonunitalGamma.normInclusion U a=NonunitalGamma.normInclusion U a*F)
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → NormalizedTrace A,2*t ≤ ((L s).functional (q F)).re)
    (φ : Unitization ℂ A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := Unitization ℂ A)).extremePoints ℝ) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      ∀ a : A,star z*NonunitalGamma.normInclusion U a*z=φ (Unitization.inr a) • E := by
  classical
  obtain ⟨e,heq,hep,hen'⟩ := NormUltra.QuotientAlgebra.positive_contraction_representative he hen
  obtain ⟨f,hfq,hfp,hfn'⟩ := NormUltra.QuotientAlgebra.positive_contraction_representative hf hfn
  have hcen (a : A) : Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0) := by
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff (f*boundedConstant (A := A) a) (boundedConstant (A := A) a*f)).mp
    rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_mul,hfq]
    exact hcentral a
  have hsm (η : ℝ) (hη : 0<η) : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n)).re<η := by
    have hezero : (familyNullIdeal T (U : Filter ℕ)).quotientMap (boundedInr (A := A) e)=0 := by
      change q (NormUltra.QuotientAlgebra.mk U e)=0
      rwa [heq]
    have hz := (familyQuotientMap_eq_zero T U (boundedInr (A := A) e)).mp hezero
    filter_upwards [hz.eventually_lt_const hη] with n hn τ
    rw [←NormalizedTrace.unitized_inr]
    exact ((Complex.re_le_norm _).trans ((trace_norm_le_twoNorm (NormalizedTrace.unitized τ) _).trans
      (traceTwoNorm_le_family T τ _))).trans_lt hn
  have hpr : IsStarProjection ((familyNullIdeal T (U : Filter ℕ)).quotientMap (boundedInr (A := A) f)) := by
    change IsStarProjection (q (NormUltra.QuotientAlgebra.mk U f))
    rwa [hfq]
  have hbig : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,t≤(τ.functional (f n)).re := by
    have hg := FamilyProjection.uniform_trace_gap_eventually T U
      (0 : lp (fun _ : ℕ => Unitization ℂ A) ∞) (boundedInr (A := A) f) ht (by
        intro s
        have hh : (familyNullIdeal T (U : Filter ℕ)).quotientStarHom (boundedInr (A := A) f)=q F := by
          change q (NormUltra.QuotientAlgebra.mk U f)=q F
          rw [hfq]
        simpa only [map_zero,Complex.zero_re,zero_add,hh] using hlarge s)
    simpa only [lp.coeFn_zero,Pi.zero_apply,map_zero,Complex.zero_re,zero_add,
      boundedInr_apply,NormalizedTrace.unitized_inr] using hg
  obtain ⟨z,hzn,hze,hzf,hza⟩ := pure_state_excision_norm_ultrapower hsimple hprojectionless hcone hcmp U hfree
    e f hep hen' hfp hfn' hcen hsm ht hbig
    (fun η hη => by
      simpa only [boundedInr_apply,←Unitization.inr_mul,←Unitization.inr_sub,
        NormalizedTrace.unitized_inr] using
        FamilyProjection.projection_lift_defect T U (boundedInr (A := A) f) hpr hη) φ hφ1 hpure
  exact ⟨z,hzn,by rwa [heq] at hze,by rwa [hfq] at hzf,
    fun a => by simpa only [heq] using hza a⟩

end NonunitalSI

end
end

end OAI
