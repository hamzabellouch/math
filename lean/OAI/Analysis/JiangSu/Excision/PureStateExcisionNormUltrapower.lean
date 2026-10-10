import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.UnitalNormToTracial
import OAI.Analysis.JiangSu.MatrixAlgebras.ProjectionLiftTraces
import OAI.Analysis.JiangSu.Excision.PureStateExcision
import OAI.Analysis.JiangSu.CentralSequences.NormUltrapowerEpsilonTest

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_state_excision_norm_ultrapower [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
    (hsimple : TopologicallySimple A) (hcmp : StrictComparison A) (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0 ≤ e n) (hen : ∀ n,‖e n‖ ≤ 1)
    (hf : ∀ n,0 ≤ f n) (hfn : ∀ n,‖f n‖ ≤ 1)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    (hsmall : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n)).re<η)
    {t : ℝ} (ht : 0<t)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,t ≤ (τ.functional (f n)).re)
    (hdefect : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (f n-f n*f n)).re<η)
    (φ : A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := A)).extremePoints ℝ)
    : ∃ s : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U, ‖s‖ ≤ 1 ∧
      star s*s=NormUltra.QuotientAlgebra.mk U e ∧
      NormUltra.QuotientAlgebra.mk U f*s=s ∧
      ∀ a : A,star s*NonunitalGamma.normInclusion U a*s=
        φ a • NormUltra.QuotientAlgebra.mk U e := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let g : ℕ → ℕ → A → ℝ
    | 0,k,s => ‖star s*s-e k‖
    | 1,k,s => ‖f k*s-s‖
    | j+2,k,s => ‖star s*a j*s-φ (a j) • e k‖
  have hg (j k : ℕ) (s : A) : 0 ≤ g j k s := by
    rcases j with _|(_|j) <;> exact norm_nonneg _
  have hsupply (m : ℕ) (ε : ℝ) (hε : 0<ε) :
      ∀ᶠ k in (U : Filter ℕ),∃ s : A,‖s‖ ≤ 2 ∧ ∀ j ≤ m,g j k s<ε := by
    have hs := pure_state_small_excision hsimple hcmp U e f he hen hf hfn hcentral
      hsmall ht hlarge hdefect φ hφ1 hpure (fun i : Fin (m+1) => a i) hε
    filter_upwards [hs] with k hk
    obtain ⟨s,hsn,hse,hsf,hsa⟩ := hk
    refine ⟨s,hsn,?_⟩
    intro j hj
    rcases j with _|(_|j)
    · exact hse
    · exact hsf
    · exact hsa ⟨j,by omega⟩
  obtain ⟨z,hzn,hzg⟩ := NormUltra.bounded_epsilon_test U hfree 2 (by norm_num) g hg hsupply
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  have hse : star (q z)*q z=q e :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star z*z) e).mpr (hzg 0)
  have hsf : q f*q z=q z :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (f*z) z).mpr (hzg 1)
  have hcoeff (i : ℕ) : star (q z)*NonunitalGamma.normInclusion U (a i)*q z=
      φ (a i) • q e :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star z*boundedDiagonal (a i)*z)
      (φ (a i) • e)).mpr (hzg (i+2))
  have hnorme : ‖q e‖ ≤ 1 := (NormUltra.QuotientAlgebra.norm_mk_le e).trans
    (lp.norm_le_of_forall_le zero_le_one hen)
  have hnorm : ‖q z‖ ≤ 1 := by
    have hh : ‖star (q z)*q z‖=‖q z‖*‖q z‖ := CStarRing.norm_star_mul_self
    rw [hse] at hh
    nlinarith [norm_nonneg (q z)]
  refine ⟨q z,hnorm,hse,hsf,?_⟩
  have hc1 : Continuous (fun b : A => star (q z)*NonunitalGamma.normInclusion U b*q z) := by fun_prop
  have hc2 : Continuous (fun b : A => φ b • q e) := by fun_prop
  have hge := ha.equalizer hc1 hc2 (funext hcoeff)
  exact fun b => congrFun hge b

end DirectComparison

end
end

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U
local notation "T" => (fun τ : TracialState A => τ)
local notation "q" => normToTracial (A := A) U
local notation "L" => familyLimitTrace T U

 theorem pure_state_excision_of_trace_projection
    (hsimple : TopologicallySimple A) (hcmp : StrictComparison A)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (E F : N) (he : 0≤E) (hen : ‖E‖≤1) (hsmall : q E=0)
    (hf : 0≤F) (hfn : ‖F‖≤1)
    (hcentral : ∀ a : A,F*NonunitalGamma.normInclusion U a=NonunitalGamma.normInclusion U a*F)
    (hprojection : IsStarProjection (q F))
    {t : ℝ} (ht : 0<t) (hlarge : ∀ s : ℕ → TracialState A,2*t ≤ ((L s).functional (q F)).re)
    (φ : A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := A)).extremePoints ℝ) :
    ∃ z : N,‖z‖≤1 ∧ star z*z=E ∧ F*z=z ∧
      ∀ a : A,star z*NonunitalGamma.normInclusion U a*z=φ a • E := by
  classical
  obtain ⟨e,heq,hep,hen'⟩ := NormUltra.QuotientAlgebra.positive_contraction_representative he hen
  obtain ⟨f,hfq,hfp,hfn'⟩ := NormUltra.QuotientAlgebra.positive_contraction_representative hf hfn
  have hcen (a : A) : Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0) := by
    apply (NormUltra.QuotientAlgebra.mk_eq_mk_iff (f*boundedDiagonal a) (boundedDiagonal a*f)).mp
    rw [NormUltra.QuotientAlgebra.mk_mul,NormUltra.QuotientAlgebra.mk_mul,hfq]
    exact hcentral a
  have hsm (η : ℝ) (hη : 0<η) : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (e n)).re<η := by
    have hezero : (familyNullIdeal T (U : Filter ℕ)).quotientMap e=0 := by
      change q (NormUltra.QuotientAlgebra.mk U e)=0
      rwa [heq]
    have hz := (familyQuotientMap_eq_zero T U e).mp hezero
    filter_upwards [hz.eventually_lt_const hη] with n hn τ
    exact ((Complex.re_le_norm _).trans ((trace_norm_le_twoNorm τ _).trans
      (traceTwoNorm_le_family T τ _))).trans_lt hn
  have hpr : IsStarProjection ((familyNullIdeal T (U : Filter ℕ)).quotientMap f) := by
    change IsStarProjection (q (NormUltra.QuotientAlgebra.mk U f))
    rwa [hfq]
  have hbig : ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,t≤(τ.functional (f n)).re := by
    have hg := uniform_trace_gap_eventually U (0 : lp (fun _ : ℕ => A) ∞) f ht (by
      intro s
      simpa only [map_zero,Complex.zero_re,zero_add,←normToTracial_mk,hfq] using hlarge s)
    change ∀ᶠ n in (U : Filter ℕ),∀ τ : TracialState A,
      (τ.functional (0:A)).re+t≤(τ.functional (f n)).re at hg
    simpa only [map_zero,Complex.zero_re,zero_add] using hg
  obtain ⟨z,hzn,hze,hzf,hza⟩ := pure_state_excision_norm_ultrapower hsimple hcmp U hfree
    e f hep hen' hfp hfn' hcen hsm ht hbig
    (fun η hη => projection_lift_defect U f hpr hη) φ hφ1 hpure
  exact ⟨z,hzn,by rwa [heq] at hze,by rwa [hfq] at hzf,
    fun a => by simpa only [heq] using hza a⟩

end DirectComparison

end
end

end OAI
