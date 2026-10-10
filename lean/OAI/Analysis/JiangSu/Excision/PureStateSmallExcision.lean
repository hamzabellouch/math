import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateExcisionNormUltrapower
import OAI.Analysis.JiangSu.Nonunital.ControlledComparison
import OAI.Analysis.JiangSu.Nonunital.EventualFullness

namespace OAI


noncomputable section
namespace NonunitalSI
open Pureness CurrentMain DirectComparison NonunitalGamma PureStateExcision Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_state_small_excision [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [Nontrivial A]
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (U : Ultrafilter ℕ)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0 ≤ e n) (hen : ∀ n,‖e n‖ ≤ 1)
    (hf : ∀ n,0 ≤ f n) (hfn : ∀ n,‖f n‖ ≤ 1)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    (hsmall : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n)).re<η)
    {t : ℝ} (ht : 0<t)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,t ≤ (τ.functional (f n)).re)
    (hdefect : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (f n-f n*f n)).re<η)
    (φ : Unitization ℂ A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := Unitization ℂ A)).extremePoints ℝ)
    {I : Type} [Fintype I] (a : I → Unitization ℂ A) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in (U : Filter ℕ),∃ s : A, ‖s‖ ≤ 2 ∧ ‖star s*s-e n‖<ε ∧
      ‖f n*s-s‖<ε ∧ ∀ i,‖compression (a i) s-φ (a i) • e n‖<ε := by
  obtain ⟨h,c,hh,hhn,hc,hcn,hc0,hhc,hex⟩ := pure_state_plateau_excision φ hφ1 hpure a
    (show 0<ε/16 by positivity)
  obtain ⟨β,hβ,hb⟩ := NonunitalSI.eventual_hereditary_upperCut_trace_lower hsimple hprojectionless U f hf hfn
    hcentral ht hlarge hdefect c hc hcn hc0
  let M : ℝ := (∑ i,‖φ (a i)‖)+1
  have hM : 1 ≤ M := by
    have hn := Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset I)) => norm_nonneg (φ (a i)))
    dsimp [M]; linarith
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hiM (i : I) : ‖φ (a i)‖ ≤ M := by
    have h := Finset.single_le_sum (fun j _ => norm_nonneg (φ (a j))) (Finset.mem_univ i)
    dsimp [M]; linarith
  let κ := min 1 (ε/(16*M))
  have hκ : 0<κ := lt_min zero_lt_one (by positivity)
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκb : 16*κ*M ≤ ε := by
    have h := min_le_right (1 : ℝ) (ε/(16*M))
    rw [le_div_iff₀ (by positivity)] at h
    dsimp [κ]; nlinarith
  have hκe : κ+κ<ε := by
    nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hM)]
  let δ := min 1 (ε*β/16)
  have hδ : 0<δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδb : δ ≤ ε*β/16 := min_le_right _ _
  have hsupport : 4*β⁻¹*δ ≤ ε/4 := by
    have heq : 4*β⁻¹*δ=(4*δ)/β := by ring
    rw [heq,div_le_iff₀ hβ]
    linarith
  have hcomm := (tendsto_order.1 (norm_central_boundedInr U f hcentral c)).2 δ hδ
  filter_upwards [hb δ hδ hδ1,hcomm,hsmall (κ*β) (mul_pos hκ hβ)] with n hn hnc hne
  let w : A := (hereditaryUpperCut δ (Unitization.inr (f n)) c).snd
  have hwI : (Unitization.inr w : Unitization ℂ A)=hereditaryUpperCut δ (Unitization.inr (f n)) c :=
    inr_hereditaryUpperCut hδ1 (f n) c
  have hw : 0≤w := Unitization.inr_nonneg_iff.mp (hwI.symm ▸
    hereditaryUpperCut_nonneg hδ.le (Unitization.inr (f n)) c hc.isSelfAdjoint)
  have hwn : ‖w‖≤1 := by
    rw [←Unitization.norm_inr (𝕜 := ℂ),hwI]
    exact hereditaryUpperCut_norm_le hδ (Unitization.inr (f n)) c
      (by simpa only [Unitization.norm_inr] using hfn n) hcn
  have hhw : h*Unitization.inr w=Unitization.inr w := by
    rw [hwI]
    exact hereditaryUpperCut_support δ (Unitization.inr (f n)) c h hhc
  have hn' (τ : NormalizedTrace A) : 2*β≤(τ.functional w).re := by
    rw [←NormalizedTrace.unitized_inr,hwI]
    exact hn τ
  obtain ⟨s,hsn,hse,hhs,hfs⟩ := small_trace_supported_isometry_inr hcone hcmp (e n) w h
    (Unitization.inr (f n)) (he n) (hen n) hw hwn hhw hκ hβ hκ hκ1 hne hn'
  refine ⟨s,hsn,hse.trans hκe,?_,?_⟩
  · change ‖Unitization.inr (f n)*c-c*Unitization.inr (f n)‖<δ at hnc
    have hwf := hereditaryUpperCut_error hδ (Unitization.inr (f n)) c
      (Unitization.inr_nonneg_iff.mpr (hf n))
      (by simpa only [Unitization.norm_inr] using hfn n) hcn
    rw [←hwI] at hwf
    rw [←Unitization.inr_mul,←Unitization.inr_sub,Unitization.norm_inr] at hfs
    have hcoef : 0 ≤ 2*β⁻¹ := by positivity
    have hbound : ‖f n*s-s‖ ≤ 4*β⁻¹*δ := by
      calc
        _ ≤ 2*β⁻¹*(‖Unitization.inr (f n)*c-c*Unitization.inr (f n)‖+δ) := hfs.trans
          (mul_le_mul_of_nonneg_left hwf hcoef)
        _ ≤ 4*β⁻¹*δ := by nlinarith [mul_le_mul_of_nonneg_left hnc.le hcoef]
    exact lt_of_le_of_lt (hbound.trans hsupport) (by linarith)
  · intro i
    have hseI : ‖star (Unitization.inr s : Unitization ℂ A)*Unitization.inr s-Unitization.inr (e n)‖≤κ+κ := by
      rw [←Unitization.inr_star,←Unitization.inr_mul,←Unitization.inr_sub,Unitization.norm_inr]
      exact hse.le
    have hx := CStarExcision.compression_error_le h (Unitization.inr s) (a i) (Unitization.inr (e n))
      (φ (a i)) hh.isSelfAdjoint.star_eq hhs (hex i).le hseI
    rw [Unitization.norm_inr,←norm_inr_compression_sub] at hx
    have hsn2 : ‖s‖^2 ≤ 4 := by nlinarith [norm_nonneg s]
    have hexc : ‖compression (a i) s-φ (a i) • e n‖ ≤ 4*(ε/16)+M*(κ+κ) :=
      hx.trans (add_le_add (mul_le_mul_of_nonneg_right hsn2 (by positivity))
        (mul_le_mul_of_nonneg_right (hiM i) (by positivity)))
    exact lt_of_le_of_lt hexc (by nlinarith)

theorem pure_state_excision_norm_ultrapower [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (e f : lp (fun _ : ℕ => A) ∞)
    (he : ∀ n,0 ≤ e n) (hen : ∀ n,‖e n‖ ≤ 1)
    (hf : ∀ n,0 ≤ f n) (hfn : ∀ n,‖f n‖ ≤ 1)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    (hsmall : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (e n)).re<η)
    {t : ℝ} (ht : 0<t)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,t ≤ (τ.functional (f n)).re)
    (hdefect : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (f n-f n*f n)).re<η)
    (φ : Unitization ℂ A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (hpure : ofPositiveState φ hφ1∈(realStateCarrier (A := Unitization ℂ A)).extremePoints ℝ)
    : ∃ s : NormUltra.QuotientAlgebra (fun _ : ℕ => A) U, ‖s‖ ≤ 1 ∧
      star s*s=NormUltra.QuotientAlgebra.mk U e ∧
      NormUltra.QuotientAlgebra.mk U f*s=s ∧
      ∀ a : A,star s*NonunitalGamma.normInclusion U a*s=
        φ (Unitization.inr a) • NormUltra.QuotientAlgebra.mk U e := by
  classical
  obtain ⟨a,ha⟩ := TopologicalSpace.exists_dense_seq A
  let g : ℕ → ℕ → A → ℝ
    | 0,k,s => ‖star s*s-e k‖
    | 1,k,s => ‖f k*s-s‖
    | j+2,k,s => ‖star s*a j*s-φ (Unitization.inr (a j)) • e k‖
  have hg (j k : ℕ) (s : A) : 0 ≤ g j k s := by
    rcases j with _|(_|j) <;> exact norm_nonneg _
  have hsupply (m : ℕ) (ε : ℝ) (hε : 0<ε) :
      ∀ᶠ k in (U : Filter ℕ),∃ s : A,‖s‖ ≤ 2 ∧ ∀ j ≤ m,g j k s<ε := by
    have hs := NonunitalSI.pure_state_small_excision hsimple hprojectionless hcone hcmp U e f he hen hf hfn hcentral
      hsmall ht hlarge hdefect φ hφ1 hpure (fun i : Fin (m+1) => Unitization.inr (a i)) hε
    filter_upwards [hs] with k hk
    obtain ⟨s,hsn,hse,hsf,hsa⟩ := hk
    refine ⟨s,hsn,?_⟩
    intro j hj
    rcases j with _|(_|j)
    · exact hse
    · exact hsf
    · simpa only [compression_inr] using hsa ⟨j,by omega⟩
  obtain ⟨z,hzn,hzg⟩ := NormUltra.bounded_epsilon_test U hfree 2 (by norm_num) g hg hsupply
  let q := NormUltra.QuotientAlgebra.mkHom (A := fun _ : ℕ => A) (U := U)
  have hse : star (q z)*q z=q e :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star z*z) e).mpr (hzg 0)
  have hsf : q f*q z=q z :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (f*z) z).mpr (hzg 1)
  have hcoeff (i : ℕ) : star (q z)*NonunitalGamma.normInclusion U (a i)*q z=
      φ (Unitization.inr (a i)) • q e :=
    (NormUltra.QuotientAlgebra.mk_eq_mk_iff (star z*boundedConstant (A := A) (a i)*z)
      (φ (Unitization.inr (a i)) • e)).mpr (hzg (i+2))
  have hnorme : ‖q e‖ ≤ 1 := (NormUltra.QuotientAlgebra.norm_mk_le e).trans
    (lp.norm_le_of_forall_le zero_le_one hen)
  have hnorm : ‖q z‖ ≤ 1 := by
    have hh : ‖star (q z)*q z‖=‖q z‖*‖q z‖ := CStarRing.norm_star_mul_self
    rw [hse] at hh
    nlinarith [norm_nonneg (q z)]
  refine ⟨q z,hnorm,hse,hsf,?_⟩
  have hc1 : Continuous (fun b : A => star (q z)*NonunitalGamma.normInclusion U b*q z) := by fun_prop
  have hc2 : Continuous (fun b : A => φ (Unitization.inr b) • q e) := by fun_prop
  have hge := ha.equalizer hc1 hc2 (funext hcoeff)
  exact fun b => congrFun hge b

end NonunitalSI

end

end OAI
