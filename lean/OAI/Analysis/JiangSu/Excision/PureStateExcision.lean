import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.ExcisionFullnessError
import OAI.Analysis.JiangSu.Excision.ExcisionCoefficientAssembly
import OAI.Analysis.JiangSu.Excision.ExcisionSoftCompression

namespace OAI

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder ComplexStarModule

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {I : Type} [Fintype I]

theorem pure_state_finite_excision (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (a : I → A) {ε ρ : ℝ} (hε : 0<ε) (hρ : 0<ρ) :
    ∃ g : A, 0 ≤ g ∧ ‖g‖ ≤ 1 ∧ 1-ρ<(f g).re ∧
      ∀ i, ‖g*a i*g-f (a i) • (g*g)‖<ε := by
  let b : I×Bool → selfAdjoint A := fun p => if p.2 then ℑ (a p.1) else ℜ (a p.1)
  obtain ⟨g,hg,hgn,hfg,herr⟩ := pure_state_finite_selfadjoint_excision f hf1 hpure b
    (show 0<ε/2 by positivity) hρ
  refine ⟨g,hg,hgn,hfg,fun i => ?_⟩
  have hR := herr (i,false)
  have hI := herr (i,true)
  change ‖g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g)‖<ε/2 at hR
  change ‖g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)‖<ε/2 at hI
  have he : g*a i*g-f (a i) • (g*g)=
      (g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g))+
      Complex.I • (g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)) := by
    conv_lhs => rw [←realPart_add_I_smul_imaginaryPart (a i)]
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,map_add,map_smul,
      smul_eq_mul,add_smul,smul_sub,smul_smul]
    module
  rw [he]
  have hn := norm_add_le (g*(ℜ (a i) : A)*g-f (ℜ (a i)) • (g*g))
    (Complex.I • (g*(ℑ (a i) : A)*g-f (ℑ (a i)) • (g*g)))
  rw [norm_smul,Complex.norm_I,one_mul] at hn
  linarith

end PureStateExcision

end
end

section

noncomputable section
namespace PureStateExcision
open DirectComparison
open scoped ComplexOrder ComplexStarModule

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private def inversePlateau (t : ℝ) : ℝ := (max (1/2) t)⁻¹
private lemma inversePlateau_continuous : Continuous inversePlateau := by
  apply Continuous.inv₀ (by fun_prop)
  intro t
  have h := le_max_left (1/2 : ℝ) t
  dsimp
  linarith
private lemma inversePlateau_bounds (t : ℝ) :
    0 ≤ inversePlateau t ∧ inversePlateau t ≤ 2 := by
  have h := le_max_left (1/2 : ℝ) t
  have hp : 0 < max (1/2 : ℝ) t := by linarith
  constructor
  · exact inv_nonneg.mpr hp.le
  · dsimp [inversePlateau]
    calc
      _ ≤ (1/2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
      _=2 := by norm_num

lemma plateau_factorization (g : A) (hg : 0 ≤ g) :
    directCutoff (1/2) g=cfc inversePlateau g*g ∧
    directCutoff (1/2) g=g*cfc inversePlateau g := by
  have he : cfc inversePlateau g*g=directCutoff (1/2) g := by
    have hid : cfc inversePlateau g*g=cfc (fun t : ℝ => inversePlateau t*t) g := by
      rw [cfc_mul inversePlateau (fun t : ℝ => t) g inversePlateau_continuous.continuousOn continuousOn_id,
        cfc_id' ℝ g hg.isSelfAdjoint]
    rw [hid]
    apply cfc_congr
    intro t ht
    change (max (1/2) t)⁻¹*t=min (t/(1/2)) 1
    have ht0 := spectrum_nonneg_of_nonneg hg ht
    by_cases h : t ≤ 1/2
    · rw [max_eq_left h,min_eq_left ((div_le_one (by norm_num : (0:ℝ)<1/2)).mpr h)]
      ring
    · rw [max_eq_right (le_of_not_ge h),min_eq_right
        ((le_div_iff₀ (by norm_num : (0:ℝ)<1/2)).mpr (by linarith))]
      exact inv_mul_cancel₀ (by linarith)
  refine ⟨he.symm,?_⟩
  have hc : cfc inversePlateau g*g=g*cfc inversePlateau g := by
    have hz := cfc_commute_cfc inversePlateau (fun t : ℝ => t) g
    simpa only [cfc_id' ℝ g hg.isSelfAdjoint] using hz.eq
  exact he.symm.trans hc

lemma plateau_error_bound (g a : A) (z : ℂ) (hg : 0 ≤ g) :
    ‖directCutoff (1/2) g*a*directCutoff (1/2) g-
      z • (directCutoff (1/2) g*directCutoff (1/2) g)‖ ≤
      4*‖g*a*g-z • (g*g)‖ := by
  let k := cfc inversePlateau g
  have hk : ‖k‖ ≤ 2 := norm_cfc_le (by norm_num) fun t _ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (inversePlateau_bounds t).1]
    exact (inversePlateau_bounds t).2
  have hfact := plateau_factorization g hg
  have he : directCutoff (1/2) g*a*directCutoff (1/2) g-
      z • (directCutoff (1/2) g*directCutoff (1/2) g)=
      k*(g*a*g-z • (g*g))*k := by
    conv_lhs => lhs; lhs; rw [hfact.1]
    conv_lhs => lhs; rhs; rw [hfact.2]
    conv_lhs => rhs; rhs; lhs; rw [hfact.1]
    conv_lhs => rhs; rhs; rhs; rw [hfact.2]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    noncomm_ring
  rw [he]
  calc
    _ ≤ (‖k‖*‖g*a*g-z • (g*g)‖)*‖k‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 4*‖g*a*g-z • (g*g)‖ := by
      have h0 := norm_nonneg (g*a*g-z • (g*g))
      have hk0 := norm_nonneg k
      nlinarith [mul_nonneg (sub_nonneg.mpr hk) h0,
        mul_nonneg (sub_nonneg.mpr hk) (mul_nonneg hk0 h0)]

theorem pure_state_plateau_excision {I : Type} [Fintype I]
    (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (a : I → A) {ε : ℝ} (hε : 0<ε) :
    ∃ h c : A, 0 ≤ h ∧ ‖h‖ ≤ 1 ∧ 0 ≤ c ∧ ‖c‖ ≤ 1 ∧ c≠0 ∧ h*c=c ∧
      ∀ i, ‖h*a i*h-f (a i) • (h*h)‖<ε := by
  obtain ⟨g,hg,hgn,hfg,herr⟩ := pure_state_finite_excision f hf1 hpure a
    (show 0<ε/4 by positivity) (show (0:ℝ)<1/4 by norm_num)
  let h := directCutoff (1/2) g
  let c := directPositiveCut (1/2) g
  have hh : 0 ≤ h := cfc_nonneg fun t ht =>
    le_min (div_nonneg (spectrum_nonneg_of_nonneg hg ht) (by norm_num)) zero_le_one
  have hh1 : h ≤ 1 := cfc_le_one _ _ fun t _ => min_le_right _ _
  have hc0 : c≠0 := by
    intro hz
    have hn := norm_sub_directPositiveCut_le g hg (1/2) (by norm_num)
    change ‖g-c‖ ≤ 1/2 at hn
    rw [hz,sub_zero] at hn
    have hs := f.norm_apply_le_of_nonneg g hg
    rw [hf1,norm_one,one_mul] at hs
    have hr := Complex.re_le_norm (f g)
    linarith
  refine ⟨h,c,hh,(CStarAlgebra.norm_le_one_iff_of_nonneg h hh).mpr hh1,
    directPositiveCut_nonneg _ _,norm_directPositiveCut_le_one g hg hgn (1/2) (by norm_num),hc0,directCutoff_fixes_cut _ (by norm_num) g,fun i => ?_⟩
  exact (plateau_error_bound g (a i) (f (a i)) hg).trans_lt (by linarith [herr i])

end PureStateExcision

end
end

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain PureStateExcision Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem pure_state_small_excision [Nonempty (TracialState A)]
    (hsimple : TopologicallySimple A) (hcmp : StrictComparison A) (U : Ultrafilter ℕ)
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
    {I : Type} [Fintype I] (a : I → A) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in (U : Filter ℕ),∃ s : A, ‖s‖ ≤ 2 ∧ ‖star s*s-e n‖<ε ∧
      ‖f n*s-s‖<ε ∧ ∀ i,‖star s*a i*s-φ (a i) • e n‖<ε := by
  obtain ⟨h,c,hh,hhn,hc,hcn,hc0,hhc,hex⟩ := pure_state_plateau_excision φ hφ1 hpure a
    (show 0<ε/16 by positivity)
  obtain ⟨β,hβ,hb⟩ := eventual_hereditary_upperCut_trace_lower hsimple U f hf hfn
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
  have hcomm := (tendsto_order.1 (hcentral c)).2 δ hδ
  filter_upwards [hb δ hδ hδ1,hcomm,hsmall (κ*β) (mul_pos hκ hβ)] with n hn hnc hne
  let w := hereditaryUpperCut δ (f n) c
  have hw : 0 ≤ w := hereditaryUpperCut_nonneg hδ.le (f n) c hc.isSelfAdjoint
  have hwn : ‖w‖ ≤ 1 := hereditaryUpperCut_norm_le hδ (f n) c (hfn n) hcn
  have hhw : h*w=w := hereditaryUpperCut_support δ (f n) c h hhc
  obtain ⟨s,hsn,hse,hhs,hfs⟩ := small_trace_supported_isometry hcmp (e n) w h (f n)
    (he n) (hen n) hw hwn hhw hκ hβ hκ hκ1 hne hn
  refine ⟨s,hsn,hse.trans hκe,?_,?_⟩
  · have hwf := hereditaryUpperCut_error hδ (f n) c (hf n) (hfn n) hcn
    have hcoef : 0 ≤ 2*β⁻¹ := by positivity
    have hbound : ‖f n*s-s‖ ≤ 4*β⁻¹*δ := by
      calc
        _ ≤ 2*β⁻¹*(‖f n*c-c*f n‖+δ) := hfs.trans
          (mul_le_mul_of_nonneg_left hwf hcoef)
        _ ≤ 4*β⁻¹*δ := by nlinarith [mul_le_mul_of_nonneg_left hnc.le hcoef]
    exact lt_of_le_of_lt (hbound.trans hsupport) (by linarith)
  · intro i
    have hx := CStarExcision.compression_error_le h s (a i) (e n) (φ (a i))
      hh.isSelfAdjoint.star_eq hhs (hex i).le hse.le
    have hsn2 : ‖s‖^2 ≤ 4 := by nlinarith [norm_nonneg s]
    have hexc : ‖star s*a i*s-φ (a i) • e n‖ ≤ 4*(ε/16)+M*(κ+κ) :=
      hx.trans (add_le_add (mul_le_mul_of_nonneg_right hsn2 (by positivity))
        (mul_le_mul_of_nonneg_right (hiM i) (by positivity)))
    exact lt_of_le_of_lt hexc (by nlinarith)

end DirectComparison

end
end

end OAI
