import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.ScalarStrictComparison
import OAI.Analysis.JiangSu.Excision.ExcisionCoefficientAssembly

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness DirectComparison NonunitalGamma
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A] in
lemma inr_snd_of_fst_eq_zero (x : Unitization ℂ A) (hx : x.fst=0) :
    (Unitization.inr x.snd : Unitization ℂ A)=x := by
  exact Unitization.ext hx.symm rfl

 theorem approximate_controlled_isometry_inr (a w : A) (h f : Unitization ℂ A)
    (han : ‖a‖≤1) (hw : 0≤w) (hhw : h*Unitization.inr w=Unitization.inr w)
    {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) (hε1 : ε≤1)
    (hcmp : CuntzSubequiv (Unitization.inr a : Unitization ℂ A)
      (directPositiveCut β (Unitization.inr w))) :
    ∃ s : A, ‖s‖≤2 ∧ ‖star s*s-a‖<ε ∧
      h*Unitization.inr s=Unitization.inr s ∧
      ‖f*Unitization.inr s-Unitization.inr s‖≤
        2*β⁻¹*‖f*Unitization.inr w-Unitization.inr w‖ := by
  let b : Unitization ℂ A := directPositiveCut β (Unitization.inr w)
  obtain ⟨v,hv⟩ := (cuntzSubequiv_iff_norm _ _).mp hcmp ε hε
  let s : Unitization ℂ A := CFC.sqrt b*v
  have hs0 : s.fst=0 := by
    dsimp [s,b]
    rw [←positiveCut_inr w β hβ.le,Unitization.sqrt_inr]
    simp only [Unitization.fst_inr,zero_mul]
  have his : (Unitization.inr s.snd : Unitization ℂ A)=s := inr_snd_of_fst_eq_zero s hs0
  have he : star s*s=star v*b*v := by
    simp only [s,star_mul,(CFC.sqrt_nonneg b).isSelfAdjoint.star_eq]
    calc
      star v*CFC.sqrt b*(CFC.sqrt b*v)=star v*(CFC.sqrt b*CFC.sqrt b)*v := by
        simp only [mul_assoc]
      _=star v*b*v := by rw [CFC.sqrt_mul_sqrt_self b (directPositiveCut_nonneg β _)]
  have herr : ‖star s*s-Unitization.inr a‖<ε := by simpa only [he,norm_sub_rev] using hv
  have hsn : ‖s‖≤2 := by
    have ht := norm_le_norm_sub_add (star s*s) (Unitization.inr a : Unitization ℂ A)
    rw [CStarRing.norm_star_mul_self,Unitization.norm_inr] at ht
    nlinarith [norm_nonneg s]
  obtain ⟨k,hkn,hks⟩ := controlled_cut_inverse (Unitization.inr w : Unitization ℂ A)
    (Unitization.inr_nonneg_iff.mpr hw) hβ
  have hfix : Unitization.inr w*k*s=s := by
    change Unitization.inr w*k*(CFC.sqrt b*v)=CFC.sqrt b*v
    rw [←mul_assoc,hks]
  have hsupport : h*s=s := by
    calc
      h*s=h*(Unitization.inr w*k*s) := congrArg (h*·) hfix.symm
      _=(h*Unitization.inr w)*k*s := by noncomm_ring
      _=s := by rw [hhw,hfix]
  have hid : f*s-s=(f*Unitization.inr w-Unitization.inr w)*k*s := by
    calc
      f*s-s=f*(Unitization.inr w*k*s)-Unitization.inr w*k*s := by rw [hfix]
      _=(f*Unitization.inr w-Unitization.inr w)*k*s := by noncomm_ring
  refine ⟨s.snd,?_,?_,by rwa [his],?_⟩
  · have hh : ‖s.snd‖=‖s‖ := by simpa only [Unitization.norm_inr] using congrArg norm his
    exact hh ▸ hsn
  · have hh : (Unitization.inr (star s.snd*s.snd-a) : Unitization ℂ A)=star s*s-Unitization.inr a := by
      rw [Unitization.inr_sub,Unitization.inr_mul,Unitization.inr_star,his]
    simpa only [←hh,Unitization.norm_inr] using herr
  · rw [his,hid]
    calc
      ‖(f*Unitization.inr w-Unitization.inr w)*k*s‖≤
          (‖f*Unitization.inr w-Unitization.inr w‖*‖k‖)*‖s‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _≤(‖f*Unitization.inr w-Unitization.inr w‖*β⁻¹)*2 := mul_le_mul
        (mul_le_mul_of_nonneg_left hkn (norm_nonneg _)) hsn (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hβ.le))
      _=2*β⁻¹*‖f*Unitization.inr w-Unitization.inr w‖ := by ring

 theorem small_trace_supported_isometry_inr [Nonempty (NormalizedTrace A)]
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (e w : A) (h f : Unitization ℂ A)
    (he : 0≤e) (hen : ‖e‖≤1) (hw : 0≤w) (hwn : ‖w‖≤1)
    (hhw : h*Unitization.inr w=Unitization.inr w)
    {α β ε : ℝ} (hα : 0<α) (hβ : 0<β) (hε : 0<ε) (hε1 : ε≤1)
    (hsmall : ∀ τ : NormalizedTrace A,(τ.functional e).re<α*β)
    (hlarge : ∀ τ : NormalizedTrace A,2*β≤(τ.functional w).re) :
    ∃ s : A, ‖s‖≤2 ∧ ‖star s*s-e‖<ε+α ∧
      h*Unitization.inr s=Unitization.inr s ∧
      ‖f*Unitization.inr s-Unitization.inr s‖≤
        2*β⁻¹*‖f*Unitization.inr w-Unitization.inr w‖ := by
  let a : A := cfcₙ (fun t : ℝ => max (t-α) 0) e
  let b : A := cfcₙ (fun t : ℝ => max (t-β) 0) w
  have haeq : (Unitization.inr a : Unitization ℂ A)=directPositiveCut α (Unitization.inr e) :=
    positiveCut_inr e α hα.le
  have hbeq : (Unitization.inr b : Unitization ℂ A)=directPositiveCut β (Unitization.inr w) :=
    positiveCut_inr w β hβ.le
  have ha : 0≤a := Unitization.inr_nonneg_iff.mp (haeq.symm ▸ directPositiveCut_nonneg α _)
  have hb : 0≤b := Unitization.inr_nonneg_iff.mp (hbeq.symm ▸ directPositiveCut_nonneg β _)
  have hgap (τ : NormalizedTrace A) :
      normalizedRootRank τ.unitized (Unitization.inr a)<normalizedRootRank τ.unitized (Unitization.inr b) := by
    rw [haeq,hbeq]
    apply (ENNReal.toReal_lt_toReal
      (directRank_ne_top τ.unitized _ (directPositiveCut_nonneg α _))
      (directRank_ne_top τ.unitized _ (directPositiveCut_nonneg β _))).mp
    have hs := directPositiveCut_rank_le_trace_div τ.unitized (Unitization.inr e)
      (Unitization.inr_nonneg_iff.mpr he) α hα
    have hl := cut_rank_lower_from_trace τ.unitized (Unitization.inr w)
      (Unitization.inr_nonneg_iff.mpr hw) (by simpa only [Unitization.norm_inr] using hwn) hβ.le
    have hd : (τ.functional e).re/α<β := (div_lt_iff₀ hα).mpr (by nlinarith [hsmall τ])
    simp only [NormalizedTrace.unitized_inr] at hs hl
    linarith [hlarge τ]
  have hb0 : b≠0 := by
    intro hz
    let τ : NormalizedTrace A := Classical.choice inferInstance
    have hn := hgap τ
    rw [hz,Unitization.inr_zero,normalizedRootRank_zero] at hn
    exact not_lt_of_ge zero_le hn
  have hab := scalar_comparison_inr hcone hcmp a b ha hb hb0 hgap
  rw [hbeq] at hab
  have han : ‖a‖≤1 := by
    rw [←Unitization.norm_inr (𝕜 := ℂ),haeq]
    exact norm_directPositiveCut_le_one _ (Unitization.inr_nonneg_iff.mpr he)
      (by simpa only [Unitization.norm_inr] using hen) α hα.le
  obtain ⟨s,hsn,hse,hhs,hfs⟩ := approximate_controlled_isometry_inr a w h f han hw hhw hβ hε hε1 hab
  have hc : ‖a-e‖≤α := by
    rw [←Unitization.norm_inr (𝕜 := ℂ),Unitization.inr_sub,haeq,norm_sub_rev]
    exact norm_sub_directPositiveCut_le _ (Unitization.inr_nonneg_iff.mpr he) α hα.le
  refine ⟨s,hsn,?_,hhs,hfs⟩
  exact (norm_sub_le_norm_sub_add_norm_sub (star s*s) a e).trans_lt (add_lt_add_of_lt_of_le hse hc)

end NonunitalSI

end
end

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain DirectComparison NonunitalGamma Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

 def compression (b : Unitization ℂ A) (s : A) : A :=
  b.fst • (star s*s)+star s*b.snd*s

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma inr_compression (b : Unitization ℂ A) (s : A) :
    (Unitization.inr (compression b s) : Unitization ℂ A)=
      star (Unitization.inr s)*b*Unitization.inr s := by
  conv_rhs => rw [←Unitization.inl_fst_add_inr_snd_eq b]
  simp only [compression,Unitization.inr_add,Unitization.inr_smul,Unitization.inr_mul,
    Unitization.inr_star,mul_add,add_mul]
  congr 1
  rw [←Unitization.inr_star,Unitization.inr_mul_inl,Unitization.inr_smul,smul_mul_assoc]

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma compression_inr (a s : A) : compression (Unitization.inr a) s=star s*a*s := by
  simp only [compression,Unitization.fst_inr,Unitization.snd_inr,zero_smul,zero_add]

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma compression_one (s : A) : compression (1 : Unitization ℂ A) s=star s*s := by
  simp [compression]

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma hereditaryUpperCut_fst {δ : ℝ} (hδ1 : δ≤1) (f : A) (c : Unitization ℂ A) :
    (hereditaryUpperCut δ (Unitization.inr f) c).fst=0 := by
  unfold hereditaryUpperCut upperCut
  rw [←positiveCut_inr f (1-δ) (sub_nonneg.mpr hδ1),←Unitization.inr_smul]
  simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero,zero_mul]

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma inr_hereditaryUpperCut {δ : ℝ} (hδ1 : δ≤1) (f : A) (c : Unitization ℂ A) :
    (Unitization.inr (hereditaryUpperCut δ (Unitization.inr f) c).snd : Unitization ℂ A)=
      hereditaryUpperCut δ (Unitization.inr f) c :=
  inr_snd_of_fst_eq_zero _ (hereditaryUpperCut_fst hδ1 f c)

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma norm_inr_compression_sub (b : Unitization ℂ A) (s e : A) (z : ℂ) :
    ‖compression b s-z • e‖=
      ‖star (Unitization.inr s : Unitization ℂ A)*b*Unitization.inr s-z • Unitization.inr e‖ := by
  rw [←Unitization.norm_inr (𝕜 := ℂ),Unitization.inr_sub,Unitization.inr_smul,inr_compression]

end NonunitalSI

end
end

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology CStarAlgebra
open scoped ComplexOrder ENNReal

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (U : Ultrafilter ℕ)
local notation "N" => NormUltra.QuotientAlgebra (fun _ : ℕ => A) U

 def unitizedNormInclusion : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ N :=
  Unitization.starMap (NonunitalGamma.normInclusion U)

 omit [PartialOrder A] [StarOrderedRing A] in
 @[simp] lemma unitizedNormInclusion_inr (a : A) :
    unitizedNormInclusion U (Unitization.inr a)=Unitization.inr (NonunitalGamma.normInclusion U a) :=
  Unitization.starMap_inr _ _

 def unitizedNormToTracial [Nonempty (NormalizedTrace A)] :
    Unitization ℂ N →⋆ₐ[ℂ] FamilyUltrapower
      (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U :=
  Unitization.starLift (NonunitalGamma.normToTracial U)

 @[simp] lemma unitizedNormToTracial_inr [Nonempty (NormalizedTrace A)] (x : N) :
    unitizedNormToTracial U (Unitization.inr x)=NonunitalGamma.normToTracial U x := by
  change (Unitization.starLift.symm (Unitization.starLift
    (NonunitalGamma.normToTracial U))) x=NonunitalGamma.normToTracial U x
  rw [Equiv.symm_apply_apply]

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma commute_unitizedInclusion (E : N)
    (h : ∀ a : A,Commute E (NonunitalGamma.normInclusion U a)) (b : Unitization ℂ A) :
    Commute (Unitization.inr E) (unitizedNormInclusion U b) := by
  induction b with
  | inl_add_inr c a =>
    rw [map_add]
    apply Commute.add_right
    · rw [unitizedNormInclusion,Unitization.starMap_inl]
      exact Algebra.commutes c _ |>.symm
    · rw [unitizedNormInclusion_inr]
      exact (h a).map (Unitization.inrNonUnitalStarAlgHom ℂ N)

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma excision_unitizedInclusion (E z : N) (hsq : star z*z=E)
    (φ : Unitization ℂ A →ₚ[ℂ] ℂ) (hφ1 : φ 1=1)
    (h : ∀ a : A,star z*NonunitalGamma.normInclusion U a*z=φ (Unitization.inr a) • E)
    (b : Unitization ℂ A) :
    star (Unitization.inr z)*unitizedNormInclusion U b*Unitization.inr z=
      φ b • Unitization.inr E := by
  induction b with
  | inl_add_inr c a =>
    have hc : φ (Unitization.inl c)=c := by
      rw [←Unitization.algebraMap_eq_inl,Algebra.algebraMap_eq_smul_one]
      rw [map_smul,hφ1,smul_eq_mul,mul_one]
    rw [map_add,map_add,hc,mul_add,add_mul,add_smul]
    congr 1
    · rw [unitizedNormInclusion,Unitization.starMap_inl,Algebra.algebraMap_eq_smul_one]
      rw [mul_smul_comm,mul_one,smul_mul_assoc,←Unitization.inr_star,
        ←Unitization.inr_mul,hsq]
    · rw [unitizedNormInclusion_inr,←Unitization.inr_star,←Unitization.inr_mul,
        ←Unitization.inr_mul,h,Unitization.inr_smul]

end NonunitalSI

end
end

end OAI
