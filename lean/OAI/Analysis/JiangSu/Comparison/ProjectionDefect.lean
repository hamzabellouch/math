import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.Corner

namespace OAI

noncomputable section
namespace CurrentMain
open Pureness Filter
open scoped Topology ComplexOrder ENNReal

lemma positive_contraction_defect_nonneg
    {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    {p : D} (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1) : 0 ≤ p-p*p := by
  have hp1 : p ≤ 1 := hp.isSelfAdjoint.le_algebraMap_norm_self.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      (smul_le_smul_of_nonneg_right hpn (zero_le_one : (0 : D) ≤ 1)))
  have hc : Commute p (1-p) := (Commute.one_right p).sub_right (Commute.refl p)
  simpa only [mul_sub,mul_one] using Commute.mul_nonneg hp (sub_nonneg.mpr hp1) hc

variable {D I X : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma limitTrace_detects_positive_zero (z : FamilyUltrapower τ U) (hz : 0 ≤ z)
    (htr : ∀ s : X → I, ((familyLimitTrace τ U s).functional z).re = 0) : z = 0 := by
  have hs : CFC.sqrt z*CFC.sqrt z = z := CFC.sqrt_mul_sqrt_self z hz
  have hzero : CFC.sqrt z = 0 := by
    apply limitTrace_detects_zero τ U
    intro s
    simp only [traceTwoNorm,(CFC.sqrt_nonneg z).isSelfAdjoint.star_eq,hs,htr,Real.sqrt_zero]
  rw [←hs,hzero,zero_mul]

theorem projection_of_vanishing_tracial_defect
    (p : lp (fun _ : X => D) ∞) (hp : 0 ≤ p) (hpn : ‖p‖ ≤ 1)
    (δ : X → ℝ) (hδ : Tendsto δ (U : Filter X) (𝓝 0))
    (hdef : ∀ n i, ((τ i).functional (p n-p n*p n)).re ≤ δ n) :
    IsStarProjection ((familyNullIdeal τ (U : Filter X)).quotientMap p) := by
  let J := familyNullIdeal τ (U : Filter X)
  let q := J.quotientMap p
  have hpq : 0 ≤ q := map_nonneg J.quotientStarHom hp
  have hnq : ‖q‖ ≤ 1 := (J.quotientMap_norm_le p).trans hpn
  have hd : 0 ≤ q-q*q := positive_contraction_defect_nonneg hpq hnq
  have hd0 : q-q*q = 0 := by
    apply limitTrace_detects_positive_zero τ U _ hd
    intro s
    have hlim := Complex.continuous_re.continuousAt.tendsto.comp
      (familyLimitTrace_tendsto τ U s (p-p*p))
    have hn (n : X) : 0 ≤ ((τ (s n)).functional (p n-p n*p n)).re := by
      have hp' : 0 ≤ p n := map_nonneg (boundedFamilyEval n) hp
      have hpn' : ‖p n‖ ≤ 1 := (lp.norm_apply_le_norm ENNReal.top_ne_zero p n).trans hpn
      exact ((τ (s n)).functional.map_nonneg (positive_contraction_defect_nonneg hp' hpn')).1
    have ht : Tendsto (fun n => ((τ (s n)).functional (p n-p n*p n)).re)
        (U : Filter X) (𝓝 0) :=
      squeeze_zero (fun n => hn n) (fun n => hdef n (s n)) hδ
    have he := tendsto_nhds_unique hlim ht
    simpa only [map_sub,map_mul] using he
  refine ⟨?_,hpq.isSelfAdjoint⟩
  change q*q=q
  exact (sub_eq_zero.mp hd0).symm

lemma limitTrace_eq_of_coordinate_errors
    (p b : lp (fun _ : X => D) ∞) (δ : X → ℝ)
    (hδ : Tendsto δ (U : Filter X) (𝓝 0))
    (herr : ∀ n i, ‖(τ i).functional (p n-b n)‖ ≤ δ n) (s : X → I) :
    (familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter X)).quotientMap p) =
    (familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter X)).quotientMap b) := by
  have hnorm : Tendsto (fun n => ‖(τ (s n)).functional (p n-b n)‖)
      (U : Filter X) (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) (fun n => herr n (s n)) hδ
  have ht : Tendsto (fun n => (τ (s n)).functional (p n-b n))
      (U : Filter X) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have he := tendsto_nhds_unique (familyLimitTrace_tendsto τ U s (p-b)) ht
  simpa only [map_sub,sub_eq_zero] using he

end CurrentMain

namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cfc_clamp_of_positive_contractive [Nontrivial A]
    {h : A} (hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1) :
    cfc (fun t : ℝ => max 0 (min t 1)) h = h := by
  calc
    _ = cfc (fun t : ℝ => t) h := by
      apply cfc_congr
      intro t ht
      have ht0 := spectrum_nonneg_of_nonneg hh ht
      have ht1 : t ≤ 1 := (le_abs_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans hhn)
      change max 0 (min t 1) = t
      rw [min_eq_left ht1, max_eq_right ht0]
    _ = h := cfc_id' ℝ h hh.isSelfAdjoint

lemma positive_contraction_lift (J : ClosedStarIdeal A)
    {h : J.Quotient} (hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1) :
    ∃ a : A, 0 ≤ a ∧ ‖a‖ ≤ 1 ∧ J.quotientMap a = h := by
  rcases subsingleton_or_nontrivial J.Quotient with hs | hn
  · let := hs
    exact ⟨0,le_rfl,by simp,Subsingleton.elim _ _⟩
  let := hn
  let : ContinuousFunctionalCalculus ℝ J.Quotient IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  obtain ⟨a,ha⟩ := J.quotientMap_surjective h
  let b : A := (realPart a : A)
  have hb : IsSelfAdjoint b := (realPart a).property
  have he : J.quotientStarHom b = h := by
    change J.quotientMap (realPart a : A) = h
    rw [J.quotientMap_realPart,ha,hh.isSelfAdjoint.coe_realPart]
  let f : ℝ → ℝ := fun t => max 0 (min t 1)
  have hf : Continuous f := continuous_const.max (continuous_id.min continuous_const)
  refine ⟨cfc f b,cfc_nonneg (fun _ _ => le_max_left _ _),?_,?_⟩
  · apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
    intro t _
    change |max 0 (min t 1)| ≤ 1
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le zero_le_one (min_le_right _ _)
  · change J.quotientStarHom (cfc f b) = h
    rw [J.quotientStarHom.map_cfc f b hf.continuousOn J.quotientStarHom_continuous hb (by simpa only [he] using hh.isSelfAdjoint),he]
    exact cfc_clamp_of_positive_contractive hh hhn

omit [StarOrderedRing A] in
lemma directPositiveCut_norm_le [Nontrivial A] (h : A) (_hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1)
    (η : ℝ) (hη : η ≤ 1) : ‖directPositiveCut η h‖ ≤ 1-η := by
  apply norm_cfc_le (sub_nonneg.mpr hη)
  intro t ht
  have ht1 : t ≤ 1 := (le_abs_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans hhn)
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (sub_le_sub_right ht1 η) (sub_nonneg.mpr hη)

omit [PartialOrder A] [StarOrderedRing A] in
lemma boundedFamilyEval_continuous [Nontrivial A] (n : ℕ) :
    Continuous (boundedFamilyEval (D := A) n) :=
  (continuous_apply n).comp lp.uniformContinuous_coe.continuous

variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U

local instance : ContinuousFunctionalCalculus ℝ (lp (fun _ : ℕ => A) ∞) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
local instance (J : ClosedStarIdeal (lp (fun _ : ℕ => A) ∞)) :
    ContinuousFunctionalCalculus ℝ J.Quotient IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

include hfree in

theorem projection_supply (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (h : D) (hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ p : D, IsStarProjection p ∧
      directCutoff η h*p=p ∧ p*directCutoff η h=p ∧
      ∀ s : ℕ → TracialState A, (Λ s).functional p = (Λ s).functional (directPositiveCut η h) := by
  classical
  let τ := fun t : TracialState A => t
  let J := familyNullIdeal τ (U : Filter ℕ)
  obtain ⟨a,ha0,han,ha⟩ := positive_contraction_lift J hh hhn
  let b : lp (fun _ : ℕ => A) ∞ := directPositiveCut η a
  have ha0' (n : ℕ) : 0 ≤ a n := map_nonneg (boundedFamilyEval n) ha0
  have hb (n : ℕ) : b n = directPositiveCut η (a n) := by
    exact (boundedFamilyEval n).map_cfc (fun t : ℝ => max (t-η) 0) a
      (by fun_prop) (boundedFamilyEval_continuous n) ha0.isSelfAdjoint (ha0' n).isSelfAdjoint
  have han' (n : ℕ) : ‖a n‖ ≤ 1 := (lp.norm_apply_le_norm ENNReal.top_ne_zero a n).trans han
  have hb0 (n : ℕ) : 0 ≤ b n := by rw [hb]; exact directPositiveCut_nonneg _ _
  have hbn (n : ℕ) : ‖b n‖ < 1 := by
    rw [hb]
    exact (directPositiveCut_norm_le (a n) (ha0' n) (han' n) η hη1.le).trans_lt (by linarith)
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto (fun n => 2*δ n) (U : Filter ℕ) (𝓝 0) := by
    have ht : Tendsto δ atTop (𝓝 0) := by
      simpa only [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0))
    simpa only [mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul ht).mono_left hfree
  choose p hpmem hp0 hpn hpτ using
    fun n => almost_projection hsimple hinf inferInstance hcmp (b n) (hb0 n) (hbn n) (δ n) (hδ n)
  let P : lp (fun _ : ℕ => A) ∞ :=
    ⟨p,memℓp_infty_iff.mpr ⟨1,by rintro _ ⟨n,rfl⟩;exact hpn n⟩⟩
  have hP0 : 0 ≤ P := by
    let Q : lp (fun _ : ℕ => A) ∞ := ⟨fun n => CFC.sqrt (p n),memℓp_infty_iff.mpr
      ⟨1,by
        rintro _ ⟨n,rfl⟩
        change ‖CFC.sqrt (p n)‖ ≤ 1
        exact (CFC.norm_sqrt (p n) (hp0 n)).le.trans (Real.sqrt_le_one.mpr (hpn n))⟩⟩
    have he : P=star Q*Q := by
      apply Subtype.ext; funext n
      change p n = star (CFC.sqrt (p n))*CFC.sqrt (p n)
      rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq,CFC.sqrt_mul_sqrt_self _ (hp0 n)]
    rw [he]; exact star_mul_self_nonneg Q
  have hPn : ‖P‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one hpn
  have hPJ : IsStarProjection (J.quotientMap P) :=
    projection_of_vanishing_tracial_defect τ U P hP0 hPn _ hδlim
      (fun n t => (hpτ n t).2.2.2.le)
  have hfix : directCutoff η a*P=P ∧ P*directCutoff η a=P := by
    constructor
    · apply Subtype.ext; funext n
      change (directCutoff η a) n*p n=p n
      have hc : (directCutoff η a) n = directCutoff η (a n) := by
        exact (boundedFamilyEval n).map_cfc (fun t : ℝ => min (t/η) 1) a
          (by fun_prop) (boundedFamilyEval_continuous n) ha0.isSelfAdjoint (ha0' n).isSelfAdjoint
      rw [hc]
      exact (directCutoff_fixes_hereditary η hη (a n) (by simpa only [hb] using hpmem n)).1
    · apply Subtype.ext; funext n
      change p n*(directCutoff η a) n=p n
      have hc : (directCutoff η a) n = directCutoff η (a n) := by
        exact (boundedFamilyEval n).map_cfc (fun t : ℝ => min (t/η) 1) a
          (by fun_prop) (boundedFamilyEval_continuous n) ha0.isSelfAdjoint (ha0' n).isSelfAdjoint
      rw [hc]
      exact (directCutoff_fixes_hereditary η hη (a n) (by simpa only [hb] using hpmem n)).2
  have hc : J.quotientMap (directCutoff η a) = directCutoff η h := by
    change J.quotientStarHom (cfc _ a) = cfc _ h
    rw [J.quotientStarHom.map_cfc _ a (by fun_prop) J.quotientStarHom_continuous ha0.isSelfAdjoint (by simpa only [show J.quotientStarHom a = h from ha] using hh.isSelfAdjoint)]
    rw [show J.quotientStarHom a = h from ha]
    rfl
  have hbJ : J.quotientMap b = directPositiveCut η h := by
    change J.quotientStarHom (cfc _ a) = cfc _ h
    rw [J.quotientStarHom.map_cfc _ a (by fun_prop) J.quotientStarHom_continuous ha0.isSelfAdjoint (by simpa only [show J.quotientStarHom a = h from ha] using hh.isSelfAdjoint)]
    rw [show J.quotientStarHom a = h from ha]
    rfl
  refine ⟨J.quotientMap P,hPJ,?_,?_,?_⟩
  · rw [←hc,←map_mul,hfix.1]
  · rw [←hc,←map_mul,hfix.2]
  · intro s
    rw [←hbJ]
    apply limitTrace_eq_of_coordinate_errors τ U P b _ hδlim _ s
    intro n t
    change ‖t.functional (p n-b n)‖ ≤ 2*δ n
    have hpR : (t.functional (p n)).im=0 := (t.functional.map_nonneg (hp0 n)).2.symm
    have hbR : (t.functional (b n)).im=0 := (t.functional.map_nonneg (hb0 n)).2.symm
    have he : t.functional (p n-b n) =
        (((t.functional (p n)).re - (t.functional (b n)).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp only [map_sub,Complex.sub_re,Complex.sub_im,
        Complex.ofReal_re,Complex.ofReal_im,hpR,hbR,sub_self]
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith [(hpτ n t).2.1])]
    linarith [(hpτ n t).1]

end DirectComparison
end

end OAI
