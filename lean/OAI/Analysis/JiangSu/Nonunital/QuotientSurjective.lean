import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.MatrixComparison

namespace OAI


noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
def boundedInr : lp (fun _ : ℕ => A) ∞ →⋆ₙₐ[ℂ] lp (fun _ : ℕ => Unitization ℂ A) ∞ where
  toFun u := ⟨fun n => Unitization.inr (u n),memℓp_infty_iff.mpr ⟨‖u‖,by
    rintro _ ⟨n,rfl⟩
    simpa only [Unitization.norm_inr] using lp.norm_apply_le_norm ENNReal.top_ne_zero u n⟩⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero (Unitization.inrNonUnitalStarAlgHom ℂ A)
  map_add' u v := by apply Subtype.ext; funext n; exact map_add (Unitization.inrNonUnitalStarAlgHom ℂ A) _ _
  map_mul' u v := by apply Subtype.ext; funext n; exact map_mul (Unitization.inrNonUnitalStarAlgHom ℂ A) _ _
  map_smul' z u := by apply Subtype.ext; funext n; exact map_smul (Unitization.inrNonUnitalStarAlgHom ℂ A) _ _
  map_star' u := by apply Subtype.ext; funext n; exact map_star (Unitization.inrNonUnitalStarAlgHom ℂ A) _

@[simp] lemma boundedInr_apply (u : lp (fun _ : ℕ => A) ∞) (n : ℕ) :
    boundedInr (A := A) u n=Unitization.inr (u n) := rfl

lemma boundedInr_norm (u : lp (fun _ : ℕ => A) ∞) : ‖boundedInr (A := A) u‖=‖u‖ := by
  apply le_antisymm
  · apply lp.norm_le_of_forall_le (norm_nonneg u)
    intro n
    simpa only [boundedInr_apply,Unitization.norm_inr] using lp.norm_apply_le_norm ENNReal.top_ne_zero u n
  · apply lp.norm_le_of_forall_le (norm_nonneg (boundedInr (A := A) u))
    intro n
    simpa only [boundedInr_apply,Unitization.norm_inr] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (boundedInr (A := A) u) n

local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
variable [Nonempty (NormalizedTrace A)] (U : Ultrafilter ℕ)

def sequenceQuotientMap : lp (fun _ : ℕ => A) ∞ →⋆ₙₐ[ℂ] FamilyUltrapower T U :=
  (familyNullIdeal T (U : Filter ℕ)).quotientStarHom.toNonUnitalStarAlgHom.comp boundedInr

@[simp] lemma sequenceQuotientMap_apply (u : lp (fun _ : ℕ => A) ∞) :
    sequenceQuotientMap (A := A) U u=
      (familyNullIdeal T (U : Filter ℕ)).quotientMap (boundedInr (A := A) u) := rfl

lemma sequenceQuotientMap_kernel (u : lp (fun _ : ℕ => A) ∞) :
    sequenceQuotientMap (A := A) U u=0 ↔
      Tendsto (fun n => ⨆ τ : NormalizedTrace A,
        Real.sqrt (τ.functional (star (u n)*u n)).re) (U : Filter ℕ) (𝓝 0) := by
  rw [sequenceQuotientMap_apply,familyQuotientMap_eq_zero]
  simp only [IsFamilyNull,familyTwoNorm,traceTwoNorm,boundedInr_apply,
    ← Unitization.inr_star,← Unitization.inr_mul,NormalizedTrace.unitized_inr]

theorem sequenceQuotientMap_bounded_lift [CompactSpace (NormalizedTrace A)]
    (hfree : (U : Filter ℕ) ≤ atTop) (x : lp (fun _ : ℕ => Unitization ℂ A) ∞) :
    ∃ a : lp (fun _ : ℕ => A) ∞, ‖a‖ ≤ ‖x‖ ∧
      sequenceQuotientMap (A := A) U a=(familyNullIdeal T (U : Filter ℕ)).quotientMap x := by
  obtain ⟨e,hef,he0,hen,he⟩ := exists_unit_representative (A := A) U hfree
  let y := e*x
  have hyf (n : ℕ) : (y n).fst=0 := by
    change (e n*x n).fst=0
    rw [Unitization.fst_mul,hef n,zero_mul]
  have hy (n : ℕ) : Unitization.inr (y n).snd=y n := by
    apply Unitization.ext
    · exact (hyf n).symm
    · rfl
  have hyn (n : ℕ) : ‖(y n).snd‖ ≤ ‖x‖ := by
    rw [← Unitization.norm_inr (𝕜 := ℂ),hy n]
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero y n).trans
      ((norm_mul_le e x).trans (mul_le_of_le_one_left (norm_nonneg x) hen))
  let a : lp (fun _ : ℕ => A) ∞ := ⟨fun n => (y n).snd,
    memℓp_infty_iff.mpr ⟨‖x‖,by rintro _ ⟨n,rfl⟩;exact hyn n⟩⟩
  have ha : boundedInr (A := A) a=y := by
    apply Subtype.ext
    funext n
    exact hy n
  refine ⟨a,lp.norm_le_of_forall_le (norm_nonneg x) hyn,?_⟩
  rw [sequenceQuotientMap_apply,ha]
  change (familyNullIdeal T (U : Filter ℕ)).quotientMap (e*x)=_
  rw [map_mul,he,one_mul]

theorem sequenceQuotientMap_surjective [CompactSpace (NormalizedTrace A)]
    (hfree : (U : Filter ℕ) ≤ atTop) : Function.Surjective (sequenceQuotientMap (A := A) U) := by
  intro z
  obtain ⟨x,rfl⟩ := (familyNullIdeal T (U : Filter ℕ)).quotientMap_surjective z
  obtain ⟨a,_ha,haz⟩ := sequenceQuotientMap_bounded_lift U hfree x
  exact ⟨a,haz⟩

end NonunitalGamma

end


noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain DirectComparison Filter Topology
open scoped ComplexOrder ENNReal NNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_inr_map {b p : A} (hp : p ∈ NonunitalGamma.hereditaryCarrier b) :
    (Unitization.inr p : Unitization ℂ A) ∈ Pureness.hereditaryCarrier (Unitization.inr b) := by
  apply closure_minimal ?_ (isClosed_closure.preimage Unitization.continuous_inr) hp
  rintro x ⟨w,rfl⟩
  exact subset_closure ⟨Unitization.inr w,by simp only [←Unitization.inr_mul]⟩

local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
variable [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D" => FamilyUltrapower T U
local notation "Λ" => familyLimitTrace T U

local instance : ContinuousFunctionalCalculus ℝ (lp (fun _ : ℕ => Unitization ℂ A) ∞) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
local instance (J : ClosedStarIdeal (lp (fun _ : ℕ => Unitization ℂ A) ∞)) :
    ContinuousFunctionalCalculus ℝ J.Quotient IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

include hfree in
lemma positive_contraction_sequence_lift {h : D} (hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1) :
    ∃ a : lp (fun _ : ℕ => Unitization ℂ A) ∞,
      (∀ n, (a n).fst=0) ∧ 0 ≤ a ∧ ‖a‖ ≤ 1 ∧
        (familyNullIdeal T (U : Filter ℕ)).quotientMap a=h := by
  let J := familyNullIdeal T (U : Filter ℕ)
  obtain ⟨x,hx0,hxn,hx⟩ := DirectComparison.positive_contraction_lift J hh hhn
  obtain ⟨e,hef,he0,hen,he⟩ := exists_unit_representative (A := A) U hfree
  refine ⟨e*x*e,?_,?_,?_,?_⟩
  · intro n
    change (e n*x n*e n).fst=0
    simp only [Unitization.fst_mul,hef,zero_mul]
  · simpa only [he0.isSelfAdjoint.star_eq] using star_right_conjugate_nonneg hx0 e
  · have hex : ‖e*x‖ ≤ 1 :=
      (norm_mul_le e x).trans ((mul_le_of_le_one_left (norm_nonneg x) hen).trans hxn)
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg e) hex).trans hen)
  · change J.quotientMap (e*x*e)=h
    rw [map_mul,map_mul,he,hx,one_mul,mul_one]

include hfree in

theorem projection_supply [Nontrivial A]
    (hsimple : NonunitalGamma.TopologicallySimple A) (hproj : Projectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (h : D) (hh : 0 ≤ h) (hhn : ‖h‖ ≤ 1) (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ p : D, IsStarProjection p ∧ directCutoff η h*p=p ∧ p*directCutoff η h=p ∧
      ∀ s : ℕ → NormalizedTrace A, (Λ s).functional p = (Λ s).functional (directPositiveCut η h) := by
  classical
  let τ := T
  let J := familyNullIdeal τ (U : Filter ℕ)
  obtain ⟨a,haf,ha0,han,ha⟩ := positive_contraction_sequence_lift U hfree hh hhn
  let b : lp (fun _ : ℕ => Unitization ℂ A) ∞ := directPositiveCut η a
  have ha0' (n : ℕ) : 0 ≤ a n := map_nonneg (boundedFamilyEval n) ha0
  have hae (n : ℕ) : (Unitization.inr (a n).snd : Unitization ℂ A)=a n := by
    apply Unitization.ext <;> simp [haf]
  let bA : ℕ → A := fun n => cfcₙ (fun t : ℝ => max (t-η) 0) (a n).snd
  have hb (n : ℕ) : b n = directPositiveCut η (a n) :=
    (boundedFamilyEval n).map_cfc (fun t : ℝ => max (t-η) 0) a
      (by fun_prop) (boundedFamilyEval_continuous n) ha0.isSelfAdjoint (ha0' n).isSelfAdjoint
  have hbe (n : ℕ) : (Unitization.inr (bA n) : Unitization ℂ A)=b n := by
    rw [hb]
    change Unitization.inr (cfcₙ _ _)=cfc _ _
    rw [Unitization.real_cfcₙ_eq_cfc_inr _ _ (by simp [hη.le]),hae]
  have han' (n : ℕ) : ‖a n‖ ≤ 1 := (lp.norm_apply_le_norm ENNReal.top_ne_zero a n).trans han
  have hb0 (n : ℕ) : 0 ≤ b n := by rw [hb]; exact directPositiveCut_nonneg _ _
  have hbA0 (n : ℕ) : 0 ≤ bA n := Unitization.inr_nonneg_iff.mp (hbe n ▸ hb0 n)
  have hbn (n : ℕ) : ‖b n‖ < 1 := by
    rw [hb]
    exact (directPositiveCut_norm_le (a n) (ha0' n) (han' n) η hη1.le).trans_lt
      (sub_lt_self _ hη)
  have hbAn (n : ℕ) : ‖bA n‖ < 1 := by rw [←Unitization.norm_inr (𝕜 := ℂ),hbe]; exact hbn n
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδlim : Tendsto (fun n => 2*δ n) (U : Filter ℕ) (𝓝 0) := by
    have ht : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [mul_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2)).mul ht).mono_left hfree
  choose p hpmem hp0 hpn hpτ using
    fun n => almost_projection hsimple hproj inferInstance hcone hcmp (bA n) (hbA0 n) (hbAn n) (δ n) (hδ n)
  let P : lp (fun _ : ℕ => Unitization ℂ A) ∞ :=
    ⟨fun n => Unitization.inr (p n),memℓp_infty_iff.mpr ⟨1,by
      rintro _ ⟨n,rfl⟩;simpa only [Unitization.norm_inr] using hpn n⟩⟩
  have hP0 : 0 ≤ P := nonunital_lp_unitized_nonneg P (fun n => Unitization.inr_nonneg_iff.mpr (hp0 n))
  have hPn : ‖P‖ ≤ 1 := lp.norm_le_of_forall_le zero_le_one (by
    intro n; change ‖(Unitization.inr (p n) : Unitization ℂ A)‖ ≤ 1; simpa only [Unitization.norm_inr] using hpn n)
  have hpτ' (n : ℕ) (t : NormalizedTrace A) :
      ((τ t).functional (b n)).re-2*δ n < ((τ t).functional (P n)).re ∧
      ((τ t).functional (P n)).re ≤ ((τ t).functional (b n)).re ∧
      0 ≤ ((τ t).functional (P n-P n*P n)).re ∧
      ((τ t).functional (P n-P n*P n)).re < 2*δ n := by
    change (t.unitized.functional (b n)).re-2*δ n < (t.unitized.functional (Unitization.inr (p n))).re ∧ _
    change _ ∧ ((t.unitized).functional (Unitization.inr (p n))).re ≤ ((t.unitized).functional (b n)).re ∧
      0 ≤ ((t.unitized).functional (Unitization.inr (p n)-Unitization.inr (p n)*Unitization.inr (p n))).re ∧
      ((t.unitized).functional (Unitization.inr (p n)-Unitization.inr (p n)*Unitization.inr (p n))).re < 2*δ n
    rw [←hbe n]
    simpa only [←Unitization.inr_mul,←Unitization.inr_sub,NormalizedTrace.unitized_inr] using hpτ n t
  have hPJ : IsStarProjection (J.quotientMap P) :=
    projection_of_vanishing_tracial_defect τ U P hP0 hPn _ hδlim (fun n t => (hpτ' n t).2.2.2.le)
  have hpmem' (n : ℕ) : P n ∈ Pureness.hereditaryCarrier (directPositiveCut η (a n)) := by
    rw [←hb,←hbe]
    exact hereditary_inr_map (hpmem n)
  have hfix : directCutoff η a*P=P ∧ P*directCutoff η a=P := by
    have hc (n : ℕ) : (directCutoff η a) n = directCutoff η (a n) :=
      (boundedFamilyEval n).map_cfc (fun t : ℝ => min (t/η) 1) a
        (by fun_prop) (boundedFamilyEval_continuous n) ha0.isSelfAdjoint (ha0' n).isSelfAdjoint
    constructor
    · apply Subtype.ext;funext n
      change (directCutoff η a) n*P n=P n
      rw [hc];exact (directCutoff_fixes_hereditary η hη (a n) (hpmem' n)).1
    · apply Subtype.ext;funext n
      change P n*(directCutoff η a) n=P n
      rw [hc];exact (directCutoff_fixes_hereditary η hη (a n) (hpmem' n)).2
  have hc : J.quotientMap (directCutoff η a) = directCutoff η h := by
    change J.quotientStarHom (cfc _ a) = cfc _ h
    rw [J.quotientStarHom.map_cfc _ a (by fun_prop) J.quotientStarHom_continuous ha0.isSelfAdjoint
      (by simpa only [show J.quotientStarHom a = h from ha] using hh.isSelfAdjoint)]
    rw [show J.quotientStarHom a = h from ha];rfl
  have hbJ : J.quotientMap b = directPositiveCut η h := by
    change J.quotientStarHom (cfc _ a) = cfc _ h
    rw [J.quotientStarHom.map_cfc _ a (by fun_prop) J.quotientStarHom_continuous ha0.isSelfAdjoint
      (by simpa only [show J.quotientStarHom a = h from ha] using hh.isSelfAdjoint)]
    rw [show J.quotientStarHom a = h from ha];rfl
  refine ⟨J.quotientMap P,hPJ,?_,?_,?_⟩
  · rw [←hc,←map_mul,hfix.1]
  · rw [←hc,←map_mul,hfix.2]
  · intro s
    rw [←hbJ]
    apply limitTrace_eq_of_coordinate_errors τ U P b _ hδlim _ s
    intro n t
    have hpR : ((τ t).functional (P n)).im=0 := ((τ t).functional.map_nonneg
      (map_nonneg (boundedFamilyEval n) hP0)).2.symm
    have hbR : ((τ t).functional (b n)).im=0 := ((τ t).functional.map_nonneg (hb0 n)).2.symm
    have he : (τ t).functional (P n-b n)=
        ((((τ t).functional (P n)).re-((τ t).functional (b n)).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp only [map_sub,Complex.sub_re,Complex.sub_im,
        Complex.ofReal_re,Complex.ofReal_im,hpR,hbR,sub_self]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith [(hpτ' n t).2.1])]
    linarith [(hpτ' n t).1]

end NonunitalGamma

end

end OAI
