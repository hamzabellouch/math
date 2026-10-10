import OAI.NumberTheory.Jacobsthal.Estimates.SourceCenteredGap

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter
open scoped Topology
namespace ErdosSourceReferenceMargin
open NumberTheoryLean.ReferenceMertens NumberTheoryLean.ReferenceProductErrors

theorem root_B_log_W {z : ℝ} (hw : 1 < ErdosInverseBoxHeight.sourceW z) :
    ErdosInverseBoxHeight.sourceB z*Real.log (ErdosInverseBoxHeight.sourceW z)=Real.log z := by
  exact div_mul_cancel₀ _ (Real.log_pos hw).ne'

theorem root_product_error_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun z : ℝ => Real.exp (-c*Real.sqrt (Real.log z))) atTop (𝓝 0) := by
  have ht := (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).const_mul_atTop hc
  simpa only [Function.comp_def,neg_mul] using! Real.tendsto_exp_neg_atTop_nhds_zero.comp ht

theorem root_referenceProduct_error_tendsto (closed : Bool) :
    Tendsto (fun z => ErdosInverseBoxHeight.sourceB z*
      referenceProduct (ErdosInverseBoxHeight.sourceW z) (ErdosInverseBoxHeight.sourceB z) closed-
      normalization (ErdosInverseBoxHeight.sourceW z)) atTop (𝓝 0) := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,h⟩ := reference_product_absolute
  have hlim : Tendsto (fun z : ℝ => C*Real.exp (-c*Real.sqrt (Real.log z))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (root_product_error_decay hc).const_mul C
  have hbound : ∀ᶠ z : ℝ in atTop,
      |ErdosInverseBoxHeight.sourceB z*referenceProduct (ErdosInverseBoxHeight.sourceW z)
        (ErdosInverseBoxHeight.sourceB z) closed-normalization (ErdosInverseBoxHeight.sourceW z)| ≤
        C*Real.exp (-c*Real.sqrt (Real.log z)) := by
    filter_upwards [rootB_tendsto.eventually (eventually_ge_atTop (2:ℝ)),
      rootW_tendsto.eventually (eventually_ge_atTop w₀)] with z hb hw
    have hW : 1 < ErdosInverseBoxHeight.sourceW z := hw₀.trans_le hw
    have hB : 0 < ErdosInverseBoxHeight.sourceB z := by linarith
    have hp := (h (ErdosInverseBoxHeight.sourceW z) hw).2.2 (ErdosInverseBoxHeight.sourceB z) hb closed
    rw [root_B_log_W hW] at hp
    have hh := mul_le_mul_of_nonneg_left hp hB.le
    have he : ErdosInverseBoxHeight.sourceB z*referenceProduct (ErdosInverseBoxHeight.sourceW z)
        (ErdosInverseBoxHeight.sourceB z) closed-normalization (ErdosInverseBoxHeight.sourceW z)=
        ErdosInverseBoxHeight.sourceB z*(referenceProduct (ErdosInverseBoxHeight.sourceW z)
          (ErdosInverseBoxHeight.sourceB z) closed-normalization (ErdosInverseBoxHeight.sourceW z)/ErdosInverseBoxHeight.sourceB z) := by
      field_simp
    rw [he,abs_mul,abs_of_pos hB]
    have hcanc : ErdosInverseBoxHeight.sourceB z*
        ((C/ErdosInverseBoxHeight.sourceB z)*Real.exp (-c*Real.sqrt (Real.log z)))=
        C*Real.exp (-c*Real.sqrt (Real.log z)) := by field_simp
    exact hh.trans_eq hcanc
  have habs := squeeze_zero' (Filter.Eventually.of_forall (fun z => abs_nonneg
    (ErdosInverseBoxHeight.sourceB z*referenceProduct (ErdosInverseBoxHeight.sourceW z)
      (ErdosInverseBoxHeight.sourceB z) closed-normalization (ErdosInverseBoxHeight.sourceW z)))) hbound hlim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

theorem root_referenceProduct_tendsto (closed : Bool) :
    Tendsto (fun z => ErdosInverseBoxHeight.sourceB z*
      referenceProduct (ErdosInverseBoxHeight.sourceW z) (ErdosInverseBoxHeight.sourceB z) closed) atTop (𝓝 1) := by
  have hh := (root_referenceProduct_error_tendsto closed).add (normalization_tendsto_one.comp rootW_tendsto)
  simpa only [sub_add_cancel,zero_add,Function.comp_def] using! hh

end ErdosSourceReferenceMargin

end

end Erdos970

end OAI
