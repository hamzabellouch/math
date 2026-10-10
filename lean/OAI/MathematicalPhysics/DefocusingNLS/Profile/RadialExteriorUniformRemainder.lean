import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCommonTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonical
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! A fixed sufficiently high expansion order gives a uniformly bounded
weighted remainder for the canonical profiles along the singular limit. -/

open Polynomial Set Filter Topology
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem radialExteriorCanonical_uniform_remainder
    (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (j : ℕ) (hj : radialExteriorMatrixBound ν₀ < 2*(j : ℝ)) :
    ∃ T C : ℝ, 0 ≤ T ∧ L ≤ T ∧ 0 ≤ C ∧
      ∃ v : ℕ → ℝ →ᵇ ℂ × ℂ, ∃ w : ℝ →ᵇ ℂ × ℂ,
        Tendsto v atTop (𝓝 w) ∧ (∀ n, ‖v n‖ ≤ C) ∧
        ∀ᶠ n in atTop, ∀ t, T ≤ t →
          ‖(radialExteriorCanonical (ν n) n (m n) L t).1‖ ≤ ‖m₀‖+δ ∧
          ‖radialExteriorPolynomialFunction (radialExteriorExpansion (ν n) n (m n) j) t‖ ≤ ‖m₀‖+δ ∧
          radialExteriorCanonical (ν n) n (m n) L t=
            radialPolynomialJet (radialExteriorExpansion (ν n) n (m n) j) t+
              radialExteriorUnweight (2*(j : ℝ)) (v n) t := by
  let κ : ℝ := 2*(j : ℝ)
  have hκ0 : 0 < κ := (radialExteriorMatrixBound_pos ν₀).trans hj
  have hm01 : ‖m₀‖ < 1 := by linarith
  have hB : Tendsto (fun n => radialExteriorMatrixBound (ν n)) atTop
      (𝓝 (radialExteriorMatrixBound ν₀)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact hc.continuousAt.tendsto.comp hν
  have hmargin : ∀ᶠ n in atTop, radialExteriorMatrixBound (ν n)+
      radialExteriorCutoffRate n m₀ δ < κ := by
    have hh := hB.add (radialExteriorCutoffRate_tendsto m₀ δ hδ.le hsmall)
    rw [add_zero] at hh
    exact hh.eventually (gt_mem_nhds hj)
  let P := fun n => radialExteriorExpansion (ν n) n (m n) j
  let Q := radialFreeExpansion ν₀ m₀ j
  obtain ⟨T,hT,R,R₀,hR,_hR₀,hr⟩ :=
    exists_radialExterior_bounded_residual_family ν m ν₀ m₀ hν hm hm01 j
  let f : ℕ → ℝ → ℂ := fun n => boundedRadialPolynomialAfter T (P n)
  let r := fun n => boundedRadialResidualAfter T (R n)
  obtain ⟨v,w,hvw,_,_,hv⟩ := exists_radialExterior_convergent_corrections κ ν ν₀ m₀ δ hν
    hδ.le hsmall hj f (fun n => (boundedRadialPolynomialAfter T (P n)).continuous) r (boundedRadialResidualAfter T R₀) hr
  let Z := fun n t => radialPolynomialJet (P n) t+radialExteriorUnweight κ (v n) t
  let Z₀ := fun t => radialPolynomialJet Q t+radialExteriorUnweight κ w t
  have hZ : TendstoUniformlyOn Z Z₀ atTop (Ici (0 : ℝ)) :=
    radialExterior_corrected_jet_uniform_limit κ hκ0.le ν m ν₀ m₀ hν hm hm01 j v w hvw
  have hZ₀lim : Tendsto Z₀ atTop (𝓝 (m₀,0)) := by
    simpa only [Q,radialFreeExpansion_constant] using
      radialExterior_corrected_jet_tendsto κ hκ0 Q w
  have hP : TendstoUniformlyOn (fun n => radialPolynomialJet (P n)) (radialPolynomialJet Q)
      atTop (Ici (0 : ℝ)) := radialPolynomialJet_uniform_limit P Q j
    (Eventually.of_forall (fun _ => radialExteriorExpansion_degree _ _ _ _))
    (radialFreeExpansion_degree _ _ _) (fun k _ =>
      radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm01 j k)
  have hQlim : Tendsto (radialPolynomialJet Q) atTop (𝓝 (m₀,0)) := by
    simpa only [Q,radialFreeExpansion_constant] using radialPolynomialJet_tendsto Q
  obtain ⟨SP,_,hSP⟩ := radial_uniform_tail_near_limit (fun n => radialPolynomialJet (P n))
    (radialPolynomialJet Q) (m₀,0) δ hδ hP hQlim
  obtain ⟨SF,_,hSF⟩ := radial_uniform_tail_near_limit Z Z₀ (m₀,0) δ hδ hZ hZ₀lim
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto v hvw).exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (v 0)).trans (hC _ (mem_range_self 0))
  let S := max L (max T (max SP SF))
  have hSL : L ≤ S := le_max_left _ _
  have hST : T ≤ S := (le_max_left T _).trans (le_max_right L _)
  have hSSP : SP ≤ S := (le_max_left SP SF).trans
    ((le_max_right T _).trans (le_max_right L _))
  have hSSF : SF ≤ S := (le_max_right SP SF).trans
    ((le_max_right T _).trans (le_max_right L _))
  refine ⟨S,C,hT.trans hST,hSL,hC0,v,w,hvw,(fun n => hC _ (mem_range_self n)),?_⟩
  have hmB : ∀ᶠ n in atTop, ‖m n‖ ≤ ‖m₀‖+2*δ :=
    (hm.norm.eventually (gt_mem_nhds (by linarith : ‖m₀‖ < ‖m₀‖+2*δ))).mono
      (fun _ h => h.le)
  filter_upwards [hX,hv,hSP,hSF,hmargin,hmB] with n hXn hvn hpn hfn hmn hmb t ht
  have hcZ : Continuous (Z n) := continuous_radialExterior_polynomialCorrection _ _ _
  have hdZ : ∀ t, S ≤ t → HasDerivAt (Z n) (radialExteriorODEField (ν n) n t (Z n t)) t := by
    intro t ht
    have hpn' : ‖radialExteriorPolynomialFunction (P n) t-m₀‖ ≤ δ :=
      ((norm_fst_le (radialPolynomialJet (P n) t-(m₀,0))).trans_lt
        (hpn t (hSSP.trans ht))).le
    have hfn' : ‖(Z n t).1-m₀‖ ≤ δ :=
      ((norm_fst_le (Z n t-(m₀,0))).trans_lt (hfn t (hSSF.trans ht))).le
    have hd := radialExterior_tail_cutoff_removal (ν n) m₀ n j δ T (P n) (R n)
      (hR n) (v n) t (hST.trans ht) hpn' hfn' (hvn.2.2 t)
    exact hd.1.prodMk hd.2
  have hexp : HasRadialOutgoingExpansion (ν n) n (m n) (Z n) := by
    refine ⟨j,v n,S,?_,fun _ _ => rfl⟩
    have hrate : (2*(n : ℝ)+1)*‖m n‖^(2*n) ≤ radialExteriorCutoffRate n m₀ δ := by
      unfold radialExteriorCutoffRate
      have hb : 0 ≤ (2*(n : ℝ)+1)*(‖m₀‖+2*δ)^(2*n) := by positivity
      calc
        (2*(n : ℝ)+1)*‖m n‖^(2*n) ≤ (2*(n : ℝ)+1)*(‖m₀‖+2*δ)^(2*n) := by gcongr
        _ ≤ _ := by nlinarith
    exact (add_le_add le_rfl hrate).trans_lt hmn
  obtain ⟨hc,he,hd⟩ := radialExteriorCanonical_spec hXn
  have heq := radialExterior_outgoing_unique (ν n) n (m n) S _ (Z n) hc hcZ
    (fun t ht => (hd t (hSL.trans ht)).2) hdZ he hexp t ht
  refine ⟨?_,?_,heq⟩
  · rw [heq]
    have hb := (norm_fst_le (Z n t-(m₀,0))).trans_lt (hfn t (hSSF.trans ht))
    change ‖(Z n t).1-m₀‖ < δ at hb
    calc
      ‖(Z n t).1‖ ≤ ‖(Z n t).1-m₀‖+‖m₀‖ := by
        simpa only [sub_add_cancel] using norm_add_le ((Z n t).1-m₀) m₀
      _ ≤ ‖m₀‖+δ := by linarith
  · have hb := (norm_fst_le (radialPolynomialJet (P n) t-(m₀,0))).trans_lt
      (hpn t (hSSP.trans ht))
    change ‖radialExteriorPolynomialFunction (P n) t-m₀‖ < δ at hb
    calc
      ‖radialExteriorPolynomialFunction (P n) t‖ ≤
          ‖radialExteriorPolynomialFunction (P n) t-m₀‖+‖m₀‖ := by
            simpa only [sub_add_cancel] using
              norm_add_le (radialExteriorPolynomialFunction (P n) t-m₀) m₀
      _ ≤ ‖m₀‖+δ := by linarith

end DefocusingNLS

end OAI
