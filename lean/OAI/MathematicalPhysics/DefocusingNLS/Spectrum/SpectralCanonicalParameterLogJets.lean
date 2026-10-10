import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralParameterLogJets
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalParameterEquation

namespace OAI

/-! The actual canonical parameter derivative has bounded normalized jets. -/

open Set Filter Topology
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_parameter_logJets (ν η b : ℂ) (n : ℕ) (hn : 1≤n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0)
    (c : ℂ × ℂ) (Y : ℂ → ℝ → E₄)
    (hY : IsCanonicalHolomorphicColumn ν η b n L c Y) (z : ℂ) :
    HasLogJetBound 0 (fun t => (deriv (fun lam => Y lam t) z).1.1) ∧
    HasLogJetBound 0 (fun t => (deriv (fun lam => Y lam t) z).2.1) := by
  let q := radialExteriorCanonical ν n b L
  let D := fun t => deriv (fun lam => Y lam t) z
  let νp := ν-2*z
  let νm := star ν-2*z
  let L₀ := max L 0
  have hq (t : ℝ) (ht : L₀<t) : HasDerivAt q (radialExteriorODEField ν n t (q t)) t :=
    ((radialExteriorCanonical_spec hX).2.2 t ((le_max_left L 0).trans ht.le)).2
  have hYe (t : ℝ) (ht : L₀<t) : HasDerivAt (Y z)
      (circularLeadingField t (Y z t)+circularBoundedField νp νm η n (q t).1 (Y z t)) t :=
    hY.1 z t ((le_max_right L 0).trans ht.le)
  have hDe (t : ℝ) (ht : L₀<t) : HasDerivAt D
      (circularLeadingField t (D t)+circularBoundedField νp νm η n (q t).1 (D t)+
        circularPointSlopeCLM νp νm 0 (Y z t)) t := by
    have h := canonical_circular_parameter_equation ν η b n hn L hX hb c Y hY z t
      ((le_max_right L 0).trans_lt ht)
    rw [circularPointSlope_shift] at h
    exact h
  let Mq := ‖(b,(0 : ℂ))‖+1
  let MY := ‖((c.1,(0 : ℂ)),(c.2,(0 : ℂ)))‖+1
  obtain ⟨Uq,hUq⟩ := eventually_atTop.mp
    ((radialExteriorCanonical_spec hX).2.1.tendsto.norm.eventually
      (gt_mem_nhds (show ‖(b,(0 : ℂ))‖<Mq by dsimp only [Mq]; linarith)))
  obtain ⟨UY,hUY⟩ := eventually_atTop.mp
    ((hY.2.1 z).norm.eventually
      (gt_mem_nhds (show ‖((c.1,(0 : ℂ)),(c.2,(0 : ℂ)))‖<MY by dsimp only [MY]; linarith)))
  obtain ⟨C,hC⟩ := canonical_circular_parameter_bounded ν η b n hn L hX hb c Y hY z
  let M := max Mq (max MY C)
  let U := max 0 (max Uq UY)
  have hM : 0≤M := (by dsimp only [Mq]; positivity : 0≤Mq).trans (le_max_left _ _)
  have hbq (t : ℝ) (ht : U≤t) : ‖q t‖≤M :=
    (hUq t (((le_max_left Uq UY).trans (le_max_right 0 _)).trans ht)).le.trans (le_max_left _ _)
  have hbY (t : ℝ) (ht : U≤t) : ‖Y z t‖≤M :=
    (hUY t (((le_max_right Uq UY).trans (le_max_right 0 _)).trans ht)).le.trans
      ((le_max_left MY C).trans (le_max_right _ _))
  have hbD (t : ℝ) (ht : U≤t) : ‖D t‖≤M :=
    (hC t ((le_max_left 0 _).trans ht)).trans
      ((le_max_right MY C).trans (le_max_right _ _))
  obtain ⟨P,hP⟩ := canonical_parameter_polynomial_approximation ν η b n hn L hX hb c Y hY z
  have hpos := spectralParameter_positive_derivatives ν νp νm η n q (Y z) D L₀ U M hM
    hq hYe hDe hbq hbY hbD P (by
      intro J
      obtain ⟨A,hA,hAT⟩ := hP J
      exact ⟨A,0,hA,hAT⟩)
  have hs := spectralParameter_solution_contDiffOn ν νp νm η n q (Y z) D L₀ hq hYe hDe
  exact ⟨HasLogJetBound.of_bounded_positive_decay _ L₀ U M hM hs.fst.fst
      (fun t ht => (norm_fst_le _).trans ((norm_fst_le _).trans (hbD t ht))) hpos.1,
    HasLogJetBound.of_bounded_positive_decay _ L₀ U M hM hs.snd.fst
      (fun t ht => (norm_fst_le _).trans ((norm_snd_le _).trans (hbD t ht))) hpos.2⟩

end DefocusingNLS

end OAI
