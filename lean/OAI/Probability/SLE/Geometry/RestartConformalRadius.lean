import OAI.Probability.SLE.StoppedMeasures

namespace OAI

/-! Exact composition of the actual restarted maps, obtained from reverse
Loewner uniqueness. The conformal-radius and marked-angle identities then
use differentiation on the actual surviving domain. -/

noncomputable section
open Set Filter
open scoped Topology NNReal

namespace SLEExactGauge

lemma IsCapacityTwoWitness.restart_inverse_composition
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (v : ℂ) (hv : v ∈ upperHalfPlane) :
    F (T + t) (v + (U T : ℂ)) = F T (F' t v + (U T : ℂ)) := by
  let Q : ℝ → ℂ := fun s => G' ((t : ℝ) - s).toNNReal (F' t v)
  have hQ0 : Q 0 = v := by
    simp only [Q, sub_zero, Real.toNNReal_coe]
    exact hb.2.2.2.2.2.2.2.2.1 t v hv
  have hQd (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :
      HasDerivWithinAt Q
        (reverseField v.im (U (T + ((t : ℝ) - s).toNNReal) - U T) (Q s))
        (Icc 0 (t : ℝ)) s := hb.reverse_path_derivative t v hv le_rfl s hs
  have hh := hw.source_shifted_reverse_identifies T t v hv le_rfl Q hQ0 hQd
  have hQt : Q t = F' t v := by
    simp only [Q, sub_self, Real.toNNReal_zero]
    exact hb.2.2.2.2.2.2.2.2.2.1 _ (hb.2.2.2.2.2.2.1 t hv).1.1
  rwa [hQt] at hh

theorem IsCapacityTwoWitness.restart_forward_composition
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    F T (z + (U T : ℂ)) ∈ survivingDomain γ (T + t) ∧
      G (T + t) (F T (z + (U T : ℂ))) = G' t z + (U T : ℂ) := by
  have hv : G' t z ∈ upperHalfPlane := hb.2.2.2.2.2.1 t hz
  have hvi : G' t z + (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hv
  have hh := hw.restart_inverse_composition T hb t (G' t z) hv
  rw [hb.2.2.2.2.2.2.2.1 t z hz] at hh
  rw [← hh]
  exact ⟨hw.2.2.2.2.2.2.1 (T + t) hvi, hw.2.2.2.2.2.2.2.2.1 (T + t) _ hvi⟩

lemma IsCapacityTwoWitness.restart_derivative_composition
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    deriv (G (T + t)) (F T (z + (U T : ℂ))) * deriv (F T) (z + (U T : ℂ)) =
      deriv (G' t) z := by
  have hphysical := (hw.restart_forward_composition T hb t z hz).1
  have hzH : z + (U T : ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.add_im, Complex.ofReal_im, add_zero] using hz.1.1
  have hDF := ((hw.2.2.2.2.1 T).differentiableAt
    (isOpen_upperHalfPlane.mem_nhds hzH)).hasDerivAt.comp z ((hasDerivAt_id z).add_const (U T : ℂ))
  have hDG := ((hw.2.2.2.1 (T + t)).differentiableAt
    ((isOpen_survivingDomain hw.1 (T + t)).mem_nhds hphysical)).hasDerivAt
  have he : (fun u => G (T + t) (F T (u + (U T : ℂ)))) =ᶠ[𝓝 z]
      (fun u => G' t u + (U T : ℂ)) := by
    filter_upwards [(isOpen_survivingDomain hb.1 t).mem_nhds hz] with u hu
    exact (hw.restart_forward_composition T hb t u hu).2
  have hD := ((hDG.comp z hDF).congr_of_eventuallyEq he.symm).unique
    (((hb.2.2.2.1 t).differentiableAt
      ((isOpen_survivingDomain hb.1 t).mem_nhds hz)).hasDerivAt.add_const (U T : ℂ))
  simpa only [mul_one] using hD

theorem IsCapacityTwoWitness.restart_radius_composition
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    fullRadius G (T + t) (F T (z + (U T : ℂ))) =
      ‖deriv (F T) (z + (U T : ℂ))‖ * fullRadius G' t z := by
  have hforward := hw.restart_forward_composition T hb t z hz
  have hnorm := congrArg norm (hw.restart_derivative_composition T hb t z hz)
  rw [norm_mul] at hnorm
  have hGpos := hw.derivative_norm_positive hU (T + t) _ hforward.1
  have hUp : Continuous (fun t => U (T + t) - U T) :=
    (hU.comp (continuous_const.add continuous_id)).sub continuous_const
  have hG'pos := hb.derivative_norm_positive hUp t z hz
  unfold fullRadius
  rw [hforward.2]
  simp only [Complex.add_im, Complex.ofReal_im, add_zero]
  rw [← mul_div_assoc]
  apply (eq_div_iff hG'pos.ne').mpr
  rw [← hnorm]
  field_simp [hGpos.ne']

lemma IsCapacityTwoWitness.restart_centered_value
    {U : ℝ≥0 → ℝ} {γ β : ℝ≥0 → ℂ} {G F G' F' : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (hb : IsCapacityTwoWitness (fun t => U (T + t) - U T) β G' F')
    (t : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain β t) :
    G (T + t) (F T (z + (U T : ℂ))) - (U (T + t) : ℂ) =
      G' t z - ((U (T + t) - U T : ℝ) : ℂ) := by
  rw [(hw.restart_forward_composition T hb t z hz).2, Complex.ofReal_sub]
  ring

end SLEExactGauge

end

end OAI
