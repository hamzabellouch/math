import OAI.Geometry.SurfaceImmersion.Atlas.GoodPhaseStability

namespace OAI

/-! The good-phase stability radius uses only the ordinary C2 difference. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry WeightedEstimates

lemma coordDeriv_sub_smooth {F G : RField 4} (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (v : Base) :
    coordDeriv v (F-G) = coordDeriv v F - coordDeriv v G := by
  funext p
  simp only [coordDeriv, fderiv_sub (hF.differentiable (by simp) p)
    (hG.differentiable (by simp) p), sub_apply, Pi.sub_apply]

lemma realTwoJet_sub {F G : RField 4} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    realTwoJet (F-G) = realTwoJet F - realTwoJet G := by
  have hx := coordDeriv_sub_smooth hF hG dx
  have hy := coordDeriv_sub_smooth hF hG dy
  have hxx := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dx)
    (contDiff_real_coordDeriv hG dx) dx
  have hxy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dx
  have hyy := coordDeriv_sub_smooth (contDiff_real_coordDeriv hF dy)
    (contDiff_real_coordDeriv hG dy) dy
  funext p i
  fin_cases i <;> simp [realTwoJet,hx,hy,hxx,hxy,hyy]

lemma norm_realTwoJet_le {F : RField 4} (hF : ContDiff ℝ ∞ F) {C : ℝ} (hC : 0 ≤ C)
    (hb : WeightedBound univ 1 2 C F) (p : Base) : ‖realTwoJet F p‖ ≤ C := by
  have h1 (v : Base) (hv : ‖v‖ = 1) : WeightedBound univ 1 1 C (coordDeriv v F) := by
    change WeightedBound univ 1 1 C (fun x => fderiv ℝ F x v)
    simpa only [hv,div_one,one_mul] using hb.directional isOpen_univ zero_lt_one hF.contDiffOn v
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) p‖ ≤ C := by
    have hd := (h1 w hw).directional isOpen_univ zero_lt_one
      (contDiff_real_coordDeriv hF w).contDiffOn v
    simpa only [coordDeriv,hv,div_one,one_mul] using hd.norm_le (mem_univ p)
  have hx : ‖dx‖ = 1 := by simp [dx]
  have hy : ‖dy‖ = 1 := by simp [dy]
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  fin_cases i
  · exact (h1 dx hx).norm_le (mem_univ p)
  · exact (h1 dy hy).norm_le (mem_univ p)
  · exact h2 dx dx hx hx
  · exact h2 dx dy hx hy
  · exact h2 dy dy hy hy

theorem compact_good_phase_C2_stability {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (K : TopologicalSpace.Compacts Base)
    (hImm : ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ (K : Set Base), Good (realSecondTensor F p) (phaseDerivative φ p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (G : RField 4), ContDiff ℝ ∞ G →
      ∀ C : ℝ, 0 ≤ C → C < ε → WeightedBound univ 1 2 C (G-F) →
      ∀ p ∈ (K : Set Base), Function.Injective (fderiv ℝ G p) ∧
        Good (realSecondTensor G p) (phaseDerivative φ p) := by
  obtain ⟨ε,hε,he⟩ := compact_good_phase_stability hF hφ K hImm hgood
  refine ⟨ε,hε,?_⟩
  intro G hG C hC hCε hb
  apply he G
  intro p _
  have hp := norm_realTwoJet_le (hG.sub hF) hC hb p
  change ‖realTwoJet (G-F) p‖ ≤ C at hp
  rw [realTwoJet_sub hG hF] at hp
  exact hp.trans_lt hCε

end ClosedSurfaceR4.RealModes

end

end OAI
