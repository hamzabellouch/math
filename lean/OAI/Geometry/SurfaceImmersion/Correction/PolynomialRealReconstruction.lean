import OAI.Geometry.SurfaceImmersion.Correction.PolynomialDualBounds

namespace OAI

/-! A common polynomial bound for every real reconstruction coefficient. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open WeightedEstimates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalRatioBudget (m : ℕ) (C K : ℝ) :=
  2^m*dotBudget m C*((m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m C)^m)

def reconstructionBudget (m : ℕ) (C K : ℝ) :=
  1+liftBudget m C K+normalBudget m C K+tangentDualBudget m C K+
    normalDualBudget m (normalBudget m C K) K+normalRatioBudget m (normalBudget m C K) K

lemma reconstructionBudget_bounds (m : ℕ) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) :
    1 ≤ reconstructionBudget m C K ∧
    liftBudget m C K ≤ reconstructionBudget m C K ∧
    normalBudget m C K ≤ reconstructionBudget m C K ∧
    tangentDualBudget m C K ≤ reconstructionBudget m C K ∧
    normalDualBudget m (normalBudget m C K) K ≤ reconstructionBudget m C K ∧
    normalRatioBudget m (normalBudget m C K) K ≤ reconstructionBudget m C K := by
  have hl := liftBudget_nonneg m hC hK
  have hn : 0 ≤ normalBudget m C K := by unfold normalBudget; positivity
  have hi := inverseGramBudget_nonneg m hC hK
  have hd := dotBudget_nonneg m hC
  have hdn := dotBudget_nonneg m hn
  have ht : 0 ≤ tangentDualBudget m C K := by unfold tangentDualBudget; positivity
  have hnd : 0 ≤ normalDualBudget m (normalBudget m C K) K := by unfold normalDualBudget; positivity
  have hnr : 0 ≤ normalRatioBudget m (normalBudget m C K) K := by unfold normalRatioBudget; positivity
  unfold reconstructionBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The two inverse bounds concern the Gram determinant and the squared
length of the transverse second fundamental form. All derivatives are
estimated by explicit polynomials in these bounds and the two-jet bound. -/
theorem weighted_realJet_coefficients {U : Set E} (hU : UniqueDiffOn ℝ U)
    {J : E → RealTwoJet} (hJ : ContDiff ℝ ∞ J) {s C K : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 1 ≤ C) (hK : 1 ≤ K) (bJ : WeightedBound U s m C J)
    (hD : ∀ x ∈ U, NormalFrame.gramDet (J x 0) (J x 1) ≠ 0)
    (hN : ∀ x ∈ U, realJetNormal (J x) 4 ≠ 0)
    (hGD : ∀ x ∈ U, ‖(NormalFrame.gramDet (J x 0) (J x 1))⁻¹‖ ≤ K)
    (hGN : ∀ x ∈ U, ‖(realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)⁻¹‖ ≤ K) :
    (∀ i, WeightedBound U s m (reconstructionBudget m C K) (fun x => realScalarCoefficients (J x) i)) ∧
    (∀ i, WeightedBound U s m (reconstructionBudget m C K) (fun x => realVectorCoefficients (J x) i)) := by
  have hC0 := zero_le_one.trans hC
  have hK0 := zero_le_one.trans hK
  have hJs (i : Fin 5) : ContDiff ℝ ∞ (fun x => J x i) := contDiff_pi.mp hJ i
  have bj (i : Fin 5) := bJ.component hU hs.le hC0 hJ.contDiffOn i
  have bc (i : Fin 5) := weighted_realConnections hU hs hC hK
    (hJs 0).contDiffOn (hJs 1).contDiffOn (hJs i).contDiffOn (bj 0) (bj 1) (bj i) hD hGD
  have bN (i : Fin 5) : WeightedBound U s m (normalBudget m C K) (fun x => realJetNormal (J x) i) :=
    weighted_realNormalPart hU hs hC hK (hJs 0).contDiffOn (hJs 1).contDiffOn
      (hJs i).contDiffOn (bj 0) (bj 1) (bj i) hD hGD
  have hNs (i : Fin 5) : ContDiffOn ℝ ∞ (fun x => realJetNormal (J x) i) U := by
    intro x hx
    exact (contDiffAt_realNormalPart (hJs 0).contDiffAt (hJs 1).contDiffAt
      (hJs i).contDiffAt (hD x hx)).contDiffWithinAt
  have hn0 : 0 ≤ normalBudget m C K := by
    have hh := liftBudget_nonneg m hC0 hK0
    unfold normalBudget
    positivity
  have hd0 := dotBudget_nonneg m hn0
  have hpos : ∀ x ∈ U, 0 < realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4 := by
    intro x hx
    have hh : 0 ≤ realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4 :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact hh.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr (hN x hx))
  have hplain : ∀ x ∈ U, (realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)⁻¹ ≤ K :=
    fun x hx => (le_abs_self _).trans (hGN x hx)
  have hsq := contDiffOn_dot_real (hNs 4) (hNs 4)
  have bsq : WeightedBound U s m (1+dotBudget m (normalBudget m C K))
      (fun x => realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4) :=
    ((bN 4).dot_real hU hs.le hn0 hn0 (hNs 4) (hNs 4) (bN 4)).mono_const (by
      change dotBudget m (normalBudget m C K) ≤ _
      linarith)
  have binv := bsq.inv_real hU hs (by linarith : 1 ≤ 1+dotBudget m (normalBudget m C K))
    hK hsq (fun x hx => (hpos x hx).ne') hGN
  have hsqi := hsq.inv (fun x hx => (hpos x hx).ne')
  have hbi : 0 ≤ (m.factorial : ℝ)^2*K^(m+1)*(1+dotBudget m (normalBudget m C K))^m := by positivity
  have bratio (i : Fin 5) : WeightedBound U s m (normalRatioBudget m (normalBudget m C K) K)
      (fun x => (realJetNormal (J x) i ⬝ᵥ realJetNormal (J x) 4)/
        (realJetNormal (J x) 4 ⬝ᵥ realJetNormal (J x) 4)) := by
    have hh := ((bN i).dot_real hU hs.le hn0 hn0 (hNs i) (hNs 4) (bN 4)).mul_real
      hU hs.le hd0 hbi (contDiffOn_dot_real (hNs i) (hNs 4)) hsqi binv
    exact hh.congr (fun x hx => div_eq_mul_inv _ _)
  have bduals := weighted_realTangentDuals hU hs hC hK (hJs 0).contDiffOn (hJs 1).contDiffOn
    (bj 0) (bj 1) hD hGD
  have bnormal := weighted_vector_over_norm_sq hU hs hn0 hK (hNs 4) (bN 4) hpos hplain
  obtain ⟨_,hbl,hbn,hbt,hbnd,hbnr⟩ := reconstructionBudget_bounds m hC0 hK0
  constructor
  · intro i
    fin_cases i
    · exact (bc 2).1.mono_const hbl
    · exact (bc 2).2.mono_const hbl
    · exact (bc 3).1.mono_const hbl
    · exact (bc 3).2.mono_const hbl
    · exact (bc 4).1.mono_const hbl
    · exact (bc 4).2.mono_const hbl
    · exact (bratio 2).mono_const hbnr
    · exact (bratio 3).mono_const hbnr
  · intro i
    fin_cases i
    · exact (bN 2).mono_const hbn
    · exact (bN 3).mono_const hbn
    · exact bduals.1.mono_const hbt
    · exact bduals.2.mono_const hbt
    · exact bnormal.mono_const hbnd

end ClosedSurfaceR4.RealModes

end

end OAI
