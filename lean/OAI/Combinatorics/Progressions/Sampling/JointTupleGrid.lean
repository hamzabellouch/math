import OAI.Combinatorics.Progressions.Estimates.JointL1TupleQuadrature
import OAI.Combinatorics.Progressions.Probability.AveragedJointImageLaw

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointAffineJetDensity_principalTuple_grid {Q Z K D α : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    {I J N : Q → Type*} [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
    (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
    (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
    (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℝ) (hz : ∀ j, |z j| ≤ 1) (rows : ∀ q, I q → Finset α)
    (degree : Q → ℕ) (hd : ∀ q n, (e q n).sum (fun _ k => k) ≤ degree q)
    (c w : ∀ q, J q ⊕ N q → ℝ) (hw : ∀ q j, 0 < w q j) (δ R : Q → ℝ≥0)
    (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (hsupport : ∀ q j, |c q j| + w q j ≤ R q)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (Cap Lip Ro : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ q, pivotKernelCap (UnselectedColumn (s q)) (A q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap)
    (hlip : ∀ q, pivotKernelLip (UnselectedColumn (s q)) (A q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip)
    (hRo : ∀ q, normalizedJetOutputRadius α (N q) (A q) (F q) (degree q) (R q) (R q) ≤ Ro)
    (a S : (Σ q, I q) → ℝ) (hS : ∀ j, 0 < S j) {mesh G : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ j, 1 / S j ≤ mesh)
    (grid : Finset ((Σ q, I q) → ℤ)) (mask : ((Σ q, I q) → ℤ) → ℝ)
    (φ : ((Σ q, I q) → ℤ) → ℂ) (hG : 0 ≤ G)
    (hmask : ∀ v ∈ grid, |mask v| ≤ G) (hφ : ∀ v ∈ grid, ‖φ v‖ ≤ 1) :
    let ρ := fun x => jointAffineJetDensity s A F e input z rows c w x ∘ sigmaAxisCoordinates I
    let KT := ∑ q, affineJetL1Cost (JointBlockParameter B h α) α (J q) (N q) (A q) (degree q) (δ q) (R q)
    let KO := Fintype.card Q * Lip * Cap^Fintype.card Q
    let E := (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + KT) *
      ∑ j, (m : ℝ)/L j
    ‖(principalResidueWeights B h L hL m hm r hsize).complexMean
        (fun y => gridDensityTest (ρ (principalTupleNormalized L y)) a S grid mask φ) -
      gridDensityTest (densityMixture (jointBooleanSource h) ρ) a S grid mask φ‖ ≤
        G * (E + (2 * (Ro : ℝ) + 2)^Fintype.card (Σ q, I q) * ((KO : ℝ) + KO) * mesh) := by
  dsimp only
  let p := principalResidueWeights B h L hL m hm r hsize
  let ρ := fun x => jointAffineJetDensity s A F e input z rows c w x ∘ sigmaAxisCoordinates I
  have hρ : Measurable (Function.uncurry ρ) :=
    jointAffineJetDensity_measurable_comp
      (Ω := (JointBlockParameter B h α → ℝ) × ((Σ q, I q) → ℝ)) s A F e input rows c w hw R hsupport
      (fun _ => z) (fun _ => measurable_const) (fun t => t.1)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun t => sigmaAxisCoordinates I t.2)
      (fun q i => (measurable_pi_apply (Sigma.mk q i)).comp measurable_snd)
  have hreg (x) := jointAffineJetDensity_output_bounds s A F e input z rows c w hw δ R hδ
    hwidth hsupport Cap Lip hCap hcap hlip x
  have hp (x) := jointAffineJetDensity_probability_data s A F e input z rows c w hw R hsupport x
  have hL1 := jointAffineJetDensity_principalTuple_l1 B h s A F e input z hz rows degree hd c w hw δ R
    hδ hwidth hsupport L (fun _ => m) hL (fun _ _ => m) r (fun _ _ => hm)
    (fun _ _ => le_rfl) hsize hsmall
  refine finiteSource_gridDensityTest_error p (principalTupleNormalized L) (jointBooleanSource h)
    (Metric.closedBall 0 1) ?_ (jointBooleanSource_ae_closedBall B h) ρ hρ
    (Cap^Fintype.card Q) (Fintype.card Q * Lip * Cap^Fintype.card Q)
    ?_ ?_ a S hS Ro.coe_nonneg hmesh0 hmesh1 hmesh ?_ grid mask φ hG hmask hφ ?_
  · intro y
    rw [Metric.mem_closedBall, dist_zero_right]
    exact principalTuple_normalized_norm_le B h hL y
  · intro x _ v
    exact ⟨(hp x).2.1 _, (le_abs_self _).trans ((hreg x).1 _)⟩
  · intro x _
    simpa only [mul_one] using (hreg x).2.comp (sigmaAxisCoordinates_lipschitz I)
  · intro x hx v hv
    exact jointAffineJetDensity_output_support s A F e input z hz rows degree hd c w hw R hsupport
      Ro hRo x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx) _
      (by simpa only [sigmaAxisCoordinates_norm] using hv)
  · have hi := (sigmaAxisCoordinates_measurePreserving I).integral_comp
      (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun v => |p.mean (fun y => jointAffineJetDensity s A F e input z rows c w
        (principalTupleNormalized L y) v) -
          densityMixture (jointBooleanSource h) (jointAffineJetDensity s A F e input z rows c w) v|)
    exact hi.trans_le hL1.2

end Erdos3

end

end OAI
