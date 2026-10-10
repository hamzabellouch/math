import OAI.Geometry.Perimeter.Regularity.MinimalGraphEquation
import OAI.Geometry.Perimeter.Regularity.MinimalGraphSmooth
import OAI.Geometry.Perimeter.Regularity.BlowupHolderGraph

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

theorem phaseSupport_blownUpSet {n : ℕ} (E : Set (Euc n))
    (c : Euc n) {r : ℝ} (hr : 0 < r) (x : Euc n) :
    x ∈ (volume.restrict (blownUpSet E c r)).support ↔
      c + r • x ∈ (volume.restrict E).support := by
  let e := blowupHomeomorph c hr
  have hd (S : Set (Euc n)) :
      volume (blownUpSet S c r) = ENNReal.ofReal ((r ^ n)⁻¹) * volume S := by
    change volume ((fun y : Euc n ↦ r • y) ⁻¹' ((fun y ↦ c + y) ⁻¹' S)) = _
    rw [Measure.addHaar_preimage_smul volume hr.ne', measure_preimage_add]
    simp [finrank_euclideanSpace, abs_of_pos (inv_pos.mpr (pow_pos hr n))]
  have hp (S : Set (Euc n)) :
      0 < volume (blownUpSet S c r) ↔ 0 < volume S := by
    rw [hd, ENNReal.mul_pos_iff]
    simp [ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr n))]
  simp only [Measure.support_eq_forall_isOpen, Set.mem_ofPred_eq]
  constructor
  · intro hx U hUx hU
    rw [Measure.restrict_apply hU.measurableSet]
    apply (hp (U ∩ E)).mp
    have hOU : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
    have h := hx (e ⁻¹' U) hUx hOU
    rw [Measure.restrict_apply hOU.measurableSet] at h
    exact h
  · intro hx U hUx hU
    rw [Measure.restrict_apply hU.measurableSet]
    have hOU := e.isOpenMap U hU
    have h := hx (e '' U) ⟨x,hUx,rfl⟩ hOU
    rw [Measure.restrict_apply hOU.measurableSet] at h
    have h' := (hp (e '' U ∩ E)).mpr h
    change 0 < volume (e ⁻¹' (e '' U ∩ E)) at h'
    change 0 < volume (U ∩ e ⁻¹' E)
    simpa only [preimage_inter, e.injective.preimage_image] using h'

theorem flat_halfspace_blowup_regular_neighborhood {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {p v : Euc n} (hp : p ∈ perimeterSupport E) (hbl : HasHalfspaceBlowup E p v) :
    ∃ U : Set (Euc n), IsOpen U ∧ p ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) ∧
        (∀ y ∈ U, (f y < 0 → y ∈ (volume.restrict E).support) ∧
          (y ∈ (volume.restrict E).support → f y ≤ 0)) := by
  obtain ⟨η,hη,_,hgraphs⟩ := hbl.exists_holder_graphs hn hmin hp
  obtain ⟨ε,hε,hsmooth⟩ := normal_graph_smooth_threshold hn hbl.1 hη
  obtain ⟨r,hr,g,_,hg,_,_,hiff,⟨a,ha,ha4,hs⟩,hh,hslope⟩ := hgraphs ε hε
  have heq : ∀ ψ : normalPlane v → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 (1/4) →
      (∫ y, inner ℝ (gradient g y) (gradient ψ y) / Real.sqrt (1+‖gradient g y‖^2)) = 0 := by
    intro ψ hψ hcψ hsψ
    exact full_graph_weak_minimal_equation hn (locally_minimizing_blownUpSet hmin p hr)
      hbl.1 ha.le ha4 hs hg hiff hψ hcψ hsψ
  have hgSmooth := hsmooth g hg hh hslope heq
  let A : Euc n → Euc n := fun x ↦ r⁻¹ • (x-p)
  let L : Euc n →L[ℝ] Euc n := r⁻¹ • ContinuousLinearMap.id ℝ (Euc n)
  have hA : ContDiff ℝ ∞ A := by
    dsimp [A]
    exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
  have hAd (x : Euc n) : HasFDerivAt A L x := by
    change HasFDerivAt (fun y : Euc n ↦ r⁻¹ • (y-p))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Euc n)) x
    convert ((hasFDerivAt_id x).sub_const p).const_smul r⁻¹ using 1
    rfl
  have hAp : A p = 0 := by simp [A]
  have hback (x : Euc n) : p + r • A x = x := by
    simp only [A, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  have hG := graphDefining_contDiffOn hgSmooth
  refine ⟨A ⁻¹' graphCylinder v, (graphCylinder_open v).preimage hA.continuous,
    ?_, graphDefining v g ∘ A, hG.comp hA.contDiffOn (fun _ hx ↦ hx), ?_, ?_, ?_⟩
  · simp [hAp, graphCylinder]
  · intro x hx hzero
    have hfd : DifferentiableAt ℝ (graphDefining v g) (A x) :=
      (hG.contDiffAt ((graphCylinder_open v).mem_nhds hx)).differentiableAt (by simp)
    have hder : fderiv ℝ (graphDefining v g ∘ A) x =
        (fderiv ℝ (graphDefining v g) (A x)).comp L :=
      (hfd.hasFDerivAt.comp x (hAd x)).fderiv
    apply graphDefining_fderiv_ne_zero hbl.1 hg hx
    ext w
    have hz := congrArg (fun T : Euc n →L[ℝ] ℝ ↦ T (r • w)) hzero
    rw [hder] at hz
    simpa [ContinuousLinearMap.comp_apply, L, smul_smul, hr.ne'] using hz
  · intro x hx
    rw [← hback x, ← perimeterSupport_blownUpSet hmin.1 p hr (A x)]
    simpa only [hback, Function.comp_apply] using graphDefining_support_iff hbl.1 hiff hx
  · intro x hx
    have hphase : x ∈ (volume.restrict E).support ↔ graphDefining v g (A x) ≤ 0 := by
      have hb : A x ∈ (volume.restrict (blownUpSet E p r)).support ↔
          x ∈ (volume.restrict E).support := by
        simpa only [hback] using phaseSupport_blownUpSet E p hr (A x)
      exact hb.symm.trans (graphDefining_phaseSupport_iff hn
        (locally_minimizing_blownUpSet hmin p hr) hbl.1 ha.le ha4 hs hiff hx)
    exact ⟨fun h ↦ hphase.mpr h.le, hphase.mp⟩

end RPISingularHarnack

end

end OAI
