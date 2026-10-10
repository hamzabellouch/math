import OAI.Geometry.Perimeter.Regularity.MinimalGraphEquation
import OAI.Geometry.Perimeter.Regularity.MinimalGraphSmooth
import OAI.Geometry.Perimeter.Regularity.BlowupHolderGraph

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff InnerProductSpace
namespace RPISingularHarnack

def HasSmoothPerimeterSheetAt {n : ℕ} (E : Set (Euc n)) (p : Euc n) : Prop :=
  ∃ U : Set (Euc n), IsOpen U ∧ p ∈ U ∧
    ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
      (∀ x ∈ U, x ∈ perimeterSupport E ↔ f x = 0) ∧
      (∀ x ∈ U, f x = 0 → fderiv ℝ f x ≠ 0)

def FlatBlowupRegularityObligation : Prop :=
  ∀ (n : ℕ), 1 < n → ∀ (E : Set (Euc n)),
    IsLocallyPerimeterMinimizing E →
    ∀ (p v : Euc n), p ∈ perimeterSupport E → HasHalfspaceBlowup E p v →
      HasSmoothPerimeterSheetAt E p

theorem HasSmoothPerimeterSheetAt.of_blownUpSet {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {p : Euc n} {r : ℝ} (hr : 0<r)
    (h : HasSmoothPerimeterSheetAt (blownUpSet E p r) 0) :
    HasSmoothPerimeterSheetAt E p := by
  obtain ⟨U,hU,h0,f,hf,hiff,hnz⟩ := h
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
  have hAp : A p=0 := by simp [A]
  have hback (x : Euc n) : p+r•A x=x := by
    simp only [A,smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
    abel
  refine ⟨A ⁻¹' U,hU.preimage hA.continuous,by simpa only [mem_preimage,hAp] using h0,
    f ∘ A,hf.comp hA.contDiffOn (fun _ hx ↦ hx),?_,?_⟩
  · intro x hx
    rw [← hback x,← perimeterSupport_blownUpSet hE p hr (A x)]
    simpa only [hback,Function.comp_apply] using hiff (A x) hx
  · intro x hx hz hzero
    have hfd : DifferentiableAt ℝ f (A x) :=
      (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hder : fderiv ℝ (f ∘ A) x=(fderiv ℝ f (A x)).comp L :=
      (hfd.hasFDerivAt.comp x (hAd x)).fderiv
    apply hnz (A x) hx hz
    ext w
    have hh := congrArg (fun T : Euc n →L[ℝ] ℝ ↦ T (r•w)) hzero
    rw [hder] at hh
    simpa [ContinuousLinearMap.comp_apply,L,smul_smul,hr.ne'] using hh

theorem smooth_perimeter_sheet_of_halfspace_blowup
    {n : ℕ} (hn : 1<n) {E : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E) {p v : Euc n}
    (hp : p∈perimeterSupport E) (hbl : HasHalfspaceBlowup E p v) :
    HasSmoothPerimeterSheetAt E p := by
  obtain ⟨η,hη,_,hgraphs⟩ := hbl.exists_holder_graphs hn hmin hp
  obtain ⟨ε,hε,hsmooth⟩ := normal_graph_smooth_threshold hn hbl.1 hη
  obtain ⟨r,hr,f,_,hf,_,_,hiff,⟨a,ha,ha4,hs⟩,hh,hslope⟩ := hgraphs ε hε
  have heq : ∀ ψ : normalPlane v → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 (1/4) →
      (∫ y, inner ℝ (gradient f y) (gradient ψ y)/Real.sqrt (1+‖gradient f y‖^2))=0 := by
    intro ψ hψ hcψ hsψ
    exact full_graph_weak_minimal_equation hn (locally_minimizing_blownUpSet hmin p hr)
      hbl.1 ha.le ha4 hs hf hiff hψ hcψ hsψ
  have hfSmooth := hsmooth f hf hh hslope heq
  apply HasSmoothPerimeterSheetAt.of_blownUpSet hmin.1 hr
  refine ⟨graphCylinder v,graphCylinder_open v,?_,graphDefining v f,
    graphDefining_contDiffOn hfSmooth,?_,?_⟩
  · simp [graphCylinder]
  · exact fun x hx ↦ graphDefining_support_iff hbl.1 hiff hx
  · exact fun x hx _ ↦ graphDefining_fderiv_ne_zero hbl.1 hf hx

theorem flatBlowupRegularity : FlatBlowupRegularityObligation :=
  fun _ hn _ hmin _ _ hp hbl ↦ smooth_perimeter_sheet_of_halfspace_blowup hn hmin hp hbl

end RPISingularHarnack

end

end OAI
