import Mathlib
import OAI.Analysis.BiholderTransport.Contact.CoordinateSupportGradient

namespace OAI


noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.exists_center_ray_of_minimizer (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ)
    {y z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v y)) (hl : 0<l) (hl1 : l<1)
    (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun a=>φ (v a)) z=φ (v y)+cost y z/τ) :
    ∃ r : TangentSpace 𝓘(ℝ,Model n) y,
      τ • r∈injectivityDomain y ∧ riemannianExp y (τ • r)=z ∧
      l⁻¹ • r∈minimizingVectors y ∧
      contactGap v u y (riemannianExp y (l⁻¹ • r))=0 ∧ r∈injectivityDomain y := by
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) y z
  let r := τ⁻¹ • q
  have hsub : r∈normalSubdifferential (fun a=>φ (v a)) y := by
    apply global_min_divided_cost_subgradient hq hτ
    intro a
    rw [hqz,←hval]
    exact hopfLax_le (hφc.comp hv.continuous) τ z a
  have H := hmtw.subgradient_dual_contact hv.continuous hu ⟨hdual.2,hdual.1⟩
    (scalar_normalSubdifferential_inv hv hφ hl hsub)
  have hr : r∈injectivityDomain y := by
    have HR := contracted_minimizer_mem_injectivityDomain H.1 hl hl1
    simpa only [smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using HR
  refine ⟨r,contracted_minimizer_mem_injectivityDomain
    (injectivityDomain_subset_minimizingVectors y hr) hτ hτ1,?_,H.1,H.2,hr⟩
  simpa only [r,smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using hqz

lemma WeakMTW.exists_center_coordinate_support (hmtw : WeakMTW (n := n) (M := M))
    {u v : M → ℝ} (hu : Continuous u) {L : ℝ≥0} (hv : LipschitzWith L v)
    (hdual : IsCostDualPair u v) {φ : ℝ → ℝ} (hφc : Continuous φ) (hmono : Monotone φ)
    {a : M} {b : Model n} (hb : b∈(extChartAt 𝓘(ℝ,Model n) a).target)
    {z : M} {l τ : ℝ} (hφ : HasDerivAt φ l (v ((extChartAt 𝓘(ℝ,Model n) a).symm b)))
    (hl : 0<l) (hl1 : l<1) (hτ : 0<τ) (hτ1 : τ<1)
    (hval : hopfLax τ (fun y=>φ (v y)) z=φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm b))+
      cost ((extChartAt 𝓘(ℝ,Model n) a).symm b) z/τ) :
    ∃ p : Model n,
      let y := (extChartAt 𝓘(ℝ,Model n) a).symm b
      let A := (trivializationAt (Model n) (TangentSpace 𝓘(ℝ,Model n)) a).symmL ℝ y
      let ψ := fun w=>coordinateScalarSupport a φ (((v y,(1+l)/2),(b,p)),w)
      A p∈minimizingVectors y ∧ contactGap v u y (movingNormal a (b,p))=0 ∧
      l • A p∈injectivityDomain y ∧ riemannianExp y ((τ*l) • A p)=z ∧
      (∀ w,ψ w≤φ (v ((extChartAt 𝓘(ℝ,Model n) a).symm w))) ∧
      ψ b=φ (v y) ∧ shortForward a ψ (τ,b)=extChartAt 𝓘(ℝ,Model n) a z := by
  obtain ⟨r,hr,hrz,hpm,hpc,hrreg⟩ :=
    hmtw.exists_center_ray_of_minimizer hu hv hdual hφc hφ hl hl1 hτ hτ1 hval
  have hmin : IsLocalMin (fun y=>φ (v y)+cost y
      (riemannianExp ((extChartAt 𝓘(ℝ,Model n) a).symm b) (τ • r))/τ)
      ((extChartAt 𝓘(ℝ,Model n) a).symm b) := by
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hrz,←hval]
    exact hopfLax_le (hφc.comp hv.continuous) τ z y
  obtain ⟨p,hs,hs1,hp,hpm,hpc,hbelow,htouch,hZ⟩ :=
    hmtw.exists_actual_center_support hu hv hdual hmono hb hφ hl hl1 hτ.ne' hr hmin
  refine ⟨p,?_,hpc,?_,?_,hbelow,htouch,?_⟩
  · rwa [hp]
  · simpa only [hp,smul_smul,mul_inv_cancel₀ hl.ne',one_smul] using hrreg
  · rw [hp,smul_smul,show τ*l*l⁻¹=τ by field_simp]
    exact hrz
  · rwa [hrz] at hZ

end WeakMTWTransport

end

end OAI
