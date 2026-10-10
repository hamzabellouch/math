import OAI.Geometry.Perimeter.Regularity.GeoAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

 theorem GeoC.const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (θ : ℝ) (k : ℕ) (c : V) (U : Set (Euc n)) : GeoC θ k (fun _ ↦ c) U := by
  induction k generalizing c with
  | zero => exact ⟨continuousOn_const,fun p _ ↦ GeometricHolderAt.const θ p c⟩
  | succ k ih =>
    refine ⟨contDiffOn_const,⟨continuousOn_const,fun p _ ↦ GeometricHolderAt.const θ p c⟩,fun e ↦ ?_⟩
    simpa only [fderiv_const_apply,zero_apply] using ih (0:V)

 theorem GeoC.clm_of_apply {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} {U : Set (Euc n)} (hU : IsOpen U)
    {f : Euc n → V →L[ℝ] W} (hf : ∀ e, GeoC θ k (fun x ↦ f x e) U) :
    GeoC θ k f U := by
  have hbase {f : Euc n → V →L[ℝ] W} (hf : ∀ e, GeoC θ 0 (fun x ↦ f x e) U) :
      GeoC θ 0 f U := by
    have hc : ContinuousOn f U := continuousOn_clm_apply.mpr (fun e ↦ (hf e).1)
    exact ⟨hc,fun p hp ↦ (GeometricHolderAt.clm_apply_iff hθ
      (hc.continuousAt (hU.mem_nhds hp))).mpr (fun e ↦ (hf e).2 p hp)⟩
  induction k generalizing f with
  | zero => exact hbase hf
  | succ k ih =>
    have hc : ContDiffOn ℝ 1 f U := contDiffOn_clm_apply.mpr (fun e ↦ (hf e).1)
    refine ⟨hc,hbase (fun e ↦ (hf e).2.1),fun e ↦ ih (fun v ↦ ?_)⟩
    apply ((hf v).2.2 e).congr hθ hU
    intro x hx
    have hd := ((hc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun L : Euc n →L[ℝ] W ↦ L e)
      (((ContinuousLinearMap.apply ℝ W v).hasFDerivAt.comp x hd).fderiv)

 theorem GeoC.fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} {U : Set (Euc n)} (hU : IsOpen U)
    {f : Euc n → V} (hf : GeoC θ (k+1) f U) : GeoC θ k (fderiv ℝ f) U :=
  GeoC.clm_of_apply hθ hU hf.2.2

 theorem GeoC.gradient {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} {U : Set (Euc n)} (hU : IsOpen U)
    {f : Euc n → ℝ} (hf : GeoC θ (k+1) f U) : GeoC θ k (gradient f) U :=
  (hf.fderiv hθ hU).linear hθ hU (InnerProductSpace.toDual ℝ (Euc n)).symm.toContinuousLinearMap

 theorem geoC_comp (k : ℕ) : ∀ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {θ : ℝ}, 0 ≤ θ →
    ∀ {U : Set (Euc n)}, IsOpen U → ∀ {f : Euc n → V}, GeoC θ k f U →
    ∀ {G : V → W}, ContDiff ℝ ∞ G → GeoC θ k (fun x ↦ G (f x)) U := by
  induction k with
  | zero =>
    intro V W _ _ _ _ θ hθ U hU f hf G hG
    exact ⟨hG.continuous.comp_continuousOn hf.1,fun p hp ↦ (hf.2 p hp).comp_C1 hθ
      (hf.1.continuousAt (hU.mem_nhds hp)) (hG.of_le (by simp))⟩
  | succ k ih =>
    intro V W _ _ _ _ θ hθ U hU f hf G hG
    have hcf : ContDiffOn ℝ 1 f U := hf.1
    have hcG : ContDiff ℝ 1 G := hG.of_le (by simp)
    have hDG : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
    have hb : GeoC θ 0 (fun x ↦ G (f x)) U :=
      ⟨hG.continuous.comp_continuousOn hf.2.1.1,fun p hp ↦ (hf.2.1.2 p hp).comp_C1 hθ
        (hcf.continuousOn.continuousAt (hU.mem_nhds hp)) hcG⟩
    refine ⟨hcG.comp_contDiffOn hcf,hb,fun e ↦ ?_⟩
    have h₁ := ih hθ hU hf.mono_order hDG
    have hh := h₁.clm_apply hθ hU (hf.2.2 e)
    apply hh.congr hθ hU
    intro x hx
    have hd := ((hcf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (congrArg (fun L : Euc n →L[ℝ] W ↦ L e)
      (((hcG.differentiable (by simp) (f x)).hasFDerivAt.comp x hd).fderiv)).symm

end RPISingularHarnack

end

end OAI
