import OAI.Geometry.Perimeter.Regularity.GeometricHolderAlgebra
import OAI.Geometry.Perimeter.Regularity.GeoRegularity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}
variable {V W Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

 theorem GeoBase.linear {θ : ℝ} (hθ : 0 ≤ θ) {f : Euc n → V} {U : Set (Euc n)}
    (hU : IsOpen U) (hf : GeoBase θ f U) (L : V →L[ℝ] W) :
    GeoBase θ (fun x ↦ L (f x)) U :=
  ⟨L.continuous.comp_continuousOn hf.1,fun p hp ↦ (hf.2 p hp).comp_C1 hθ
    (hf.1.continuousAt (hU.mem_nhds hp)) L.contDiff⟩

 theorem GeoBase.prodMk {θ : ℝ} (hθ : 0 ≤ θ) {f : Euc n → V} {g : Euc n → W}
    {U : Set (Euc n)} (hf : GeoBase θ f U) (hg : GeoBase θ g U) :
    GeoBase θ (fun x ↦ (f x,g x)) U :=
  ⟨hf.1.prodMk hg.1,fun p hp ↦ (hf.2 p hp).prodMk hθ (hg.2 p hp)⟩

 theorem GeoC.linear {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} {f : Euc n → V} {U : Set (Euc n)}
    (hU : IsOpen U) (hf : GeoC θ k f U) (L : V →L[ℝ] W) :
    GeoC θ k (fun x ↦ L (f x)) U := by
  induction k generalizing f with
  | zero => exact GeoBase.linear hθ hU hf L
  | succ k ih =>
    refine ⟨L.contDiff.comp_contDiffOn hf.1,(GeoBase.linear hθ hU hf.2.1 L),fun e ↦ ?_⟩
    apply (ih (hf.2.2 e)).congr hθ hU
    intro x hx
    have hh := L.hasFDerivAt.comp x (((hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt)
    exact (congrArg (fun A : Euc n →L[ℝ] W ↦ A e) hh.fderiv).symm

 theorem GeoC.prodMk {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f : Euc n → V} {g : Euc n → W} {U : Set (Euc n)}
    (hU : IsOpen U) (hf : GeoC θ k f U) (hg : GeoC θ k g U) :
    GeoC θ k (fun x ↦ (f x,g x)) U := by
  induction k generalizing f g with
  | zero => exact GeoBase.prodMk hθ hf hg
  | succ k ih =>
    refine ⟨hf.1.prodMk hg.1,GeoBase.prodMk hθ hf.2.1 hg.2.1,fun e ↦ ?_⟩
    apply (ih (hf.2.2 e) (hg.2.2 e)).congr hθ hU
    intro x hx
    have hdf := ((hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hdg := ((hg.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (congrArg (fun A : Euc n →L[ℝ] (V×W) ↦ A e) (hdf.prodMk hdg).fderiv).symm

 theorem GeoC.add {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f g : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ k f U) (hg : GeoC θ k g U) : GeoC θ k (fun x ↦ f x+g x) U :=
  (hf.prodMk hθ hU hg).linear hθ hU (ContinuousLinearMap.fst ℝ V V+ContinuousLinearMap.snd ℝ V V)

 theorem GeoC.neg {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ k f U) : GeoC θ k (fun x ↦ -f x) U :=
  hf.linear hθ hU (-ContinuousLinearMap.id ℝ V)

 theorem GeoC.sub {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f g : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ k f U) (hg : GeoC θ k g U) : GeoC θ k (fun x ↦ f x-g x) U := by
  simpa only [sub_eq_add_neg] using hf.add hθ hU (hg.neg hθ hU)

 theorem GeoC.bilinear {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f : Euc n → V} {g : Euc n → W} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ k f U) (hg : GeoC θ k g U) (B : V →L[ℝ] W →L[ℝ] Z) :
    GeoC θ k (fun x ↦ B (f x) (g x)) U := by
  have hb : ContDiff ℝ 1 (fun z : V×W ↦ B z.1 z.2) :=
    (B.contDiff.comp contDiff_fst).clm_apply contDiff_snd
  have hbase {f : Euc n → V} {g : Euc n → W} (hf : GeoBase θ f U) (hg : GeoBase θ g U) :
      GeoBase θ (fun x ↦ B (f x) (g x)) U :=
    ⟨(B.continuous.comp_continuousOn hf.1).clm_apply hg.1,fun p hp ↦
      ((hf.2 p hp).prodMk hθ (hg.2 p hp)).comp_C1 hθ
        ((hf.1.continuousAt (hU.mem_nhds hp)).prodMk (hg.1.continuousAt (hU.mem_nhds hp))) hb⟩
  induction k generalizing f g with
  | zero => exact hbase hf hg
  | succ k ih =>
    refine ⟨(B.contDiff.comp_contDiffOn hf.1).clm_apply hg.1,hbase hf.2.1 hg.2.1,fun e ↦ ?_⟩
    have h₁ := ih hf.mono_order (hg.2.2 e)
    have h₂ := ih (hf.2.2 e) hg.mono_order
    apply (h₁.add hθ hU h₂).congr hθ hU
    intro x hx
    have hdf := ((hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hdg := ((hg.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hh := ((B.hasFDerivAt.comp x hdf).clm_apply hdg).fderiv
    exact (congrArg (fun A : Euc n →L[ℝ] Z ↦ A e) hh).symm

 theorem GeoC.clm_apply {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ}
    {f : Euc n → V →L[ℝ] W} {g : Euc n → V} {U : Set (Euc n)} (hU : IsOpen U)
    (hf : GeoC θ k f U) (hg : GeoC θ k g U) : GeoC θ k (fun x ↦ f x (g x)) U :=
  hf.bilinear hθ hU hg (ContinuousLinearMap.apply ℝ W).flip

end RPISingularHarnack

end

end OAI
