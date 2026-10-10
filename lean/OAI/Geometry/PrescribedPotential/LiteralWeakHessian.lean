import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.GlobalStrongEmbedding
import OAI.Geometry.PrescribedPotential.StrongDerivatives

namespace OAI

/-! Literal Weak Hessian. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzCoordLinear (s : ℝ) : 𝓢(E,ℂ) →ₗ[ℝ] L2 E where
  toFun := schwartzCoord s
  map_add' := schwartzCoord_add s
  map_smul' c f := by
    change schwartzCoord s (c • f) = c • schwartzCoord s f
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), schwartzCoord_smul,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]

 
def literalComplexHessian (f : EC d → ℂ) (x : EC d) (i j : Fin d) : ℂ :=
  (1/4 : ℂ) * (fderiv ℝ (fderiv ℝ f) x (hessianDirection i) (hessianDirection j) +
    fderiv ℝ (fderiv ℝ f) x (hessianIDirection i) (hessianIDirection j) +
    Complex.I * (fderiv ℝ (fderiv ℝ f) x (hessianIDirection i) (hessianDirection j) -
      fderiv ℝ (fderiv ℝ f) x (hessianDirection i) (hessianIDirection j)))

lemma literalComplexHessian_schwartz (f : 𝓢(EC d,ℂ)) (x : EC d) (i j : Fin d) :
    literalComplexHessian f x i j = hessianEntrySchwartz i j f x :=
  (hessianEntrySchwartz_apply i j f x).symm

lemma literalComplexHessian_congr {f h : EC d → ℂ} {x : EC d}
    (he : f =ᶠ[𝓝 x] h) (i j : Fin d) :
    literalComplexHessian f x i j = literalComplexHessian h x i j := by
  unfold literalComplexHessian
  rw [(he.fderiv (𝕜 := ℝ)).fderiv_eq]

lemma literalComplexHessian_strong_continuous (s : ℝ)
    (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (hN : (Module.finrank ℝ (EC d) : ℝ) < 2*(s-4)) (x : EC d) (i j : Fin d) :
    Continuous (fun u : L2 (EC d) => literalComplexHessian (strongEmbedding s hs u) x i j) := by
  have h1 : (Module.finrank ℝ (EC d) : ℝ) < 2*(s-1) := by linarith
  have h2 : (Module.finrank ℝ (EC d) : ℝ) < 2*((s-1)-1) := by linarith
  simp only [literalComplexHessian, strong_second_fderiv s hs h1 h2 hN]
  fun_prop

namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

def completedLocalize (s : ℝ) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) :
    D.localizers.Sobolev s →L[ℝ] L2 (EC d) :=
  ((schwartzCoordLinear s).comp (localizeLinear A i ρ hρ)).extendOfNorm (D.localizers.embed s)

lemma completedLocalize_embed (k : ℕ) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (f : Smooth A) :
    D.completedLocalize (k : ℝ) i ρ hρ (D.localizers.embed (k : ℝ) f) =
      schwartzCoord (k : ℝ) (localize A i ρ hρ f) := by
  obtain ⟨C,_,hC⟩ := D.localization_integer_bound i ρ hρ k
  exact LinearMap.extendOfNorm_eq (D.localizers.embed_dense (k : ℝ)) ⟨C,hC⟩ f

lemma completedLocalize_plus_two_embed (k : ℕ) (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (f : Smooth A) :
    D.completedLocalize ((k : ℝ)+2) i ρ hρ (D.localizers.embed ((k : ℝ)+2) f) =
      schwartzCoord ((k : ℝ)+2) (localize A i ρ hρ f) := by
  obtain ⟨C,_,hC⟩ := D.localization_integer_bound i ρ hρ (k+2)
  rw [Nat.cast_add, Nat.cast_ofNat] at hC
  exact LinearMap.extendOfNorm_eq (D.localizers.embed_dense ((k : ℝ)+2)) ⟨C,hC⟩ f

lemma completedLocalize_strong (k : ℕ)
    (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ))
    (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source)
    (u : D.localizers.Sobolev (k : ℝ)) (y : EC d) :
    strongEmbedding (k : ℝ) hs (D.completedLocalize (k : ℝ) i ρ hρ u) y =
      if y ∈ (A.euclideanChart i).target then
        ρ ((A.euclideanChart i).symm y) * D.localizers.strong (k : ℝ) u ((A.euclideanChart i).symm y)
      else 0 := by
  have he : (fun u : D.localizers.Sobolev (k : ℝ) =>
      strongEmbedding (k : ℝ) hs (D.completedLocalize (k : ℝ) i ρ hρ u) y) =
      (fun u => if y ∈ (A.euclideanChart i).target then
        ρ ((A.euclideanChart i).symm y) * D.localizers.strong (k : ℝ) u ((A.euclideanChart i).symm y)
      else 0) := by
    apply (D.localizers.embed_dense (k : ℝ)).equalizer
    · fun_prop
    · split_ifs <;> fun_prop
    funext f
    dsimp only [Function.comp_apply]
    rw [D.completedLocalize_embed, strongEmbedding_schwartz, D.localizers.strong_embed _ hs]
    rfl
  exact congr_fun he u

lemma completedLocalize_plus_two_strong (k : ℕ)
    (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2))
    (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source)
    (u : D.localizers.Sobolev ((k : ℝ)+2)) (y : EC d) :
    strongEmbedding ((k : ℝ)+2) hs (D.completedLocalize ((k : ℝ)+2) i ρ hρ u) y =
      if y ∈ (A.euclideanChart i).target then
        ρ ((A.euclideanChart i).symm y) * D.localizers.strong ((k : ℝ)+2) u ((A.euclideanChart i).symm y)
      else 0 := by
  have he : (fun u : D.localizers.Sobolev ((k : ℝ)+2) =>
      strongEmbedding ((k : ℝ)+2) hs (D.completedLocalize ((k : ℝ)+2) i ρ hρ u) y) =
      (fun u => if y ∈ (A.euclideanChart i).target then
        ρ ((A.euclideanChart i).symm y) * D.localizers.strong ((k : ℝ)+2) u ((A.euclideanChart i).symm y)
      else 0) := by
    apply (D.localizers.embed_dense ((k : ℝ)+2)).equalizer
    · fun_prop
    · split_ifs <;> fun_prop
    funext f
    dsimp only [Function.comp_apply]
    rw [D.completedLocalize_plus_two_embed, strongEmbedding_schwartz,
      D.localizers.strong_embed _ hs]
    rfl
  exact congr_fun he u

lemma completedHessian_strong_localize (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ))
    (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2))
    (hN : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2-4))
    (u : D.localizers.Sobolev ((k : ℝ)+2)) (p : ι) (i j : Fin d)
    {x : X} (hx : x ∈ (A.euclideanChart (D.patch p).index).source) :
    D.localizers.strong (k : ℝ) (D.completedHessian k p i j u) x =
      D.cutoff p (A.euclideanChart (D.patch p).index x) *
      literalComplexHessian (strongEmbedding ((k : ℝ)+2) hs
        (D.completedLocalize ((k : ℝ)+2) (D.patch p).index
          (cutoffGlobal (D.patch p).index (D.outerCutoff p)) (cutoffGlobal_support _ _) u))
          (A.euclideanChart (D.patch p).index x) i j := by
  have he : (fun u : D.localizers.Sobolev ((k : ℝ)+2) =>
      D.localizers.strong (k : ℝ) (D.completedHessian k p i j u) x) =
      (fun u => D.cutoff p (A.euclideanChart (D.patch p).index x) *
      literalComplexHessian (strongEmbedding ((k : ℝ)+2) hs
        (D.completedLocalize ((k : ℝ)+2) (D.patch p).index
          (cutoffGlobal (D.patch p).index (D.outerCutoff p)) (cutoffGlobal_support _ _) u))
          (A.euclideanChart (D.patch p).index x) i j) := by
    apply (D.localizers.embed_dense ((k : ℝ)+2)).equalizer
    · fun_prop
    · exact continuous_const.mul ((literalComplexHessian_strong_continuous _ hs hN _ i j).comp
        (D.completedLocalize ((k : ℝ)+2) _ _ _).continuous)
    funext f
    dsimp only [Function.comp_apply]
    rw [D.completedHessian_embed, D.localizers.strong_embed _ hk,
      D.completedLocalize_plus_two_embed, strongEmbedding_schwartz]
    change globalize (D.patch p).index (D.cutoff p) _ x =
      D.cutoff p (A.euclideanChart (D.patch p).index x) *
        literalComplexHessian (localize A (D.patch p).index
          (cutoffGlobal (D.patch p).index (D.outerCutoff p)) (cutoffGlobal_support _ _) f)
          (A.euclideanChart (D.patch p).index x) i j
    rw [literalComplexHessian_schwartz, globalize_apply, ite_eq_left hx]
    rfl
  exact congr_fun he u

lemma completedHessian_literal (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ))
    (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2))
    (hN : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2-4))
    (u : D.localizers.Sobolev ((k : ℝ)+2)) (p : ι) (i j : Fin d)
    {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.localizers.strong (k : ℝ) (D.completedHessian k p i j u) x =
      literalComplexHessian ((D.localizers.strong ((k : ℝ)+2) u) ∘
        (A.euclideanChart (D.patch p).index).symm)
        (A.euclideanChart (D.patch p).index x) i j := by
  let q := (D.patch p).index
  let e := A.euclideanChart q
  have hx' : x ∈ e.source := by
    have hh := D.localizers.support_sub p hx
    rwa [D.index_eq] at hh
  have hcut := D.cutoff_one p x hx
  rw [D.completedHessian_strong_localize k hk hs hN u p i j hx', hcut, one_mul]
  apply literalComplexHessian_congr
  have ht : e x ∈ e.target := e.mapsTo hx'
  have hn : ∀ᶠ y in 𝓝 (e x), D.cutoff p y ≠ 0 :=
    (isOpen_ne_fun (D.cutoff p).val.continuous continuous_const).mem_nhds
      (by change D.cutoff p (e x) ≠ 0; rw [hcut]; exact one_ne_zero)
  filter_upwards [e.open_target.mem_nhds ht, hn] with y hy hny
  rw [D.completedLocalize_plus_two_strong, ite_eq_left hy]
  change (if e.symm y ∈ e.source then D.outerCutoff p (e (e.symm y)) else 0) *
    D.localizers.strong ((k : ℝ)+2) u (e.symm y) = _
  rw [ite_eq_left (e.mapsTo_symm hy), e.right_inv hy,
    D.outerCutoff_one p y (subset_tsupport _ hny), one_mul]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
