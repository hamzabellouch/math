import Mathlib
import OAI.Geometry.PrescribedPotential.RealSmoothOperator
import OAI.Geometry.PrescribedPotential.PointPoisson

namespace OAI

/-! Real Poisson. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma pointPoissonOrder_realCore (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X) (f : RealSmooth A) :
    ∃ (u : RealSmooth A) (c : ℝ),
      D.pointPoissonOrder m hm he P k x₀ (D.localizers.embed (k : ℝ) f.val) =
        D.localizers.embed ((k : ℝ)+2) u.val ∧
      D.poissonResidue m hm he P (D.localizers.embed 0 f.val) = (c : ℂ) := by
  obtain ⟨u,c,hu,heq⟩ := exists_real_smooth_poisson g x₀ f
  refine ⟨u,c,?_⟩
  apply D.pointPoissonOrder_unique m hm he k hk x₀
  · rw [D.pointPoissonOrder_equation, D.localizers.lower_embed (Nat.cast_nonneg k),
      D.completedLOrder_embed, heq, map_add]
    change (_ + D.localizers.constantsOrder (k : ℝ) _) - _ = (_ + D.localizers.constantsOrder (k : ℝ) _) - _
    abel
  · rw [D.pointPoissonOrder_normalized m hm he P k hk,
      D.pointEvaluation_embed hk, hu]

def realLOrder (k : ℕ) :
    D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ] D.localizers.RealSobolev (k : ℝ) :=
  ((D.completedLOrder k).comp (D.localizers.realCompletion ((k : ℝ)+2)).subtypeL).codRestrict
    (D.localizers.realCompletion (k : ℝ)) (fun u =>
      D.localizers.maps_realCompletion (D.completedLOrder k) (fun f =>
        ⟨RealSmooth.laplace g f, D.completedLOrder_embed k f.val⟩) u.val u.property)

def realConstants (s : ℝ) : ℝ →L[ℝ] D.localizers.RealSobolev s :=
  ((D.localizers.constantsOrder s).comp Complex.ofRealCLM).codRestrict
    (D.localizers.realCompletion s) (fun c => (D.localizers.realEmbed s (RealSmooth.const c)).property)

def realEvaluation (s : ℝ) (x₀ : X) : D.localizers.RealSobolev s →L[ℝ] ℝ :=
  Complex.reCLM ∘L D.pointEvaluation s x₀ ∘L (D.localizers.realCompletion s).subtypeL

def realPointPoisson (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X) :
    D.localizers.RealSobolev (k : ℝ) →L[ℝ] D.localizers.RealSobolev ((k : ℝ)+2) :=
  ((D.pointPoissonOrder m hm he P k x₀).comp (D.localizers.realCompletion (k : ℝ)).subtypeL).codRestrict
    (D.localizers.realCompletion ((k : ℝ)+2)) (fun u =>
      D.localizers.maps_realCompletion (D.pointPoissonOrder m hm he P k x₀) (fun f => by
        obtain ⟨v,c,hv,_⟩ := D.pointPoissonOrder_realCore m hm he P k hk x₀ f
        exact ⟨v,hv⟩) u.val u.property)

lemma residue_real (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (u : D.localizers.RealSobolev (k : ℝ)) :
    (D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 u.val)).im = 0 := by
  have hh : (fun u : D.localizers.RealSobolev (k : ℝ) =>
      (D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 u.val)).im) = (fun _ => 0) := by
    apply (D.localizers.realEmbed_dense (k : ℝ)).equalizer (by fun_prop) continuous_const
    funext f
    dsimp only [Function.comp_apply]
    rw [D.localizers.realEmbed_val, D.localizers.lower_embed (Nat.cast_nonneg k)]
    obtain ⟨v,c,_,hc⟩ := D.pointPoissonOrder_realCore m hm he P k hk x₀ f
    rw [hc, Complex.ofReal_im]
  exact congr_fun hh u

def realResidue (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ) : D.localizers.RealSobolev (k : ℝ) →L[ℝ] ℝ :=
  Complex.reCLM ∘L D.poissonResidue m hm he P ∘L D.localizers.lower (k : ℝ) 0 ∘L
    (D.localizers.realCompletion (k : ℝ)).subtypeL

lemma realPointPoisson_equation (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (f : D.localizers.RealSobolev (k : ℝ)) :
    D.realLOrder k (D.realPointPoisson m hm he P k hk x₀ f) =
      f + D.realConstants (k : ℝ) (D.realResidue m hm he P k f) := by
  apply Subtype.ext
  change D.completedLOrder k (D.pointPoissonOrder m hm he P k x₀ f.val) =
    f.val + D.localizers.constantsOrder (k : ℝ)
      ((D.poissonResidue m hm he P (D.localizers.lower (k : ℝ) 0 f.val)).re : ℂ)
  rw [D.pointPoissonOrder_equation]
  congr 2
  exact Complex.ext rfl (D.residue_real m hm he P k hk x₀ f)

lemma realPointPoisson_normalized (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2)) (x₀ : X)
    (f : D.localizers.RealSobolev (k : ℝ)) :
    D.realEvaluation ((k : ℝ)+2) x₀ (D.realPointPoisson m hm he P k hk x₀ f) = 0 := by
  change (D.pointEvaluation ((k : ℝ)+2) x₀
    (D.pointPoissonOrder m hm he P k x₀ f.val)).re = 0
  rw [D.pointPoissonOrder_normalized m hm he P k hk]
  rfl

omit [ConnectedSpace X] in
lemma realLOrder_constants (k : ℕ) (c : ℝ) :
    D.realLOrder k (D.realConstants ((k : ℝ)+2) c) = 0 :=
  Subtype.ext (D.completedLOrder_constants k (c : ℂ))

omit [ConnectedSpace X] in
lemma realEvaluation_constants {s : ℝ} (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (x₀ : X) (c : ℝ) : D.realEvaluation s x₀ (D.realConstants s c) = c := by
  change (D.pointEvaluation s x₀ (D.localizers.embed s (Smooth.const (c : ℂ)))).re = c
  rw [D.pointEvaluation_embed hs]
  rfl

end GluingData
end GlobalElliptic

end
end

end OAI
