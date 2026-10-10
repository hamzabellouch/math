import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalHessian
import OAI.Geometry.PrescribedPotential.GlobalMetricEntries
import OAI.Geometry.PrescribedPotential.MatrixPositivity
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.RealSobolev

namespace OAI

/-! Weak Positive. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance weakPositiveNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance weakPositiveNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance weakPositiveTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance weakPositiveCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def weakMatrix (k : ℕ) (u : D.localizers.RealSobolev ((k : ℝ)+2)) (p : ι) (x : X) :
    Matrix (Fin d) (Fin d) ℂ := fun i j => D.metricEntry p i j x +
      D.localizers.strong (k : ℝ) (D.completedHessian k p i j u.val) x

lemma weakMatrix_continuous (k : ℕ) (p : ι) :
    Continuous (fun z : D.localizers.RealSobolev ((k : ℝ)+2) × X => D.weakMatrix k z.1 p z.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply ((D.metricEntry p i j).continuous.comp continuous_snd).add
  have hc : Continuous (fun z : D.localizers.RealSobolev ((k : ℝ)+2) × X =>
      D.localizers.strong (k : ℝ) (D.completedHessian k p i j z.1.val)) :=
    (D.localizers.strong (k : ℝ)).continuous.comp ((D.completedHessian k p i j).continuous.comp
      (continuous_subtype_val.comp continuous_fst))
  exact hc.eval continuous_snd

lemma weakMatrix_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (f : RealSmooth A)
    (p : ι) {x : X} (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.weakMatrix k (D.localizers.realEmbed ((k : ℝ)+2) f) p x =
      g.matrix (D.patch p).index (A.chart (D.patch p).index x) +
        f.source.hessian (D.patch p).index (A.chart (D.patch p).index x) := by
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*(k : ℝ) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  ext i j
  change D.metricEntry p i j x + D.localizers.strong (k : ℝ)
    (D.completedHessian k p i j (D.localizers.embed ((k : ℝ)+2) f.val)) x = _
  rw [D.completedHessian_embed, D.localizers.strong_embed _ hs]
  change D.metricEntry p i j x + D.localizedHessian p i j f.val x = _
  rw [D.metricEntry_apply p i j hx, ← f.ofReal_source, D.localizedHessian_source p i j f.source hx]
  rfl

lemma weakMatrix_hermitian (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) (p : ι) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) : (D.weakMatrix k u p x).IsHermitian := by
  have hc : Continuous (fun v : D.localizers.RealSobolev ((k : ℝ)+2) => D.weakMatrix k v p x) :=
    (D.weakMatrix_continuous k p).comp (continuous_id.prodMk continuous_const)
  have he : (fun v : D.localizers.RealSobolev ((k : ℝ)+2) => (D.weakMatrix k v p x)ᴴ) =
      (fun v => D.weakMatrix k v p x) := by
    apply (D.localizers.realEmbed_dense ((k : ℝ)+2)).equalizer hc.matrix_conjTranspose hc
    funext f
    dsimp only [Function.comp_apply]
    rw [D.weakMatrix_embed k hk f p hx]
    have hs : A.chart (D.patch p).index x ∈ (A.chart (D.patch p).index).target :=
      (A.chart (D.patch p).index).mapsTo (by simpa using D.patch_source p hx)
    exact (g.positive _ _ hs).isHermitian.add (f.source.hessian_hermitian _ hs)
  exact congr_fun he u

lemma weakMatrix_zero (k : ℕ) (p : ι) {x : X}
    (hx : x ∈ tsupport (D.localizers.weight p : X → ℂ)) :
    D.weakMatrix k 0 p x = g.matrix (D.patch p).index (A.chart (D.patch p).index x) := by
  ext i j
  change D.metricEntry p i j x + D.localizers.strong (k : ℝ) (D.completedHessian k p i j 0) x = _
  rw [map_zero, map_zero]
  exact (add_zero _).trans (D.metricEntry_apply p i j hx)

def WeakPositive (k : ℕ) (u : D.localizers.RealSobolev ((k : ℝ)+2)) : Prop :=
  ∀ p x, x ∈ tsupport (D.localizers.weight p : X → ℂ) → (D.weakMatrix k u p x).PosDef

lemma weakPositive_nhds (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev ((k : ℝ)+2)), D.WeakPositive k u := by
  apply Filter.eventually_all.mpr
  intro p
  apply CompactMatrixPositivity.eventually_posDef (isClosed_tsupport _).isCompact
    (D.weakMatrix_continuous k p)
  · intro u x hx
    exact D.weakMatrix_hermitian k hk u p hx
  · intro x hx
    rw [D.weakMatrix_zero k p hx]
    exact g.positive _ _ ((A.chart (D.patch p).index).mapsTo (by simpa using D.patch_source p hx))

end GluingData
end GlobalElliptic

end
end

end OAI
