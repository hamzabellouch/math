import Mathlib
import OAI.Geometry.SmoothYau.Limits.RestrictedPinningPencil
import OAI.Geometry.SmoothYau.Spectrum.RealHSmulCommClass
import OAI.Geometry.SmoothYau.Spectrum.VaryingSpectralResolventBase

namespace OAI

noncomputable section
open Set Filter Function Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction
namespace YauCounterexamples

theorem exists_annular_simple_pinned_family
    (I : MetricIntegralAtlas (E := Euclidean 3) (M := Sphere 3))
    (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (a b c : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hc : inner ℝ c c = 1)
    (hab : inner ℝ a b = 0) (hac : inner ℝ a c = 0) (hbc : inner ℝ b c = 0)
    (n : ℕ) (hn : 2 ≤ n) {l h : ℝ} (hl : 0 < l) (hlh : l < h) (hh : h < 1)
    (u : RealSmoothFunctions (Euclidean 3) (Sphere 3))
    (hu0 : (u : Sphere 3 → ℝ) ≠ 0)
    (hue : ∀ p, -laplaceBeltrami g u p = ((n:ℝ)*((n:ℝ)+2))*u p)
    (hup : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h → u p = roundPower a b n p)
    (hgp : ∀ p : Sphere 3, l < Complex.normSq (planarLinear a b p) →
      Complex.normSq (planarLinear a b p) < h →
      ∀ (X Y : TangentSpace 𝓘(ℝ,Euclidean 3) p),
        g.inner p X Y = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p X)
          (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4)
            (fun q : Sphere 3 => (q : Euclidean 4)) p Y))
    : ∃ K : pinningTensorSpace g (u : Sphere 3 → ℝ)
      {p | l < Complex.normSq (planarLinear a b p) ∧ Complex.normSq (planarLinear a b p) < h},
      ∀ᶠ t in 𝓝[≠] (0:ℝ), ∀ v : Sphere 3 → ℝ,
        ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v →
        (∀ x, -laplaceBeltrami (pinnedMetric g K.val K.property.1 t) v x =
          ((n:ℝ)*((n:ℝ)+2))*v x) → ∃ c : ℝ, v = fun x => c*u x := by
  classical
  have hs : Module.finrank ℝ (Euclidean 3) < 2*(2*(2:ℝ)) := by norm_num [Euclidean]
  let A := (nonempty_compactMetricAtlas g 2 hs).some
  let B : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  obtain ⟨α,hα1,hα⟩ := A.exists_parametrix_threshold B
  have hα0 : 0 < α := zero_lt_one.trans_le hα1
  let lam : ℝ := (n:ℝ)*((n:ℝ)+2)
  have hla : 0 < lam := by
    dsimp [lam]
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hαl : α+lam ≠ 0 := ne_of_gt (add_pos hα0 hla)
  let μ : ℝ := (α+lam)⁻¹
  have hμ : μ ≠ 0 := inv_ne_zero hαl
  have hlam : μ⁻¹-α = lam := by dsimp [μ]; rw [inv_inv]; ring
  let T := A.realSpectralResolvent B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
  let uz := A.realOfSmooth (2*(2:ℝ)) hs u u.contMDiff
  let P := A.intrinsicPairing I (2*(2:ℝ)) hs
  let W := Module.End.eigenspace T.toLinearMap μ ⊓ (P.form uz).ker
  let : FiniteDimensional ℝ (Module.End.eigenspace T.toLinearMap μ) :=
    compact_eigenspace_finite T (A.realSpectralResolvent_compact B α hα0 (hα α le_rfl).1 (hα α le_rfl).2) hμ
  let : FiniteDimensional ℝ W := Submodule.finiteDimensional_of_le
    (show W ≤ Module.End.eigenspace T.toLinearMap μ from inf_le_left)
  have heigen (w : W) : T w = μ • (w : A.realH (2*(2:ℝ))) :=
    Module.End.mem_eigenspace_iff.mp w.property.1
  have hf (w : W) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (A.realValue (2*(2:ℝ)) w) :=
    (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).1
  let σ := A.realSmoothRepresentativeLM (2*(2:ℝ)) W hf
  have hσe (w : W) (x : Sphere 3) : -laplaceBeltrami g (σ w) x = lam*σ w x := by
    have hh := (A.realSpectralResolvent_eigenfunction B α hα0 (hα α le_rfl).1 (hα α le_rfl).2 hμ w (heigen w)).2 x
    change -laplaceBeltrami g (A.realValue (2*(2:ℝ)) w) x = lam*A.realValue (2*(2:ℝ)) w x
    convert hh using 1; simp only [hlam,Nat.cast_ofNat]
  have hp (z : A.realH (2*(2:ℝ))) : P.form uz z =
      I.mean g (fun x => u x*A.realValue (2*(2:ℝ)) z x) := by
    change I.mean g (fun x => A.realValue (2*(2:ℝ)) uz x*A.realValue (2*(2:ℝ)) z x) = _
    congr 1
    funext x
    rw [A.realOfSmooth_value]
  have hσo (w : W) : I.mean g (fun x => σ w x*u x) = 0 := by
    have hw : P.form uz w = 0 := w.property.2
    rw [hp] at hw
    convert hw using 2
    funext x
    exact mul_comm _ _
  obtain ⟨K,hK⟩ := annular_nondegenerate_pinning_tensor I g a b c ha hb hc hab hac hbc
    n hn hl hlh hh u hue hup hgp σ
    (A.realSmoothRepresentativeLM_injective (2*(2:ℝ)) hs W hf) hσe hσo
  refine ⟨K,A.actual_pinned_eventually_simple I B α hα0 (hα α le_rfl).1 (hα α le_rfl).2
    lam hαl u u.contMDiff hu0 hue K ?_⟩
  intro z hz hzo hzz
  have hzW : z ∈ W := ⟨Module.End.mem_eigenspace_iff.mpr hz,(hp z).trans hzo⟩
  let w : W := ⟨z,hzW⟩
  have hw : w = 0 := hK.1 w (fun v => by
    change I.mean g (fun x => g.inner x (metricGradient g (A.realValue (2*(2:ℝ)) z) x)
      (K.val x (metricGradient g (A.realValue (2*(2:ℝ)) v) x))) = 0
    exact hzz v (heigen v) ((hp v).symm.trans v.property.2))
  exact congrArg Subtype.val hw
end YauCounterexamples
end

end OAI
