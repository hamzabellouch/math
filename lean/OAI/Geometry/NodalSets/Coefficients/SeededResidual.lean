import OAI.Geometry.NodalSets.Elliptic.OperatorAddition
import OAI.Geometry.NodalSets.Waves.FiniteWaveSupport

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

def realSourceResidual (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (w : Coord → ℝ)
    (lam : ℝ) (u : Coord → ℝ) (x : Coord) : ℂ :=
  sourceWeightedOperator g w (fun z ↦ (u z:ℂ)) x+(lam:ℂ)*(u x:ℂ)

lemma realSourceResidual_smoothAt {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u : Coord → ℝ) (hu : ContDiff ℝ ∞ u) {x : Coord} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (realSourceResidual g w lam u) x :=
  (sourceOperator_smoothAt hU g hg hs hp w hw hwp _ (Complex.ofRealCLM.contDiff.comp hu) hx).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.comp hu).contDiffAt)

lemma realSourceResidual_add_supported {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u t : Coord → ℝ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) :
    realSourceResidual g w lam (fun z ↦ u z+t z) =
      fun z ↦ realSourceResidual g w lam u z+realSourceResidual g w lam t z := by
  have hsub' : tsupport (fun z ↦ (t z:ℂ)) ⊆ U := by
    have he : Function.support (fun z ↦ (t z:ℂ)) = Function.support t := by
      ext z
      simp [Function.mem_support]
    simpa only [tsupport,he] using hsub
  have he := sourceOperator_add_supported hU g hg hs hp w hw hwp
    (fun z ↦ (u z:ℂ)) (fun z ↦ (t z:ℂ))
    (Complex.ofRealCLM.contDiff.comp hu) (Complex.ofRealCLM.contDiff.comp ht) hsub'
  funext x
  simp only [realSourceResidual,Complex.ofReal_add,he]
  ring

lemma derivativeBound_add_at {k : ℕ} {f g : Coord → ℂ} {x : Coord} {A B : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x)
    (ha : DerivativeBound k f x A) (hb : DerivativeBound k g x B) :
    DerivativeBound k (fun z ↦ f z+g z) x (A+B) := by
  intro j hj
  change ‖iteratedFDeriv ℝ j (f+g) x‖ ≤ A+B
  rw [iteratedFDeriv_add_apply
    (hf.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))
    (hg.of_le (by exact_mod_cast (show (j:ℕ∞) ≤ ⊤ from le_top)))]
  exact (norm_add_le _ _).trans (add_le_add (ha j hj) (hb j hj))

theorem realSourceResidual_add_bound {U : Set Coord} (hU : IsOpen U)
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiffOn ℝ ∞ g U)
    (hs : ∀ x ∈ U, ∀ u v, g x u v = g x v u)
    (hp : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < g x v v)
    (w : Coord → ℝ) (hw : ContDiffOn ℝ ∞ w U) (hwp : ∀ x ∈ U, 0 < w x)
    (lam : ℝ) (u t : Coord → ℝ) (hu : ContDiff ℝ ∞ u) (ht : ContDiff ℝ ∞ t)
    (hsub : tsupport t ⊆ U) {x : Coord} (hx : x ∈ U) (k : ℕ) (B C : ℝ)
    (hb : DerivativeBound k (realSourceResidual g w lam u) x B)
    (hc : DerivativeBound k (realSourceResidual g w lam t) x C) :
    DerivativeBound k (realSourceResidual g w lam (fun z ↦ u z+t z)) x (B+C) := by
  rw [realSourceResidual_add_supported hU g hg hs hp w hw hwp lam u t hu ht hsub]
  exact derivativeBound_add_at (realSourceResidual_smoothAt hU g hg hs hp w hw hwp lam u hu hx)
    (realSourceResidual_smoothAt hU g hg hs hp w hw hwp lam t ht hx) hb hc

end
end Yau.Geometry

end OAI
