import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm
import OAI.Geometry.Immersion.ClosedSurface.SupportedCancellation
import OAI.Geometry.Immersion.ClosedSurface.ModeDifferences
import OAI.Geometry.Immersion.ClosedSurface.ModeScaling

namespace OAI

/-! The geometric finite differential parametrix as a linear map on actual
compactly supported smooth fields. -/
noncomputable section
open TopologicalSpace Set
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial WeightedEstimates

variable {n : ℕ} {G : Field n} {U : Set Base}

lemma tsupport_conjugatedD (τ : ℝ) (G Z : Field n) :
    tsupport (conjugatedD τ G Z) ⊆ tsupport Z := by
  apply closure_minimal _ (isClosed_tsupport Z)
  intro p hp
  by_contra hn
  have hz : Z =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
  exact hp (by rw [conjugatedD_congr τ G hz]; exact congrFun (conjugatedD_zero τ G) p)

def conjugatedDLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (K : Compacts Base) :
    SupportedField (F := Ambient n) K →ₗ[ℂ] SupportedField (F := Fin 3 → ℂ) K where
  toFun Z := ContDiffMapSupportedIn.of_support_subset
    (contDiff_iff_contDiffAt.mpr (fun _ => contDiffAt_conjugatedD τ hG.contDiffAt Z.contDiff.contDiffAt))
    (subset_closure.trans ((tsupport_conjugatedD τ G Z).trans Z.tsupport_subset))
  map_add' Z W := by
    apply DFunLike.ext
    intro p
    change conjugatedD τ G (fun q => Z q + W q) p =
      conjugatedD τ G Z p + conjugatedD τ G W p
    have hh := conjugatedD_sub τ G ((Z.contDiff.add W.contDiff).differentiable (by simp) p)
      (W.contDiff.differentiable (by simp) p)
    have he : (fun q => (Z q + W q) - W q) = (Z : Field n) := by
      funext q
      exact add_sub_cancel_right _ _
    rw [he] at hh
    exact sub_eq_iff_eq_add.mp hh.symm
  map_smul' c Z := by
    apply DFunLike.ext
    intro p
    exact conjugatedD_smul τ c G (Z.contDiff.differentiable (by simp) p)

lemma conjugatedDLM_apply (τ : ℝ) (hG : ContDiff ℝ ∞ G) (K : Compacts Base)
    (Z : SupportedField (F := Ambient n) K) (p : Base) :
    conjugatedDLM τ hG K Z p = conjugatedD τ G Z p := rfl

/-- All correction depths preserve the same compact support. -/
def forcedMode (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (q : ℕ) (f : SupportedField (F := Fin 3 → ℂ) K) :
    SupportedField (F := Ambient n) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_of_tsupport_subset h.isOpen
      ((forcedMode_tsupport τ G f q).trans (f.tsupport_subset.trans hKU))
      (contDiffOn_modeApprox τ h contDiffOn_const f.contDiff.contDiffOn q))
    (subset_closure.trans ((forcedMode_tsupport τ G f q).trans f.tsupport_subset))

lemma forcedMode_apply (τ : ℝ) (h : ModeDomain G U) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (q : ℕ) (f : SupportedField (F := Fin 3 → ℂ) K) (p : Base) :
    forcedMode τ h K hKU q f p = modeApprox τ G (fun _ => 0) f q p := rfl

lemma forcedMode_sub (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (q : ℕ)
    (f g : SupportedField (F := Fin 3 → ℂ) K) :
    forcedMode τ h K hKU q (f - g) =
      forcedMode τ h K hKU q f - forcedMode τ h K hKU q g := by
  apply DFunLike.ext
  intro p
  by_cases hp : p ∈ U
  · have hh := modeApprox_sub τ hG h (V := fun _ => 0) (W := fun _ => 0)
      contDiffOn_const contDiffOn_const f.contDiff.contDiffOn g.contDiff.contDiffOn q hp
    change modeApprox τ G (fun _ => 0) (fun p => f p - g p) q p =
      modeApprox τ G (fun _ => 0) f q p - modeApprox τ G (fun _ => 0) g q p
    simpa only [sub_self] using hh
  · have hk : p ∉ (K : Set Base) := fun hmem => hp (hKU hmem)
    change forcedMode τ h K hKU q (f - g) p =
      forcedMode τ h K hKU q f p - forcedMode τ h K hKU q g p
    rw [(forcedMode τ h K hKU q (f - g)).zero_on_compl hk,
      (forcedMode τ h K hKU q f).zero_on_compl hk,
      (forcedMode τ h K hKU q g).zero_on_compl hk]
    exact (sub_self _).symm

def forcedModeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (q : ℕ) :
    SupportedField (F := Fin 3 → ℂ) K →ₗ[ℂ] SupportedField (F := Ambient n) K where
  toFun := forcedMode τ h K hKU q
  map_add' f g := by
    have hh := forcedMode_sub τ hG h K hKU q (f + g) g
    rw [add_sub_cancel_right] at hh
    exact sub_eq_iff_eq_add.mp hh.symm
  map_smul' c f := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_smul τ c hG h (V := fun _ => 0)
        contDiffOn_const f.contDiff.contDiffOn q hp
      change modeApprox τ G (fun _ => 0) (fun p => c • f p) q p =
        c • modeApprox τ G (fun _ => 0) f q p
      simpa only [smul_zero] using hh
    · have hk : p ∉ (K : Set Base) := fun hmem => hp (hKU hmem)
      change forcedMode τ h K hKU q (c • f) p = c • forcedMode τ h K hKU q f p
      rw [(forcedMode τ h K hKU q (c • f)).zero_on_compl hk,
        (forcedMode τ h K hKU q f).zero_on_compl hk]
      simp only [Pi.zero_apply, smul_zero]

lemma forcedModeLM_apply (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) (q : ℕ)
    (f : SupportedField (F := Fin 3 → ℂ) K) (p : Base) :
    forcedModeLM τ hG h K hKU q f p = modeApprox τ G (fun _ => 0) f q p := rfl

end ClosedSurfaceR4.SmallModes

end

end OAI
