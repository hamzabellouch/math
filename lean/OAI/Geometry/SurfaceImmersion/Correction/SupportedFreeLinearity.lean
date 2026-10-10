import OAI.Geometry.SurfaceImmersion.Correction.PerturbedFreeModeSize
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteParametrixLinearity

namespace OAI

/-! The free seed and its finite perturbed correction are actual linear maps. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff

namespace ClosedSurfaceR4.SmallModes
open JetPolynomial
variable {n : ℕ} {G : Field n} {U : Set Base}

def initialFreeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U) :
    SupportedField (F := Ambient n) K →ₗ[ℂ] SupportedField (F := Ambient n) K where
  toFun V := initialMode τ h K hKU V 0
  map_add' V W := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_sub τ hG h (V.contDiff.add W.contDiff).contDiffOn W.contDiff.contDiffOn
        (f := fun _ => 0) (g := fun _ => 0) contDiffOn_const contDiffOn_const 0 hp
      change initialAmplitude τ G (fun x => V x + W x) (fun _ => 0) p =
        initialAmplitude τ G V (fun _ => 0) p + initialAmplitude τ G W (fun _ => 0) p
      simp only [modeApprox, add_sub_cancel_right, sub_self] at hh
      exact sub_eq_iff_eq_add.mp hh.symm
    · have hk : p ∉ (K : Set Base) := fun hk => hp (hKU hk)
      change initialMode τ h K hKU (V + W) 0 p =
        initialMode τ h K hKU V 0 p + initialMode τ h K hKU W 0 p
      rw [(initialMode τ h K hKU (V + W) 0).zero_on_compl hk,
        (initialMode τ h K hKU V 0).zero_on_compl hk,
        (initialMode τ h K hKU W 0).zero_on_compl hk]
      simp only [Pi.zero_apply, zero_add]
  map_smul' c V := by
    apply DFunLike.ext
    intro p
    by_cases hp : p ∈ U
    · have hh := modeApprox_smul τ c hG h V.contDiff.contDiffOn
        (f := fun _ => 0) contDiffOn_const 0 hp
      change initialAmplitude τ G (fun x => c • V x) (fun _ => 0) p =
        c • initialAmplitude τ G V (fun _ => 0) p
      simpa only [modeApprox, smul_zero] using hh
    · have hk : p ∉ (K : Set Base) := fun hk => hp (hKU hk)
      change initialMode τ h K hKU (c • V) 0 p = c • initialMode τ h K hKU V 0 p
      rw [(initialMode τ h K hKU (c • V) 0).zero_on_compl hk,
        (initialMode τ h K hKU V 0).zero_on_compl hk]
      simp only [Pi.zero_apply, smul_zero]

def perturbedFreeLM (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K :=
  (FiniteParametrix.homogeneousLM ((conjugatedDLM τ hG K).restrictScalars ℝ + R)
    ((forcedModeLM τ hG h K hKU 0).restrictScalars ℝ) q).comp
    ((initialFreeLM τ hG h K hKU).restrictScalars ℝ)

lemma perturbedFreeLM_apply (τ : ℝ) (hG : ContDiff ℝ ∞ G) (h : ModeDomain G U)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (R : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Fin 3 → ℂ) K)
    (q : ℕ) (V : SupportedField (F := Ambient n) K) :
    perturbedFreeLM τ hG h K hKU R q V = perturbedFreeMode τ hG h K hKU R V q := by
  exact FiniteParametrix.homogeneousLM_apply _ _ q _

end ClosedSurfaceR4.SmallModes

end

end OAI
