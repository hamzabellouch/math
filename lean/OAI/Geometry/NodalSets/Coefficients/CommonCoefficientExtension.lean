import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import OAI.Geometry.NodalSets.Elliptic.LocalSpatialJet

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
variable {P E F T : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace T]

def cutoffCoefficient (beta : E → ℝ) (f : P → E → F) (p : P) (x : E) : F :=
  beta x • f p x

lemma cutoffCoefficient_smooth_at (beta : E → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (f : P → E → F) (p : P) (x : E)
    (hf : x ∈ tsupport beta → ContDiffAt ℝ ∞ (Function.uncurry f) (p,x)) :
    ContDiffAt ℝ ∞ (Function.uncurry (cutoffCoefficient beta f)) (p,x) := by
  by_cases hx : x ∈ tsupport beta
  · exact (hbeta.contDiffAt.comp (p,x) contDiffAt_snd).smul (hf hx)
  · apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
    have hn : (tsupport beta)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
    have hpair : ∀ᶠ z : P × E in 𝓝 (p,x), z.2 ∈ (tsupport beta)ᶜ :=
      continuousAt_snd.tendsto.eventually hn
    filter_upwards [hpair] with z hz
    simp [Function.uncurry_def, cutoffCoefficient, image_eq_zero_of_notMem_tsupport hz]

theorem common_cutoff_coefficient_family (beta : E → ℝ) (hbeta : ContDiff ℝ ∞ beta)
    (f : P → E → F) (p : T → P) (hp : Continuous p)
    (hf : ∀ t x, x ∈ tsupport beta → ContDiffAt ℝ ∞ (Function.uncurry f) (p t,x)) :
    (∀ t, ContDiff ℝ ∞ (cutoffCoefficient beta f (p t))) ∧
    ∀ k, Continuous (fun z : T × E ↦
      iteratedFDeriv ℝ k (cutoffCoefficient beta f (p z.1)) z.2) := by
  constructor
  · intro t
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (cutoffCoefficient_smooth_at beta hbeta f (p t) x (hf t x)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  · intro k
    apply continuous_iff_continuousAt.mpr
    rintro ⟨t,x⟩
    exact ContinuousAt.comp (x := (t,x))
      (g := fun z : P × E ↦ iteratedFDeriv ℝ k (cutoffCoefficient beta f z.1) z.2)
      (f := fun z : T × E ↦ (p z.1,z.2))
      (smooth_spatial_iteratedFDeriv_at (cutoffCoefficient beta f) (p t) x
        (cutoffCoefficient_smooth_at beta hbeta f (p t) x (hf t x)) k).continuousAt
      ((hp.comp continuous_fst).prodMk continuous_snd).continuousAt

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ E] in
lemma cutoffCoefficient_germ (beta : E → ℝ) (f : P → E → F) (p : P) (x : E)
    (hbeta : beta =ᶠ[𝓝 x] fun _ ↦ 1) : cutoffCoefficient beta f p =ᶠ[𝓝 x] f p := by
  filter_upwards [hbeta] with z hz
  simp [cutoffCoefficient, hz]

end
end Yau.Geometry

end OAI
