import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRegularGluing

namespace OAI

/-! Construction of the Gauss-series continuation from the published
Voronoi identity. Nonzero local Mellin tests glue the regular part; the
actual Euler factor is then removed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

def metaplecticChosenTest (s : ℂ) : ℝ → ℂ := (exists_mellin_nonzero_test s).choose

lemma metaplecticChosenTest_spec (s : ℂ) :
    HasCompactSupport (metaplecticChosenTest s) ∧ tsupport (metaplecticChosenTest s) ⊆ Ioi 0 ∧
      ContDiff ℝ ∞ (metaplecticChosenTest s) ∧ mellin (metaplecticChosenTest s) s ≠ 0 :=
  (exists_mellin_nonzero_test s).choose_spec

def metaplecticRegularContinuation (r : Eisenstein) (s : ℂ) : ℂ :=
  metaplecticRegularNumerator r (metaplecticChosenTest s) s/mellin (metaplecticChosenTest s) s

lemma metaplecticRegularContinuation_eq_test
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hWp : tsupport W ⊆ Ioi 0)
    (hWs : ContDiff ℝ ∞ W) {s : ℂ} (hs : 0 < s.re) (hM : mellin W s ≠ 0) :
    metaplecticRegularContinuation r s = metaplecticRegularNumerator r W s/mellin W s := by
  obtain ⟨hC,hCp,hCs,hCn⟩ := metaplecticChosenTest_spec s
  apply (div_eq_div_iff hCn hM).mpr
  exact metaplecticRegularNumerator_compatible hV hr hsr (metaplecticChosenTest s) W
    hC hCp hCs hW hWp hWs hs

lemma metaplecticRegularContinuation_differentiableOn
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) :
    DifferentiableOn ℂ (metaplecticRegularContinuation r) {s : ℂ | 0 < s.re} := by
  intro s hs
  obtain ⟨hW,hWp,hWs,hMn⟩ := metaplecticChosenTest_spec s
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hN := (metaplecticRegularNumerator_differentiableOn hV hr hsr
    (metaplecticChosenTest s) hW hWp hWs).differentiableAt (hopen.mem_nhds hs)
  have hM := smooth_mellin_entire (metaplecticChosenTest s) hW hWp hWs.continuous
  have hn : ∀ᶠ z in 𝓝 s, mellin (metaplecticChosenTest s) z ≠ 0 :=
    hM.continuous.continuousAt.eventually (eventually_ne_nhds hMn)
  have he : metaplecticRegularContinuation r =ᶠ[𝓝 s]
      (fun z => metaplecticRegularNumerator r (metaplecticChosenTest s) z/
        mellin (metaplecticChosenTest s) z) := by
    filter_upwards [hopen.mem_nhds hs,hn] with z hz hzn
    exact metaplecticRegularContinuation_eq_test hV hr hsr (metaplecticChosenTest s)
      hW hWp hWs hz hzn
  exact ((hN.div (hM s) hMn).congr_of_eventuallyEq he).differentiableWithinAt

lemma metaplecticRegularContinuation_right
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {r : Eisenstein} (hr : primary r) (hsr : Squarefree r) {s : ℂ} (hs : 1 < s.re) :
    metaplecticRegularContinuation r s =
      metaplecticCompletionEuler r s*metaplecticGaussSeries r s-
        metaplecticCompletedResidue r/(s-5/6) := by
  obtain ⟨hW,hWp,hWs,hMn⟩ := metaplecticChosenTest_spec s
  rw [metaplecticRegularContinuation,metaplecticRegularNumerator_right hV hr hsr
    (metaplecticChosenTest s) hW hWp hWs hs,mul_div_cancel_left₀ _ hMn]

def metaplecticFullContinuation (r : Eisenstein) (s : ℂ) : ℂ :=
  metaplecticRegularContinuation r s+metaplecticCompletedResidue r/(s-5/6)

def metaplecticCanonicalGauss (r : Eisenstein) (s : ℂ) : ℂ :=
  metaplecticFullContinuation r s/metaplecticCompletionEuler r s

theorem metaplecticContinuation_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a) :
    MetaplecticContinuation metaplecticCanonicalGauss := by
  intro r hr hsr
  constructor
  · intro s hs
    have hE := metaplecticCompletionEuler_ne_zero (primary_ne_zero hr) (s := s) (by linarith)
    unfold metaplecticCanonicalGauss metaplecticFullContinuation
    rw [metaplecticRegularContinuation_right hV hr hsr hs,sub_add_cancel,mul_div_cancel_left₀ _ hE]
  · have hg : DifferentiableOn ℂ (metaplecticRegularContinuation r)
        {s : ℂ | (1/2:ℝ) < s.re} :=
      (metaplecticRegularContinuation_differentiableOn hV hr hsr).mono
        (fun s hs => by change (1/2:ℝ) < s.re at hs; change 0 < s.re; linarith)
    obtain ⟨g,hg,he⟩ := metaplectic_decompletion_regular (primary_ne_zero hr)
      (metaplecticRegularContinuation r) hg
    exact ⟨g,hg,he⟩

end CubicFirstMoment

end

end OAI
