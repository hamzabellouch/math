import OAI.Analysis.RCDHeat.Foundations

namespace OAI

/-!
# Regularity and convergence of rescalings

The compactness input is kept separate from regularity. In particular,
regularity is never used as an assertion that a tangent already exists.
Once subsequential pointed compactness is available, all rescaling
sequences at a regular point converge to Euclidean space.
-/

open Filter
open scoped Topology

namespace RegularPointCoordinates

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
  [MetricSpace X] [MetricSpace Y] [MetricSpace Z]

/-- Pointed metric approximations are preserved by a target isometry. -/
theorem IsPointedApproximation.postcomp_isometry
    {p : X} {q : Y} {r R epsilon : ℝ} {f : X → Y}
    (hf : IsPointedApproximation p q r R epsilon f) (e : Y ≃ᵢ Z) :
    IsPointedApproximation p (e q) r R epsilon (fun x => e (f x)) := by
  refine ⟨by simpa only [e.dist_eq] using hf.1, ?_, ?_⟩
  · intro x z hx hz
    simpa only [e.dist_eq] using hf.2.1 x z hx hz
  · intro y hy
    have hy' : dist (e.symm y) q ≤ R - epsilon := by
      simpa only [← e.dist_eq, e.apply_symm_apply] using hy
    obtain ⟨x, hx, hxy⟩ := hf.2.2 (e.symm y) hy'
    refine ⟨x, hx, ?_⟩
    simpa only [← e.dist_eq, e.apply_symm_apply] using hxy

theorem RescalingsConverge.postcomp_isometry {p : X} {q : Y} {r : ℕ → ℝ}
    (h : RescalingsConverge p q r) (e : Y ≃ᵢ Z) :
    RescalingsConverge p (e q) r := by
  intro R hR epsilon hepsilon
  filter_upwards [h R hR epsilon hepsilon] with i hi
  obtain ⟨f, hf⟩ := hi
  exact ⟨fun x => e (f x), hf.postcomp_isometry e⟩

/-- Rescalings at a point admit a pointed-convergent subsequence with a proper
metric-space limit. -/
def PointedRescalingPrecompactness (p : X) : Prop :=
  ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      ∃ (Y : Type u) (dY : MetricSpace Y),
        letI := dY
        ∃ (_ : ProperSpace Y) (q : Y), RescalingsConverge p q (r ∘ phi)

/-- The all-tangents definition of regularity and pointed compactness
imply convergence along every prescribed sequence of scales. -/
theorem regular_rescalings_converge {n : ℕ} {p : X}
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrzero : Tendsto r atTop (𝓝 0)) :
    RescalingsConverge p (0 : Euclidean n) r := by
  intro R hR epsilon hepsilon
  by_contra hnot
  have hbad : ∃ᶠ i in atTop,
      ¬ ∃ f : X → Euclidean n, IsPointedApproximation p 0 (r i) R epsilon f :=
    Filter.not_eventually.mp hnot
  obtain ⟨phi, hphi, hbadphi⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨psi, hpsi, Y, dY, hproper, q, hlimit⟩ :=
    hcompact (r ∘ phi) (fun i => hr (phi i)) (hrzero.comp hphi.tendsto_atTop)
  let : MetricSpace Y := dY
  let : ProperSpace Y := hproper
  have htangent : IsTangent p q := by
    refine ⟨(r ∘ phi) ∘ psi, fun i => hr (phi (psi i)), ?_, hlimit⟩
    exact (hrzero.comp hphi.tendsto_atTop).comp hpsi.tendsto_atTop
  obtain ⟨e, he⟩ := hregular Y dY hproper q htangent
  have heuc := hlimit.postcomp_isometry e
  rw [he] at heuc
  obtain ⟨i, f, hf⟩ := (heuc R hR epsilon hepsilon).exists
  exact hbadphi (psi i) ⟨f, hf⟩

/-- Compactness also proves existence of a Euclidean tangent; this is
not silently built into the universal definition of regularity. -/
theorem regular_has_euclidean_tangent {n : ℕ} {p : X}
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p) :
    IsTangent p (0 : Euclidean n) := by
  let r : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1)
  have hr (i : ℕ) : 0 < r i := by dsimp [r]; positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨r, hr, hrzero, regular_rescalings_converge hcompact hregular r hr hrzero⟩

/-- The sequential statement gives a uniform approximation threshold
for every fixed radius and tolerance, not merely a chosen blow-up sequence. -/
theorem regular_small_scale_approximation {n : ℕ} {p : X}
    (hcompact : PointedRescalingPrecompactness p) (hregular : IsRegular n p)
    {R epsilon : ℝ} (hR : 0 < R) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r : ℝ, 0 < r → r < delta →
      ∃ f : X → Euclidean n, IsPointedApproximation p 0 r R epsilon f := by
  by_contra hnot
  push Not at hnot
  have hchoice (i : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      ∀ f : X → Euclidean n, ¬IsPointedApproximation p 0 r R epsilon f :=
    hnot (1 / ((i : ℝ) + 1)) (by positivity)
  choose r hrpos hrsmall hrbad using hchoice
  have hrzero : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i => (hrpos i).le) (fun i => (hrsmall i).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := regular_rescalings_converge hcompact hregular r hrpos hrzero
  obtain ⟨i, f, hf⟩ := (hconv R hR epsilon hepsilon).exists
  exact hrbad i f hf

end RegularPointCoordinates

end OAI
