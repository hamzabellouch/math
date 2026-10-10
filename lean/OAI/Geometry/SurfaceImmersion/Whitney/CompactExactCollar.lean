import OAI.Geometry.SurfaceImmersion.Whitney.ExactRegularCollar

namespace OAI

/-! Stationary longitudinal ends turn exact collar interpolation into
an actual compactly supported replacement. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem compact_exact_collar {f g : Base → W} {V : ℝ × ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hV : ContDiff ℝ ∞ V)
    (hc : ∀ t, f (crosscapAxis t) = g (crosscapAxis t))
    (hV0 : ∀ t, V (0,t) = axisTransverse f t)
    (hV1 : ∀ t, V (1,t) = axisTransverse g t)
    {a b R : ℝ} (hR : 0 < R)
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet (axisValue f) V s t 0 0))
    (hstation : ∀ x : Base, x 1 ∉ Ioo a b → g x = f x ∧
      ∀ s ∈ Icc (0:ℝ) 1, V (s,x 1) = axisTransverse f (x 1)) :
    ∃ (r : ℝ) (F : Base → W) (K : Set Base),
      0 < r ∧ r < R ∧ ContDiff ℝ ∞ F ∧ IsCompact K ∧
      K ⊆ {x | |x 0| ≤ r/2 ∧ x 1 ∈ Icc a b} ∧
      (∀ x ∉ K, F =ᶠ[𝓝 x] f) ∧
      (∀ u : ℝ, |u| < r → ∀ t ∈ Icc a b,
        Function.Injective (fderiv ℝ F ![u,t])) ∧
      ∀ t, F =ᶠ[𝓝 (crosscapAxis t)] g := by
  obtain ⟨r,F,hr,hrR,hF,hFI,hinner,hstationF,houter⟩ :=
    exact_regular_collar hf hg hV hc hV0 hV1 hR hI
  let K : Set Base := Icc (![(-r/2),a] : Base) ![r/2,b]
  have hK : IsCompact K := isCompact_Icc
  have hKs : K ⊆ {x | |x 0| ≤ r/2 ∧ x 1 ∈ Icc a b} := by
    intro x hx
    exact ⟨abs_le.mpr ⟨by simpa only [Matrix.cons_val_zero,neg_div] using hx.1 0,
      by simpa only [Matrix.cons_val_zero] using hx.2 0⟩,
      by simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using hx.1 1,
      by simpa only [Matrix.cons_val_one,Matrix.cons_val_zero] using hx.2 1⟩
  have hsupp : tsupport (F-f) ⊆ K := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have hneq : F x ≠ f x := by simpa only [Function.mem_support,Pi.sub_apply,sub_ne_zero] using hx
    have ht : x 1 ∈ Ioo a b := by
      by_contra ht
      exact hneq (hstationF x (hstation x ht).1 (hstation x ht).2)
    have hu : |x 0| ≤ r/2 := le_of_not_gt fun hu => hneq (houter x hu).self_of_nhds
    constructor
    · intro i
      fin_cases i
      · change -r/2 ≤ x 0
        simpa only [neg_div] using (abs_le.mp hu).1
      · change a ≤ x 1
        exact ht.1.le
    · intro i
      fin_cases i
      · change x 0 ≤ r/2
        exact (abs_le.mp hu).2
      · change x 1 ≤ b
        exact ht.2.le
  refine ⟨r,F,K,hr,hrR,hF,hK,hKs,?_,hFI,hinner⟩
  intro x hx
  have he := notMem_tsupport_iff_eventuallyEq.mp (fun hm => hx (hsupp hm))
  filter_upwards [he] with y hy
  exact sub_eq_zero.mp hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
