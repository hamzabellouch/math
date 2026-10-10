import OAI.Probability.DilutedSpin.CountedSpinMean

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

lemma abs_integral_sub_le_const {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] {f g : Z → ℝ} {B : ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ z, |f z-g z| ≤ B) :
    |(∫ z, f z ∂μ)-(∫ z, g z ∂μ)| ≤ B := by
  rw [← integral_sub hf hg]
  exact abs_integral_le_const μ h

/-- The independent additional field is integrated under its original law.
The per-count cost is uniform in every auxiliary mark prior and parameter. -/
theorem fieldMean_size_coupling (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (field : Y → ℝ) (hfm : Measurable field)
    (theta : Fin k → InteractionSample p)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |(∫ h : RootPath Y (N+1), spinMean Q m theta (fun i => field (rootArray (N+1) h i)) ψ
        ∂rootLaw (N+1) (fun _ => ξ))-
      (∫ h : RootPath Y N, spinMean Q m theta (fun i => field (rootArray N h i)) ψ
        ∂rootLaw N (fun _ => ξ))| ≤
      H+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let P := rootLaw N (fun _ => ξ)
  let f := fun h : Y × RootPath Y N => spinMean Q m theta
    (fun i => field (rootArray (N+1) h i)) ψ
  let g := fun h : Y × RootPath Y N => spinMean Q m theta
    (fun i => field (rootArray N h.2 i)) ψ
  have hfm' : Measurable f := measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hfm.comp (measurable_rootArray (N+1) i))
  have hgm' : Measurable g := measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hfm.comp ((measurable_rootArray N i).comp measurable_snd))
  have hf : Integrable f (ξ.prod P) := Integrable.of_bound hfm'.aestronglyMeasurable
    (H*(N+1)+C*k+D*l) (ae_of_all _ (fun h => by
      simpa only [Real.norm_eq_abs,Nat.cast_add,Nat.cast_one] using
        spinMean_bound Q m hm theta (fun i => field (rootArray (N+1) h i)) ψ hθ (fun i => hh _) hψ))
  have hg : Integrable g (ξ.prod P) := Integrable.of_bound hgm'.aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun h => by
      simpa only [Real.norm_eq_abs] using spinMean_bound Q m hm theta (fun i => field (rootArray N h.2 i)) ψ hθ (fun i => hh _) hψ))
  have he : (∫ h, g h ∂ξ.prod P) = ∫ h : RootPath Y N,
      spinMean Q m theta (fun i => field (rootArray N h i)) ψ ∂P := by
    rw [integral_prod _ hg]
    simp only [g,integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ h, f h ∂ξ.prod P)-_| ≤ _
  rw [← he]
  apply abs_integral_sub_le_const _ hf hg
  intro h
  have ha := spinMean_size_coupling Q m hm theta
    (fun i => field (rootArray (N+1) h i)) ψ hC hD hθ hψ
  have hh0 : |field (rootArray (N+1) h 0)| ≤ H := hh _
  exact ha.trans (by linarith)

/-- Uniform finite-size comparison for the same quenched countable dictionary
and the same counts. All three root measures are the actual independent laws. -/
theorem countedMean_size_coupling (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N+1) μ ξ ν theta field Q m ψ k l-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤
      H+2*C*k*p/(N+1)+2*D*l/(N+1) := by
  let F := fun (n : ℕ) [NeZero n] (a : RootPath I l) (x : RootPath X k) =>
    ∫ h : RootPath Y n, spinMean (fun j => Q (rootArray l a j)) m
      (fun j => theta (rootArray k x j)) (fun i => field (rootArray n h i))
      (fun j => ψ (rootArray l a j)) ∂rootLaw n (fun _ => ξ)
  have hFm (n : ℕ) [NeZero n] (a : RootPath I l) : Measurable (F n a) :=
    (measurable_countedIntegrand (N := n) theta field hθm hhm Q m ψ k l a).stronglyMeasurable.integral_prod_right'.measurable
  have hFb (n : ℕ) [NeZero n] (a : RootPath I l) (x : RootPath X k) :
      |F n a x| ≤ H*n+C*k+D*l := abs_integral_le_const _ (fun h =>
    spinMean_bound _ m hm _ _ _ (fun j σ => hθ _ σ) (fun i => hh _) (fun j σ a => hψ _ σ a))
  have hFi (n : ℕ) [NeZero n] (a : RootPath I l) : Integrable (F n a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm n a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb n a x))
  have hOi (n : ℕ) [NeZero n] : Integrable (fun a => ∫ x, F n a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*n+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb n a)))
  apply abs_integral_sub_le_const _ (hOi (N+1)) (hOi N)
  intro a
  apply abs_integral_sub_le_const _ (hFi (N+1) a) (hFi N a)
  intro x
  exact fieldMean_size_coupling ξ field hhm _ _ m hm _ hC hD
    (fun j σ => hθ _ σ) hh (fun j σ a => hψ _ σ a)

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
