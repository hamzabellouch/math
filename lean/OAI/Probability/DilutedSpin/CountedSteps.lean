import OAI.Probability.DilutedSpin.CountedSizeCoupling
import OAI.Probability.DilutedSpin.CountedSpinMean
import OAI.Probability.DilutedSpin.PoissonRateCoupling
import OAI.Probability.DilutedSpin.RegularDepth

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} {A : I → Type} {L n : ℕ}

/-- Vary only the selected type, not the entire countable reservoir. -/
noncomputable def selectedFactor (sel : I → Bool)
    (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (i : I) (x : FinitePath Ω L) (y : FinitePath (A i) L) : ℝ :=
  if sel i then 1+t*D i x y+u*E i x y else fixed i x y

noncomputable def otherLog (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) :
    FinitePath (Ω × Row (A := A) roots) L → ℝ :=
  logWeight base roots (fun i x y => if sel i then 1 else fixed i x y)

noncomputable def selectedCoefficient (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) : ℝ :=
  if sel (roots q) then D (roots q) (physical roots L y) (mark q L y) else 0

theorem selectedCoefficient_bound (roots : Fin n → I) (sel : I → Bool)
    (D : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (q : Fin n) (y : FinitePath (Ω × Row (A := A) roots) L) :
    |selectedCoefficient roots sel D q y| ≤ 1 := by
  unfold selectedCoefficient
  split
  · exact hD _ _ _
  · norm_num

/-- Every unselected term remains in the same log weight and the same finite
mark prior. This is an identity, not a distributional truncation. -/
theorem selected_perturbLog_eq (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.perturbLog (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      logWeight base roots (selectedFactor sel fixed D E t u) := by
  funext y
  unfold KernelTower.perturbLog otherLog logWeight
  rw [add_assoc,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  cases h : sel (roots q) <;> simp [selectedFactor,selectedCoefficient,h]

variable [Fintype Ω] [∀ i, Fintype (A i)]

noncomputable def selectedScore (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) : ℝ :=
  (KernelTower.law L (KernelTower.tilt L (tower roots L T Q) m
    (logWeight base roots (selectedFactor sel fixed D E t u)))).expect
      (KernelTower.perturbScore (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u)

theorem corrected_log_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbLog (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      root T Q m base roots (selectedFactor sel fixed D E t u)+2*n*u^2 := by
  rw [KernelTower.correctedPerturbLog,selected_perturbLog_eq]
  rfl

theorem corrected_score_eq (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) :
    KernelTower.correctedPerturbScore (tower roots L T Q) m (otherLog base roots sel fixed)
      (selectedCoefficient roots sel D) (selectedCoefficient roots sel E) t u =
      selectedScore T Q m base roots sel fixed D E t u+4*n*u := by
  rw [KernelTower.correctedPerturbScore,selected_perturbLog_eq]
  rfl

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.SizeCoupling
open MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
  [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {A : I → Type} [∀ i, Fintype (A i)]

noncomputable def fieldMean (ξ : Measure Y) {p r N k l : ℕ} [NeZero N]
    {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ) : ℝ :=
  ∫ h : RootPath Y N, spinMean Q m theta (fun i => field (rootArray N h i)) ψ
      ∂rootLaw N (fun _ => ξ)

lemma fieldMean_bound (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |fieldMean (N := N) ξ theta field Q m ψ| ≤ H*N+C*k+D*l :=
  abs_integral_le_const _ (fun root => spinMean_bound Q m hm theta _ ψ hθ
    (fun index => hh (rootArray N root index)) hψ)

lemma measurable_fieldMean {Z : Type} [MeasurableSpace Z] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Z → Fin k → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ j σ, Measurable (fun z => (theta z j).1 σ)) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ) :
    Measurable (fun z => fieldMean (N := N) ξ (theta z) field Q m ψ) := by
  exact (measurable_spinMean Q m (fun z : Z × RootPath Y N => theta z.1)
    (fun z i => field (rootArray N z.2 i)) ψ
    (fun j σ => (hθm j σ).comp measurable_fst)
    (fun i => hhm.comp ((measurable_rootArray N i).comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable

lemma integrable_spinMean (ξ : Measure Y) [IsProbabilityMeasure ξ]
    {p r N k l : ℕ} [NeZero N] {B : Fin l → Type} [∀ i, Fintype (B i)]
    (theta : Fin k → InteractionSample p) (field : Y → ℝ) (hhm : Measurable field)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    Integrable (fun h : RootPath Y N => spinMean Q m theta
      (fun i => field (rootArray N h i)) ψ) (rootLaw N (fun _ => ξ)) := by
  apply Integrable.of_bound (measurable_spinMean Q m (fun _ => theta) _ ψ
    (fun _ _ => measurable_const) (fun i => hhm.comp (measurable_rootArray N i))).aestronglyMeasurable
    (H*N+C*k+D*l)
  filter_upwards [] with h
  simpa only [Real.norm_eq_abs,Function.comp_def] using
    spinMean_bound Q m hm theta (fun i => field (rootArray N h i)) ψ hθ (fun i => hh _) hψ

/-- Count insertion of the original independent physical interaction sample. -/
theorem countedMean_interaction_step (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ (k+1) l-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ C := by
  let F := fun (k : ℕ) (a : RootPath I l) (x : RootPath X k) =>
    fieldMean (N := N) ξ (fun j => theta (rootArray k x j)) field
      (fun j => Q (rootArray l a j)) m (fun j => ψ (rootArray l a j))
  have hFm (k : ℕ) (a : RootPath I l) : Measurable (F k a) :=
    measurable_fieldMean ξ _ field (fun j σ => (hθm σ).comp (measurable_rootArray k j)) hhm _ m _
  have hFb (k : ℕ) (a : RootPath I l) (x : RootPath X k) : |F k a x| ≤ H*N+C*k+D*l :=
    fieldMean_bound ξ _ field _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b)
  have hFi (k : ℕ) (a : RootPath I l) : Integrable (F k a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm k a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb k a x))
  have hOi (k : ℕ) : Integrable (fun a => ∫ x, F k a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb k a)))
  change |(∫ a, ∫ x, F (k+1) a x ∂rootLaw (k+1) (fun _ => μ) ∂rootLaw l (fun _ => ν))-
    (∫ a, ∫ x, F k a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν))| ≤ C
  apply abs_integral_sub_le_const _ (hOi (k+1)) (hOi k)
  intro a
  have hg : Integrable (fun x : X × RootPath X k => F k a x.2)
      (μ.prod (rootLaw k (fun _ => μ))) := (hFi k a).comp_snd μ
  have he : (∫ x : X × RootPath X k, F k a x.2 ∂μ.prod (rootLaw k (fun _ => μ))) =
      ∫ x, F k a x ∂rootLaw k (fun _ => μ) := by
    rw [integral_prod _ hg]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ x, F (k+1) a x ∂μ.prod (rootLaw k (fun _ => μ)))-_| ≤ C
  rw [← he]
  apply abs_integral_sub_le_const (μ.prod (rootLaw k (fun _ => μ))) (hFi (k+1) a) hg
  intro x
  apply abs_integral_sub_le_const _
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
  intro h
  exact spinMean_interaction_step _ m hm _ _ _ (hθ x.1)

/-- Count insertion draws the original countable dictionary type; its entire
finite mark alphabet and all level priors are kept. -/
theorem countedMean_mark_step (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k (l+1)-
      countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ D := by
  let F := fun (l : ℕ) (a : RootPath I l) (x : RootPath X k) =>
    fieldMean (N := N) ξ (fun j => theta (rootArray k x j)) field
      (fun j => Q (rootArray l a j)) m (fun j => ψ (rootArray l a j))
  have hFm (l : ℕ) (a : RootPath I l) : Measurable (F l a) :=
    measurable_fieldMean ξ _ field (fun j σ => (hθm σ).comp (measurable_rootArray k j)) hhm _ m _
  have hFb (l : ℕ) (a : RootPath I l) (x : RootPath X k) : |F l a x| ≤ H*N+C*k+D*l :=
    fieldMean_bound ξ _ field _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b)
  have hFi (l : ℕ) (a : RootPath I l) : Integrable (F l a) (rootLaw k (fun _ => μ)) :=
    Integrable.of_bound (hFm l a).aestronglyMeasurable _
      (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hFb l a x))
  have hOi (l : ℕ) : Integrable (fun a => ∫ x, F l a x ∂rootLaw k (fun _ => μ))
      (rootLaw l (fun _ => ν)) := Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
    (H*N+C*k+D*l) (ae_of_all _ (fun a => by
      simpa only [Real.norm_eq_abs] using abs_integral_le_const _ (hFb l a)))
  have hg := (hOi l).comp_snd ν
  have he : (∫ a : I × RootPath I l, (∫ x, F l a.2 x ∂rootLaw k (fun _ => μ))
      ∂ν.prod (rootLaw l (fun _ => ν))) =
      ∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν) := by
    rw [integral_prod _ hg]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  change |(∫ a, ∫ x, F (l+1) a x ∂rootLaw k (fun _ => μ) ∂ν.prod (rootLaw l (fun _ => ν)))-
    (∫ a, ∫ x, F l a x ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν))| ≤ D
  rw [← he]
  apply abs_integral_sub_le_const (ν.prod (rootLaw l (fun _ => ν))) (hOi (l+1)) hg
  intro a
  apply abs_integral_sub_le_const _ (hFi (l+1) a) (hFi l a.2)
  intro x
  apply abs_integral_sub_le_const _
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
    (integrable_spinMean ξ _ field hhm _ m hm _ (fun j σ => hθ _ σ) hh (fun j σ b => hψ _ σ b))
  intro h
  exact spinMean_mark_step _ m hm _ _ _ (hψ a.1)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal

lemma poisson_abs_mean_le (r : ℝ≥0) {f : ℕ → ℝ} {A B : ℝ}
    (h : ∀ n, |f n| ≤ A+B*n) : |∫ n, f n ∂poissonMeasure r| ≤ A+B*r := by
  have hi := poisson_integrable_linear r h
  have hg : Integrable (fun n : ℕ => A+B*n) (poissonMeasure r) :=
    (integrable_const A).add ((poisson_integrable_count r).const_mul B)
  calc
    _ ≤ ∫ n, |f n| ∂poissonMeasure r := abs_integral_le_integral_abs
    _ ≤ ∫ n : ℕ, A+B*n ∂poissonMeasure r := integral_mono hi.abs hg h
    _ = _ := by rw [integral_add (integrable_const A) ((poisson_integrable_count r).const_mul B),
        integral_const_mul,poisson_mean]; simp

noncomputable def twoPoissonMean (r s : ℝ≥0) (f : ℕ → ℕ → ℝ) : ℝ :=
  ∫ k, ∫ l, f k l ∂poissonMeasure s ∂poissonMeasure r

lemma twoPoisson_inner_integrable (r s : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D : ℝ}
    (h : ∀ k l, |f k l| ≤ A+B*k+D*l) :
    Integrable (fun k => ∫ l, f k l ∂poissonMeasure s) (poissonMeasure r) := by
  apply poisson_integrable_linear r (A := A+D*s) (B := B)
  intro k
  have ht := poisson_abs_mean_le s (h k)
  linarith

lemma twoPoisson_abs_mean_le (r s : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D : ℝ}
    (h : ∀ k l, |f k l| ≤ A+B*k+D*l) :
    |twoPoissonMean r s f| ≤ A+B*r+D*s := by
  have ht := poisson_abs_mean_le r (A := A+D*s) (B := B) (f := fun k => ∫ l, f k l ∂poissonMeasure s)
    (fun k => by have := poisson_abs_mean_le s (h k); linarith)
  dsimp [twoPoissonMean]
  linarith

lemma twoPoissonMean_sub (r s : ℝ≥0) {f g : ℕ → ℕ → ℝ} {A B D A' B' D' : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hg : ∀ k l, |g k l| ≤ A'+B'*k+D'*l) :
    twoPoissonMean r s f-twoPoissonMean r s g = twoPoissonMean r s (fun k l => f k l-g k l) := by
  unfold twoPoissonMean
  rw [← integral_sub (twoPoisson_inner_integrable r s hf) (twoPoisson_inner_integrable r s hg)]
  apply integral_congr_ae
  exact ae_of_all _ (fun k => (integral_sub (poisson_integrable_linear s (hf k))
    (poisson_integrable_linear s (hg k))).symm)

lemma twoPoisson_abs_sub_le (r s : ℝ≥0) {f g : ℕ → ℕ → ℝ}
    {A B D A' B' D' E F G : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hg : ∀ k l, |g k l| ≤ A'+B'*k+D'*l)
    (h : ∀ k l, |f k l-g k l| ≤ E+F*k+G*l) :
    |twoPoissonMean r s f-twoPoissonMean r s g| ≤ E+F*r+G*s := by
  rw [twoPoissonMean_sub r s hf hg]
  exact twoPoisson_abs_mean_le r s h

lemma twoPoissonMean_rate_add_left (r s t : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D C : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hC : 0 ≤ C)
    (hs : ∀ k l, |f (k+1) l-f k l| ≤ C) :
    |twoPoissonMean (r+t) s f-twoPoissonMean r s f| ≤ C*t := by
  apply poisson_average_rate_add r t hC
  intro k
  exact SizeCoupling.abs_integral_sub_le_const _ (poisson_integrable_linear s (hf (k+1)))
    (poisson_integrable_linear s (hf k)) (hs k)

lemma twoPoissonMean_rate_add_right (r s t : ℝ≥0) {f : ℕ → ℕ → ℝ} {A B D C : ℝ}
    (hf : ∀ k l, |f k l| ≤ A+B*k+D*l) (hC : 0 ≤ C)
    (hs : ∀ k l, |f k (l+1)-f k l| ≤ C) :
    |twoPoissonMean r (s+t) f-twoPoissonMean r s f| ≤ C*t := by
  apply SizeCoupling.abs_integral_sub_le_const _ (twoPoisson_inner_integrable r (s+t) hf)
    (twoPoisson_inner_integrable r s hf)
  intro k
  exact poisson_average_rate_add s t hC (hs k)

end DilutedSpinGlass
end

end

end OAI
