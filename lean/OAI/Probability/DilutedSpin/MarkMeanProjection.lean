import OAI.Probability.DilutedSpin.InsertionPoissonAlgebra
import OAI.Probability.DilutedSpin.MarkSiteCoupling
import OAI.Probability.DilutedSpin.PerturbedEnergyMean
import OAI.Probability.DilutedSpin.RootProductLaw

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower PhysicalRoot
open scoped BigOperators NNReal
variable {I : Type} [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N J k L : ℕ}

noncomputable def locatedTerminalRoot
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    (a : RootPath (I×Fin J) k) : ℝ :=
  terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform (fun i : I×Fin J => Q i.1)
    m E (rootArray k a) (fun i σ b => ψ i.1 (σ (site i.2)) b)

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_bound
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (a : RootPath (I×Fin J) k) :
    |locatedTerminalRoot Q m ψ site E a|≤‖E‖+D*k := by
  unfold locatedTerminalRoot terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m hm _ (rootArray k a) _ (B := ‖E‖) (C := D)
      (hf := fun i _ b => hf i.1 _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

omit [MeasurableSpace I] [Countable I] [MeasurableSingletonClass I] in
lemma locatedTerminalRoot_pullback
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ) (a : RootPath (I×Fin J) k) :
    locatedTerminalRoot Q m ψ site E a =
      terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
        (fun j : Fin k => Q (rootArray k a j).1) m E id
        (fun j σ b => ψ (rootArray k a j).1 (σ (site (rootArray k a j).2)) b) := by
  unfold locatedTerminalRoot terminalRoot
  exact (root_pullback (fun j : Fin k => rootArray k a j) id
    (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I×Fin J => Q i.1) m _ _).symm

lemma integral_locatedTerminalRoot [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    (∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
      ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))=
      ∫ a : Fin k → I,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b))
        ∂Measure.pi (fun _ : Fin k => ν) := by
  simp_rw [locatedTerminalRoot_pullback]
  have he : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))=
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin J)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [he]
  apply integral_root_prod_finite ν k
    (fun z : (Fin k → I) × (Fin k → Fin J) => terminalRoot (fun _ : Fin N => false) FiniteLaw.uniform
      (fun j : Fin k => Q (z.1 j)) m E id (fun j σ b => ψ (z.1 j) (σ (site (z.2 j))) b))
    (measurable_of_countable _) (B := ‖E‖+D*k)
  intro z
  unfold terminalRoot
  apply root_uniform_bound (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun j : Fin k => Q (z.1 j)) m hm _ id _ (B := ‖E‖) (C := D)
      (hf := fun j y b => hf (z.1 j) _ b)
  intro y
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)

noncomputable def terminalMean [NeZero J]
    (ν : Measure I) (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ) : ℝ :=
  ∫ a : Sigma (RootPath (I×Fin J)),locatedTerminalRoot Q m ψ site E a.2
    ∂compoundRootLaw (ν.prod (finiteUniform (Fin J))) s

lemma terminalMean_count_integral [NeZero J]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (site : Fin J → Fin N) (E : (Fin N → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    terminalMean ν s Q m ψ site E =
      ∫ k,∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))) ∂poissonMeasure s := by
  apply integral_familyLaw (poissonMeasure s) (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
  exact familyLaw_integrable_bound (poissonMeasure s)
    (fun k => rootLaw k (fun _ => ν.prod (finiteUniform (Fin J))))
    (fun k a => locatedTerminalRoot Q m ψ site E a) (fun k => measurable_of_countable _)
    ((integrable_const ‖E‖).add ((poisson_integrable_count s).const_mul D))
    (fun k a => locatedTerminalRoot_bound Q m hm ψ site E hf a)

/-- The original Poisson marked system may move mark sites off the added
spin at cost exactly twice the mark amplitude times its expected new-site count. -/
lemma terminalMean_mark_projection [NeZero N]
    (ν : Measure I) [IsProbabilityMeasure ν] (s : ℝ≥0)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ j,0 < m j)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (E : (Fin (N+1) → Spin) → ℝ)
    {D : ℝ} (hf : ∀ i σ a,|Real.log (ψ i σ a)|≤D) :
    |terminalMean ν s Q m ψ (id : Fin (N+1) → Fin (N+1)) E-
      terminalMean ν s Q m ψ (Fin.succ : Fin N → Fin (N+1)) E|≤2*D*s/(N+1) := by
  have hx (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) (k : ℕ) :
      Integrable (fun a : Fin k → I =>
        (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin J)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (a j)) m E id (fun j σ b => ψ (a j) (σ (site (sites j))) b)))
        (Measure.pi (fun _ : Fin k => ν)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable (‖E‖+D*k)
    apply ae_of_all
    intro a
    simp only [Real.norm_eq_abs]
    apply FiniteLaw.abs_expect_le
    intro sites
    unfold terminalRoot
    apply root_uniform_bound (terminalTower (fun _ : Fin (N+1) => false) FiniteLaw.uniform L)
      (fun j : Fin k => Q (a j)) m hm _ id _ (B := ‖E‖) (C := D)
        (hf := fun j y b => hf (a j) _ b)
    intro y
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm E (terminalState L y)
  have hi (J : ℕ) [NeZero J] (site : Fin J → Fin (N+1)) :
      Integrable (fun k => ∫ a : RootPath (I×Fin J) k,locatedTerminalRoot Q m ψ site E a
        ∂rootLaw k (fun _ => ν.prod (finiteUniform (Fin J)))) (poissonMeasure s) := by
    apply poisson_average_integrable s _
    intro k
    exact abs_integral_le_bound (fun a => locatedTerminalRoot_bound Q m hm ψ site E hf a)
  rw [terminalMean_count_integral ν s Q m hm ψ id E hf,
    terminalMean_count_integral ν s Q m hm ψ Fin.succ E hf,← integral_sub (hi (N+1) id) (hi N Fin.succ)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ k : ℕ,2*D*k/(N+1) ∂poissonMeasure s := by
      apply integral_mono ((hi (N+1) id).sub (hi N Fin.succ)).abs
        ((((poisson_integrable_count s).const_mul (2*D)).div_const (N+1)))
      intro k
      simp only [Pi.sub_apply]
      rw [integral_locatedTerminalRoot ν Q m hm ψ id E hf,
        integral_locatedTerminalRoot ν Q m hm ψ Fin.succ E hf,← integral_sub (hx (N+1) id k) (hx N Fin.succ k)]
      exact abs_integral_le_bound (fun a => terminalRoot_mark_site_expect Q m hm E a ψ hf)
    _ = _ := by rw [integral_div,integral_const_mul,poisson_mean]

end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
