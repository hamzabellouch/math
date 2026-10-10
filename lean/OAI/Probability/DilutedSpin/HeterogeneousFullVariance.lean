import OAI.Probability.DilutedSpin.HeterogeneousTwoPoisson

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- Both random counts and all physical fields contribute to this bound.
The heterogeneous auxiliary priors remain inside the finite power means. -/
theorem full_root_variance
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hbmeas : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {B C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ h k x y, |base h k x y| ≤ B+C*k)
    (hf : ∀ i x y, |Real.log (factor i x y)| ≤ D)
    (hrep : ∀ h k (j : Fin k) x z y,
      |base h k x y-base h k (replaceRoot k x j z) y| ≤ 2*C)
    (hadd : ∀ h k z x y, |base h (k+1) (z,x) y-base h k x y| ≤ C)
    (E : Fin M → ℝ)
    (hfield : ∀ j h z k x y, |base h k x y-base (replaceRoot M h j z) k x y| ≤ E j)
    (c : ℝ) :
    let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
      root T Q m (base h k x) (rootArray n y) factor+c*n
    let G := fun h => poissonRootAverage μ r (fun k x => poissonRootAverage ν s (F h k x))
    (∫ h, ∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y, (F h k x n y-(∫ z, G z ∂rootLaw M ξ))^2
      ∂rootLaw n (fun _ => ν) ∂poissonMeasure s ∂rootLaw k (fun _ => μ)
        ∂poissonMeasure r ∂rootLaw M ξ) ≤
      3*C^2*(r : ℝ)+3*(D+|c|)^2*(s : ℝ)+∑ j, (E j)^2/2 := by
  dsimp only
  let F := fun h k (x : RootPath X k) n (y : RootPath I n) =>
    root T Q m (base h k x) (rootArray n y) factor+c*n
  let H := fun h k x => poissonRootAverage ν s (F h k x)
  let G := fun h => poissonRootAverage μ r (H h)
  have hF (k n : ℕ) : Measurable (fun z : (RootPath Y M × RootPath X k) × RootPath I n =>
      F z.1.1 k z.1.2 n z.2) :=
    (measurable_root_base T Q m (fun z : RootPath Y M × RootPath X k => base z.1 k z.2) (hbmeas k) factor n).add measurable_const
  have hFh (h : RootPath Y M) (k n : ℕ) :
      Measurable (fun z : RootPath X k × RootPath I n => F h k z.1 n z.2) :=
    (hF k n).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hFm (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) :
      Measurable (F h k x n) := (hFh h k n).comp (measurable_const.prodMk measurable_id)
  have hB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ) (y : RootPath I n) :
      |F h k x n y| ≤ B+C*k+(D+|c|)*n := by
    have hh := root_uniform_bound T Q m hm (base h k x) (rootArray n y) factor (hb h k x) hf
    calc
      _ ≤ |root T Q m (base h k x) (rootArray n y) factor|+|c*(n:ℝ)| := abs_add_le _ _
      _ ≤ B+C*k+D*n+|c| *n := by
        rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
        exact add_le_add hh le_rfl
      _ = _ := by ring
  have hH (k : ℕ) : Measurable (fun z : RootPath Y M × RootPath X k => H z.1 k z.2) :=
    measurable_poissonRootAverage ν s (hF k)
  have hG : Measurable G := measurable_poissonRootAverage μ r hH
  have hHB (h : RootPath Y M) (k : ℕ) (x : RootPath X k) :
      |H h k x| ≤ B+C*k+(D+|c|)*(s:ℝ) := poissonRootAverage_bound ν s (hB h k x)
  have hGB (h : RootPath Y M) : |G h| ≤ (B+(D+|c|)*(s:ℝ))+C*r := by
    apply poissonRootAverage_bound μ r
    intro k x
    convert hHB h k x using 1; ring
  have hHE (j : Fin M) (h : RootPath Y M) (z : Y) (k : ℕ) (x : RootPath X k) :
      |H h k x-H (replaceRoot M h j z) k x| ≤ E j := by
    apply poissonRootAverage_stability ν s (hFm h k x) (hFm (replaceRoot M h j z) k x)
      (hB h k x) (hB (replaceRoot M h j z) k x)
    intro n y
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hfield j h z k x)
  have hGE (j : Fin M) (h : RootPath Y M) (z : Y) : |G h-G (replaceRoot M h j z)| ≤ E j := by
    apply poissonRootAverage_stability μ r (A := B+(D+|c|)*(s:ℝ)) (B := C)
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
      (fun k => (hH k).comp (measurable_const.prodMk measurable_id))
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB h k x
    · intro k x; simpa only [add_right_comm, Function.comp_apply, id_eq] using hHB (replaceRoot M h j z) k x
    · exact hHE j h z
  have hv := root_variance_bound M ξ hG hGB E hGE
  have hrep1 (h : RootPath Y M) (k : ℕ) (j : Fin k) (x : RootPath X k) (z : X)
      (n : ℕ) (y : RootPath I n) :
      |F h k x n y-F h k (replaceRoot k x j z) n y| ≤ 2*C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hrep h k j x z)
  have hadd1 (h : RootPath Y M) (k : ℕ) (z : X) (x : RootPath X k)
      (n : ℕ) (y : RootPath I n) : |F h (k+1) (z,x) n y-F h k x n y| ≤ C := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub]
    exact root_base_stability T Q m hm _ _ _ factor (hadd h k z x)
  have hrep2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (j : Fin n) (y : RootPath I n) (z : I) :
      |F h k x n y-F h k x n (replaceRoot n y j z)| ≤ 2*(D+|c|) := by
    dsimp only [F]
    rw [add_sub_add_right_eq_sub,rootArray_replace,abs_sub_comm]
    exact (root_update_bound T Q m hm _ _ j z factor hf).trans (by linarith [abs_nonneg c])
  have hadd2 (h : RootPath Y M) (k : ℕ) (x : RootPath X k) (n : ℕ)
      (z : I) (y : RootPath I n) : |F h k x (n+1) (z,y)-F h k x n y| ≤ D+|c| := by
    change |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor+c*(n+1:ℕ)-
      (root T Q m (base h k x) (rootArray n y) factor+c*n)| ≤ _
    rw [Nat.cast_add,Nat.cast_one]
    calc
      _ = |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor+c| := by congr 1; ring
      _ ≤ |root T Q m (base h k x) (Fin.cons z (rootArray n y)) factor-
        root T Q m (base h k x) (rootArray n y) factor|+|c| := abs_add_le _ _
      _ ≤ D+|c| := add_le_add (root_cons_bound T Q m hm _ _ z factor (hf z)) le_rfl
  have hstep (h : RootPath Y M) := two_poisson_roots_second_moment μ ν r s hC
    (add_nonneg hD (abs_nonneg c)) (hFh h) (hB h) (hrep1 h) (hadd1 h) (hrep2 h) (hadd2 h)
    (∫ z, G z ∂rootLaw M ξ)
  have hi : Integrable (fun h => (G h-∫ z, G z ∂rootLaw M ξ)^2) (rootLaw M ξ) :=
    ((bounded_memLp hG hGB 2).sub (memLp_const (∫ z, G z ∂rootLaw M ξ))).integrable_sq
  have hnn (h : RootPath Y M) : 0 ≤ (∫ k : ℕ, ∫ x, ∫ n : ℕ, ∫ y,
      (F h k x n y-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw n (fun _ => ν)
      ∂poissonMeasure s ∂rootLaw k (fun _ => μ) ∂poissonMeasure r) :=
    integral_nonneg (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ =>
      integral_nonneg (fun _ => sq_nonneg _))))
  have hh := integral_mono_of_nonneg (μ := rootLaw M ξ) (ae_of_all _ hnn)
    ((integrable_const (3*C^2*(r:ℝ)+3*(D+|c|)^2*(s:ℝ))).add hi) (ae_of_all _ hstep)
  simp only [Pi.add_apply] at hh
  rw [integral_add (integrable_const _) hi,integral_const,probReal_univ,smul_eq_mul,one_mul] at hh
  have heq : (∫ h, (G h-∫ z, G z ∂rootLaw M ξ)^2 ∂rootLaw M ξ) =
      variance G (rootLaw M ξ) := (variance_eq_integral hG.aemeasurable).symm
  change _ ≤ _
  exact hh.trans (add_le_add le_rfl (heq.le.trans hv))

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
