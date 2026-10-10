import OAI.Probability.DilutedSpin.ActualPrefix
import OAI.Probability.DilutedSpin.SizeSpinRoot
import OAI.Probability.DilutedSpin.UniformIndexCoupling

namespace OAI

section
section
namespace DilutedSpinGlass.SizeCoupling
open MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {Z : Type} [MeasurableSpace Z]

/-- Measurability for the literal root before quenched averaging. Only the
interaction table values are read; auxiliary factorization witnesses are not. -/
theorem measurable_spinMean {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (theta : Z → Fin k → InteractionSample p) (h : Z → Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    (hθ : ∀ j σ, Measurable (fun z => (theta z j).1 σ))
    (hh : ∀ i, Measurable (fun z => h z i)) :
    Measurable (fun z => spinMean Q m (theta z) (h z) ψ) := by
  unfold spinMean
  apply FiniteLaw.measurable_expect
  intro indices
  apply FiniteLaw.measurable_expect
  intro sites
  apply measurable_root
  · intro x
    exact (Finset.measurable_sum _ (fun j _ => hθ j _)).add
      (Finset.measurable_sum _ (fun i _ => (hh i).mul_const _))
  · intro i x a
    exact measurable_const

lemma finite_logWeight_bound {N p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin)
    {C H : ℝ} (hθ : ∀ j x, |(theta j).1 x| ≤ C) (hh : ∀ i, |h i| ≤ H) :
    |logWeight theta h indices σ| ≤ H*N+C*k := by
  have hs (s : Spin) : |spin s| = 1 := by cases s <;> norm_num [spin]
  unfold logWeight
  apply (abs_add_le _ _).trans
  have h1 := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) => hθ j (fun q => σ (indices j q))))
  have h2 : |∑ i, h i*spin (σ i)| ≤ ∑ _i : Fin N, H :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
      simpa only [abs_mul,hs,mul_one] using hh i))
  simpa [mul_comm,add_comm] using add_le_add h1 h2

theorem spinMean_bound {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ j σ, |(theta j).1 σ| ≤ C) (hh : ∀ i, |h i| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    |spinMean Q m theta h ψ| ≤ H*N+C*k+D*l := by
  apply FiniteLaw.abs_expect_le
  intro indices
  apply FiniteLaw.abs_expect_le
  intro sites
  exact root_uniform_bound _ Q m hm _ id _
    (fun x => finite_logWeight_bound theta h indices (KernelTower.terminalState r x) hθ hh)
    (fun i x a => hψ i _ a)

variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

/-- Quenched mean at fixed physical and perturbation counts, under one common
countable type law. Marks retain their own finite alphabets. -/
noncomputable def countedMean (μ : Measure X) (ξ : Measure Y) (ν : Measure I)
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) : ℝ :=
  ∫ a : RootPath I l, ∫ x : RootPath X k, ∫ h : RootPath Y N,
    spinMean (fun j => Q (rootArray l a j)) m (fun j => theta (rootArray k x j))
      (fun i => field (rootArray N h i)) (fun j => ψ (rootArray l a j))
      ∂rootLaw N (fun _ => ξ) ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν)

lemma abs_integral_le_const (μ : Measure Z) [IsProbabilityMeasure μ] {f : Z → ℝ} {B : ℝ}
    (h : ∀ z, |f z| ≤ B) : |∫ z, f z ∂μ| ≤ B := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := f)
      (ae_of_all μ (fun z => by simpa only [Real.norm_eq_abs] using h z)))

omit [Countable I] [MeasurableSingletonClass I] in
theorem countedMean_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (ξ : Measure Y) [IsProbabilityMeasure ξ] (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ, |(theta x).1 σ| ≤ C) (hh : ∀ y, |field y| ≤ H)
    (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) μ ξ ν theta field Q m ψ k l| ≤ H*N+C*k+D*l := by
  apply abs_integral_le_const
  intro a
  apply abs_integral_le_const
  intro x
  apply abs_integral_le_const
  intro h
  exact spinMean_bound _ m hm _ _ _ (fun j σ => hθ _ σ) (fun i => hh _) (fun j σ a => hψ _ σ a)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Joint measurability in the genuine independent physical roots. -/
theorem measurable_countedIntegrand {p r N : ℕ} [NeZero N]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ, Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    (k l : ℕ) (a : RootPath I l) :
    Measurable (fun z : RootPath X k × RootPath Y N =>
      spinMean (fun j => Q (rootArray l a j)) m (fun j => theta (rootArray k z.1 j))
        (fun i => field (rootArray N z.2 i)) (fun j => ψ (rootArray l a j))) := by
  apply measurable_spinMean
  · intro j σ
    exact (hθ σ).comp ((measurable_rootArray k j).comp measurable_fst)
  · intro j
    exact hh.comp ((measurable_rootArray N j).comp measurable_snd)

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
theorem abs_expect_sub_le {f g : Ω → ℝ} {C : ℝ} (h : ∀ x, |f x-g x| ≤ C) :
    |P.expect f-P.expect g| ≤ C := by
  rw [← expect_sub]
  exact P.abs_expect_le h
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open HeterogeneousMarks
open scoped BigOperators

theorem spinRoot_interaction_step {N p k l r : ℕ} {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin (k+1) → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin (k+1) → Fin p → Fin N) (sites : Fin l → Fin N)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C : ℝ} (hθ : ∀ σ, |(theta 0).1 σ| ≤ C) :
    |spinRoot Q m theta h indices sites ψ-
      spinRoot Q m (fun j => theta j.succ) h (fun j => indices j.succ) sites ψ| ≤ C := by
  apply root_base_stability _ Q m hm
  intro x
  simpa only [DilutedSpinGlass.logWeight, Fin.sum_univ_succ,add_sub_add_right_eq_sub,
    add_sub_cancel_right] using hθ (fun q => KernelTower.terminalState r x (indices 0 q))

theorem spinMean_interaction_step {N p k l r : ℕ} [NeZero N] {A : Fin l → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin (k+1) → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin l) → Spin → FinitePath (A i) (r+1) → ℝ)
    {C : ℝ} (hθ : ∀ σ, |(theta 0).1 σ| ≤ C) :
    |spinMean Q m theta h ψ-spinMean Q m (fun j => theta j.succ) h ψ| ≤ C := by
  unfold spinMean
  rw [FiniteLaw.expect_pi_cons]
  rw [← (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect_const
    ((FiniteLaw.pi (fun _ : Fin k => FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N))))).expect _)]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  exact spinRoot_interaction_step Q m hm theta h (Fin.cons i indices) sites ψ hθ

/-- Deleting one realized factor integrates out only its own independent marks.
The surviving factors keep their alphabets and level priors exactly. -/
theorem spinRoot_mark_step {N p k l r : ℕ} {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (indices : Fin k → Fin p → Fin N) (sites : Fin (l+1) → Fin N)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinRoot Q m theta h indices sites ψ-
      spinRoot (fun j => Q j.succ) m theta h indices (fun j => sites j.succ) (fun j => ψ j.succ)| ≤ D := by
  have hid : Fin.cons 0 (fun j : Fin l => j.succ) = (id : Fin (l+1) → Fin (l+1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hp := root_pullback (Fin.succ : Fin l → Fin (l+1)) id
    (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m
    (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
    (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
  unfold spinRoot
  rw [hp]
  exact (by
    simpa only [hid,Function.comp_id] using
      root_cons_bound
        (KernelTower.terminalTower (fun _ : Fin N => false) FiniteLaw.uniform r) Q m hm
        (fun x => DilutedSpinGlass.logWeight theta h indices (KernelTower.terminalState r x))
        (fun j : Fin l => j.succ) 0
        (fun i x a => ψ i (KernelTower.terminalState r x (sites i)) a)
        (fun x a => hψ _ a))

theorem spinMean_mark_step {N p k l r : ℕ} [NeZero N] {A : Fin (l+1) → Type}
    [∀ i, Fintype (A i)]
    (Q : (i : Fin (l+1)) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (theta : Fin k → InteractionSample p) (h : Fin N → ℝ)
    (ψ : (i : Fin (l+1)) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ σ a, |Real.log (ψ 0 σ a)| ≤ D) :
    |spinMean Q m theta h ψ-
      spinMean (fun j => Q j.succ) m theta h (fun j => ψ j.succ)| ≤ D := by
  apply FiniteLaw.abs_expect_sub_le
  intro indices
  rw [FiniteLaw.expect_pi_cons]
  rw [← (FiniteLaw.uniform : FiniteLaw (Fin N)).expect_const
    ((FiniteLaw.pi (fun _ : Fin l => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect _)]
  apply FiniteLaw.abs_expect_sub_le
  intro i
  apply FiniteLaw.abs_expect_sub_le
  intro sites
  exact spinRoot_mark_step Q m hm theta h indices (Fin.cons i sites) ψ hψ

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
