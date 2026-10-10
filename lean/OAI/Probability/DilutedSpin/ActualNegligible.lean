import OAI.Probability.DilutedSpin.ForkTree
import OAI.Probability.DilutedSpin.PerturbedSizeCoupling
import OAI.Probability.DilutedSpin.SizeSpinRoot
import OAI.Probability.DilutedSpin.SpinBaseComparison

namespace OAI

section
section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω] {N : ℕ}

/-- Conditional covariance density at the branching depth, averaged over the
actual shared prefix kernels. -/
noncomputable def prefixCovarianceEnergy (h : ℕ) : (d : ℕ) →
    KernelTower Ω (h+1+d) → (FinitePath Ω (h+1+d) → Fin N → ℝ) → ℝ
  | 0, T, X => (law (h+1) T).covarianceEnergy X
  | d+1, T, X => T.1.expect (fun z => prefixCovarianceEnergy h d (T.2 z) (fun y => X (z,y)))

noncomputable def tripleExpect (h : ℕ) : (d : ℕ) → KernelTower Ω (h+1+d) →
    (FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → ℝ) → ℝ
  | 0, T, F => (law (h+1) T).expect (fun x => (law (h+1) T).expect
      (fun y => (law (h+1) T).expect (F x y)))
  | d+1, T, F => T.1.expect (fun z => tripleExpect h d (T.2 z) (fun x y w => F (z,x) (z,y) (z,w)))

lemma prefixCovarianceEnergy_nonneg (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (X : FinitePath Ω (h+1+d) → Fin N → ℝ) : 0 ≤ prefixCovarianceEnergy h d T X := by
  induction d with
  | zero => unfold prefixCovarianceEnergy FiniteLaw.covarianceEnergy; positivity
  | succ d ih => exact T.1.expect_nonneg (fun z => ih (T.2 z) (fun y => X (z,y)))

/-- The first genuinely new branch at the divergence vertex controls squared
conditional covariance, including the zero-site normalization endpoint. -/
lemma prefix_three_copy_bound (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (X : FinitePath Ω (h+1+d) → Fin N → ℝ) :
    2*prefixCovarianceEnergy h d T X ≤ tripleExpect h d T
      (fun x y z => (FiniteLaw.dot (X x) (X y)-FiniteLaw.dot (X x) (X z))^2) := by
  induction d with
  | zero =>
    have he : 2*(law (h+1) T).covarianceEnergy X =
      (2/(N:ℝ)^2) * (∑ i, ∑ j, (law (h+1) T).covariance (fun x => X x i) (fun x => X x j)^2) := by
      unfold FiniteLaw.covarianceEnergy
      ring
    change 2*(law (h+1) T).covarianceEnergy X ≤ _
    rw [he]
    exact (law (h+1) T).three_copy_bound X
  | succ d ih =>
    change 2*T.1.expect _ ≤ T.1.expect _
    rw [← FiniteLaw.expect_mul_left]
    exact T.1.expect_mono (fun z => ih (T.2 z) (fun y => X (z,y)))

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω] {N : ℕ}

lemma fork_fresh_joint (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (F : FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → ℝ) :
    ((fork h 2 d).sampleLaw T).expect (fun x => freshEval (fork h 2 d) T (forkVertex h 2 d)
      (fun y => F ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x)
        ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x) y) x) =
      KernelTower.tripleExpect h d T F := by
  induction d with
  | zero =>
    change ((fork h 2 0).sampleLaw T).expect
      (fun x => (KernelTower.law (h+1) T).expect (fun y =>
        F ((fork h 2 0).pathAt (forkLeaf h 2 0 0) x)
          ((fork h 2 0).pathAt (forkLeaf h 2 0 1) x) y)) = _
    refine (fork_zero_expect h 2 T (fun xs => (KernelTower.law (h+1) T).expect
      (fun y => F (xs 0) (xs 1) y))).trans ?_
    exact FiniteLaw.expect_pi_pair (fun _ : Fin (2:ℕ+) => KernelTower.law (h+1) T)
      0 1 (by decide) (fun x y => (KernelTower.law (h+1) T).expect (F x y))
  | succ d ih =>
    rcases T with ⟨μ,K⟩
    change (FiniteLaw.pi (fun _ : Fin (1:ℕ+) => μ.bind (fun z => (fork h 2 d).sampleLaw (K z)))).expect
      (fun x => freshEval (fork h 2 d) (K (x 0).1) (forkVertex h 2 d)
        (fun y => F ((x 0).1,(fork h 2 d).pathAt (forkLeaf h 2 d 0) (x 0).2)
          ((x 0).1,(fork h 2 d).pathAt (forkLeaf h 2 d 1) (x 0).2) ((x 0).1,y)) (x 0).2) = _
    refine (FiniteLaw.expect_pi_marginal
      (fun _ : Fin (1:ℕ+) => μ.bind (fun z => (fork h 2 d).sampleLaw (K z))) 0
      (fun x => freshEval (fork h 2 d) (K x.1) (forkVertex h 2 d)
        (fun y => F (x.1,(fork h 2 d).pathAt (forkLeaf h 2 d 0) x.2)
          (x.1,(fork h 2 d).pathAt (forkLeaf h 2 d 1) x.2) (x.1,y)) x.2)).trans ?_
    erw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro z
    exact ih (K z) (fun x y w => F (z,x) (z,y) (z,w))

/-- Exact conditional independence of the three ACTUAL continuations at d,
not an independence hypothesis added to the eventual Gibbs reservoir. -/
theorem fork_three_joint (h d : ℕ) (T : KernelTower Ω (h+1+d))
    (F : FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → FinitePath Ω (h+1+d) → ℝ) :
    ((grow (fork h 2 d) (forkVertex h 2 d)).sampleLaw T).expect
      (fun x => F
        ((fork h 2 d).pathAt (forkLeaf h 2 d 0) (oldSample (fork h 2 d) (forkVertex h 2 d) x))
        ((fork h 2 d).pathAt (forkLeaf h 2 d 1) (oldSample (fork h 2 d) (forkVertex h 2 d) x))
        (newPath (fork h 2 d) (forkVertex h 2 d) x)) = KernelTower.tripleExpect h d T F := by
  exact (extension_sampling_dependent (fork h 2 d) T (forkVertex h 2 d)
    (fun x y => F ((fork h 2 d).pathAt (forkLeaf h 2 d 0) x)
      ((fork h 2 d).pathAt (forkLeaf h 2 d 1) x) y)).trans (fork_fresh_joint h d T F)

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.SizeCoupling
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks
open scoped BigOperators NNReal

variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i, Fintype (A i)]

 
omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_eq_pi (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (M : Model p)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ k l =
    ∫ a : RootPath I l, ∫ theta : Fin k → InteractionSample p, ∫ h : Fin N → ℝ,
      spinMean (fun j => Q (rootArray l a j)) m theta h (fun j => ψ (rootArray l a j))
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂rootLaw l (fun _ => ν) := by
  unfold countedMean
  apply integral_congr_ae
  filter_upwards [] with a
  calc
    _ = ∫ theta : Fin k → InteractionSample p, ∫ h : RootPath ℝ N,
        spinMean (fun j => Q (rootArray l a j)) m theta (rootArray N h) (fun j => ψ (rootArray l a j))
        ∂rootLaw N (fun _ => M.field.toMeasure)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) :=
      integral_rootArray_eq_pi M.disorder.toMeasure k _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with theta
      exact integral_rootArray_eq_pi (X := ℝ) M.field.toMeasure N
        (fun h : Fin N → ℝ => spinMean (fun j => Q (rootArray l a j)) m theta h
          (fun j => ψ (rootArray l a j)))

lemma spinFieldIntegral_close {p r N k l : ℕ} [NeZero N] {B : Fin l → Type}
    [∀ i, Fintype (B i)] (M : Model p)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (theta : Fin k → InteractionSample p)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    Integrable (fun h : Fin N → ℝ => spinMean Q m theta h ψ)
      (Measure.pi (fun _ : Fin N => M.field.toMeasure)) ∧
    |(∫ h : Fin N → ℝ, spinMean Q m theta h ψ ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))-
      (fieldAverage M (N := N) theta-N*Real.log 2)| ≤ D*l := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hg := (indexAverage_integrable_and_fieldAverage_bound M hh hN theta).1
  have hf := measurable_spinMean Q m (fun _ : Fin N → ℝ => theta) id ψ
    (fun _ _ => measurable_const) (fun i => measurable_pi_apply i)
  have hc := integrate_close (Measure.pi (fun _ : Fin N => M.field.toMeasure)) hf
    (hg.sub (integrable_const (N*Real.log 2))) (fun h => spinMean_base_distance Q m hm hend theta h ψ hψ)
  have he : (∫ h : Fin N → ℝ, indexAverage theta h-N*Real.log 2
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)) = fieldAverage M (N := N) theta-N*Real.log 2 := by
    rw [integral_sub hg (integrable_const _)]
    simp only [fieldAverage,integral_const,probReal_univ,smul_eq_mul,one_mul]
  refine ⟨hc.1, ?_⟩
  simpa only [Pi.sub_apply,id_eq,he] using hc.2

lemma spinDisorderIntegral_close {p r N k l : ℕ} [NeZero N] {B : Fin l → Type}
    [∀ i, Fintype (B i)] (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : Fin l) → Fin (r+1) → FiniteLaw (B i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : (i : Fin l) → Spin → FinitePath (B i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) :
    Integrable (fun theta : Fin k → InteractionSample p => ∫ h : Fin N → ℝ,
      spinMean Q m theta h ψ ∂Measure.pi (fun _ : Fin N => M.field.toMeasure))
      (Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) ∧
    |(∫ theta : Fin k → InteractionSample p, ∫ h : Fin N → ℝ,
      spinMean Q m theta h ψ ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure))-
      (disorderAverage M N k-N*Real.log 2)| ≤ D*l := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hg := (fieldAverage_integrable_and_disorderAverage_bound M hθ hh hN k).1
  have hfm : Measurable (fun z : (Fin k → InteractionSample p) × (Fin N → ℝ) => spinMean Q m z.1 z.2 ψ) :=
    measurable_spinMean Q m Prod.fst Prod.snd ψ (fun j σ => by fun_prop) (fun i => by fun_prop)
  have hc := integrate_close (Measure.pi (fun _ : Fin k => M.disorder.toMeasure))
    hfm.stronglyMeasurable.integral_prod_right'.measurable (hg.sub (integrable_const (N*Real.log 2)))
    (fun theta => (spinFieldIntegral_close M hh Q m hm hend theta ψ hψ).2)
  have he : (∫ theta : Fin k → InteractionSample p, fieldAverage M (N := N) theta-N*Real.log 2
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)) = disorderAverage M N k-N*Real.log 2 := by
    rw [integral_sub hg (integrable_const _)]
    simp only [disorderAverage,integral_const,probReal_univ,smul_eq_mul,one_mul]
  refine ⟨hc.1, ?_⟩
  simpa only [Pi.sub_apply,id_eq,he] using hc.2

 
theorem actual_countedMean_close (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (k l : ℕ) :
    |countedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ k l-
      (disorderAverage M N k-N*Real.log 2)| ≤ D*l := by
  rw [countedMean_eq_pi]
  have hc := integrate_close (rootLaw l (fun _ => ν))
    (measurable_of_countable _) (integrable_const (disorderAverage M N k-N*Real.log 2))
    (fun a : RootPath I l => (spinDisorderIntegral_close M hθ hh
      (fun j => Q (rootArray l a j)) m hm hend (fun j => ψ (rootArray l a j))
      (fun j σ b => hψ _ σ b)).2)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hc.2

 
theorem actual_perturbedMean_close (ν : Measure I) [IsProbabilityMeasure ν]
    {p r N : ℕ} [NeZero N] (M : Model p)
    (hθ : Integrable (fun z : InteractionSample p => ‖z.1‖) M.disorder.toMeasure)
    (hh : Integrable (fun h : ℝ => |h|) M.field.toMeasure)
    (Q : (i : I) → Fin (r+1) → FiniteLaw (A i)) (m : Fin (r+1) → ℝ)
    (hm : ∀ j, 0 < m j) (hend : m (Fin.last r) = 1)
    (ψ : (i : I) → Spin → FinitePath (A i) (r+1) → ℝ)
    {D : ℝ} (hψ : ∀ i σ a, |Real.log (ψ i σ a)| ≤ D) (s : ℝ≥0) :
    |perturbedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
      (M.alpha*N) s-N*pressure M N| ≤ D*s := by
  let f := countedMean (N := N) M.disorder.toMeasure M.field.toMeasure ν id id Q m ψ
  let g (count : ℕ) (_ : ℕ) := disorderAverage M N count-N*Real.log 2
  have hg : ∀ k l, |g k l| ≤ N*fieldMoment M+interactionMoment M*k+(0:ℝ)*l := by
    intro k l
    have := (fieldAverage_integrable_and_disorderAverage_bound M hθ hh
      (Nat.pos_of_ne_zero (NeZero.ne N)) k).2
    dsimp [g]
    linarith
  have hc : ∀ k l, |f k l-g k l| ≤ D*l :=
    actual_countedMean_close ν M hθ hh Q m hm hend ψ hψ
  have hf : ∀ k l, |f k l| ≤ N*fieldMoment M+interactionMoment M*k+D*l := by
    intro k l
    have htri := abs_add_le (f k l-g k l) (g k l)
    rw [sub_add_cancel] at htri
    have hg' := hg k l
    have hc' := hc k l
    linarith
  have ht := twoPoisson_abs_sub_le (M.alpha*N) s hf hg
    (E := 0) (F := 0) (G := D) (fun k l => by simpa using hc k l)
  have he : twoPoissonMean (M.alpha*N) s g = N*pressure M N-N*Real.log 2 := by
    unfold twoPoissonMean g
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    rw [integral_sub (disorderAverage_integrable_and_pressure_bound M hθ hh
      (Nat.pos_of_ne_zero (NeZero.ne N))).1 (integrable_const _)]
    simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    change _ = N*((∫ k, disorderAverage M N k ∂poissonMeasure (M.alpha*N))/N)-_
    rw [mul_div_cancel₀ _ hN]
  rw [he] at ht
  dsimp [perturbedMean]
  convert (show |twoPoissonMean (M.alpha*N) s f-(N*pressure M N-N*Real.log 2)| ≤ D*s by
    simpa using ht) using 1; congr 1; ring

end DilutedSpinGlass.SizeCoupling
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree

/-- Two independent branches at the designated physical height; all other
levels are unary. The height stays fixed, avoiding transports of spin paths. -/
def forkAt : (n d : ℕ) → d < n → PrescribedTree n
  | 0, _, hd => False.elim (Nat.not_lt_zero _ hd)
  | n+1, 0, _ => .node 2 (fun _ => single n)
  | n+1, d+1, hd => .node 1 (fun _ => forkAt n d (Nat.lt_of_succ_lt_succ hd))

def forkAtLeaf : (n d : ℕ) → (hd : d < n) → Fin 2 → (forkAt n d hd).Leaf
  | 0, _, hd, _ => False.elim (Nat.not_lt_zero _ hd)
  | _+1, 0, _, i => ⟨i,singleLeaf _⟩
  | n+1, d+1, hd, i => ⟨0,forkAtLeaf n d (Nat.lt_of_succ_lt_succ hd) i⟩

def forkAtVertex : (n d : ℕ) → (hd : d < n) → (forkAt n d hd).Internal
  | 0, _, hd => False.elim (Nat.not_lt_zero _ hd)
  | _+1, 0, _ => none
  | n+1, d+1, hd => some ⟨0,forkAtVertex n d (Nat.lt_of_succ_lt_succ hd)⟩

lemma forkAtLeaf_surjective (n d : ℕ) (hd : d < n) : Function.Surjective (forkAtLeaf n d hd) := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero =>
      rintro ⟨i,a⟩
      refine ⟨i,?_⟩
      exact congrArg (fun a : (single n).Leaf => (⟨i,a⟩ : (forkAt (n+1) 0 hd).Leaf))
        (leaf_single_unique n a).symm
    | succ d =>
      rintro ⟨i,a⟩
      have hi := Fin.eq_zero i
      subst i
      obtain ⟨j,rfl⟩ := ih d (Nat.lt_of_succ_lt_succ hd) a
      exact ⟨j,rfl⟩

lemma forkAt_split (n d : ℕ) (hd : d < n) (i j : Fin 2) (hij : i ≠ j) :
    splitDepth (forkAt n d hd) (forkAtLeaf n d hd i) (forkAtLeaf n d hd j) = d := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => exact splitDepth_diff_child (fun _ : Fin (2:ℕ+) => single n) i j hij _ _
    | succ d =>
      exact (splitDepth_same_child (fun _ : Fin (1:ℕ+) => forkAt n d (Nat.lt_of_succ_lt_succ hd))
        0 (forkAtLeaf n d _ i) (forkAtLeaf n d _ j)).trans (by rw [ih]; omega)

lemma forkAt_fresh (n d : ℕ) (hd : d < n) (i : Fin 2) :
    freshSplitDepth (forkAt n d hd) (forkAtVertex n d hd) (forkAtLeaf n d hd i) = d := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => rfl
    | succ d =>
      exact (freshSplitDepth_same_child (fun _ : Fin (1:ℕ+) => forkAt n d (Nat.lt_of_succ_lt_succ hd))
        0 (forkAtVertex n d _) (forkAtLeaf n d _ i)).trans (by rw [ih]; omega)

lemma forkAt_gamma (n d : ℕ) (hd : d < n) (m : Fin (n+1) → ℝ) :
    gamma (forkAt n d hd) m (forkAtVertex n d hd) = m ⟨d,by omega⟩ - 2*m ⟨d+1,by omega⟩ := by
  induction n generalizing d with
  | zero => omega
  | succ n ih =>
    cases d with
    | zero => rfl
    | succ d =>
      change gamma (forkAt n d _) (fun j => m j.succ) (forkAtVertex n d _) = _
      exact ih d (Nat.lt_of_succ_lt_succ hd) (fun j => m j.succ)

lemma forkAt_unique (n d : ℕ) (hd : d < n) (a : (forkAt n d hd).Leaf)
    (ha : splitDepth (forkAt n d hd) (forkAtLeaf n d hd 0) a = d) : a = forkAtLeaf n d hd 1 := by
  obtain ⟨i,rfl⟩ := forkAtLeaf_surjective n d hd a
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl
  · rw [splitDepth_self] at ha
    omega
  · rfl

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
