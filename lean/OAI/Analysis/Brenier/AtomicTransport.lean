import OAI.Analysis.Brenier.Atomic
import OAI.Analysis.Brenier.FiniteCoupling
import OAI.Analysis.Brenier.Quantization

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

/-- Real-valued finite matrix weights have the expected real quadratic cost. -/
theorem quadraticPlanCost_atomicMatchingPlan_ofReal_toReal
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (y : ι → E d) (z : κ → E d) :
    (quadraticPlanCost (atomicMatchingPlan
      (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
      (fun q => y q.1) (fun q => z q.2))).toReal =
      ∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2 := by
  rw [quadraticPlanCost_atomicMatchingPlan, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
      ENNReal.toReal_ofReal (hp _ _), Fintype.sum_prod_type]
  · intro q _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- Criterion turning any real matrix minimizer into a minimum among arbitrary
couplings, without changing the chosen matrix. -/
theorem atomicMatchingPlan_minimal_of_matrix_minimal
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (y : ι → E d) (z : κ → E d)
    (hy : Function.Injective y) (hz : Function.Injective z)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hcoupling : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j))
      (atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)))
    (hmin : ∀ q : ι → κ → ℝ, (∀ i j, 0 ≤ q i j) →
      (∀ i, ∑ j, q i j = (w i).toReal) →
      (∀ j, ∑ i, q i j = (v j).toReal) →
      (∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2) ≤ ∑ i, ∑ j, q i j * ‖y i - z j‖ ^ 2) :
    ∀ π, IsCoupling (∑ i, w i • Measure.dirac (y i))
        (∑ j, v j • Measure.dirac (z j)) π →
      quadraticPlanCost (atomicMatchingPlan
        (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)) ≤ quadraticPlanCost π := by
  intro π hπ
  apply (ENNReal.toReal_le_toReal (hcoupling.atomic_cost_ne_top hy hz)
    (hπ.atomic_cost_ne_top hy hz)).mp
  rw [quadraticPlanCost_atomicMatchingPlan_ofReal_toReal p hp,
    hπ.atomic_cost_toReal hy hz, Fintype.sum_prod_type]
  exact hmin (fun i j => (π {(y i, z j)}).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (hπ.atomic_row_sum_toReal hy hz) (hπ.atomic_col_sum_toReal hy hz)

/-- A minimizing transportation matrix also minimizes over every measure-valued
coupling of the two injectively indexed finite atomic laws. -/
theorem exists_optimal_atomic_matrix
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (y : ι → E d) (z : κ → E d)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    ∃ p : ι → κ → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = (w i).toReal) ∧
      (∀ j, ∑ i, p i j = (v j).toReal) ∧
      IsCoupling (∑ i, w i • Measure.dirac (y i))
        (∑ j, v j • Measure.dirac (z j))
        (atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
          (fun q => y q.1) (fun q => z q.2)) ∧
      ∀ π, IsCoupling (∑ i, w i • Measure.dirac (y i))
          (∑ j, v j • Measure.dirac (z j)) π →
        quadraticPlanCost (atomicMatchingPlan
          (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
          (fun q => y q.1) (fun q => z q.2)) ≤ quadraticPlanCost π := by
  have hwfin : ∀ i, w i ≠ ∞ := by
    have h : (∑ i, w i) ≠ ∞ := by rw [hw]; exact ENNReal.one_ne_top
    exact fun i => ENNReal.sum_ne_top.mp h i (Finset.mem_univ i)
  have hvfin : ∀ j, v j ≠ ∞ := by
    have h : (∑ j, v j) ≠ ∞ := by rw [hv]; exact ENNReal.one_ne_top
    exact fun j => ENNReal.sum_ne_top.mp h j (Finset.mem_univ j)
  have hwreal : ∑ i, (w i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => hwfin i), hw]
    simp
  have hvreal : ∑ j, (v j).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun j _ => hvfin j), hv]
    simp
  obtain ⟨p, hp, hrow, hcol, hmin⟩ := exists_minimal_finite_coupling
    (fun i => (w i).toReal) (fun j => (v j).toReal)
    (fun i j => ‖y i - z j‖ ^ 2)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg) hwreal hvreal
  have hrowE : ∀ i, ∑ j, ENNReal.ofReal (p i j) = w i := by
    intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp i j), hrow i,
      ENNReal.ofReal_toReal (hwfin i)]
  have hcolE : ∀ j, ∑ i, ENNReal.ofReal (p i j) = v j := by
    intro j
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i j), hcol j,
      ENNReal.ofReal_toReal (hvfin j)]
  have hcoupling := atomicMatchingPlan_isCoupling_of_marginal_sums w v
    (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2)) y z hw hrowE hcolE
  refine ⟨p, hp, hrow, hcol, hcoupling, ?_⟩
  exact atomicMatchingPlan_minimal_of_matrix_minimal w v y z hy hz p hp hcoupling hmin

/-- Existence of a globally optimal coupling for two finite atomic probability laws. -/
theorem exists_optimal_atomic_coupling
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (y : ι → E d) (z : κ → E d)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    ∃ π, IsCoupling (∑ i, w i • Measure.dirac (y i))
        (∑ j, v j • Measure.dirac (z j)) π ∧
      ∀ σ, IsCoupling (∑ i, w i • Measure.dirac (y i))
          (∑ j, v j • Measure.dirac (z j)) σ →
        quadraticPlanCost π ≤ quadraticPlanCost σ := by
  obtain ⟨p, _, _, _, hp, hmin⟩ := exists_optimal_atomic_matrix w v y z hw hv hy hz
  exact ⟨_, hp, hmin⟩

/-- Any actual minimum realizes the infimum in the challenge's Wasserstein definition. -/
theorem wasserstein2_sq_eq_planCost_of_minimal {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)}
    (hπ : IsCoupling μ ν π)
    (hmin : ∀ σ, IsCoupling μ ν σ → quadraticPlanCost π ≤ quadraticPlanCost σ) :
    wasserstein2 μ ν ^ 2 = (quadraticPlanCost π).toReal := by
  have hInf : sInf {r : ℝ≥0∞ | ∃ σ : Measure (E d × E d),
      IsCoupling μ ν σ ∧ quadraticPlanCost σ = r} = quadraticPlanCost π := by
    apply le_antisymm
    · exact sInf_le ⟨π, hπ, rfl⟩
    · apply le_sInf
      rintro r ⟨σ, hσ, rfl⟩
      exact hmin σ hσ
  simp only [wasserstein2, hInf, Real.sq_sqrt ENNReal.toReal_nonneg]

/-- The finite minimizing matrix has squared speed exactly equal to W₂². -/
theorem exists_atomic_coupling_matrix_with_wasserstein_cost
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (y : ι → E d) (z : κ → E d)
    (hw : ∑ i, w i = 1) (hv : ∑ j, v j = 1)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    ∃ p : ι → κ → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = (w i).toReal) ∧
      (∀ j, ∑ i, p i j = (v j).toReal) ∧
      (∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2) =
        wasserstein2 (∑ i, w i • Measure.dirac (y i))
          (∑ j, v j • Measure.dirac (z j)) ^ 2 := by
  obtain ⟨p, hp, hrow, hcol, hcoupling, hmin⟩ :=
    exists_optimal_atomic_matrix w v y z hw hv hy hz
  refine ⟨p, hp, hrow, hcol, ?_⟩
  rw [wasserstein2_sq_eq_planCost_of_minimal hcoupling hmin]
  exact (quadraticPlanCost_atomicMatchingPlan_ofReal_toReal p hp y z).symm

end Problem358

namespace Problem358

/-- Removing the zero weights also preserves finite sums of weighted measures. -/
theorem sum_ofReal_smul_positive_support {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (w : ι → ℝ) (μ : ι → Measure X) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : PositiveFiniteCoupling.Support w, ENNReal.ofReal (w i) • μ i) =
      ∑ i, ENNReal.ofReal (w i) • μ i := by
  classical
  have hzero : (∑ i : {i : ι // ¬ 0 < w i}, ENNReal.ofReal (w i) • μ i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : w i = 0 := le_antisymm (le_of_not_gt i.property) (hw i)
    simp [hi]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i)
    (fun i => ENNReal.ofReal (w i) • μ i)
  simpa only [hzero, add_zero] using h

/-- A nonnegative real matrix with probability margins induces a coupling of
those atomic probability laws. -/
theorem real_atomic_matrix_isCoupling
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hm1 : ∑ i, m i = 1)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    IsCoupling (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
      (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j))
      (atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
        (fun q => y q.1) (fun q => z q.2)) := by
  apply atomicMatchingPlan_isCoupling_of_marginal_sums
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hm i), hm1]
    exact ENNReal.ofReal_one
  · intro i
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hp i j), hrow i]
  · intro j
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i j), hcol j]

/-- The cost of any chosen optimal real matrix is exactly the squared Wasserstein
quantity of its two atomic laws. -/
theorem FiniteCoupling.IsOptimal.wasserstein_cost
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {m : ι → ℝ} {n : κ → ℝ} {y : ι → E d} {z : κ → E d}
    (hm : ∀ i, 0 ≤ m i) (hn : ∀ j, 0 ≤ n j) (hm1 : ∑ i, m i = 1)
    (hy : Function.Injective y) (hz : Function.Injective z)
    {p : ι → κ → ℝ} (hopt : FiniteCoupling.IsOptimal (fun i j => ‖y i - z j‖ ^ 2) p)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    (∑ i, ∑ j, p i j * ‖y i - z j‖ ^ 2) =
      wasserstein2 (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
        (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ^ 2 := by
  have hc := real_atomic_matrix_isCoupling m n y z hm hm1 p hopt.1 hrow hcol
  have hmin := atomicMatchingPlan_minimal_of_matrix_minimal
    (fun i => ENNReal.ofReal (m i)) (fun j => ENNReal.ofReal (n j))
    y z hy hz p hopt.1 hc (by
      intro q hq hqr hqc
      apply hopt.2 q hq
      · intro i
        rw [hrow i]
        simpa only [ENNReal.toReal_ofReal (hm i)] using hqr i
      · intro j
        rw [hcol j]
        simpa only [ENNReal.toReal_ofReal (hn j)] using hqc j)
  rw [wasserstein2_sq_eq_planCost_of_minimal hc hmin]
  exact (quadraticPlanCost_atomicMatchingPlan_ofReal_toReal p hopt.1 y z).symm

/-- The positive-pair family has the same explicit joint law as the whole matrix. -/
theorem positive_atomic_plan_eq_full
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j) (y : ι → E d) (z : κ → E d) :
    atomicMatchingPlan
      (fun q : PositiveFiniteCoupling.Pairs p => ENNReal.ofReal (p q.1.1 q.1.2))
      (fun q => y q.1.1) (fun q => z q.1.2) =
    atomicMatchingPlan (fun q : ι × κ => ENNReal.ofReal (p q.1 q.2))
      (fun q => y q.1) (fun q => z q.2) := by
  exact sum_ofReal_smul_positive_support (fun q : ι × κ => p q.1 q.2)
    (fun q => Measure.dirac (y q.1, z q.2)) (fun q => hp q.1 q.2)

/-- Endpoint atomic laws survive removal of the zero matrix entries. -/
theorem positive_atomic_marginal_laws
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hm1 : ∑ i, m i = 1)
    (p : ι → κ → ℝ) (hp : ∀ i j, 0 ≤ p i j)
    (hrow : ∀ i, ∑ j, p i j = m i) (hcol : ∀ j, ∑ i, p i j = n j) :
    (∑ q : PositiveFiniteCoupling.Pairs p,
      ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (y q.1.1)) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
    (∑ q : PositiveFiniteCoupling.Pairs p,
      ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (z q.1.2)) =
        ∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j) := by
  have hc := real_atomic_matrix_isCoupling m n y z hm hm1 p hp hrow hcol
  rw [← positive_atomic_plan_eq_full p hp y z] at hc
  exact ⟨(atomicMatchingPlan_fst _ _ _).symm.trans hc.2.1,
    (atomicMatchingPlan_snd _ _ _).symm.trans hc.2.2⟩

/-- Fully semantic positive-pair input for the moving-site stability argument:
positive normalized weights, the original endpoint laws, exact W₂ speed, and
no site collisions at interior interpolation times. -/
theorem exists_positive_atomic_coupling_data
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (m : ι → ℝ) (n : κ → ℝ) (y : ι → E d) (z : κ → E d)
    (hm : ∀ i, 0 ≤ m i) (hn : ∀ j, 0 ≤ n j)
    (hm1 : ∑ i, m i = 1) (hn1 : ∑ j, n j = 1)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    ∃ p : ι → κ → ℝ,
      (∀ q : PositiveFiniteCoupling.Pairs p, 0 < p q.1.1 q.1.2) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p, p q.1.1 q.1.2) = 1 ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (y q.1.1)) =
          (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i)) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        ENNReal.ofReal (p q.1.1 q.1.2) • Measure.dirac (z q.1.2)) =
          (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ∧
      Function.Injective (fun q : PositiveFiniteCoupling.Pairs p => (y q.1.1, z q.1.2)) ∧
      (∑ q : PositiveFiniteCoupling.Pairs p,
        p q.1.1 q.1.2 * ‖y q.1.1 - z q.1.2‖ ^ 2) =
          wasserstein2 (∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
            (∑ j, ENNReal.ofReal (n j) • Measure.dirac (z j)) ^ 2 ∧
      ∀ t : ℝ, 0 < t → t < 1 → Function.Injective
        (fun q : PositiveFiniteCoupling.Pairs p => (1-t) • y q.1.1 + t • z q.1.2) := by
  classical
  obtain ⟨p, hrow, hcol, hopt, hsum, hinj⟩ :=
    PositiveFiniteCoupling.exists_optimal_positive_pairs m n y z hm hn hm1 hn1 hy hz
  have hlaws := positive_atomic_marginal_laws m n y z hm hm1 p hopt.1 hrow hcol
  refine ⟨p, fun q => q.property, hsum, hlaws.1, hlaws.2,
    PositiveFiniteCoupling.endpoint_pairs_injective hy hz p, ?_, hinj⟩
  rw [PositiveFiniteCoupling.sum_pairs_mul p (fun i j => ‖y i - z j‖ ^ 2) hopt.1]
  exact hopt.wasserstein_cost hm hn hm1 hy hz hrow hcol

end Problem358

namespace Problem358

/-- Two finitely supported probabilities admit a common strictly positive finite
weight family. Its paired sites give the original laws, exact Wasserstein energy,
and an injective moving family at every interior interpolation time. -/
theorem exists_finite_atomic_motion
    {d : ℕ} {μ ν : Measure (E d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {F G : Set (E d)} (hF : F.Finite) (hG : G.Finite)
    (hμ : IsSupported μ F) (hν : IsSupported ν G) :
    ∃ N : ℕ, 0 < N ∧ ∃ (w : Fin N → ℝ) (y z : Fin N → E d),
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧
      (∀ i, y i ∈ F) ∧ (∀ i, z i ∈ G) ∧
      μ = (∑ i, ENNReal.ofReal (w i) • Measure.dirac (y i)) ∧
      ν = (∑ i, ENNReal.ofReal (w i) • Measure.dirac (z i)) ∧
      Function.Injective (fun i => (y i, z i)) ∧
      (∑ i, w i * ‖y i - z i‖ ^ 2) = wasserstein2 μ ν ^ 2 ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun i => (1-t) • y i + t • z i) := by
  classical
  obtain ⟨m, _, y, a, hy, hyF, ha, ha1, hμeq⟩ :=
    exists_positive_finite_atomic_presentation hF hμ
  obtain ⟨n, _, z, b, hz, hzG, hb, hb1, hνeq⟩ :=
    exists_positive_finite_atomic_presentation hG hν
  obtain ⟨p, hp, hp1, hpμ, hpν, hpair, hcost, hinj⟩ :=
    exists_positive_atomic_coupling_data a b y z (fun i => (ha i).le)
      (fun i => (hb i).le) ha1 hb1 hy hz
  let P := PositiveFiniteCoupling.Pairs p
  let e : Fin (Fintype.card P) ≃ P := (Fintype.equivFin P).symm
  have hN : 0 < Fintype.card P := by
    by_contra h
    have hzcard : Fintype.card P = 0 := by omega
    have : IsEmpty P := Fintype.card_eq_zero_iff.mp hzcard
    have hzero : (∑ q : P, p q.1.1 q.1.2) = 0 := by simp
    have : (0 : ℝ) = 1 := hzero.symm.trans hp1
    norm_num at this
  refine ⟨Fintype.card P, hN, (fun i => p (e i).1.1 (e i).1.2),
    (fun i => y (e i).1.1), (fun i => z (e i).1.2),
    (fun i => hp (e i)), ?_, (fun i => hyF _), (fun i => hzG _), ?_, ?_,
    hpair.comp e.injective, ?_, ?_⟩
  · exact (e.sum_comp (fun q : P => p q.1.1 q.1.2)).trans hp1
  · exact hμeq.trans (hpμ.symm.trans
      (e.sum_comp (fun q : P => ENNReal.ofReal (p q.1.1 q.1.2) •
        Measure.dirac (y q.1.1))).symm)
  · exact hνeq.trans (hpν.symm.trans
      (e.sum_comp (fun q : P => ENNReal.ofReal (p q.1.1 q.1.2) •
        Measure.dirac (z q.1.2))).symm)
  · calc
      _ = ∑ q : P, p q.1.1 q.1.2 * ‖y q.1.1 - z q.1.2‖ ^ 2 := e.sum_comp _
      _ = wasserstein2 μ ν ^ 2 := by simpa only [← hμeq, ← hνeq] using hcost
  · intro t ht0 ht1
    exact (hinj t ht0 ht1).comp e.injective

/-- Synchronous linear interpolation has Wasserstein speed at most its weighted
root-mean-square site velocity. No injectivity or optimality is needed here. -/
theorem wasserstein2_interpolated_atomic_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (y z : ι → E d) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (s t : ℝ) :
    wasserstein2
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-s) • y i + s • z i))
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-t) • y i + t • z i)) ≤
        |s-t| * Real.sqrt (∑ i, w i * ‖y i - z i‖ ^ 2) := by
  have hsum : (∑ i, ENNReal.ofReal (w i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1]
    exact ENNReal.ofReal_one
  have h := wasserstein2_atomic_le (fun i => ENNReal.ofReal (w i))
    (fun i => (1-s) • y i + s • z i)
    (fun i => (1-t) • y i + t • z i) hsum
  have hdiff (i : ι) :
      ((1-s) • y i + s • z i) - ((1-t) • y i + t • z i) =
        (s-t) • (z i-y i) := by module
  have henergy : (∑ i, (ENNReal.ofReal (w i)).toReal *
      ‖((1-s) • y i + s • z i) - ((1-t) • y i + t • z i)‖ ^ 2) =
      (s-t)^2 * (∑ i, w i * ‖y i-z i‖ ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_ofReal (hw i), hdiff i, norm_smul, Real.norm_eq_abs,
      norm_sub_rev, mul_pow, sq_abs]
    ring
  rw [henergy, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs] at h
  exact h

/-- In particular, an optimal endpoint pairing gives a constant upper speed
in terms of the exact endpoint Wasserstein distance. -/
theorem wasserstein2_interpolated_atomic_le_of_energy
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (y z : ι → E d) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) {μ ν : Measure (E d)}
    (henergy : (∑ i, w i * ‖y i-z i‖ ^ 2) = wasserstein2 μ ν ^ 2)
    (s t : ℝ) :
    wasserstein2
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-s) • y i + s • z i))
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-t) • y i + t • z i)) ≤
        |s-t| * wasserstein2 μ ν := by
  have h := wasserstein2_interpolated_atomic_le w y z hw hw1 s t
  rwa [henergy, Real.sqrt_sq (wasserstein2_nonneg μ ν)] at h

/-- Those interpolated laws remain probabilities for every real time. -/
theorem interpolated_atomic_isProbability
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (y z : ι → E d) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (t : ℝ) :
    IsProbabilityMeasure
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-t) • y i + t • z i)) := by
  constructor
  have hsum : (∑ i, ENNReal.ofReal (w i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i), hw1]
    exact ENNReal.ofReal_one
  simpa using hsum

/-- On the unit time interval, the whole atomic motion stays in any convex set
containing both endpoint site families. -/
theorem interpolated_atomic_supported
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (y z : ι → E d) {Y : Set (E d)} (hY : Convex ℝ Y)
    (hy : ∀ i, y i ∈ Y) (hz : ∀ i, z i ∈ Y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsSupported
      (∑ i, ENNReal.ofReal (w i) • Measure.dirac ((1-t) • y i + t • z i)) Y := by
  have hsite (i : ι) : (1-t) • y i + t • z i ∈ Y :=
    hY (hy i) (hz i) (sub_nonneg.mpr ht1) ht0 (sub_add_cancel 1 t)
  simp [IsSupported, Measure.finsetSum_apply, Measure.smul_apply, hsite]

end Problem358

end

end OAI
