import OAI.Probability.DilutedSpin.CompoundPhysicalMean
import OAI.Probability.DilutedSpin.RootProductLaw
import OAI.Probability.DilutedSpin.SpinMarginal

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open KernelTower SizeCoupling
open scoped BigOperators
variable {I : Type} {A : I → Type} [∀ i,Fintype (A i)] {N k L : ℕ} [NeZero N]

omit [NeZero N] in
/-- Move only perturbation sites off the added spin, leaving energy and all
auxiliary mark labels and count laws unchanged. -/
lemma terminalRoot_mark_sites
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D)
    (z : Fin k → Fin (N+1) × Fin N) :
    |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a) -
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id
        (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)| ≤
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
  have h := root_factor_stability (terminalTower (fun _ : Fin (N+1) => false)
    FiniteLaw.uniform L) (fun j : Fin k => Q (roots j)) m hm
    (fun y => E (terminalState L y)) id
    (fun j y a => ψ (roots j) (terminalState L y (newIndex (z j))) a)
    (fun j y a => ψ (roots j) (terminalState L y (oldIndex (z j)).succ) a)
    (fun j => if (z j).1=0 then 2*D else 0) (by
      intro j y a
      by_cases hj : (z j).1=0
      · simp only [hj,↓reduceIte]
        have h1 := hψ (roots j) (terminalState L y (newIndex (z j))) a
        have h2 := hψ (roots j) (terminalState L y (oldIndex (z j)).succ) a
        exact (abs_sub _ _).trans (by linarith)
      · simp only [hj,↓reduceIte,same_index_off_new (z j) hj,sub_self,abs_zero,le_refl])
  have he : (∑ j : Fin k,if (z j).1=0 then 2*D else 0) =
      2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0) := by
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero]
  exact h.trans_eq he

lemma terminalRoot_mark_site_expect
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (hm : ∀ j,0 < m j) (E : (Fin (N+1) → Spin) → ℝ) (roots : Fin k → I)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {D : ℝ} (hψ : ∀ i s a,|Real.log (ψ i s a)|≤D) :
    |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin (N+1))))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)) -
      (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin N)))).expect
        (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
          (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a))| ≤
      2*D*k/(N+1) := by
  let R := FiniteLaw.pi (fun _ : Fin k => indexLaw N)
  have hn := FiniteLaw.Projects.pi (fun _ : Fin k => newIndex_projects N)
  have ho := FiniteLaw.Projects.pi (fun _ : Fin k => oldIndex_projects N)
  rw [← hn (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j)) a)),
    ← ho (fun sites => terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
      (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (sites j).succ) a)),
    ← FiniteLaw.expect_sub]
  calc
    _ ≤ R.expect (fun z => |terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (newIndex (z j))) a)-
      terminalRoot (fun _ : Fin (N+1) => false) FiniteLaw.uniform
        (fun j : Fin k => Q (roots j)) m E id (fun j σ a => ψ (roots j) (σ (oldIndex (z j)).succ) a)|) :=
      FiniteLaw.abs_expect_le_expect_abs R _
    _ ≤ R.expect (fun z => 2*D*(∑ j,if (z j).1=0 then (1:ℝ) else 0)) :=
      R.expect_mono (terminalRoot_mark_sites Q m hm E roots ψ hψ)
    _ = _ := by rw [FiniteLaw.expect_mul_left,expected_new_count]; ring

end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

noncomputable def indexedPotential (theta : X → InteractionSample p)
    (z : X × (Fin p → Fin N)) (σ : Fin N → Spin) : ℝ :=
  (theta z.1).1 (fun j => σ (z.2 j))

noncomputable def locatedFactor
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (i : I × Fin N) (y : FinitePath (Fin N → Spin) (L+1))
    (a : FinitePath (A i.1) (L+1)) : ℝ := ψ i.1 (terminalState L y i.2) a

lemma measurable_indexedPotential (theta : X → InteractionSample p)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (indexedPotential (N := N) theta) := by
  apply Measurable.of_eval
  intro σ
  apply measurable_from_prod_countable_left
  intro j
  simpa only [indexedPotential] using hθ (fun q => σ (j q))

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable I] [MeasurableSpace I]
  [MeasurableSingletonClass I] in
lemma rootSample_eq_spinRoot
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (h : RootPath Y N) (k : ℕ) (x : RootPath (X × (Fin p → Fin N)) k)
    (l : ℕ) (a : RootPath (I × Fin N) l) :
    rootSample (indexedPotential theta) field (fun i : I × Fin N => Q i.1)
      m (locatedFactor ψ) h k x l a =
    SizeCoupling.spinRoot (fun j => Q (rootArray l a j).1) m
      (fun j => theta (rootArray k x j).1) (fun i => field (rootArray N h i))
      (fun j => (rootArray k x j).2) (fun j => (rootArray l a j).2)
      (fun j => ψ (rootArray l a j).1) := by
  unfold rootSample SizeCoupling.spinRoot
  have he := root_pullback (fun j : Fin l => rootArray l a j) id
    (terminalTower (fun _ : Fin N => false) FiniteLaw.uniform L)
    (fun i : I × Fin N => Q i.1) m
    (fun y => energy (indexedPotential theta) field h k x (terminalState L y))
    (locatedFactor ψ)
  convert he.symm using 1 <;> rfl

end DilutedSpinGlass.PhysicalRoot

end

end OAI
