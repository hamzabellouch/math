import OAI.Probability.DilutedSpin.FiniteProjection
import OAI.Probability.DilutedSpin.HeterogeneousVariance

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {Ω I X : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace X] {L : ℕ}

theorem root_uniform_bound (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (hm : ∀ j, 0 < m j) (base : FinitePath Ω L → ℝ)
    {n : ℕ} (roots : Fin n → I)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) {B C : ℝ}
    (hb : ∀ y, |base y| ≤ B) (hf : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |root T Q m base roots factor| ≤ B+C*n := by
  have hh := KernelTower.backwardLog_stability L T m hm
    (f := base) (g := fun _ => 0) (by simpa only [sub_zero] using hb)
  rw [KernelTower.backwardLog_const L T m (fun j => ne_of_gt (hm j)) 0, sub_zero] at hh
  exact (abs_root_le T Q m hm base roots factor hf).trans (add_le_add hh le_rfl)

theorem measurable_root (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ) {n : ℕ} (roots : Fin n → I)
    (factor : X → (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (hf : ∀ i y z, Measurable (fun x => factor x i y z)) :
    Measurable (fun x => root T Q m (base x) roots (factor x)) := by
  apply KernelTower.measurable_backwardLog
  intro y
  exact (hb _).add (Finset.measurable_sum _ (fun j _ => (hf _ _ _).log))

theorem measurable_root_base [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i))
    (m : Fin L → ℝ) (base : X → FinitePath Ω L → ℝ)
    (hb : ∀ y, Measurable (fun x => base x y))
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) (n : ℕ) :
    Measurable (fun z : X × RootPath I n => root T Q m (base z.1) (rootArray n z.2) factor) := by
  apply measurable_from_prod_countable_left
  intro roots
  exact measurable_root T Q m base (rootArray n roots) (fun _ => factor) hb
    (fun _ _ _ => measurable_const)

end DilutedSpinGlass.HeterogeneousMarks
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Coordinatewise pushforwards tensorize even for tests that do not factor. -/
theorem Projects.pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {P : (i : ι) → FiniteLaw (α i)} {Q : (i : ι) → FiniteLaw (β i)}
    {π : (i : ι) → α i → β i} (h : ∀ i, Projects (P i) (Q i) (π i)) :
    Projects (FiniteLaw.pi P) (FiniteLaw.pi Q) (fun x i => π i (x i)) := by
  intro f
  have hh := expect_pi_weighted_map P Q π (fun _ _ => 1) (fun _ _ => 1)
    (fun i g => by simpa only [one_mul] using h i g) f
  simpa only [Finset.prod_const_one,mul_one] using hh

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.SizeCoupling
open scoped BigOperators

/-- Choose a potential new index uniformly and an independent old fallback.
Only the zero new index uses the fallback; all other old indices coincide. -/
noncomputable def indexLaw (N : ℕ) [NeZero N] : FiniteLaw (Fin (N+1) × Fin N) :=
  FiniteLaw.uniform.bind (fun _ => FiniteLaw.uniform)

def oldIndex {N : ℕ} (z : Fin (N+1) × Fin N) : Fin N := Fin.cases z.2 (fun i => i) z.1

def newIndex {N : ℕ} (z : Fin (N+1) × Fin N) : Fin (N+1) := z.1

theorem oldIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform oldIndex := by
  intro f
  unfold indexLaw
  rw [FiniteLaw.expect_bind,FiniteLaw.uniform_expect,Fin.sum_univ_succ]
  simp only [oldIndex, Fin.cases_zero, Fin.cases_succ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  change ((FiniteLaw.uniform : FiniteLaw (Fin N)).expect f+
    ∑ i, (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun _ => f i))/(N+1) = _
  simp only [FiniteLaw.expect_const,FiniteLaw.uniform_expect,Fintype.card_fin]
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : (N:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

theorem newIndex_projects (N : ℕ) [NeZero N] :
    (indexLaw N).Projects FiniteLaw.uniform newIndex := by
  intro f
  simp only [indexLaw,FiniteLaw.expect_bind,newIndex,FiniteLaw.expect_const]

/-- The exact probability of changing a site is 1/(N+1). -/
theorem newIndex_probability (N : ℕ) [NeZero N] :
    (indexLaw N).expect (fun z => if z.1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
  calc
    _ = (FiniteLaw.uniform : FiniteLaw (Fin (N+1))).expect
        (fun j => if j = 0 then (1:ℝ) else 0) :=
      newIndex_projects N (fun j => if j = 0 then (1:ℝ) else 0)
    _ = _ := by rw [FiniteLaw.uniform_expect]; simp

lemma same_index_off_new {N : ℕ} (z : Fin (N+1) × Fin N) (hz : z.1 ≠ 0) :
    (oldIndex z).succ = newIndex z := by
  rcases z with ⟨j,i⟩
  induction j using Fin.cases with
  | zero => exact (hz rfl).elim
  | succ j => rfl

theorem expected_new_count (N p : ℕ) [NeZero N] :
    (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
      (fun z => ∑ j, if (z j).1 = 0 then (1:ℝ) else 0) = (p:ℝ)/(N+1) := by
  rw [FiniteLaw.expect_fintype_sum]
  have hm (j : Fin p) :
      (FiniteLaw.pi (fun _ : Fin p => indexLaw N)).expect
        (fun z => if (z j).1 = 0 then (1:ℝ) else 0) = 1/(N+1) := by
    exact (FiniteLaw.expect_pi_marginal (fun _ : Fin p => indexLaw N) j
      (fun z => if z.1 = 0 then (1:ℝ) else 0)).trans (newIndex_probability N)
  simp only [hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end DilutedSpinGlass.SizeCoupling
end

end

end OAI
