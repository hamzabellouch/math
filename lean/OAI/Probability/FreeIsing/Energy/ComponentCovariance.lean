import OAI.Probability.FreeIsing.Estimates.ComponentPairCount
import OAI.Probability.FreeIsing.Estimates.PairCorrelation

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem367

theorem componentWordDistance_eq_reducedWordDistance {α : Type*} [DecidableEq α]
    (u v : List α) : componentWordDistance u v = reducedWordDistance u v := by
  induction u generalizing v with
  | nil => rfl
  | cons a u ih =>
    cases v with
    | nil => rfl
    | cons b v =>
      by_cases hab : a = b <;> simp [componentWordDistance, reducedWordDistance, hab, ih]

def componentVertex {d n : ℕ} {c : Fin d} (u : ReducedTail c n) : TreeVertex d :=
  ⟨c :: u.1, u.2.2⟩

theorem componentVertex_injective {d n : ℕ} {c : Fin d} :
    Function.Injective (componentVertex : ReducedTail c n → TreeVertex d) := by
  intro u v h
  apply Subtype.ext
  exact (List.cons.inj (congrArg Subtype.val h)).2

theorem HasFreeIsingLaw.component_pair_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {c : Fin d} {k l : ℕ} (u : ReducedTail c k) (v : ReducedTail c l) :
    (∫ x, spinSign (x (componentVertex u)) * spinSign (x (componentVertex v)) ∂mu) =
      theta ^ componentWordDistance u.1 v.1 := by
  rw [hmu.pair_correlation hlo hhi]
  simp [componentVertex, componentWordDistance_eq_reducedWordDistance]

theorem HasFreeIsingLaw.component_level_covariance_critical {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k l : ℕ) :
    (∑ u : ReducedTail c k, ∑ v : ReducedTail c l, theta ^ k * theta ^ l *
      (∫ x, spinSign (x (componentVertex u)) * spinSign (x (componentVertex v)) ∂mu)) =
      1 + (min k l : ℕ) * (1 - theta ^ 2) := by
  simp_rw [hmu.component_pair_correlation hlo hhi]
  exact sum_component_weighted_correlation_critical theta c hcritical k l

theorem HasFreeIsingLaw.component_covariance_sum_critical_le {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
      ∑ u : ReducedTail c k, ∑ v : ReducedTail c l, theta ^ k * theta ^ l *
        (∫ x, spinSign (x (componentVertex u)) * spinSign (x (componentVertex v)) ∂mu)) ≤
      (n + 1 : ℝ) ^ 3 := by
  simp_rw [hmu.component_pair_correlation hlo hhi]
  exact sum_component_weighted_correlation_critical_le theta c hcritical n

theorem HasFreeIsingLaw.component_root_correlation {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    {c : Fin d} {k : ℕ} (u : ReducedTail c k) :
    (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
      spinSign (x (componentVertex u)) ∂mu) = theta ^ k := by
  rw [hmu.pair_correlation hlo hhi]
  simp only [componentVertex, reducedWordDistance_cons_same, reducedWordDistance_nil_left, u.2.1]

theorem HasFreeIsingLaw.component_level_signal_critical {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (k : ℕ) :
    (∑ u : ReducedTail c k, theta ^ k *
      (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
        spinSign (x (componentVertex u)) ∂mu)) = 1 := by
  simp_rw [hmu.component_root_correlation hlo hhi]
  have hlen (u : ReducedTail c k) : u.1.length = k := u.2.1
  simpa only [hlen, pow_two] using sum_component_radial_sq_critical theta c hcritical k

theorem HasFreeIsingLaw.component_signal_critical {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), ∑ u : ReducedTail c k, theta ^ k *
      (∫ x, spinSign (x ⟨[c], List.IsChain.singleton c⟩) *
        spinSign (x (componentVertex u)) ∂mu)) = (n + 1 : ℝ) := by
  simp [hmu.component_level_signal_critical hlo hhi c hcritical]

def componentIndexedVertex {d : ℕ} {c : Fin d}
    (u : Σ k : ℕ, ReducedTail c k) : TreeVertex d := componentVertex u.2

theorem componentIndexedVertex_injective {d : ℕ} {c : Fin d} :
    Function.Injective (componentIndexedVertex (c := c)) := by
  rintro ⟨k, u⟩ ⟨l, v⟩ h
  have hw : u.1 = v.1 := (List.cons.inj (congrArg Subtype.val h)).2
  have hkl : k = l := by rw [← u.2.1, ← v.2.1, hw]
  subst l
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hw))

def componentIndexFinset {d : ℕ} (c : Fin d) (n : ℕ) :
    Finset (Σ k : ℕ, ReducedTail c k) :=
  (Finset.range (n + 1)).sigma (fun _ => Finset.univ)

theorem sum_componentIndexFinset {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (n : ℕ) (f : (Σ k : ℕ, ReducedTail c k) → M) :
    (∑ s ∈ componentIndexFinset c n, f s) =
      ∑ k ∈ Finset.range (n + 1), ∑ u : ReducedTail c k, f ⟨k, u⟩ := by
  rw [componentIndexFinset, Finset.sum_sigma]

theorem sum_componentIndexFinset_pair {M : Type*} [AddCommMonoid M]
    {d : ℕ} (c : Fin d) (n : ℕ)
    (f : (Σ k : ℕ, ReducedTail c k) → (Σ k : ℕ, ReducedTail c k) → M) :
    (∑ u ∈ componentIndexFinset c n, ∑ v ∈ componentIndexFinset c n, f u v) =
      ∑ k ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        ∑ u : ReducedTail c k, ∑ v : ReducedTail c l, f ⟨k, u⟩ ⟨l, v⟩ := by
  simp_rw [sum_componentIndexFinset]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

end Problem367

end

end OAI
