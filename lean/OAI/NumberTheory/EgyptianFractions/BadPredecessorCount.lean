import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- An indexed bipartite degree count. Repeated values of the maps retain
separate indices in `I`, exactly as required by the divisor descent. -/
theorem indexed_predecessor_count
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (U : Finset α) (H : Finset β) (I : Finset ι)
    (r : ι → α → β) (w : ι → β → ℝ) (L : ℝ) (hL : 0 < L)
    (hleft : ∀ u ∈ U, L ≤ ((I.filter (fun i => r i u ∈ H)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ H,
      ((U.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (U.card : ℝ) ≤ (∑ i ∈ I, ∑ h ∈ H, w i h) / L := by
  classical
  have hswap : (∑ u ∈ U, (I.filter (fun i => r i u ∈ H)).card) =
      ∑ i ∈ I, (U.filter (fun u => r i u ∈ H)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  apply (le_div_iff₀ hL).2
  calc
    (U.card : ℝ) * L = ∑ _u ∈ U, L := by simp
    _ ≤ ∑ u ∈ U, ((I.filter (fun i => r i u ∈ H)).card : ℝ) :=
      Finset.sum_le_sum hleft
    _ = ∑ i ∈ I, ((U.filter (fun u => r i u ∈ H)).card : ℝ) := by
      exact_mod_cast hswap
    _ = ∑ i ∈ I, ∑ h ∈ H, ((U.filter (fun u => r i u = h)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact_mod_cast (Finset.sum_card_fiberwise_eq_card_filter U H (r i)).symm
    _ ≤ ∑ i ∈ I, ∑ h ∈ H, w i h := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hright i hi))

/-- The degree count with an inherited set and an exceptional set removed. -/
theorem indexed_predecessor_count_with_exceptions
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (S E B U : Finset α) (H : Finset β) (I : Finset ι)
    (r : ι → α → β) (w : ι → β → ℝ) (L : ℝ) (hL : 0 < L)
    (hcover : S ⊆ E ∪ B ∪ U)
    (hleft : ∀ u ∈ U, L ≤ ((I.filter (fun i => r i u ∈ H)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ H,
      ((U.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (S.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) +
      (∑ i ∈ I, ∑ h ∈ H, w i h) / L := by
  have hcard : S.card ≤ E.card + B.card + U.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (E ∪ B) U
    have h3 := Finset.card_union_le E B
    omega
  have hcardR : (S.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast hcard
  have hU := indexed_predecessor_count U H I r w L hL hleft hright
  linarith

/-- The exact finite combinatorial inequality used to propagate bad numerators.
`H` is the current bad set, `Hnext` the next bad set, and `E` the Fourier
exception set. Fibers may be bounded by truncated divisor counts. -/
theorem descent_bad_predecessor_count
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (Y : ℝ) (ρ : ℝ)
    (r : ι → ℕ → ℕ) (w : ι → ℕ → ℝ)
    (hρ : 0 < ρ) (hI : I.Nonempty)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / 2 ≤ ((I.filter (fun i => r i u ∈ Hnext)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ Hnext,
      ((H.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (2 / (ρ * (I.card : ℝ))) * (∑ i ∈ I, ∑ h ∈ Hnext, w i h) := by
  classical
  let U := H.filter (fun u => u ∉ E ∧ Y < (u : ℝ))
  have hIpos : (0 : ℝ) < (I.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hL : 0 < ρ * (I.card : ℝ) / 2 := by positivity
  have hcover : H ⊆ E ∪ Hnext ∪ U := by
    intro u hu
    by_cases huE : u ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ huE)
    · by_cases huY : (u : ℝ) ≤ Y
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hinherit u hu huY))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, huE, lt_of_not_ge huY⟩)
  have h := indexed_predecessor_count_with_exceptions H E Hnext U Hnext I r w
    (ρ * (I.card : ℝ) / 2) hL hcover
    (fun u hu => by
      obtain ⟨huH, huE, huY⟩ := Finset.mem_filter.mp hu
      exact hleft u huH huE huY)
    (fun i hi h hh => by
      have hsub : U.filter (fun u => r i u = h) ⊆ H.filter (fun u => r i u = h) := by
        intro u hu
        obtain ⟨huU, hur⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huU).1, hur⟩
      have hcard : ((U.filter (fun u => r i u = h)).card : ℝ) ≤
          ((H.filter (fun u => r i u = h)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hright i hi h hh))
  convert h using 1; ring


/-- A fiber of a residue map consists of divisors of the shifted numerator. -/
theorem predecessor_fiber_le_divisors
    (H : Finset ℕ) (X : ℝ) (N h : ℕ) (r : ℕ → ℕ)
    (hN : 0 < N) (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hdiv : ∀ u ∈ H, u ∣ N + r u) :
    (H.filter (fun u => r u = h)).card ≤
      ((N + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card := by
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huH, hur⟩ := Finset.mem_filter.mp hu
  apply Finset.mem_filter.mpr
  constructor
  · apply Nat.mem_divisors.mpr
    constructor
    · simpa only [hur] using hdiv u huH
    · omega
  · exact hX u huH

/-- The manuscript's bad-pair inequality, with actual truncated divisor counts. -/
theorem descent_bad_predecessor_divisor_count
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (X Y ρ : ℝ)
    (r : ι → ℕ → ℕ) (N : ι → ℕ)
    (hρ : 0 < ρ) (hI : I.Nonempty)
    (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hN : ∀ i ∈ I, 0 < N i)
    (hdiv : ∀ i ∈ I, ∀ u ∈ H, u ∣ N i + r i u)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / 2 ≤ ((I.filter (fun i => r i u ∈ Hnext)).card : ℝ)) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (2 / (ρ * (I.card : ℝ))) *
        (∑ i ∈ I, ∑ h ∈ Hnext,
          (((N i + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)) := by
  apply descent_bad_predecessor_count H Hnext E I Y ρ r _ hρ hI hinherit hleft
  intro i hi h hh
  exact_mod_cast predecessor_fiber_le_divisors H X (N i) h (r i)
    (hN i hi) hX (hdiv i hi)

end Problem337

end

end OAI
