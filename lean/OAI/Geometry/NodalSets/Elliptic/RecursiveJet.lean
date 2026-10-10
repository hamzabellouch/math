import OAI.Geometry.NodalSets.Elliptic.DirectionalJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
abbrev CPoly := MvPolynomial (Fin 4) ℂ
abbrev Jet := ℕ → CPoly

theorem finite_triangular_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (lower : ℕ → Jet → CPoly)
    (hlower : ∀ n a, (lower n a).IsHomogeneous n)
    (hcausal : ∀ n a b, (∀ k, k ≤ n → a k = b k) → lower n a = lower n b)
    (initial : Jet) (hinitial : ∀ k, (initial k).IsHomogeneous k)
    (base steps : ℕ) :
    ∃ a : Jet, (∀ k, (a k).IsHomogeneous k) ∧
      (∀ k, k ≤ base → a k = initial k) ∧
      ∀ n, base ≤ n → n < base + steps →
        direction v (a (n + 1)) + lower n a = 0 := by
  induction steps with
  | zero => exact ⟨initial, hinitial, fun _ _ ↦ rfl, by omega⟩
  | succ steps ih =>
    obtain ⟨a, ha, hkeep, hsolve⟩ := ih
    let n := base + steps
    obtain ⟨q, hq, hdq⟩ := complex_directional_primitive v hv (hlower n a).neg
    let b : Jet := Function.update a (n + 1) q
    have heq (k : ℕ) (hk : k ≤ n) : b k = a k := by
      exact Function.update_of_ne (by omega) _ _
    refine ⟨b, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = n + 1
      · subst k; simpa [b] using hq
      · simpa [b, Function.update_of_ne hk] using ha k
    · intro k hk
      exact (heq k (by dsimp [n]; omega)).trans (hkeep k hk)
    · intro r hr hrbound
      by_cases hrn : r = n
      · subst r
        rw [hcausal n b a heq]
        simp [b, hdq]
      · have hrlt : r < n := by dsimp [n] at *; omega
        rw [heq (r + 1) (by omega), hcausal r b a (fun k hk ↦ heq k (by omega))]
        exact hsolve r hr hrlt

def gradientJet (v : Fin 4 → ℂ) (a : Jet) (k : ℕ) (i : Fin 4) : CPoly :=
  if k = 0 then C (v i) else pderiv i (a (k + 1))

lemma gradientJet_congr (v : Fin 4 → ℂ) {a b : Jet} {k n : ℕ}
    (hk : k ≤ n) (h : ∀ j, j ≤ n + 1 → a j = b j) (i : Fin 4) :
    gradientJet v a k i = gradientJet v b k i := by
  unfold gradientJet
  split_ifs
  · rfl
  · rw [h (k + 1) (by omega)]

def eikonalKnown (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a : Jet) : CPoly :=
  (∑ t ∈ Finset.range n, ∑ i,
    gradientJet v a (t + 1) i * gradientJet v a (n - t) i) +
  ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
    g (r + 1) i j * gradientJet v a t i * gradientJet v a (n - r - t) j

def eikonalCoefficient (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a : Jet) : CPoly :=
  homogeneousComponent (n + 1)
    ((∑ t ∈ Finset.range (n + 2), ∑ i,
      gradientJet v a t i * gradientJet v a (n + 1 - t) i) +
    ∑ r ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1 - r), ∑ i, ∑ j,
      g (r + 1) i j * gradientJet v a t i * gradientJet v a (n - r - t) j)

lemma eikonalKnown_congr (v : Fin 4 → ℂ) (g : ℕ → Fin 4 → Fin 4 → CPoly)
    (n : ℕ) (a b : Jet) (h : ∀ k, k ≤ n + 1 → a k = b k) :
    eikonalKnown v g n a = eikonalKnown v g n b := by
  unfold eikonalKnown
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i _
    rw [gradientJet_congr v (by have := Finset.mem_range.mp ht; omega) h,
      gradientJet_congr v (Nat.sub_le _ _) h]
  · apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [gradientJet_congr v (by have := Finset.mem_range.mp ht; omega) h,
      gradientJet_congr v (by omega) h]

lemma direction_apply (v : Fin 4 → ℂ) (p : CPoly) :
    direction v p = ∑ i, C (v i) * pderiv i p := by
  rw [direction_eq_sum]
  have hs (s : Finset (Fin 4)) :
      (∑ i ∈ s, v i • pderiv (R := ℂ) i) p =
        ∑ i ∈ s, C (v i) * pderiv i p := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp [Finset.sum_insert, hi, Derivation.smul_apply,
        Algebra.smul_def, ih]
  exact hs _

lemma direction_two (v : Fin 4 → ℂ) (p : CPoly) :
    direction (fun i ↦ 2 * v i) p = 2 * ∑ i, C (v i) * pderiv i p := by
  rw [direction_apply]
  simp only [map_mul, map_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eikonalCoefficient_split (v : Fin 4 → ℂ)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (n : ℕ) (a : Jet) :
    eikonalCoefficient v g n a = homogeneousComponent (n + 1)
      (direction (fun i ↦ 2 * v i) (a (n + 2)) + eikonalKnown v g n a) := by
  unfold eikonalCoefficient eikonalKnown
  apply congrArg (homogeneousComponent (n + 1))
  rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ',
    Finset.sum_range_succ]
  simp only [Nat.sub_zero, gradientJet, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ite_false]
  rw [direction_two]
  simp only [Nat.add_sub_add_right, Nat.sub_self, ite_true]
  have hc : (∑ i : Fin 4, pderiv i (a (n + 1 + 1)) * C (v i)) =
      ∑ i : Fin 4, C (v i) * pderiv i (a (n + 1 + 1)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hc]
  ring

lemma pderiv_homogeneous {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous (n + 1))
    (i : Fin 4) : (pderiv i p).IsHomogeneous n := by
  intro d hd
  rw [coeff_pderiv] at hd
  have hc : p.coeff (d + Finsupp.single i 1) ≠ 0 := by
    intro h; simp [h] at hd
  have h := hp hc
  simpa [map_add, Finsupp.weight_single] using h

lemma direction_homogeneous (v : Fin 4 → ℂ) {p : CPoly} {n : ℕ}
    (hp : p.IsHomogeneous (n + 1)) : (direction v p).IsHomogeneous n := by
  rw [direction_apply]
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_C _ (v i)).mul (pderiv_homogeneous hp i)

theorem finite_eikonal_jets (v : Fin 4 → ℂ) (hv : v ≠ 0)
    (g : ℕ → Fin 4 → Fin 4 → CPoly) (initial : Jet)
    (hi : ∀ k, (initial k).IsHomogeneous k) (steps : ℕ) :
    ∃ a : Jet, (∀ k, (a k).IsHomogeneous k) ∧
      (∀ k, k ≤ 2 → a k = initial k) ∧
      ∀ n, 1 ≤ n → n < 1 + steps → eikonalCoefficient v g n a = 0 := by
  have hv2 : (fun i ↦ 2 * v i) ≠ (0 : Fin 4 → ℂ) := by
    intro h
    apply hv
    funext i
    have := congrFun h i
    simpa using this
  let lower : ℕ → Jet → CPoly := fun n a ↦
    homogeneousComponent n (eikonalKnown v g (n - 1) a)
  have hl : ∀ n a, (lower n a).IsHomogeneous n :=
    fun n a ↦ homogeneousComponent_isHomogeneous _ _

  let low : ℕ → Jet → CPoly := fun n a ↦ if n = 0 then 0 else lower n a
  have hlow : ∀ n a, (low n a).IsHomogeneous n := by
    intro n a; dsimp [low]; split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact hl n a
  have hc : ∀ n a b, (∀ k, k ≤ n → a k = b k) → low n a = low n b := by
    intro n a b h
    dsimp [low, lower]
    split_ifs with hn
    · rfl
    · rw [eikonalKnown_congr v g (n - 1) a b (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h)]
  obtain ⟨a, ha, hkeep, hsolve⟩ := finite_triangular_jets
    (fun i ↦ 2 * v i) hv2 low hlow hc initial hi 2 steps
  refine ⟨a, ha, hkeep, ?_⟩
  intro n hn hnb
  rw [eikonalCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha (n + 2)))]
  simpa [low, lower] using hsolve (n + 1) (by omega) (by omega)

end
end Yau.Jets

end OAI
