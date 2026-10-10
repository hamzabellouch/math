import OAI.Geometry.NodalSets.Elliptic.UniformRecursiveJet
import OAI.Geometry.NodalSets.Waves.FiniteWaveJet

namespace OAI

namespace Yau.Jets
open MvPolynomial
noncomputable section
variable {T : Type*} [TopologicalSpace T]

lemma gradientJet_family (v : T → Fin 4 → ℂ) (hv : ∀ i, Continuous (fun t ↦ v t i))
    (a : T → Jet) (ha : ∀ k, ContinuousPolyFamily (fun t ↦ a t k)) (k : ℕ) (i : Fin 4) :
    ContinuousPolyFamily (fun t ↦ gradientJet (v t) (a t) k i) := by
  unfold gradientJet
  split_ifs
  · exact ContinuousPolyFamily.C (hv i)
  · exact (ha _).pderiv i

lemma eikonalKnown_family (v : T → Fin 4 → ℂ) (hv : ∀ i, Continuous (fun t ↦ v t i))
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (a : T → Jet) (ha : ∀ k, ContinuousPolyFamily (fun t ↦ a t k)) (n : ℕ) :
    ContinuousPolyFamily (fun t ↦ eikonalKnown (v t) (g t) n (a t)) := by
  unfold eikonalKnown
  apply ContinuousPolyFamily.add
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro i _
    exact (gradientJet_family v hv a ha _ i).mul (gradientJet_family v hv a ha _ i)
  · apply ContinuousPolyFamily.sum
    intro r _
    apply ContinuousPolyFamily.sum
    intro u _
    apply ContinuousPolyFamily.sum
    intro i _
    apply ContinuousPolyFamily.sum
    intro j _
    exact ((hg _ i j).mul (gradientJet_family v hv a ha _ i)).mul
      (gradientJet_family v hv a ha _ j)

theorem finite_eikonal_jets_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k)) (steps : ℕ) :
    ∃ a : T → Jet,
      (∀ t k, (a t k).IsHomogeneous k) ∧
      (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) ∧
      (∀ t k, k ≤ 2 → a t k = initial t k) ∧
      ∀ t n, 1 ≤ n → n < 1 + steps → eikonalCoefficient (v t) (g t) n (a t) = 0 := by
  let low : T → ℕ → Jet → CPoly := fun t n a ↦
    if n = 0 then 0 else homogeneousComponent n (eikonalKnown (v t) (g t) (n - 1) a)
  have hlow : ∀ t n a, (low t n a).IsHomogeneous n := by
    intro t n a
    dsimp [low]
    split_ifs
    · exact isHomogeneous_zero _ _ _
    · exact homogeneousComponent_isHomogeneous _ _
  have hcausal : ∀ t n a b, (∀ k, k ≤ n → a k = b k) → low t n a = low t n b := by
    intro t n a b h
    dsimp [low]
    split_ifs with hn
    · rfl
    · rw [eikonalKnown_congr (v t) (g t) (n - 1) a b
        (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ n)] using h)]
  have hlc : ∀ n (a : T → Jet), (∀ k, ContinuousPolyFamily (fun t ↦ a t k)) →
      ContinuousPolyFamily (fun t ↦ low t n (a t)) := by
    intro n a ha
    dsimp [low]
    split_ifs
    · exact .const _
    · exact (eikonalKnown_family v hv g hg a ha _).homogeneousComponent n
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ := finite_triangular_jets_continuous
    (fun t j ↦ 2 * v t j) (fun j ↦ continuous_const.mul (hv j))
    i (fun t ↦ mul_ne_zero (by norm_num) (hi t)) low hlow hcausal hlc
    initial hinitial hic 2 steps
  refine ⟨a, ha, hac, hkeep, ?_⟩
  intro t n hn hnb
  rw [eikonalCoefficient_split, map_add,
    homogeneousComponent_eq_self (direction_homogeneous _ (ha t (n + 2)))]
  simpa [low] using hsolve t (n + 1) (by omega) (by omega)

theorem finite_eikonal_polynomial_continuous
    (v : T → Fin 4 → ℂ) (hv : ∀ j, Continuous (fun t ↦ v t j))
    (i : Fin 4) (hi : ∀ t, v t i ≠ 0)
    (g : T → ℕ → Fin 4 → Fin 4 → CPoly)
    (hg : ∀ r i j, ContinuousPolyFamily (fun t ↦ g t r i j))
    (initial : T → Jet) (hinitial : ∀ t k, (initial t k).IsHomogeneous k)
    (hic : ∀ k, ContinuousPolyFamily (fun t ↦ initial t k))
    (hsecond : ∀ t, eikonalCoefficient (v t) (g t) 0 (initial t) = 0) (steps : ℕ) :
    ∃ p : T → CPoly, ContinuousPolyFamily p ∧
      (∀ t k, k ≤ 2 → polynomialJet (p t) k = initial t k) ∧
      (∀ t k, steps + 2 < k → polynomialJet (p t) k = 0) ∧
      (∀ t n, n ≤ steps → eikonalCoefficient (v t) (g t) n (polynomialJet (p t)) = 0) ∧
      ∀ (s : Set T), IsCompact s → ∀ R k, ∃ C > 0, ∀ t ∈ s, ∀ x : Coord,
        ‖x‖ ≤ R → ‖iteratedFDeriv ℝ k (reval (p t)) x‖ ≤ C := by
  obtain ⟨a, ha, hac, hkeep, hsolve⟩ :=
    finite_eikonal_jets_continuous v hv i hi g hg initial hinitial hic steps
  have hpc : ContinuousPolyFamily (fun t ↦ truncateJet (a t) (steps + 2)) :=
    ContinuousPolyFamily.sum _ (fun k _ ↦ hac k)
  refine ⟨fun t ↦ truncateJet (a t) (steps + 2), hpc, ?_, ?_, ?_,
    fun s hs R k ↦ hpc.uniform_derivative_bound s hs R k⟩
  · intro t k hk
    rw [polynomialJet_truncate_eq (a t) (ha t) _ _ (by omega), hkeep t k hk]
  · intro t k hk
    simp [polynomialJet_truncate (a t) (ha t), show ¬ k ≤ steps + 2 by omega]
  · intro t n hn
    rw [eikonalCoefficient_congr (v t) (g t) n _ (a t)
      (fun k hk ↦ polynomialJet_truncate_eq (a t) (ha t) _ _ (by omega))]
    by_cases hz : n = 0
    · subst n
      rw [eikonalCoefficient_congr (v t) (g t) 0 (a t) (initial t) (by simpa using hkeep t)]
      exact hsecond t
    · exact hsolve t n (by omega) (by omega)

end
end Yau.Jets

end OAI
