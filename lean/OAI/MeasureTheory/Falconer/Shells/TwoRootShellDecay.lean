import OAI.MeasureTheory.Falconer.Shells.TwoRootMixtureFinite
import OAI.MeasureTheory.Falconer.Shells.TwoSidedShell
import OAI.MeasureTheory.Falconer.Estimates.IndependentClassEquation27

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_two_root_shell_decay {δ β lam sig kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ μ ν : Measure Plane, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ H₀ H₁ : ℕ, 0 < H₀ → 0 < H₁ → H₀ ≤ N → H₁ ≤ N →
      ∀ m₀ m₁ : List ℕ → ℝ → ℝ,
      ActualClassFamily (Q 0) μ N H₀ δ lam sig m₀ → ActualClassFamily (Q 1) ν N H₁ δ lam sig m₁ →
      shellEnergy (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β) N ≤
        2*((2:ℝ)^N)^(-β/2) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_independent_class_equation27 hδ hδ1 hβ hlam hlamδ hsig
    hkap hkapβ hgap hratio hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro N hN Q hQ hlo hhi μ ν instμ instν H₀ H₁ hH₀ hH₁ hNH₀ hNH₁ m₀ m₁ hf₀ hf₁
  have hQ₀ : 0 < (Q 0).side := by rw [hQ 0]; norm_num
  have hQ₁ : 0 < (Q 1).side := by rw [hQ 1]; norm_num
  have hsep : ∀ x ∈ (Q 0).carrier, ∀ y ∈ (Q 1).carrier, 90 ≤ dist x y :=
    fun x hx y hy => (separated_unit_roots_distance Q hQ hlo hhi x y hx hy).1
  let : ∀ classPair : List ℕ × List ℕ, IsFiniteMeasure
      (twoRootClassMeasure (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β classPair) :=
    fun classPair => twoRootClassMeasure_isFinite (Q 0) (Q 1) hQ₀ hQ₁ μ ν
      m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β (by norm_num : (0:ℝ) < 90) hsep classPair
  rw [restoredTwoRootCandidate_eq_sum]
  apply shellEnergy_weighted_sum_uniform _ _ _ N
    (twoRootClassCoefficient_sum_le_one (Q 0) (Q 1) hQ₀ hQ₁ μ ν N (N/H₀) (N/H₁) lam) (by positivity)
  intro a ha
  have ha := Finset.mem_product.mp ha
  let ρ : Fin 2 → Measure Plane := ![actualClassMeasure (Q 0) μ N (N/H₀) a.1,
    actualClassMeasure (Q 1) ν N (N/H₁) a.2]
  let mass : Fin 2 → ℝ → ℝ := ![m₀ a.1,m₁ a.2]
  let B : Fin 2 → ℕ := ![N/H₀,N/H₁]
  have hcarry (l : Fin 2) : ρ l (Q l).carrierᶜ = 0 := by
    fin_cases l
    · exact actualClassMeasure_carry (Q 0) hQ₀ μ N (N/H₀) a.1
    · exact actualClassMeasure_carry (Q 1) hQ₁ ν N (N/H₁) a.2
  have hB (l : Fin 2) : 0 < B l := by
    fin_cases l
    · exact Nat.div_pos hNH₀ hH₀
    · exact Nat.div_pos hNH₁ hH₁
  have hp (l : Fin 2) : RegularizedProfileData (Q l) (ρ l) N (B l) δ lam (mass l) := by
    fin_cases l
    · exact (hf₀.profiles a.1 ha.1).1
    · exact (hf₁.profiles a.2 ha.2).1
  have hpair := h₀ N hN Q ρ mass hQ hcarry hlo hhi B hB hp
  rw [shellEnergy_eq_twice_positive]
  exact mul_le_mul_of_nonneg_left hpair (by norm_num)

end PlanarFalconer

end OAI
