import OAI.MeasureTheory.Falconer.Radial.ProfileProjectionCollision
import OAI.MeasureTheory.Falconer.Radial.SuffixProjectionWidths

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_profile_projection_collision {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (B : ℕ) (δ lam : ℝ) (m : ℝ → ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
      ∀ i ≤ J, ∀ ω e : UnitCircle,
      dist (ω:Plane) (e:Plane) ≤ C/(2:ℝ)^(u-p) →
      ω ∈ descriptorGoodSet Q ρ m N lam sig J i P (.projection p u) →
      ((ρ.restrict (Q.descendant P).carrier).prod (ρ.restrict (Q.descendant P).carrier))
        {z : Plane × Plane | |planeDot (z.1-z.2) (e:Plane)| ≤ K/(2:ℝ)^u} ≤
        (ρ (Q.descendant P).carrier)^2 * ENNReal.ofReal (((2:ℝ)^N)^
          (-(m u-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+
            2000*(lam+sig)+12*lam)) := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_projection_gap hsig hJ C K
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ B δ lam m hprof p u hpu hu P hP i hi ω e hd hg
  exact profile_projection_collision Q hQ ρ hprof hpu hu hP hd
    (hN₀ N hN p u hpu i hi) hg

end PlanarFalconer

end OAI
