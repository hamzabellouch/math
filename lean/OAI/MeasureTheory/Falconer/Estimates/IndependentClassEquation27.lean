import OAI.MeasureTheory.Falconer.Shells.NormalizedOuterShell
import OAI.MeasureTheory.Falconer.Recursion.ProfileBlockRefinement

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_independent_class_equation27 {δ β lam sig kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ),
      (∀ l, (Q l).side = 1) → (∀ l, ρ l (Q l).carrierᶜ = 0) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ B : Fin 2 → ℕ, (∀ l, 0 < B l) →
      (∀ l, RegularizedProfileData (Q l) (ρ l) N (B l) δ lam (mass l)) →
      let c := outerEntry (mass 0) (mass 1) N β
      let d := RootShellData.ofOuter (Q 0) (Q 1) (ρ 0) (ρ 1) (mass 0) (mass 1)
        N lam lam sig kap c (Q 0) (Q 1)
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun d.measure r‖^2) ≤
        ((2:ℝ)^N)^(-β/2) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_normalized_equation27 hδ hδ1 hβ hlam hlamδ hsig
    hkap hkapβ hgap hratio hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro N hN Q ρ mass hQ hcarry hlo hhi B hB hprof
  exact h₀ N hN Q ρ mass hQ hcarry hlo hhi 1 (fun l => (hprof l).unitBlocks (hB l))

end PlanarFalconer

end OAI
