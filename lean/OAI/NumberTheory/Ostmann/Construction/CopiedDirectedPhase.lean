import OAI.NumberTheory.Ostmann.Construction.TransferDirectedPhase
import OAI.NumberTheory.Ostmann.Construction.TransferPhaseSupport

namespace OAI

/-! # The next directed phase with support derived from the original ranges -/

namespace Ostmann

open scoped BigOperators ComplexConjugate Classical

theorem transferredPrimeFact {H Y : Type*} (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (i : (Bool × H) ⊕ Y) : Fact (transferredLabels L R U i).Prime := by
  rcases i with ⟨c, h⟩ | y
  · cases c
    · exact (inferInstance : Fact (R h).Prime)
    · exact (inferInstance : Fact (L h).Prime)
  · exact (inferInstance : Fact (U y).Prime)

noncomputable def copiedDirectedPhase {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (v w s : ℤ) : ℂ := by
  letI := transferredPrimeFact L R U
  exact directedPrimePhase (transferredLabels L R U)
    (fun i => copiedSlotCharacter χH χY i (transferredLabels L R U i))
    (fun i => t (transferredLabels L R U i))
    (copiedSlotUnary (transferredLabels L R U) χH b νL νR νYL νYR v w s)
    (transferredGraph b) s

theorem transfer_copiedDirectedPhase_of_ranges {H Y : Type*} [Fintype H] [Fintype Y]
    (L R : H → ℕ) (U : Y → ℕ)
    [∀ h, Fact (L h).Prime] [∀ h, Fact (R h).Prime] [∀ y, Fact (U y).Prime]
    (t : ∀ p : ℕ, ZMod p)
    (χH : H → ∀ p : ℕ, DirichletCharacter ℂ p)
    (χY : Y → ∀ p : ℕ, DirichletCharacter ℂ p)
    (b : Option (H ⊕ Y) → Option (H ⊕ Y) → ℤ)
    (νL νR : H → ℂ) (νYL νYR : Y → ℂ) (M : ℕ) (v w s : ℤ)
    (hrel : v * (∏ h, R h) - w * (∏ h, L h) = s * M)
    (B K V : ℕ) (hMpos : 0 < M) (hs : s ≠ 0)
    (hv : v.natAbs ≤ B) (hw : w.natAbs ≤ B)
    (hLbound : (∏ h, L h) ≤ K) (hRbound : (∏ h, R h) ≤ K)
    (hscale : 2 * B * K ≤ V * M)
    (hL : Pairwise (fun h k => (L h).Coprime (L k)))
    (hR : Pairwise (fun h k => (R h).Coprime (R k)))
    (hU : Pairwise (fun y z => (U y).Coprime (U z)))
    (hLU : (∏ h, L h).Coprime (∏ y, U y)) (hRU : (∏ h, R h).Coprime (∏ y, U y))
    (hML : M.Coprime (∏ h, L h)) (hMR : M.Coprime (∏ h, R h)) (hMU : M.Coprime (∏ y, U y))
    (hlargeL : ∀ h, V < L h) (hlargeR : ∀ h, V < R h) (hlargeU : ∀ y, V < U y)
    (hb : ∀ y, b (some (.inr y)) (some (.inr y)) = 0) :
    retainedPrimePhase L U t χH χY b νL νYL M v *
      conj (retainedPrimePhase R U t χH χY b νR νYR M w) =
        copiedDirectedPhase L R U t χH χY b νL νR νYL νYR v w s := by
  let := transferredPrimeFact L R U
  obtain ⟨_, hc, hM, hsu⟩ := transfer_copied_support_of_ranges L R U M B K V v w s
    hMpos hs hrel hv hw hLbound hRbound hscale hL hR hU hLU hRU hML hMR hMU
    hlargeL hlargeR hlargeU
  exact transfer_directed_phase (transferredLabels L R U) t χH χY b νL νR νYL νYR
    M v w s hrel hc hM hsu hb

end Ostmann

end OAI
