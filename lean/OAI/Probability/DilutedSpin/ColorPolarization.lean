import OAI.Probability.DilutedSpin.ColorSymmetry
import OAI.Probability.DilutedSpin.Polarization

namespace OAI

section
section
open scoped ContDiff BigOperators

namespace DilutedSpinGlass.PrescribedTree
variable {Ω : Type} [Fintype Ω]

 
theorem coloredAt_polarization {n k : ℕ} (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hm : ∀ j : Fin n, m j.succ ≠ 0) (hroot : m 0 = 0) (hend : m (Fin.last n) = 1)
    (hk : 0 < k) {ι : Type} [DecidableEq ι]
    (S : PrescribedTree n) (U : Finset ι)
    (paths : ι → Sample Ω S → FinitePath Ω n) (G : Sample Ω S → ℝ)
    (ds : Fin k → FinitePath Ω n → ℝ) :
    coloredAt T m (List.ofFn ds).reverse S U paths G (fun _ => 1) =
      ((k : ℝ)^k / (2^k * k.factorial)) *
      ∑ ε : Fin k → Bool, (∏ j, Polarization.sign (ε j)) *
        anchorIterate T m (Polarization.averageDirection ε ds) k S U paths G 0 := by
  rw [← iteratedFDeriv_anchorAt T m hm hroot hend k S U paths G (by simp)]
  have hsym := fun (v : Fin k → FinitePath Ω n → ℝ) (π : Equiv.Perm (Fin k)) => (contDiffAt_anchorAt S T m U paths G (A := fun _ => 1)
    (by simp)).iteratedFDeriv_comp_perm v π
  have hp := Polarization.normalized_polarization hk
    (iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1)).toMultilinearMap hsym ds
  change iteratedFDeriv ℝ k (anchorAt S T m U paths G) (fun _ => 1) ds = _ at hp
  rw [hp]
  apply congrArg (((k : ℝ)^k / (2^k * k.factorial)) * ·)
  apply Finset.sum_congr rfl
  intro ε _
  apply congrArg ((∏ j, Polarization.sign (ε j)) * ·)
  exact iteratedFDeriv_anchorAt_diagonal T m hm hroot hend k
    (Polarization.averageDirection ε ds) S U paths G

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
