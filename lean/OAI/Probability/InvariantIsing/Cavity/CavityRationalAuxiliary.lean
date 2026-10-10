import OAI.Probability.InvariantIsing.Cavity.CavityRationalBaseCounts
import OAI.Probability.InvariantIsing.Cavity.CavityRationalWindows
import OAI.Probability.InvariantIsing.Cavity.CavityLimitingComplement

namespace OAI

/-! Rational spectral proportions provide all finite auxiliary axes and
the fixed orthogonal complement in the cavity construction. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

theorem cavity_rational_auxiliary_geometry {m n : ℕ} (hm : 2  ≤  m) (hn : 0 < n)
    (s : Fin m → ℕ) (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n) :
    let d := m*n-n
    0 < d ∧ ∃ es : Fin (m*n) ≃ Fin (d+n),
      ∃ a₀ : Fin d → Fin m, ∃ B₀ : Matrix (Fin (d+n)) (Fin d) ℝ,
        (∀ a, (Finset.univ.filter (fun j => a₀ j=a)).card=n-s a) ∧
        B₀.transpose*B₀=1 ∧
        (cavityReindexedStack es (fun a => ((s a : ℝ)/n) • 1)).transpose*B₀=0 := by
  intro d
  have hmn : n+n ≤ m*n := by
    have hh := Nat.mul_le_mul_right n hm
    simpa only [two_mul] using hh
  have hdn : d+n=m*n := Nat.sub_add_cancel (by omega)
  have hd : 0 < d := by dsimp only [d]; omega
  let es : Fin (m*n) ≃ Fin (d+n) := finCongr hdn.symm
  obtain ⟨a₀,ha₀⟩ := cavity_special_labels_exists s (cavityRationalSpecial_sum s hsum)
  obtain ⟨B₀,hB₀,hperp⟩ := cavity_limiting_complement_exists es (fun a => (s a : ℝ)/n)
    (fun a => (cavityRationalMass_positive s hs hn a).le) (cavityRationalMass_sum s hsum hn)
  exact ⟨hd,es,a₀,B₀,ha₀,hB₀,hperp⟩

end InvariantIsing

end

end OAI
