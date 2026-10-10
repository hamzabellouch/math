import OAI.NumberTheory.Ostmann.Quadratic.RootPopulations
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootContradiction

namespace OAI

/-! # The collision estimate for the constructed quadratic root populations -/

namespace Ostmann

open scoped BigOperators

theorem kernel_populations_scale_bound (P R : Finset ℕ) (S T : Finset ℤ)
    (hSnon : S.Nonempty) (hTnon : T.Nonempty)
    (rootS rootT : ℤ → ℕ) (m Ds Dt : ℕ) (hm : 0 < m)
    (hDs : 1 ≤ Ds) (hDt : 1 ≤ Dt) (h u v : ℤ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hS : ∀ x ∈ S, u * (rootS x : ℤ) ^ 2 = (m : ℤ) * x - h)
    (hT : ∀ y ∈ T, v * (rootT y : ℤ) ^ 2 = (m : ℤ) * y - h)
    (X : ℝ) (hspanS : ∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X)
    (hspanT : ∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X)
    (hdiamS : Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) ≤ Ds)
    (hdiamT : Real.sqrt ((m : ℝ) * X / |(v : ℝ)|) ≤ Dt)
    (hprimeDiff : ∀ x ∈ S, ∀ y ∈ T, (x - y).natAbs.Prime)
    (L η C : ℝ) (hRP : R ⊆ P) (hP : ∀ p ∈ P, p.Prime)
    (c : (p : ℕ) → ZMod p)
    (hc : ∀ p ∈ R, (u : ZMod p) * c p ^ 2 = (v : ZMod p))
    (hpm : ∀ p ∈ R, ¬p ∣ m) (hpv : ∀ p ∈ R, ¬p ∣ v.natAbs)
    (hsmall : ∀ p ∈ R, ∀ x ∈ S, ∀ y ∈ T, p < (x - y).natAbs)
    (hL : 0 ≤ L) (hη : η ≤ 1 / 1000)
    (hmertens : (1 / 2 - 5 * η) * L - C ≤
      ∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ))
    (hsplitmass : (3 / 100) * L ≤ ∑ p ∈ R, Real.log (p : ℝ) / (p : ℝ))
    (hbudget : Real.log (Ds : ℝ) + Real.log (Dt : ℝ) +
      (1 / (S.card : ℝ) + 1 / (T.card : ℝ)) * ∑ p ∈ P, Real.log (p : ℝ) ≤
        (101 / 100) * L) : L ≤ 50 * C := by
  classical
  have hcardS := kernelRootPopulation_card S rootS m hm h u hS
  have hcardT := kernelRootPopulation_card T rootT m hm h v hT
  apply root_population_scale_bound P R
    (kernelRootPopulation S rootS) (kernelRootPopulation T rootT)
    (hSnon.image rootS) (hTnon.image rootT) Ds Dt hDs hDt
    (kernelRootPopulation_diameter S rootS m Ds h u hu X hS hspanS hdiamS)
    (kernelRootPopulation_diameter T rootT m Dt h v hv X hT hspanT hdiamT)
    L η C hRP hP c
  · intro p hp hc0
    have hv0 : (v : ZMod p) = 0 := by simpa [hc0] using (hc p hp).symm
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd v p).mp hv0
    exact hpv p hp (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hdiv))
  · intro p hp
    let : Fact p.Prime := ⟨hP p (hRP hp)⟩
    exact kernelRootPopulation_residues_disjoint S T rootS rootT m h u v (c p)
      (hpm p hp) hS hT (hc p hp) hprimeDiff (hsmall p hp)
  · exact hL
  · exact hη
  · exact hmertens
  · exact hsplitmass
  · simpa only [hcardS, hcardT] using hbudget

end Ostmann

end OAI
