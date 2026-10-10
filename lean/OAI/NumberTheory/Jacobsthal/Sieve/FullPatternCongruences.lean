import OAI.NumberTheory.Jacobsthal.Partitions.FullPatternCoordinates

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceLargeMap
open ErdosVarianceSmallModel ErdosVarianceMoments
attribute [local instance] Classical.propDecidable

theorem full_pattern_units (w : ℝ) (H : ℕ) (v : ErdosLargePatternLaw.FullPattern w H) :
    Int.gcd (v.1.val.val : ℤ) (divisorModulus w H : ℤ) = 1 ∧
      Int.gcd (v.2.2.1.val.val : ℤ) (coprimeModulus w H : ℤ) = 1 := by
  constructor
  · simpa only [Int.gcd_def,Int.natAbs_natCast] using (ZMod.val_coe_unit_coprime v.1).gcd_eq_one
  · simpa only [Int.gcd_def,Int.natAbs_natCast] using (ZMod.val_coe_unit_coprime v.2.2.1).gcd_eq_one

theorem full_pattern_residue_congruences (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    Int.ModEq (divisorModulus w H : ℤ) (p.val : ℤ) (v.1.val.val : ℤ) ∧
    Int.ModEq (coprimeModulus w H : ℤ) (p.val : ℤ) (v.2.2.1.val.val : ℤ) ∧
    Int.ModEq (coprimeModulus w H : ℤ) (primeM P H C0 hP p) (v.2.2.2.val : ℤ) := by
  dsimp only
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_natCast] using (full_p0_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm
  · constructor
    · rw [← ZMod.intCast_eq_intCast_iff]
      simpa only [Int.cast_natCast] using (full_p1_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm
    · rw [← ZMod.intCast_eq_intCast_iff]
      simpa only [Int.cast_natCast] using (full_m1_projection P w H C0 hw hP hlarge p _ dvd_rfl).symm

theorem full_pattern_product_congruence (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    Int.ModEq ((H*divisorModulus w H : ℕ) : ℤ) ((p.val : ℤ)*primeM P H C0 hP p)
      (C0+(H : ℤ)*(v.2.1.val : ℤ)) := by
  dsimp only
  have hk : Int.ModEq (divisorModulus w H : ℤ)
      ((actualFullPattern P w H C0 hw hP hlarge p).2.1.val : ℤ) (primeK P H C0 hP p : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff]
    simpa only [Int.cast_natCast] using full_k0_projection P w H C0 hw hP hlarge p _ dvd_rfl
  obtain ⟨u,hu⟩ := Int.modEq_iff_add_fac.mp hk
  apply Int.ModEq.symm
  apply Int.modEq_iff_add_fac.mpr
  refine ⟨u,?_⟩
  rw [primeMK_identity,hu]
  push_cast
  ring

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
