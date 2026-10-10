import OAI.NumberTheory.Ostmann.Construction.FavorableGiant
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open scoped BigOperators

lemma residueTest_norm_le_prime (d : Decomposition) {p : ℕ} (hp : p.Prime) (x : ZMod p) :
    ‖residueTest d p x‖ ≤ (p:ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hlo : 0<Supply.density (d.residueSupport p) := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_pos p hp
  have hhi : Supply.density (d.residueSupport p)<1 := by
    simpa only [Supply.density,Decomposition.residueDensity,ZMod.card] using d.residueDensity_lt_one p hp
  have hsum : ∑r,‖residueTest d p r‖^2=(p:ℝ) := by
    simp only [residueTest_eq,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    simpa only [ZMod.card] using Supply.sum_normalizedIndicator_sq (d.residueSupport p) hlo hhi
  have hx := Finset.single_le_sum (s := Finset.univ) (f := fun r : ZMod p => ‖residueTest d p r‖^2)
    (fun r _ => sq_nonneg _) (Finset.mem_univ x)
  rw [hsum] at hx
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_le
  have hn := norm_nonneg (residueTest d p x)
  nlinarith

lemma favorableGiantResidueTest_norm_le_prime (d : Decomposition) (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (x : ZMod p) :
    ‖favorableGiantResidueTest d P p x‖ ≤ (p:ℝ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  by_cases hP : p∈P
  · simp only [favorableGiantResidueTest,hP,ite_true,giantResidueTest_eq]
    have hx := Finset.single_le_sum (s := Finset.univ)
      (f := fun r : ZMod p => ‖giantTest (d.residueSupport p) r‖^2)
      (fun r _ => sq_nonneg _) (Finset.mem_univ x)
    have h := hx.trans (giantTest_sum_sq_le (d.residueSupport p))
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_le
    have hn := norm_nonneg (giantTest (d.residueSupport p) x)
    nlinarith
  · simp only [favorableGiantResidueTest,hP,ite_false,norm_zero]
    exact Nat.cast_nonneg _

def primeSourceBound (S : PrimeSource) : ℝ := ∑p∈S.candidates,(p:ℝ)

lemma primeSourceBound_nonneg (S : PrimeSource) : 0≤primeSourceBound S :=
  Finset.sum_nonneg (fun p _ => Nat.cast_nonneg p)

lemma primeSource_le_bound (S : PrimeSource) (p : S.Sample) : (p:ℝ)≤primeSourceBound S :=
  Finset.single_le_sum (fun q _ => Nat.cast_nonneg q) p.property

lemma residueTest_re_abs_le_source (d : Decomposition) (S : PrimeSource) (p : S.Sample) (n : ℤ) :
    |(residueTest d p (n:ZMod (p:ℕ))).re|≤primeSourceBound S :=
  (Complex.abs_re_le_norm _).trans ((residueTest_norm_le_prime d (S.prime _ p.property) _).trans
    (primeSource_le_bound S p))

lemma favorableGiantResidueTest_re_abs_le_source (d : Decomposition) (P : Finset ℕ)
    (S : PrimeSource) (p : S.Sample) (n : ℤ) :
    |(favorableGiantResidueTest d P p (n:ZMod (p:ℕ))).re|≤primeSourceBound S :=
  (Complex.abs_re_le_norm _).trans ((favorableGiantResidueTest_norm_le_prime d P
    (S.prime _ p.property) _).trans (primeSource_le_bound S p))

end Ostmann.Construction

end

end OAI
