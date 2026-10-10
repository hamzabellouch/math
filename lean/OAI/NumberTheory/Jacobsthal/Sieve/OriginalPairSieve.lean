import OAI.NumberTheory.Jacobsthal.Estimates.HarmonicLevelBound
import OAI.NumberTheory.Jacobsthal.Estimates.OriginalPairMembership
import OAI.NumberTheory.Jacobsthal.Estimates.PatternMainTerm

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def largeSieveLevel : ℝ := 480024
noncomputable def largeSieveExponent : ℝ := 1/(10*largeSieveLevel)
noncomputable def largeSieveCutoff (R : ℝ) : ℝ := R^largeSieveExponent

theorem largeSieveExponent_bounds : 0 < largeSieveExponent ∧ largeSieveExponent < 1 := by
  norm_num [largeSieveExponent,largeSieveLevel]

theorem largeSieveCutoff_level (R : ℝ) (hR : 0 < R) :
    (largeSieveCutoff R)^largeSieveLevel = R^((1 : ℝ)/10) := by
  unfold largeSieveCutoff
  rw [← Real.rpow_mul hR.le]
  norm_num [largeSieveExponent,largeSieveLevel]

theorem largeSieveCutoff_log (R : ℝ) (hR : 0 < R) :
    Real.log (largeSieveCutoff R) = largeSieveExponent*Real.log R := Real.log_rpow hR _

theorem largeSieveCutoff_tendsto : Tendsto largeSieveCutoff atTop atTop :=
  tendsto_rpow_atTop largeSieveExponent_bounds.1

theorem largeSieveCutoff_lt (R : ℝ) (hR : 1 < R) : largeSieveCutoff R < R := by
  simpa only [largeSieveCutoff,Real.rpow_one] using
    Real.rpow_lt_rpow_of_exponent_lt hR largeSieveExponent_bounds.2

theorem source_main_R_upper : ∃ C : ℝ,0 < C ∧ ∀ᶠ R : ℝ in atTop,1 < R ∧ 2 ≤ largeSieveCutoff R ∧
    ∀ (H T0 T1 : ℕ),0 < H → 0 < T0 → 0 < T1 → T0 ∣ H → H.Coprime T1 →
      ∀ (U V : ℝ),0 ≤ U → 0 ≤ V → V ≤ 2*(H : ℝ) →
      sourceMain H T0 T1 U V*
        (∏ t ∈ reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*T1),(1-1/(t : ℝ)))*
          (1+Real.exp (-largeSieveLevel/96)) ≤
            C*U/((patternCard T0 T1 : ℝ)*Real.log R) := by
  obtain ⟨C,v0,hC,hv0,hmain⟩ := source_main_uniform_upper
  refine ⟨C/largeSieveExponent,div_pos hC largeSieveExponent_bounds.1,?_⟩
  filter_upwards [largeSieveCutoff_tendsto.eventually_ge_atTop v0,eventually_gt_atTop (1 : ℝ)]
    with R hv hR
  refine ⟨hR,hv0.trans hv,?_⟩
  intro H T0 T1 hH hT0 hT1 hT0H hcop U V hU hV hVH
  have hh := hmain (largeSieveCutoff R) hv H T0 T1 hH hT0 hT1 hT0H hcop U V largeSieveLevel hU hV hVH
    (by norm_num [largeSieveLevel])
  rw [largeSieveCutoff_log R (by linarith)] at hh
  calc
    _ ≤ C*U/((patternCard T0 T1 : ℝ)*(largeSieveExponent*Real.log R)) := hh
    _ = _ := by ring

end ErdosVarianceLargeCount

end

section

namespace ErdosVarianceLargeMap
open NumberTheoryLean ErdosVarianceSmallModel ErdosVarianceLargeCount ErdosHyperbolaError
  ErdosPrimeInputs.PrimeProductOmissions
attribute [local instance] Classical.propDecidable

theorem prime_avoids_cutoff (p : ℕ) (hp : p.Prime) (v : ℝ) (hvp : v < (p : ℝ))
    (t : ℕ) (ht : t.Prime) (htv : (t : ℝ) ≤ v) : ¬(t : ℤ) ∣ (p : ℤ) := by
  intro hdiv
  have hd : t ∣ p := by exact_mod_cast hdiv
  rcases (Nat.dvd_prime hp).mp hd with he|he
  · exact ht.ne_one he
  · subst t
    linarith

theorem original_pair_mem_sifted (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ)) (p : goodPrimes P H)
    (R : ℝ) (hR : 1 < R) (hpR : R < (p.val : ℝ))
    (x0 x1 y0 y1 : ℝ) (hp : x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1)
    (hm : y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1) :
    let v := actualFullPattern P w H C0 hw hP hlarge p
    ((p.val : ℤ),primeM P H C0 hP p) ∈
      siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
        (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) x0 x1 y0 y1 false true true false
          (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H)) := by
  dsimp only
  apply Finset.mem_filter.mpr
  refine ⟨original_pair_mem_sourcePairs P w H C0 hw hP hlarge p x0 x1 y0 y1 hp hm,?_⟩
  intro t ht
  have hc := LargePrimeDeletion.mem_cutoffPrimes.mp (Finset.mem_sdiff.mp ht).1
  have hcut0 : 0 ≤ largeSieveCutoff R := Real.rpow_nonneg (by linarith) _
  have htv := (Nat.le_floor_iff hcut0).mp hc.2
  exact prime_avoids_cutoff p.val (hP p.val (Finset.mem_filter.mp p.property).1) (largeSieveCutoff R)
    ((largeSieveCutoff_lt R hR).trans hpR) t hc.1 htv

theorem original_prime_fibre_le_pairs (P : Finset ℕ) (w : ℝ) (H : ℕ) (C0 : ℤ)
    (hw : 0 ≤ w) (hP : ∀ p ∈ P,p.Prime) (hlarge : ∀ p ∈ P,w < (p : ℝ))
    (A : Finset (goodPrimes P H)) (v : ErdosLargePatternLaw.FullPattern w H)
    (R : ℝ) (hR : 1 < R) (x0 x1 y0 y1 : ℝ)
    (hA : ∀ p ∈ A,actualFullPattern P w H C0 hw hP hlarge p = v ∧ R < (p.val : ℝ) ∧
      (x0 < (p.val : ℝ) ∧ (p.val : ℝ) ≤ x1) ∧
      (y0 ≤ (primeM P H C0 hP p : ℝ) ∧ (primeM P H C0 hP p : ℝ) < y1)) :
    A.card ≤ (siftedSourcePairs H (divisorModulus w H) (coprimeModulus w H) C0 (v.2.1.val : ℤ)
      (v.1.val.val : ℤ) (v.2.2.1.val.val : ℤ) (v.2.2.2.val : ℤ) x0 x1 y0 y1 false true true false
        (reducedPrimes ⌊largeSieveCutoff R⌋₊ (H*coprimeModulus w H))).card := by
  apply Finset.card_le_card_of_injOn (fun p => ((p.val : ℤ),primeM P H C0 hP p))
  · intro p hp
    obtain ⟨he,hpR,hpI,hmI⟩ := hA p hp
    have hm := original_pair_mem_sifted P w H C0 hw hP hlarge p R hR hpR x0 x1 y0 y1 hpI hmI
    dsimp only at hm
    rwa [he] at hm
  · exact (original_prime_pair_injective P H C0 hP).injOn

end ErdosVarianceLargeMap

end

end Erdos970

end OAI
