import Lean.Elab.Tactic.Omega
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrimary
import OAI.NumberTheory.SiegelZeros.Intersection.TorusPolynomial
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalizedRadical
import OAI.NumberTheory.SiegelZeros.Structure.RectangleGenerators

namespace OAI

namespace SiegelZeros

noncomputable section
namespace SiegelZerosAwei.W21

open SiegelZeros.W58 WeightedTorusJets.W19

variable {K : Type*} [Field K]

def rectangleGenerator (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (a : Fin 3 → ℕ) : TorusRing K :=
  algebraMap (AmbientPolynomial K) (TorusRing K) (mixedInvariant v a F)

def derivativeIdeal (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t : Fin 3 → ℕ) (b : ℕ) : Ideal (TorusRing K) :=
  Ideal.span {f | ∃ a : Fin 3 → ℕ, (∀ j, a j ≤ b * t j) ∧
    f = rectangleGenerator v F a}

theorem rectangleGenerator_mem_derivativeIdeal (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t a : Fin 3 → ℕ) (b : ℕ)
    (ha : ∀ j, a j ≤ b * t j) :
    rectangleGenerator v F a ∈ derivativeIdeal v F t b :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem derivativeIdeal_mono (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t : Fin 3 → ℕ) : Monotone (derivativeIdeal v F t) := by
  intro b c hbc
  apply Ideal.span_mono
  rintro f ⟨a, ha, rfl⟩
  exact ⟨a, fun j => (ha j).trans (Nat.mul_le_mul_right (t j) hbc), rfl⟩

@[simp] theorem rectangleGenerator_zero (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) :
    rectangleGenerator v F 0 = algebraMap (AmbientPolynomial K) (TorusRing K) F := by
  rfl

theorem polynomial_mem_derivativeIdeal (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ) :
    algebraMap (AmbientPolynomial K) (TorusRing K) F ∈ derivativeIdeal v F t b := by
  simpa only [rectangleGenerator_zero] using
    rectangleGenerator_mem_derivativeIdeal v F t 0 b (fun j => Nat.zero_le _)

theorem derivativeIdeal_le_identityIdeal (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ)
    (hvanish : ∀ a : Fin 3 → ℕ, (∀ j, a j ≤ b * t j) →
      MvPolynomial.eval (fun _ : Fin 4 => 1) (mixedInvariant v a F) = 0) :
    derivativeIdeal v F t b ≤ identityIdeal K := by
  apply Ideal.span_le.mpr
  rintro f ⟨a, ha, rfl⟩
  change identityEvaluation K (rectangleGenerator v F a) = 0
  simpa only [rectangleGenerator, identityEvaluation_polynomial] using hvanish a ha

section PrimeChains
variable {R : Type*} [CommRing R]

theorem prime_height_toNat_succ_le {P Q : Ideal R} [P.IsPrime] [Q.IsPrime]
    (hP : P.height ≤ 4) (hQ : Q.height ≤ 4) (hPQ : P < Q) :
    P.height.toNat + 1 ≤ Q.height.toNat := by
  have hpfin : P.height ≠ ⊤ := (lt_of_le_of_lt hP (ENat.natCast_lt_top 4)).ne
  have hqfin : Q.height ≠ ⊤ := (lt_of_le_of_lt hQ (ENat.natCast_lt_top 4)).ne
  have hinc : P.height + 1 ≤ Q.height := Ideal.height_add_one_le_of_lt_of_isPrime hPQ
  have hnat := ENat.toNat_le_toNat hinc hqfin
  rw [ENat.toNat_add (m := P.height) (n := (1 : ℕ∞)) hpfin
    (ENat.natCast_ne_top 1), ENat.toNat_one] at hnat
  exact hnat

theorem common_minimalPrime_of_five [IsDomain R] (J : ℕ → Ideal R)
    (hm : Monotone J) (hJ : J 0 ≠ ⊥) (M : Ideal R) [M.IsPrime]
    (hJM : J 4 ≤ M)
    (hdim : ∀ P : Ideal R, P.IsPrime → P.height ≤ 4) :
    ∃ b, b < 4 ∧ ∃ P : Ideal R,
      P ∈ (J b).minimalPrimes ∧ P ∈ (J (b + 1)).minimalPrimes ∧ P ≤ M := by
  obtain ⟨P4, hP4, hP4M⟩ := Ideal.exists_minimalPrimes_le hJM
  have : P4.IsPrime := hP4.isPrime
  obtain ⟨P3, hP3, hP34⟩ := Ideal.exists_minimalPrimes_le
    ((hm (show 3 ≤ 4 by omega)).trans hP4.1.2)
  have : P3.IsPrime := hP3.isPrime
  obtain ⟨P2, hP2, hP23⟩ := Ideal.exists_minimalPrimes_le
    ((hm (show 2 ≤ 3 by omega)).trans hP3.1.2)
  have : P2.IsPrime := hP2.isPrime
  obtain ⟨P1, hP1, hP12⟩ := Ideal.exists_minimalPrimes_le
    ((hm (show 1 ≤ 2 by omega)).trans hP2.1.2)
  have : P1.IsPrime := hP1.isPrime
  obtain ⟨P0, hP0, hP01⟩ := Ideal.exists_minimalPrimes_le
    ((hm (show 0 ≤ 1 by omega)).trans hP1.1.2)
  have : P0.IsPrime := hP0.isPrime
  by_cases h01 : P0 = P1
  · exact ⟨0, by omega, P0, hP0, h01.symm ▸ hP1,
      hP01.trans (hP12.trans (hP23.trans (hP34.trans hP4M)))⟩
  by_cases h12 : P1 = P2
  · exact ⟨1, by omega, P1, hP1, h12.symm ▸ hP2,
      hP12.trans (hP23.trans (hP34.trans hP4M))⟩
  by_cases h23 : P2 = P3
  · exact ⟨2, by omega, P2, hP2, h23.symm ▸ hP3,
      hP23.trans (hP34.trans hP4M)⟩
  by_cases h34 : P3 = P4
  · exact ⟨3, by omega, P3, hP3, h34.symm ▸ hP4, hP34.trans hP4M⟩
  have hP0ne : P0 ≠ ⊥ := by
    intro h
    apply hJ
    exact le_antisymm (h ▸ hP0.1.2) bot_le
  have hbotP0 : (⊥ : Ideal R) < P0 := lt_of_le_of_ne bot_le hP0ne.symm
  have hh0 := prime_height_toNat_succ_le (P := (⊥ : Ideal R))
    (by simp) (hdim P0 inferInstance) hbotP0
  have hh1 := prime_height_toNat_succ_le (hdim P0 inferInstance) (hdim P1 inferInstance)
    (lt_of_le_of_ne hP01 h01)
  have hh2 := prime_height_toNat_succ_le (hdim P1 inferInstance) (hdim P2 inferInstance)
    (lt_of_le_of_ne hP12 h12)
  have hh3 := prime_height_toNat_succ_le (hdim P2 inferInstance) (hdim P3 inferInstance)
    (lt_of_le_of_ne hP23 h23)
  have hh4 := prime_height_toNat_succ_le (hdim P3 inferInstance) (hdim P4 inferInstance)
    (lt_of_le_of_ne hP34 h34)
  have htop : P4.height.toNat ≤ 4 :=
    ENat.toNat_le_of_le_natCast (n := 4) (hdim P4 inferInstance)
  simp only [Ideal.height_bot, ENat.toNat_zero] at hh0
  omega

end PrimeChains

theorem derivativeIdeals_common_component
    (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ, (∀ j, a j ≤ 4 * t j) →
      MvPolynomial.eval (fun _ : Fin 4 => 1) (mixedInvariant v a F) = 0) :
    ∃ b, b < 4 ∧ ∃ P : PrimeSpectrum (TorusRing K),
      P.asIdeal ≤ identityIdeal K ∧
      P.asIdeal ∈ (derivativeIdeal v F t b).minimalPrimes ∧
      P.asIdeal ∈ (derivativeIdeal v F t (b + 1)).minimalPrimes ∧
      ((derivativeIdeal v F t b).map
        (algebraMap (TorusRing K) (Localization.AtPrime P.asIdeal))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) := by
  have : IsDomain (TorusRing K) := SiegelZeros.W17.torus_isDomain K
  have hJ : derivativeIdeal v F t 0 ≠ ⊥ := by
    intro heq
    have hmem := polynomial_mem_derivativeIdeal v F t 0
    rw [heq, Ideal.mem_bot] at hmem
    exact SiegelZeros.W17.polynomial_to_torus_ne_zero K hF hmem
  have hdim : ∀ P : Ideal (TorusRing K), P.IsPrime → P.height ≤ 4 := by
    intro P hP
    have hh := (ringKrullDim_le_iff_height_le 4).mp (torus_dimension_le_four K) hP
    exact WithBot.coe_le_coe.mp hh
  obtain ⟨b, hb, P, hPb, hPb', hPid⟩ := common_minimalPrime_of_five
    (derivativeIdeal v F t) (derivativeIdeal_mono v F t) hJ (identityIdeal K)
    (derivativeIdeal_le_identityIdeal v F t 4 hvanish) hdim
  have : P.IsPrime := hPb.isPrime
  exact ⟨b, hb, ⟨P, inferInstance⟩, hPid, hPb, hPb',
    WeightedTorusJets.W22.localized_radical_eq_maximal_of_mem_minimalPrimes
      (derivativeIdeal v F t b) P hPb⟩

theorem derivativeIdeal_localized_isPrimary
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : P ∈ (derivativeIdeal v F t b).minimalPrimes) :
    ((derivativeIdeal v F t b).map
      (algebraMap (TorusRing K) (Localization.AtPrime P))).IsPrimary := by
  apply Ideal.isPrimary_of_isMaximal_radical
  rw [WeightedTorusJets.W22.localized_radical_eq_maximal_of_mem_minimalPrimes
    (derivativeIdeal v F t b) P hP]
  infer_instance

end SiegelZerosAwei.W21


namespace SiegelZerosAwei.W21
open SiegelZeros.W58 WeightedTorusJets.W19

variable {K : Type*} [Field K] [Algebra ℚ K]

theorem derivativeIdeal_eq_map_rectangle_span (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ) :
    derivativeIdeal v F t b =
      (Ideal.span (rectangleGenerators (fun j => rationalInvariant (v j)) t b F)).map
        (algebraMap (AmbientPolynomial K) (TorusRing K)) := by
  rw [Ideal.map_span]
  unfold derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    refine ⟨mixedInvariant v a F, ?_, ?_⟩
    · exact ⟨a, ha, (derivativeTriple_rationalInvariant v a F).symm⟩
    · exact hg.symm
  · rintro ⟨p, ⟨a, ha, hp⟩, hpg⟩
    refine ⟨a, ha, ?_⟩
    rw [hp, derivativeTriple_rationalInvariant] at hpg
    exact hpg.symm

end SiegelZerosAwei.W21

end

end SiegelZeros

end OAI
