import Mathlib.RingTheory.Spectrum.Prime.Topology
import OAI.NumberTheory.SiegelZeros.Selection.InvariantBox
import OAI.NumberTheory.SiegelZeros.Structure.IdentityHeight

namespace OAI

namespace SiegelZeros


noncomputable section

namespace W17

open W58

variable (K : Type*) [Field K]

theorem coordinateProduct_ne_zero : coordinateProduct K ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => MvPolynomial.X_ne_zero i)

theorem polynomial_to_torus_injective :
    Function.Injective (algebraMap (AmbientPolynomial K) (TorusRing K)) :=
  IsLocalization.injective (TorusRing K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coordinateProduct_ne_zero K))

theorem polynomial_to_torus_ne_zero {F : AmbientPolynomial K} (hF : F ≠ 0) :
    algebraMap (AmbientPolynomial K) (TorusRing K) F ≠ 0 := by
  intro h
  apply hF
  apply polynomial_to_torus_injective K
  simpa using h

theorem torus_isDomain : IsDomain (TorusRing K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (TorusRing K)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (coordinateProduct_ne_zero K))

def torusZeroIdeal (F : AmbientPolynomial K) : Ideal (TorusRing K) :=
  Ideal.span {algebraMap (AmbientPolynomial K) (TorusRing K) F}

abbrev TorusHypersurfaceRing (F : AmbientPolynomial K) :=
  TorusRing K ⧸ torusZeroIdeal K F

theorem torusZeroIdeal_ne_bot {F : AmbientPolynomial K} (hF : F ≠ 0) :
    torusZeroIdeal K F ≠ ⊥ := by
  intro h
  have hmem := Ideal.mem_span_singleton_self
    (algebraMap (AmbientPolynomial K) (TorusRing K) F)
  change algebraMap (AmbientPolynomial K) (TorusRing K) F ∈ torusZeroIdeal K F at hmem
  rw [h, Ideal.mem_bot] at hmem
  exact polynomial_to_torus_ne_zero K hF hmem

theorem torusZeroIdeal_le_identity {F : AmbientPolynomial K}
    (hF : MvPolynomial.eval (fun _ : Fin 4 => 1) F = 0) :
    torusZeroIdeal K F ≤ identityIdeal K := by
  apply (Ideal.span_singleton_le_iff_mem (identityIdeal K)).mpr
  rw [mem_identityIdeal, identityEvaluation_polynomial]
  exact hF

theorem torusZeroIdeal_ne_top {F : AmbientPolynomial K}
    (hF : MvPolynomial.eval (fun _ : Fin 4 => 1) F = 0) :
    torusZeroIdeal K F ≠ ⊤ := by
  intro h
  have hmem : (1 : TorusRing K) ∈ torusZeroIdeal K F := by rw [h]; trivial
  have hz := (mem_identityIdeal K 1).mp (torusZeroIdeal_le_identity K hF hmem)
  simp at hz

def torusZeroLocus (F : AmbientPolynomial K) : Set (PrimeSpectrum (TorusRing K)) :=
  PrimeSpectrum.zeroLocus {algebraMap (AmbientPolynomial K) (TorusRing K) F}

theorem torusZeroLocus_isClosed (F : AmbientPolynomial K) :
    IsClosed (torusZeroLocus K F) := PrimeSpectrum.isClosed_zeroLocus _

theorem torusZeroLocus_nonempty {F : AmbientPolynomial K}
    (hF : MvPolynomial.eval (fun _ : Fin 4 => 1) F = 0) :
    (torusZeroLocus K F).Nonempty := by
  refine ⟨⟨identityIdeal K, inferInstance⟩, ?_⟩
  change {algebraMap (AmbientPolynomial K) (TorusRing K) F} ⊆ (identityIdeal K : Set _)
  rw [Set.singleton_subset_iff]
  change identityEvaluation K (algebraMap (AmbientPolynomial K) (TorusRing K) F) = 0
  rw [identityEvaluation_polynomial]
  exact hF

theorem torusZeroLocus_ne_univ {F : AmbientPolynomial K} (hF : F ≠ 0) :
    torusZeroLocus K F ≠ Set.univ := by
  let : IsDomain (TorusRing K) := torus_isDomain K
  let η : PrimeSpectrum (TorusRing K) := ⟨⊥, Ideal.isPrime_bot⟩
  intro h
  have hη : η ∈ torusZeroLocus K F := by rw [h]; trivial
  have hz : algebraMap (AmbientPolynomial K) (TorusRing K) F ∈ η.asIdeal :=
    hη (Set.mem_singleton _)
  change algebraMap (AmbientPolynomial K) (TorusRing K) F ∈ (⊥ : Ideal _) at hz
  exact polynomial_to_torus_ne_zero K hF (Ideal.mem_bot.mp hz)

variable {K}

theorem iterate_invariantDerivation_mem (v : Fin 4 → K) {N : ℕ}
    {F : AmbientPolynomial K} (hF : F ∈ boxPolynomials K N) (m : ℕ) :
    ((fun G => WeightedTorusJets.W18.invariantDerivation v G)^[m]) F ∈
      boxPolynomials K N := by
  induction m with
  | zero => exact hF
  | succ m hm =>
    rw [Function.iterate_succ_apply']
    exact invariantDerivation_mem_boxPolynomials v hm

def derivativeJet (v : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ)
    (F : AmbientPolynomial K) : AmbientPolynomial K :=
  ((fun G => WeightedTorusJets.W18.invariantDerivation (v 0) G)^[a 0])
    (((fun G => WeightedTorusJets.W18.invariantDerivation (v 1) G)^[a 1])
      (((fun G => WeightedTorusJets.W18.invariantDerivation (v 2) G)^[a 2]) F))

theorem derivativeJet_mem (v : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ) {N : ℕ}
    {F : AmbientPolynomial K} (hF : F ∈ boxPolynomials K N) :
    derivativeJet v a F ∈ boxPolynomials K N :=
  iterate_invariantDerivation_mem (v 0)
    (iterate_invariantDerivation_mem (v 1)
      (iterate_invariantDerivation_mem (v 2) hF (a 2)) (a 1)) (a 0)

theorem derivativeJet_totalDegree_lt (v : Fin 3 → Fin 4 → K) (a : Fin 3 → ℕ)
    {N : ℕ} (hN : 0 < N) {F : AmbientPolynomial K}
    (hF : F ∈ boxPolynomials K N) : (derivativeJet v a F).totalDegree < 4 * N :=
  totalDegree_lt K hN (derivativeJet_mem v a hF)

end W17

end


end SiegelZeros

end OAI
