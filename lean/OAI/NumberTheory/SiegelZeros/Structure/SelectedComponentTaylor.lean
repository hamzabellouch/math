import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeGeneratorBridge
import OAI.NumberTheory.SiegelZeros.LocalAlgebra.LocalResidueTaylor

namespace OAI

noncomputable section
namespace SiegelZeros.W23
open SiegelZeros.W58 SiegelZerosAwei.W21
open WeightedTorusJets.W18 WeightedTorusJets.W19 Result.Workers.W57

variable {K : Type*} [Field K] [Algebra ℚ K]

local instance componentLocalHasQuotient (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

private theorem actual_residue_rat_smul {L : Type*} [CommRing L] [IsLocalRing L]
    [Algebra ℚ L] (r : ℚ) (x : L) :
    IsLocalRing.residue L (r • x) = r • IsLocalRing.residue L x := by
  exact (Ideal.Quotient.mkₐ ℚ (IsLocalRing.maximalIdeal L)).toLinearMap.map_smul r x

def rationalTorusDerivation (v : Fin 4 → K) :
    Derivation ℚ (TorusRing K) (TorusRing K) :=
  (torusDerivation K v).restrictScalars ℚ

theorem rationalTorusDerivation_commute (v w : Fin 4 → K) :
    Commute (rationalTorusDerivation v).toLinearMap
      (rationalTorusDerivation w).toLinearMap := by
  change (rationalTorusDerivation v).toLinearMap *
      (rationalTorusDerivation w).toLinearMap =
    (rationalTorusDerivation w).toLinearMap *
      (rationalTorusDerivation v).toLinearMap
  ext f
  exact torusDerivation_commute K v w f

@[simp] theorem rationalTorusDerivation_polynomial (v : Fin 4 → K)
    (F : AmbientPolynomial K) :
    rationalTorusDerivation v (algebraMap (AmbientPolynomial K) (TorusRing K) F) =
      algebraMap (AmbientPolynomial K) (TorusRing K) (rationalInvariant v F) :=
  torusDerivation_polynomial K v F

theorem iter_rationalTorus_polynomial (v : Fin 4 → K) (n : ℕ)
    (F : AmbientPolynomial K) :
    iter (rationalTorusDerivation v) n
      (algebraMap (AmbientPolynomial K) (TorusRing K) F) =
      algebraMap (AmbientPolynomial K) (TorusRing K) (iter (rationalInvariant v) n F) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iter_succ, ih, rationalTorusDerivation_polynomial, iter_succ]

theorem derivativeTriple_torus_polynomial (v : Fin 3 → Fin 4 → K)
    (a : Fin 3 → ℕ) (F : AmbientPolynomial K) :
    derivativeTriple (fun j => rationalTorusDerivation (v j)) a
      (algebraMap (AmbientPolynomial K) (TorusRing K) F) =
      algebraMap (AmbientPolynomial K) (TorusRing K)
        (derivativeTriple (fun j => rationalInvariant (v j)) a F) := by
  simp only [derivativeTriple, iter_rationalTorus_polynomial]

theorem torus_rectangleGenerators_eq_image (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ) :
    rectangleGenerators (fun j => rationalTorusDerivation (v j)) t b
        (algebraMap (AmbientPolynomial K) (TorusRing K) F) =
      algebraMap (AmbientPolynomial K) (TorusRing K) ''
        rectangleGenerators (fun j => rationalInvariant (v j)) t b F := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨derivativeTriple (fun j => rationalInvariant (v j)) a F, ⟨a, ha, rfl⟩, ?_⟩
    exact (derivativeTriple_torus_polynomial v a F).symm
  · rintro ⟨f, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (derivativeTriple_torus_polynomial v a F).symm⟩

theorem derivativeIdeal_eq_torus_rectangle_span (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ) :
    derivativeIdeal v F t b =
      Ideal.span (rectangleGenerators (fun j => rationalTorusDerivation (v j)) t b
        (algebraMap (AmbientPolynomial K) (TorusRing K) F)) := by
  rw [derivativeIdeal_eq_map_rectangle_span, Ideal.map_span,
    torus_rectangleGenerators_eq_image]

theorem localRectangleIdeal_eq_derivativeIdeal_map
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime] :
    localRectangleIdeal (L := Localization.AtPrime P)
        (fun j => rationalTorusDerivation (v j)) t b
        (algebraMap (AmbientPolynomial K) (TorusRing K) F) =
      (derivativeIdeal v F t b).map
        (algebraMap (TorusRing K) (Localization.AtPrime P)) := by
  rw [derivativeIdeal_eq_torus_rectangle_span, Ideal.map_span]
  rfl

theorem component_next_rectangle_mem_maximal
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) :
    ∀ g ∈ rectangleGenerators (fun j => rationalTorusDerivation (v j)) t (b+1)
      (algebraMap (AmbientPolynomial K) (TorusRing K) F),
      algebraMap (TorusRing K) (Localization.AtPrime P) g ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  intro g hg
  have hgP : g ∈ P := hP (by
    rw [derivativeIdeal_eq_torus_rectangle_span]
    exact Ideal.subset_span hg)
  change g ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime P)).under (TorusRing K)
  rw [Localization.AtPrime.under_maximalIdeal]
  exact hgP

abbrev componentDerivation (P : Ideal (TorusRing K)) [P.IsPrime]
    (v : Fin 4 → K) : Derivation ℚ (Localization.AtPrime P) (Localization.AtPrime P) :=
  localizedDerivation (K := ℚ) (A := TorusRing K) (S := Localization.AtPrime P)
    P.primeCompl (rationalTorusDerivation v)

def componentJet (v : Fin 3 → Fin 4 → K) (t : Fin 3 → ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Localization.AtPrime P →+*
      RectangleJet (IsLocalRing.ResidueField (Localization.AtPrime P))
        (t 0+1) (t 1+1) (t 2+1) :=
  rectangularJetHom _ (componentDerivation P (v 0)) (componentDerivation P (v 1))
    (componentDerivation P (v 2)) (IsLocalRing.residue _) (t 0+1) (t 1+1) (t 2+1)

theorem localized_derivativeIdeal_le_componentJet_ker
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) :
    (derivativeIdeal v F t b).map
      (algebraMap (TorusRing K) (Localization.AtPrime P)) ≤ RingHom.ker (componentJet v t P) := by
  rw [← localRectangleIdeal_eq_derivativeIdeal_map]
  unfold componentJet componentDerivation
  rw [← localizedRectangularJet_eq_residueTaylor
    (R := TorusRing K) (L := Localization.AtPrime P) P.primeCompl
    (rationalTorusDerivation (v 0)) (rationalTorusDerivation (v 1))
    (rationalTorusDerivation (v 2)) (t 0+1) (t 1+1) (t 2+1)]
  apply localRectangleIdeal_le_ker P.primeCompl
    (fun j => rationalTorusDerivation (v j))
    (fun i j => rationalTorusDerivation_commute (v i) (v j))
    (localResidueOnBase (L := Localization.AtPrime P)) t b
    (algebraMap (AmbientPolynomial K) (TorusRing K) F)
    (localResidueOnBase_unit (L := Localization.AtPrime P) P.primeCompl)
  intro g hg
  exact (IsLocalRing.residue_eq_zero_iff _).mpr
    (component_next_rectangle_mem_maximal v F t b P hP g hg)

def componentTaylor (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t : Fin 3 → ℕ) (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) :
    (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
      (algebraMap (TorusRing K) (Localization.AtPrime P))) →+*
      RectangleJet (IsLocalRing.ResidueField (Localization.AtPrime P))
        (t 0+1) (t 1+1) (t 2+1) :=
  Ideal.Quotient.lift _ (componentJet v t P)
    (fun x hx => (RingHom.mem_ker (f := componentJet v t P) (r := x)).mp
      (localized_derivativeIdeal_le_componentJet_ker v F t b P hP hx))

@[simp] theorem componentTaylor_mk (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t : Fin 3 → ℕ) (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (f : Localization.AtPrime P) :
    componentTaylor v F t b P hP (Ideal.Quotient.mk _ f) = componentJet v t P f := rfl

def componentFormalSeries (v : Fin 3 → Fin 4 → K)
    (P : Ideal (TorusRing K)) [P.IsPrime] (f : Localization.AtPrime P) :
    Series₃ (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
  PowerSeries.map (PowerSeries.map (PowerSeries.map (IsLocalRing.residue _)))
    (taylorHom₃ (componentDerivation P (v 0)) (componentDerivation P (v 1))
      (componentDerivation P (v 2)) f)

theorem componentFormalSeries_coeff (v : Fin 3 → Fin 4 → K)
    (P : Ideal (TorusRing K)) [P.IsPrime] (f : Localization.AtPrime P) (i j k : ℕ) :
    PowerSeries.coeff k (PowerSeries.coeff j (PowerSeries.coeff i
      (componentFormalSeries v P f))) =
    (1 / (k.factorial : ℚ)) • ((1 / (j.factorial : ℚ)) • ((1 / (i.factorial : ℚ)) •
      IsLocalRing.residue _ (iter (componentDerivation P (v 2)) k
        (iter (componentDerivation P (v 1)) j (iter (componentDerivation P (v 0)) i f))))) := by
  unfold componentFormalSeries
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map,
    coeff_taylorHom₃, actual_residue_rat_smul, actual_residue_rat_smul,
    actual_residue_rat_smul]

theorem componentTaylor_mk_eq_projection (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (f : Localization.AtPrime P) :
    componentTaylor v F t b P hP (Ideal.Quotient.mk _ f) =
      rectangleProjection _ (t 0+1) (t 1+1) (t 2+1) (componentFormalSeries v P f) := rfl

theorem exists_componentTaylor_of_rectangle_vanishing
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K) (t : Fin 3 → ℕ)
    (hF : F ≠ 0)
    (hvanish : ∀ a : Fin 3 → ℕ, (∀ j, a j ≤ 4 * t j) →
      MvPolynomial.eval (fun _ : Fin 4 => 1) (mixedInvariant v a F) = 0) :
    ∃ b, b < 4 ∧ ∃ P : PrimeSpectrum (TorusRing K),
      P.asIdeal ≤ identityIdeal K ∧
      P.asIdeal ∈ (derivativeIdeal v F t b).minimalPrimes ∧
      P.asIdeal ∈ (derivativeIdeal v F t (b+1)).minimalPrimes ∧
      ((derivativeIdeal v F t b).map
        (algebraMap (TorusRing K) (Localization.AtPrime P.asIdeal))).radical =
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
      ∃ Φ : (Localization.AtPrime P.asIdeal ⧸ (derivativeIdeal v F t b).map
          (algebraMap (TorusRing K) (Localization.AtPrime P.asIdeal))) →+*
          RectangleJet (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal))
            (t 0+1) (t 1+1) (t 2+1),
        ∀ f : Localization.AtPrime P.asIdeal, Φ (Ideal.Quotient.mk _ f) =
          rectangleProjection _ (t 0+1) (t 1+1) (t 2+1)
            (componentFormalSeries v P.asIdeal f) := by
  obtain ⟨b, hb, P, hPid, hPb, hPnext, hrad⟩ :=
    derivativeIdeals_common_component v F t hF hvanish
  refine ⟨b, hb, P, hPid, hPb, hPnext, hrad,
    componentTaylor v F t b P.asIdeal hPnext.1.2, ?_⟩
  intro f
  exact componentTaylor_mk_eq_projection v F t b P.asIdeal hPnext.1.2 f

end SiegelZeros.W23

end

noncomputable section
namespace SiegelZeros.W23
open SiegelZeros.W58 SiegelZerosAwei.W21 Result.Workers.W57

variable {K : Type*} [Field K] [Algebra ℚ K]

@[reducible] local instance selectedLocalRatModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module ℚ (Localization.AtPrime P) := Algebra.toModule

@[reducible] local instance selectedLocalBaseModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module K (Localization.AtPrime P) := Algebra.toModule

@[reducible] local instance selectedLocalTorusModule
    (P : Ideal (TorusRing K)) [P.IsPrime] :
    Module (TorusRing K) (Localization.AtPrime P) := Algebra.toModule

local instance selectedLocalHasQuotient (P : Ideal (TorusRing K)) [P.IsPrime] :
    HasQuotient (Localization.AtPrime P) (Ideal (Localization.AtPrime P)) :=
  @Ideal.instHasQuotient (Localization.AtPrime P) inferInstance

theorem componentDerivation_eq_localTorus_restrict
    (P : Ideal (TorusRing K)) [P.IsPrime] (v : Fin 4 → K) :
    componentDerivation P v =
      Derivation.restrictScalars ℚ (S := K)
        (A := Localization.AtPrime P) (M := Localization.AtPrime P)
        (WeightedTorusJets.W18.localTorusDerivation K P v) := by
  apply WeightedTorusJets.W18.localization_derivation_ext
    (K := ℚ) (A := TorusRing K) (S := Localization.AtPrime P) P.primeCompl
  intro f
  simp only [componentDerivation, WeightedTorusJets.W18.localizedDerivation_algebraMap,
    Derivation.restrictScalars_apply, WeightedTorusJets.W18.localTorusDerivation_algebraMap,
    rationalTorusDerivation]

theorem componentJet_ker_mono_cutoff (v : Fin 3 → Fin 4 → K)
    (s t : Fin 3 → ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hst : ∀ j, s j ≤ t j) :
    RingHom.ker (componentJet v t P) ≤ RingHom.ker (componentJet v s P) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  change rectangleProjection _ (t 0+1) (t 1+1) (t 2+1)
    (componentFormalSeries v P f) = 0 at hf
  change rectangleProjection _ (s 0+1) (s 1+1) (s 2+1)
    (componentFormalSeries v P f) = 0
  rw [rectangleProjection_eq_zero_iff] at hf ⊢
  intro i hi j hj k hk
  exact hf i (hi.trans_le (Nat.add_le_add_right (hst 0) 1))
    j (hj.trans_le (Nat.add_le_add_right (hst 1) 1))
    k (hk.trans_le (Nat.add_le_add_right (hst 2) 1))

theorem localized_derivativeIdeal_le_smaller_componentJet_ker
    (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t s : Fin 3 → ℕ) (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j) :
    (derivativeIdeal v F t b).map
      (algebraMap (TorusRing K) (Localization.AtPrime P)) ≤ RingHom.ker (componentJet v s P) :=
  (localized_derivativeIdeal_le_componentJet_ker v F t b P hP).trans
    (componentJet_ker_mono_cutoff v s t P hst)

def smallerComponentTaylor (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t s : Fin 3 → ℕ) (b : ℕ) (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j) :
    (Localization.AtPrime P ⧸ (derivativeIdeal v F t b).map
      (algebraMap (TorusRing K) (Localization.AtPrime P))) →+*
      RectangleJet (IsLocalRing.ResidueField (Localization.AtPrime P))
        (s 0+1) (s 1+1) (s 2+1) :=
  Ideal.Quotient.lift _ (componentJet v s P)
    (fun x hx => (RingHom.mem_ker (f := componentJet v s P) (r := x)).mp
      (localized_derivativeIdeal_le_smaller_componentJet_ker v F t s b P hP hst hx))

@[simp] theorem smallerComponentTaylor_mk (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t s : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j)
    (f : Localization.AtPrime P) :
    smallerComponentTaylor v F t s b P hP hst (Ideal.Quotient.mk _ f) =
      componentJet v s P f := rfl

theorem smallerComponentTaylor_mk_eq_projection (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t s : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j)
    (f : Localization.AtPrime P) :
    smallerComponentTaylor v F t s b P hP hst (Ideal.Quotient.mk _ f) =
      rectangleProjection _ (s 0+1) (s 1+1) (s 2+1) (componentFormalSeries v P f) := rfl

theorem smallerComponentTaylor_coeff (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t s : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j)
    (f : Localization.AtPrime P) (i j k : ℕ)
    (hi : i < s 0+1) (hj : j < s 1+1) (hk : k < s 2+1) :
    rectangleCoeff _ (s 0+1) (s 1+1) (s 2+1) i j k hi hj hk
      (smallerComponentTaylor v F t s b P hP hst (Ideal.Quotient.mk _ f)) =
      (1 / (k.factorial : ℚ)) • ((1 / (j.factorial : ℚ)) • ((1 / (i.factorial : ℚ)) •
        IsLocalRing.residue _ (iter (componentDerivation P (v 2)) k
          (iter (componentDerivation P (v 1)) j (iter (componentDerivation P (v 0)) i f))))) := by
  rw [smallerComponentTaylor_mk_eq_projection, rectangleCoeff_projection]
  exact componentFormalSeries_coeff v P f i j k

theorem smallerComponentTaylor_residue (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t s : Fin 3 → ℕ) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (hst : ∀ j, s j ≤ t j)
    (f : Localization.AtPrime P) :
    rectangleResidue _ (s 0+1) (s 1+1) (s 2+1)
      (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
      (smallerComponentTaylor v F t s b P hP hst (Ideal.Quotient.mk _ f)) =
      IsLocalRing.residue _ f := by
  rw [smallerComponentTaylor_mk]
  exact rectangleResidue_taylor _ _ _ _ _ _ _ _ _ _ _ f

def selectedCutoffs (t : Fin 3 → ℕ) (S : Set (Fin 3)) : Fin 3 → ℕ := by
  classical
  exact fun j => if j ∈ S then t j else 0

@[simp] theorem selectedCutoffs_of_mem (t : Fin 3 → ℕ) (S : Set (Fin 3))
    (j : Fin 3) (hj : j ∈ S) : selectedCutoffs t S j = t j := by
  classical
  simp [selectedCutoffs, hj]

@[simp] theorem selectedCutoffs_of_not_mem (t : Fin 3 → ℕ) (S : Set (Fin 3))
    (j : Fin 3) (hj : j ∉ S) : selectedCutoffs t S j = 0 := by
  classical
  simp [selectedCutoffs, hj]

theorem selectedCutoffs_le (t : Fin 3 → ℕ) (S : Set (Fin 3)) :
    ∀ j, selectedCutoffs t S j ≤ t j := by
  classical
  intro j
  simp only [selectedCutoffs]
  split_ifs <;> simp

theorem selectedCutoffs_multiindex_iff (t : Fin 3 → ℕ) (S : Set (Fin 3))
    (α : Fin 3 → ℕ) :
    (∀ j, α j ≤ selectedCutoffs t S j) ↔
      (∀ j, α j ≤ t j) ∧ (∀ j, j ∉ S → α j = 0) := by
  constructor
  · intro hα
    refine ⟨fun j => (hα j).trans (selectedCutoffs_le t S j), ?_⟩
    intro j hj
    exact Nat.eq_zero_of_le_zero (by simpa only [selectedCutoffs_of_not_mem t S j hj] using hα j)
  · rintro ⟨hα, hsupp⟩ j
    by_cases hj : j ∈ S
    · simpa only [selectedCutoffs_of_mem t S j hj] using hα j
    · simp only [selectedCutoffs_of_not_mem t S j hj, hsupp j hj, le_refl]

def selectedComponentTaylor (v : Fin 3 → Fin 4 → K) (F : AmbientPolynomial K)
    (t : Fin 3 → ℕ) (S : Set (Fin 3)) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) :=
  smallerComponentTaylor v F t (selectedCutoffs t S) b P hP (selectedCutoffs_le t S)

@[simp] theorem selectedComponentTaylor_mk (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (S : Set (Fin 3)) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (f : Localization.AtPrime P) :
    selectedComponentTaylor v F t S b P hP (Ideal.Quotient.mk _ f) =
      componentJet v (selectedCutoffs t S) P f := rfl

theorem selectedComponentTaylor_mk_eq_projection (v : Fin 3 → Fin 4 → K)
    (F : AmbientPolynomial K) (t : Fin 3 → ℕ) (S : Set (Fin 3)) (b : ℕ)
    (P : Ideal (TorusRing K)) [P.IsPrime]
    (hP : derivativeIdeal v F t (b+1) ≤ P) (f : Localization.AtPrime P) :
    selectedComponentTaylor v F t S b P hP (Ideal.Quotient.mk _ f) =
      rectangleProjection _ (selectedCutoffs t S 0+1) (selectedCutoffs t S 1+1)
        (selectedCutoffs t S 2+1) (componentFormalSeries v P f) := rfl

end SiegelZeros.W23

end

end OAI
