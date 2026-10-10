import OAI.NumberTheory.PiExponent.Analysis.LogarithmicContactIdeal
import OAI.NumberTheory.PiExponent.Jets.AlgebraicJetPackets
import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezout

namespace OAI

noncomputable section

namespace PiExponent.CompactJetPolynomial

open MvPolynomial AlgebraicJetPackets
open scoped BigOperators

variable {k : Type*} [Field k] {m : ℕ}

def center (c : Fin m → k) : Fin (m+1) → k := Fin.cases 1 c

def coordinates (c : Fin m → k) (G : Fin m → Polynomial k) (i : Fin (m+1)) :
    MvPolynomial (Fin (m+1)) k := inverseTriangularMap c G (X i)

def powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k) (e : Fin (m+1) → ℕ) :
    Ideal (MvPolynomial (Fin (m+1)) k) :=
  Ideal.span (Set.range (fun i => coordinates c G i ^ e i))

theorem eval_center_inverse (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    (MvPolynomial.aeval (center c)).comp (inverseTriangularMap c G) =
      MvPolynomial.aeval (0 : Fin (m+1) → k) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [center]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, ← Polynomial.aeval_algHom_apply]
    simp [center, Polynomial.coe_aeval_eq_eval, hG i]

theorem span_coordinates (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    Ideal.span (Set.range (coordinates c G)) = WeightedBezout.pointIdeal (center c) := by
  let φ := (inverseTriangularMap c G).toRingHom
  have hs : Function.Surjective φ := (triangularEquiv c G).symm.surjective
  have hc : (WeightedBezout.pointIdeal (center c)).comap φ =
      WeightedBezout.pointIdeal (0 : Fin (m+1) → k) := by
    ext P
    change MvPolynomial.aeval (center c) (inverseTriangularMap c G P) = 0 ↔
      MvPolynomial.aeval (0 : Fin (m+1) → k) P = 0
    rw [← AlgHom.comp_apply, eval_center_inverse c G hG]
  calc
    Ideal.span (Set.range (coordinates c G)) =
        (Ideal.span (Set.range (X (R := k) : Fin (m+1) → _))).map φ := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = (WeightedBezout.pointIdeal (0 : Fin (m+1) → k)).map φ := by
      congr 1
      rw [WeightedBezout.pointIdeal_eq_span]
      simp
    _ = WeightedBezout.pointIdeal (center c) := by
      rw [← hc, Ideal.map_comap_of_surjective φ hs]

theorem radical_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal c G e).radical = WeightedBezout.pointIdeal (center c) := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal (center c)).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hz : coordinates c G i ∈ WeightedBezout.pointIdeal (center c) := by
      rw [← span_coordinates c G hG]
      exact Ideal.subset_span ⟨i,rfl⟩
    change MvPolynomial.aeval (center c) (coordinates c G i ^ e i) = 0
    rw [map_pow, (WeightedBezout.mem_pointIdeal _ _).mp hz, zero_pow (he i).ne']
  · rw [← span_coordinates c G hG]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i,rfl⟩⟩

def centerPoint (c : Fin m → k) : PrimeSpectrum (MvPolynomial (Fin (m+1)) k) :=
  ⟨WeightedBezout.pointIdeal (center c), inferInstance⟩

theorem zeroLocus_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdeal c G e : Set _) = {centerPoint c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal c G hG e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem zeroLocus_finset_prod_powerIdeal {J : Type*} (s : Finset J)
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j ∈ s, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      (fun j => centerPoint (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdeal (c j) G hG e he, ih]
    simp

theorem zeroLocus_prod_powerIdeal {J : Type*} [Fintype J]
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      Set.range (fun j => centerPoint (c j)) := by
  simpa using zeroLocus_finset_prod_powerIdeal Finset.univ c G hG e he

def logPolynomials (T : Fin m → ℕ) : Fin m → Polynomial ℂ :=
  fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)

@[simp] theorem logPolynomials_eval_zero (T : Fin m → ℕ) (i : Fin m) :
    (logPolynomials T i).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp [logPolynomials, PowerSeries.coeff_trunc, PowerSeries.coeff_log]

theorem truncatedFormalJet_coordinates (c : Fin m → ℂ) (T : Fin m → ℕ)
    (i : Fin (m+1)) :
    FormalLogTruncation.truncatedFormalJet c T (coordinates c (logPolynomials T) i) =
      MvPowerSeries.X i := by
  change FormalLogTruncation.truncatedFormalJet c T
    (inverseTriangularMap c (fun j => PowerSeries.trunc (T j) (PowerSeries.log ℂ)) (X i)) = _
  rw [truncatedFormalJet_inverse]
  simp

theorem map_powerIdeal_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) :
    (powerIdeal c (logPolynomials T) e).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change FormalLogTruncation.truncatedFormalJet c T
    (coordinates c (logPolynomials T) i ^ e i) = MvPowerSeries.X i ^ e i
  rw [map_pow, truncatedFormalJet_coordinates]

theorem map_powerIdeal_pow_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (n : ℕ) :
    (powerIdeal c (logPolynomials T) e ^ n).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e ^ n := by
  rw [Ideal.map_pow, map_powerIdeal_truncatedFormalJet]

theorem truncatedFormalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogTruncation.truncatedFormalJet c T P ∈
      JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  apply JetGeometry.coordinatePowerIdeal_pow_le_rational v hv e R he n
  rw [← map_powerIdeal_pow_truncatedFormalJet c T e n]
  exact Ideal.mem_map_of_mem _ hP

theorem formalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogJet.formalJet c P ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  rw [← FormalLogTruncation.shiftMap_truncatedFormalJet c T P]
  exact FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal
    (fun i => FormalLogTruncation.logTail (T i))
    (fun i => FormalLogTruncation.logTail_constantCoeff (T i)) v hv
    (fun i => FormalLogTruncation.logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i))
    (n * R) _ (truncatedFormalJet_mem_weighted_of_mem_pow c T e v hv R he n P hP)

theorem formalJet_packet_zero_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n * R) (FormalLogJet.formalJet c P) = (fun _ => (0 : ℂ)) := by
  funext d
  exact formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n P hP d.val d.property

theorem aeval_coordinates {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (y : A) (x : Fin m → A) (i : Fin (m+1)) :
    MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i) =
      LogarithmicContactIdeal.truncatedCoordinates c y x T i := by
  cases i using Fin.cases with
  | zero => simp [coordinates, LogarithmicContactIdeal.truncatedCoordinates]
  | succ i =>
    simp only [coordinates, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, Fin.cases_succ,
      ← Polynomial.aeval_algHom_apply, Fin.cases_zero, map_one,
      LogarithmicContactIdeal.truncatedCoordinates]
    rfl

theorem map_powerIdeal_aeval {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A) :
    (powerIdeal c (logPolynomials T) e).map (MvPolynomial.aeval (Fin.cases y x)).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c y x T e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i ^ e i) =
    LogarithmicContactIdeal.truncatedCoordinates c y x T i ^ e i
  rw [map_pow, aeval_coordinates]

end PiExponent.CompactJetPolynomial

end

end OAI
