import OAI.Geometry.HeilbronnTriangle.ActualPointLaw
import OAI.Geometry.HeilbronnTriangle.MainDigitOrbitObstruction
import OAI.Geometry.HeilbronnTriangle.DigitBadTripleAverage
import OAI.Geometry.HeilbronnTriangle.PointLawBadTripleBound

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.ActualPointLaw

open Parameters FiniteFieldLabels DigitColumnLaw OrbitSampling IntegerSampling
open scoped BigOperators

variable {r : ℕ} [Fact r.Prime]

def latentSmith (D : PrimeParameterData heilbronnK r)
    (z : Fin 3 → MainDigitLaw.Latent r) :
    PrimePowerData D.B heilbronnK
      (Matrix.transpose (fun j => MainDigitLaw.column D (z j))) :=
  MainDigitLaw.smith D (tripleEquiv z).1 (tripleEquiv z).2

theorem latentSmith_moment (D : PrimeParameterData heilbronnK r)
    (labels : Fin 3 → Label r) :
    (∑ f : MainDigitLaw.Array r,
      uniformWeight (MainDigitLaw.Array r) f *
        ((D.B ^ (latentSmith D (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2 := by
  change (∑ f : MainDigitLaw.Array r,
    uniformWeight (MainDigitLaw.Array r) f *
      ((D.B ^ (MainDigitLaw.smith D labels f).b : ℕ) : ℝ)) ≤ 2
  simpa only [Nat.cast_pow] using
    MainDigitLaw.conditional_moment D labels

theorem two_lt_label_prime {r : ℕ} [Fact r.Prime]
    (D : PrimeParameterData heilbronnK r) : 2 < r := by
  have hk := D.two_le_k
  have hr := D.large_r
  have hk2 : 4 ≤ heilbronnK ^ 2 := by nlinarith
  omega

theorem latent_separation (D : PrimeParameterData heilbronnK r)
    [NeZero (D.B ^ heilbronnK)] (z : Fin 3 → MainDigitLaw.Latent r)
    (h01 : (z 0).1 ≠ (z 1).1) (h02 : (z 0).1 ≠ (z 2).1)
    (h12 : (z 1).1 ≠ (z 2).1)
    {N : ℕ} {shift : Fin 3 → ℤ} (x : Fin 3 → Box N 3 shift)
    (hx : (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
      orbitFinset (MainGroup (D.B ^ heilbronnK)) (fun j => MainDigitLaw.column D (z j))) :
    (D.tau : ℤ) < |(integralMatrix x).det| := by
  have hinj : Function.Injective (fun i => (z i).1) := by
    have hz : (![ (z 0).1, (z 1).1, (z 2).1 ] : Fin 3 → Label r) =
        (fun i => (z i).1) := by
      funext i
      fin_cases i <;> rfl
    rw [← hz]
    exact DigitBadTripleAverage.injective_labels h01 h02 h12
  exact MainDigitOrbitObstruction.det_abs_gt_of_injective_labels D
    (two_lt_label_prime D) (D.B ^ heilbronnK) rfl (tripleEquiv z).1 hinj
    (tripleEquiv z).2 (integralMatrix x) hx

def WeightedFiberBound (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2)) (K : ℝ) : Prop := by
  classical
  letI : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  exact ∀ z : Fin 3 → MainDigitLaw.Latent r, ∀ t : ℤ, |t| ≤ (D.tau : ℤ) →
    (∑ x ∈ ((IntegerPointLaw.projectedDistinctTriples D.N).filter
      (fun x => (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
        orbitFinset (MainGroup (D.B ^ heilbronnK))
          (fun j => MainDigitLaw.column D (z j)))).filter
      (fun x => (integralMatrix x).det = t),
      LiftingProbability.auxiliaryWeight D.q A.size A.weight A.sets
        (fun i => residue D.q (x i))) ≤
      K * (Real.log (2 * (D.N : ℝ))) ^ 2 * (D.N : ℝ) ^ 6 /
        (((D.B ^ (latentSmith D z).b : ℕ) : ℝ) ^ 2 *
          ((D.B ^ (latentSmith D z).e : ℕ) : ℝ) ^ 2)

theorem withAuxiliary_tripleProbability_le_of_count
    [Fintype (Label r)] (D : PrimeParameterData heilbronnK r)
    [Fact D.q.Prime] (A : AuxiliarySampling.Law D.q (D.h ^ 2))
    {K : ℝ} (hK : 0 ≤ K) (hcount : WeightedFiberBound D A K) :
    (withAuxiliary D A).tripleProbability
      (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
        ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  classical
  let : NeZero (D.B ^ heilbronnK) := ⟨pow_ne_zero _ D.base_prime.ne_zero⟩
  let : NeZero (r ^ 9) := ⟨pow_ne_zero _ D.r_pos.ne'⟩
  let : NeZero D.q := ⟨D.auxiliary_prime.ne_zero⟩
  have hN : D.liftMultiplicity * (D.B ^ heilbronnK * D.q) = D.N :=
    D.liftMultiplicity_mul_moduli
  have hwidth : 2 * (D.tau : ℤ) < (D.B ^ heilbronnK : ℕ) := by
    exact_mod_cast D.twice_tau_lt_h
  have hcard : Fintype.card (Label r) = r ^ 41 := by
    rw [← Nat.card_eq_fintype_card, FiniteFieldLabels.card_label]
    rfl
  have hb := IntegerPointLaw.ofSpecialLinear_tripleProbability_le
    (R := Real.log (2 * (D.N : ℝ)))
    D.base_prime heilbronnK_pos D.q D.liftMultiplicity A.size
    D.coprime D.auxiliary_prime.pos D.liftMultiplicity_pos A.size_pos
    (MainDigitLaw.column D) (latentSmith D) A.weight A.sets
    A.weight_nonneg A.weight_sum A.sets_card
    (show (0 : ℤ) ≤ D.tau by positivity) hwidth hK
    (latentSmith_moment D)
    (fun z h01 h02 h12 x _ hx => latent_separation D z h01 h02 h12 x hx)
    (by
      unfold WeightedFiberBound at hcount
      rw [hN]
      exact hcount)
  have hcardreal : (Fintype.card (Label r) : ℝ) = (r : ℝ) ^ 41 := by
    rw [hcard, Nat.cast_pow]
  rw [hN, hcardreal, Int.cast_natCast] at hb
  change (withAuxiliary D A).tripleProbability
    (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
    6 * (K / (21 / 64)) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
      ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) at hb
  convert hb using 1; ring

theorem tripleProbability_le_of_count
    (D : PrimeParameterData heilbronnK r) {K : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ A : @AuxiliarySampling.Law D.q (D.h ^ 2) ⟨D.auxiliary_prime⟩,
      @WeightedFiberBound r _ D ⟨D.auxiliary_prime⟩ A K) :
    (pointLaw D).tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      ((128 / 7 : ℝ) * K) * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
        ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  let : Fintype (Label r) := Fintype.ofFinite (Label r)
  let : Fact D.q.Prime := ⟨D.auxiliary_prime⟩
  unfold pointLaw
  exact withAuxiliary_tripleProbability_le_of_count D _ hK (hcount _)

end Problem355.ActualPointLaw

end

end OAI
