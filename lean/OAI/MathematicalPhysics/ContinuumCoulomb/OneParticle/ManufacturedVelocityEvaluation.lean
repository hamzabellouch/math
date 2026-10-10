import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFieldEvaluation
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserDifferenceBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserVelocityNumerics

namespace OAI

/-! The actual manufactured Moser velocity is sampled using rational
coordinate differences, the certified scalar field evaluator and π.
No value or derivative evaluator is assumed. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.ManufacturedVelocityEvaluation
open CappedKernelProgram (Triple position)
open NeutralAtom (dirPartial axis)

def precision (rho P : ℕ) : ℕ :=
  12*(1+MoserDifferenceBudget.guard*(4*rho+1))*(P+1)

def sample (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : ℚ :=
  ManufacturedFieldEvaluation.value rho (MoserDifferenceBudget.precision p) scale S sites q

def gradient (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) (a : Fin 3) : ℚ :=
  RationalFieldDifferences.first (sample rho p scale S sites) (MoserDifferenceBudget.step p) q a

def laplacian (rho p : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (q : Triple) : ℚ :=
  RationalFieldDifferences.laplacian (sample rho p scale S sites) (MoserDifferenceBudget.step p) q

def pi (p : ℕ) : ℚ := PiProgram.approximate (8*(p+1))

def component (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ))
    (t : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  let p := precision rho P;
  -(gradient rho p scale S sites q a) /
    max (rho:ℚ) (4*pi p*(rho:ℚ)+t*laplacian rho p scale S sites q)

def value (rho P : ℕ) (scale S : ℚ) (sites : List (ℚ×ℚ)) (t : ℚ) (q : Triple) : Triple :=
  (component rho P scale S sites t q 0,
    (component rho P scale S sites t q 1,component rho P scale S sites t q 2))

theorem pi_error (p : ℕ) : |(pi p:ℝ)-Real.pi| ≤ ((p:ℝ)+1)⁻¹ := by
  have h := PiProgram.error (8*(p+1)) (by omega)
  have he : 8/((8*(p+1):ℕ):ℝ) = ((p:ℝ)+1)⁻¹ := by
    push_cast
    field_simp
  exact h.trans_eq he

theorem precision_budget (rho P : ℕ) :
    3*(1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1))*
      ((precision rho P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  let A : ℝ := 1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hP : 0 < (P:ℝ)+1 := by positivity
  have hp : (precision rho P:ℝ) = 12*A*((P:ℝ)+1) := by
    simp only [precision,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,A]
  change 3*A*((precision rho P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹
  apply (mul_inv_le_iff₀ (by positivity : (0:ℝ) < (precision rho P:ℝ)+1)).mpr
  rw [hp]
  have he : ((P:ℝ)+1)⁻¹*(12*A*((P:ℝ)+1)+1) = 12*A+((P:ℝ)+1)⁻¹ := by field_simp
  rw [he]
  linarith [inv_nonneg.mpr hP.le]

theorem gradient_laplacian_error (rho p : ℕ) (hrho : 0 < rho)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale) (q : Triple) :
    (∀ a, |(gradient rho p scale S (List.ofFn u) q a:ℝ)-
      dirPartial (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i))) (axis a) (position q)| ≤ ((p:ℝ)+1)⁻¹) ∧
    |(laplacian rho p scale S (List.ofFn u) q:ℝ)-
      NeutralAtom.coordinateLaplacian (manufacturedWellField (GaussianFrequency.frequency rho) scale S
        (fun i => PlanarForcingProgram.position (u i))) (position q)| ≤ ((p:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  have hV : ContDiff ℝ 6 V := (manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)
  have hb (k : ℕ) (hk : k ≤ 6) (x : Position) :
      ‖iteratedFDeriv ℝ k V x‖ ≤ (MoserDifferenceBudget.guard:ℝ) :=
    (manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc hk x).trans MoserDifferenceBudget.guard_bound
  have hs (r : Triple) : |(sample rho p scale S (List.ofFn u) r:ℝ)-V (position r)| ≤
      ((MoserDifferenceBudget.precision p:ℝ)+1)⁻¹ :=
    ManufacturedFieldEvaluation.approximation_error rho (MoserDifferenceBudget.precision p)
      hrho hscale S u hu hc r
  have hB : (0:ℝ) ≤ MoserDifferenceBudget.guard := Nat.cast_nonneg _
  have hε : 0 ≤ ((MoserDifferenceBudget.precision p:ℝ)+1)⁻¹ :=
    inv_nonneg.mpr (add_nonneg (Nat.cast_nonneg _) zero_le_one)
  constructor
  · intro a
    have he := RationalFieldDifferences.first_error V hV _ hB hε
      (MoserDifferenceBudget.step_positive p) hb hs q a
    apply he.trans
    apply (MoserDifferenceBudget.first_budget p).trans
    apply inv_anti₀ (by positivity)
    linarith [Nat.cast_nonneg (α := ℝ) p]
  · exact (RationalFieldDifferences.laplacian_error V hV _ hB hε
      (MoserDifferenceBudget.step_positive p) hb hs q).trans (MoserDifferenceBudget.laplacian_budget p)

theorem approximation_error (rho P : ℕ) (hrho : 0 < rho)
    {scale S : ℚ} (hscale : (1:ℝ) ≤ scale) (hS : (1:ℝ) ≤ S)
    {m : ℕ} (u : Fin m → ℚ×ℚ) (hu : Function.Injective u)
    (hsep : ∀ i j, i ≠ j → 3 ≤ ‖PlanarForcingProgram.position (u i)-PlanarForcingProgram.position (u j)‖)
    (hc : ∀ i, localizedCounterterm (GaussianFrequency.frequency rho)
      (fun j => PlanarForcingProgram.position (u j)) i ≤ scale)
    (hcharge : ∀ x, |manufacturedCharge (manufacturedWellField (GaussianFrequency.frequency rho)
      scale S (fun i => PlanarForcingProgram.position (u i))) x| ≤ (rho:ℝ)/2)
    {t : ℚ} (ht : (t:ℝ) ∈ Set.Icc (0:ℝ) 1) (q : Triple) :
    ‖position (value rho P scale S (List.ofFn u) t q)-
      moserVelocity (rho:ℝ) (manufacturedWellField (GaussianFrequency.frequency rho)
        scale S (fun i => PlanarForcingProgram.position (u i))) t (position q)‖ ≤ ((P:ℝ)+1)⁻¹ := by
  let V := manufacturedWellField (GaussianFrequency.frequency rho) scale S
    (fun i => PlanarForcingProgram.position (u i))
  let p := precision rho P
  let E : ℝ := (1+(MoserDifferenceBudget.guard:ℝ)*(4*(rho:ℝ)+1))*((p:ℝ)+1)⁻¹
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hg := gradient_laplacian_error rho p hrho hscale hS u hu hsep hc q
  have hbound (a : Fin 3) : |dirPartial V (axis a) (position q)| ≤ (MoserDifferenceBudget.guard:ℝ) := by
    have he := dirPartial_iterated_norm_bound V
      ((manufacturedWellField_C7 _ _ _ _).of_le (by norm_num)) (axis a) (k := 0) (by omega) (position q)
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,show ‖axis a‖=1 by simp [axis],one_mul] at he
    exact he.trans ((manufacturedWellField_derivative_bound (GaussianFrequency.frequency rho)
      (show (0:ℝ) < scale by linarith) hS _ hsep hc (k := 1) (by omega) _).trans
      MoserDifferenceBudget.guard_bound)
  have he (a : Fin 3) : |(component rho P scale S (List.ofFn u) t q a:ℝ)-
      moserVelocity (rho:ℝ) V t (position q) a| ≤ E := by
    have hh := MoserVelocityNumerics.component_error (rho:ℝ) (by exact_mod_cast (Nat.succ_le_of_lt hrho))
      V hcharge ht (position q) a
      (gradient rho p scale S (List.ofFn u) q a) (laplacian rho p scale S (List.ofFn u) q)
      (pi p) (hbound a) (hg.1 a) hg.2 (pi_error p)
    simpa only [component,Rat.cast_div,Rat.cast_neg,Rat.cast_max,Rat.cast_natCast,Rat.cast_add,
      Rat.cast_mul,Rat.cast_ofNat,p,E] using hh
  let e : Position := position (value rho P scale S (List.ofFn u) t q)-moserVelocity (rho:ℝ) V t (position q)
  have hecoord (a : Fin 3) : |e a| ≤ E := by
    fin_cases a
    · simpa [e,value,position] using he 0
    · simpa [e,value,position] using he 1
    · simpa [e,value,position] using he 2
  have hsq : ‖e‖^2 ≤ 3*E^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
      (sq_le_sq₀ (abs_nonneg _) hE).mpr (hecoord a))
    simpa only [sq_abs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using h
  have hn : ‖e‖ ≤ 3*E := by nlinarith [norm_nonneg e,sq_nonneg E]
  apply hn.trans
  simpa only [E,p,mul_assoc] using precision_budget rho P

end ContinuumCoulomb.ManufacturedVelocityEvaluation

end

end OAI
