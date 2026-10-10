import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.AutomaticCalibrationNormalization

namespace OAI

/-! A fixed positive rational prefactor in the physical amplification is
absorbed into the requested edge weight. This retains the proved evaluator
and bisection, including their polynomial running times. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorCalibration

def adjustedWeight (a K : ℚ) : ℚ := K / a^2
def precision (C P : ℕ) : ℕ := C*(P+1)
def input (a : ℚ) (C : ℕ) (x : AutomaticCalibration.Input) : AutomaticCalibration.Input :=
  (x.1,(precision C x.2.1,adjustedWeight a x.2.2))
def value (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ)
    (x : AutomaticCalibration.Input) : ℚ :=
  AutomaticCalibration.value rho ε c k A B (input a C x)
def normalizedValue (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ) (k A B : ℕ)
    (x : AutomaticCalibration.Input) : ℚ :=
  value rho a C ε c k A B x / AutomaticCalibration.spacing c k x.1

theorem normalizedValue_mem (rho : ℕ) (a : ℚ) (C : ℕ) {ε c : ℚ}
    (hε : 0 ≤ ε) (hc : 0 < c) (k A B : ℕ) (x : AutomaticCalibration.Input)
    (hN : 0 < x.1) : normalizedValue rho a C ε c k A B x ∈
      Set.Icc (1-ε/2) (1+ε/2) :=
  AutomaticCalibration.normalizedValue_mem rho hε hc k A B (input a C x) hN

theorem target_scale {a : ℝ} (ha : 0 < a) (freq τ K d : ℝ) :
    a*coulombHoppingTarget freq τ (K/a^2) d = coulombHoppingTarget freq τ K d := by
  unfold coulombHoppingTarget
  rw [show K/a^2*(localizedCoulombProfile freq 0-localizedCoulombProfile freq d) =
    (K*(localizedCoulombProfile freq 0-localizedCoulombProfile freq d))/a^2 by ring,
    Real.sqrt_div' _ (sq_nonneg a),Real.sqrt_sq ha.le]
  field_simp [ha.ne']

theorem weight_polynomial_range {a : ℚ} (ha : 0 < a) (A : ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∀ (N : ℝ), 2 ≤ N → ∀ K : ℚ,
      (N^A)⁻¹ ≤ (K:ℝ) → (K:ℝ) ≤ N^A →
      (N^(A+L))⁻¹ ≤ (adjustedWeight a K:ℝ) ∧
        (adjustedWeight a K:ℝ) ≤ N^(A+L) := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have ha2 : 0 < ((a:ℝ)^2)⁻¹ := inv_pos.mpr (sq_pos_of_pos haR)
  obtain ⟨L,hL,hbound⟩ := exists_polynomial_constant_bounds ha2 (((a:ℝ)^2)⁻¹)
  refine ⟨L,hL,fun N hN K hlo hhi => ?_⟩
  have hNp : 0 < N := by linarith
  have hK : (0:ℝ) ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hlo
  obtain ⟨hcl,hcu⟩ := hbound N hN
  have he : (adjustedWeight a K:ℝ) = (K:ℝ)*((a:ℝ)^2)⁻¹ := by
    rw [adjustedWeight,Rat.cast_div,Rat.cast_pow,div_eq_mul_inv]
  rw [he,pow_add,mul_inv_rev]
  constructor
  · have hm := mul_le_mul hlo hcl (inv_nonneg.mpr (pow_nonneg hNp.le L)) hK
    simpa only [mul_comm] using hm
  · exact mul_le_mul hhi hcu ha2.le (pow_nonneg hNp.le A)

theorem precision_error {a : ℝ} {C : ℕ} (_ha : 0 ≤ a) (hC : a ≤ C) (P : ℕ) :
    a*((precision C P:ℝ)+1)⁻¹ ≤ ((P:ℝ)+1)⁻¹ := by
  rw [← div_eq_mul_inv,inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right hC (by positivity : (0:ℝ) ≤ (P:ℝ)+1)
  simp only [precision,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  nlinarith

theorem exists_calibration (rho : ℕ) (hrho : 0 < rho)
    (a : ℚ) (ha : 0 < a) (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (A B : ℕ) (kmin : ℝ) :
    ∃ (C L : ℕ) (c : ℚ) (k : ℕ), 0 < C ∧ 0 < L ∧ 0 < c ∧ 0 < k ∧ kmin ≤ (k:ℝ) ∧
      ∀ (N P : ℕ) (K : ℚ), 2 ≤ N → ((N:ℝ)^A)⁻¹ ≤ K → (K:ℝ) ≤ (N:ℝ)^A →
        let d := value rho a C ε c k (A+L) B (N,(P,K))
        let D := (k:ℝ)*Real.log (N:ℝ)
        (1-(ε:ℝ))*D ≤ d ∧ (d:ℝ) ≤ (1+(ε:ℝ))*D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0-
              localizedCoulombProfile (GaussianFrequency.frequency rho) d ∧
          |(a:ℝ)*(N:ℝ)^k*planarHopping d-
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d| ≤
              ((P:ℝ)+1)⁻¹ := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  obtain ⟨C,hC⟩ := exists_nat_gt (max 1 (a:ℝ))
  have hCp : 0 < C := by
    have hp : (0:ℝ) < C := lt_trans zero_lt_one ((le_max_left _ _).trans_lt hC)
    exact_mod_cast hp
  have hCa : (a:ℝ) ≤ C := ((le_max_right _ _).trans_lt hC).le
  obtain ⟨L,hL,hweights⟩ := weight_polynomial_range ha A
  obtain ⟨c,k,hc,hk,hkmin,hcal⟩ := AutomaticCalibration.exists_automatic_calibration
    rho hrho ε hε hε1 (A+L) B kmin
  refine ⟨C,L,c,k,hCp,hL,hc,hk,hkmin,fun N P K hN hlo hhi => ?_⟩
  obtain ⟨hwl,hwu⟩ := hweights N (by exact_mod_cast hN) K hlo hhi
  obtain ⟨hdl,hdu,hgap,herror⟩ := hcal N (precision C P) (adjustedWeight a K) hN hwl hwu
  change (1-(ε:ℝ))*((k:ℝ)*Real.log (N:ℝ)) ≤
    AutomaticCalibration.value rho ε c k (A+L) B (N,(precision C P,adjustedWeight a K)) ∧ _
  refine ⟨hdl,hdu,hgap,?_⟩
  let d := AutomaticCalibration.value rho ε c k (A+L) B (N,(precision C P,adjustedWeight a K))
  have ht := target_scale haR (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d
  have hweight : (adjustedWeight a K:ℝ) = (K:ℝ)/(a:ℝ)^2 := by
    simp only [adjustedWeight,Rat.cast_div,Rat.cast_pow]
  rw [hweight] at herror
  change |(a:ℝ)*(N:ℝ)^k*planarHopping d-
    coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹ K d| ≤ ((P:ℝ)+1)⁻¹
  calc
    _ = |(a:ℝ)*((N:ℝ)^k*planarHopping d-
        coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
          ((K:ℝ)/(a:ℝ)^2) d)| := by rw [mul_sub,ht]; congr 1; ring
    _ = (a:ℝ)*|(N:ℝ)^k*planarHopping d-
        coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
          ((K:ℝ)/(a:ℝ)^2) d| := by rw [abs_mul,abs_of_pos haR]
    _ ≤ (a:ℝ)*((precision C P:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_left herror haR.le
    _ ≤ ((P:ℝ)+1)⁻¹ := precision_error haR.le hCa P

end ContinuumCoulomb.PrefactorCalibration

end

end OAI
