import OAI.Combinatorics.Progressions.Probability.AllocatedAmbientProjectedDensityMultiple

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

def allocatedProjectedAmbientLog (m q A : ℕ) (P : ℝ) : ℝ :=
  (P ^ 2 + 1) * allocatedAmbientLog m P + 3 * P + 2 * (q + 2 : ℕ) +
    (P + (q + 2 : ℕ) + A) ^ A

theorem allocatedProjectedAmbientConstants_exp_bounds (q A : ℕ)
    (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L)
    (d : Fin m → ℕ) (C V : Fin m → ℝ≥0) {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hd : ∀ j, (d j : ℝ) ≤ P) (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (L : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    let count := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cap := allocatedAmbientFactorCap (G := G) B R σ L V ^ count
    let densityLip := count * allocatedAmbientFactorLip (G := G) B R σ L d C V * cap
    let sectionLip : ℝ≥0 := Fintype.card (Finset (Fin q)) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip : ℝ≥0 := ∑ j : Fin m,
      (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    (cap : ℝ) ≤ Real.exp (allocatedProjectedAmbientLog m q A P) ∧
      ((densityLip * sectionLip * reconstructionLip : ℝ≥0) : ℝ) ≤
        Real.exp (allocatedProjectedAmbientLog m q A P) := by
  intro count cap densityLip sectionLip reconstructionLip
  let Q := allocatedAmbientLog m P
  have hQ : 0 ≤ Q := allocatedAmbientLog_nonneg m hP
  obtain ⟨hcap, hlip⟩ := allocatedAmbientConstants_exp_bounds B R σ L hL d C V hP hm
    hR hσ hRP hσP hcount hI hn hd hAP hLP hCP hVP
  have hcnt : (count : ℝ) ≤ P ^ 2 := by
    change (Fintype.card (Σ j : Fin m, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _ : Fin m, P := Finset.sum_le_sum (fun j _ => hcount j)
      _ = (m : ℝ) * P := by simp
      _ ≤ _ := by nlinarith
  have hc : (cap : ℝ) ≤ Real.exp (P ^ 2 * Q) := by
    simp only [cap, NNReal.coe_pow]
    apply (pow_le_pow_left₀ (NNReal.coe_nonneg _) hcap count).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcnt hQ)
  have hcntE : (count : ℝ) ≤ Real.exp (2 * P) := by
    calc
      _ ≤ P ^ 2 := hcnt
      _ ≤ Real.exp P ^ 2 := pow_le_pow_left₀ hP (by linarith [Real.add_one_le_exp P]) 2
      _ = _ := (Real.exp_nat_mul P 2).symm
  have hdl : (densityLip : ℝ) ≤ Real.exp ((P ^ 2 + 1) * Q + 2 * P) := by
    simp only [densityLip, NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp (2 * P) * Real.exp Q * Real.exp (P ^ 2 * Q) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsites : (Fintype.card (Finset (Fin q)) : ℝ) ≤ Real.exp (q + 2 : ℕ) := by
    simp only [Fintype.card_finset, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    apply (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2 q).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hsl : (sectionLip : ℝ) ≤ Real.exp ((q + 2 : ℕ) + (P + (q + 2 : ℕ) + A) ^ A) := by
    simp only [sectionLip, NNReal.coe_mul, NNReal.coe_natCast, Real.toNNReal_of_nonneg (Real.exp_nonneg _)]
    exact (mul_le_mul_of_nonneg_right hsites (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  have hrl : (reconstructionLip : ℝ) ≤ Real.exp (P + (q + 2 : ℕ)) := by
    simp only [reconstructionLip, NNReal.coe_sum, NNReal.coe_natCast]
    calc
      _ ≤ ∑ _j : Fin m, Real.exp (q + 2 : ℕ) := Finset.sum_le_sum (fun j _ =>
        (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hsites)
      _ = (m : ℝ) * Real.exp (q + 2 : ℕ) := by simp
      _ ≤ Real.exp P * Real.exp (q + 2 : ℕ) := mul_le_mul_of_nonneg_right
        (hm.trans (by linarith [Real.add_one_le_exp P])) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  constructor
  · apply hc.trans (Real.exp_le_exp.mpr ?_)
    unfold allocatedProjectedAmbientLog
    have hpow : 0 ≤ (P + (q + 2 : ℕ) + A) ^ A := by positivity
    change P ^ 2 * Q ≤ (P ^ 2 + 1) * Q + 3 * P + 2 * (q + 2 : ℕ) + (P + (q + 2 : ℕ) + A) ^ A
    nlinarith
  · simp only [NNReal.coe_mul]
    calc
      _ ≤ Real.exp ((P ^ 2 + 1) * Q + 2 * P) *
          Real.exp ((q + 2 : ℕ) + (P + (q + 2 : ℕ) + A) ^ A) *
          Real.exp (P + (q + 2 : ℕ)) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold allocatedProjectedAmbientLog; ring

theorem exists_allocatedProjectedAmbientLog_bound (m q A : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ P : ℝ, 0 ≤ P →
      allocatedProjectedAmbientLog m q A P ≤ (P + K) ^ K := by
  let X : Polynomial ℕ := Polynomial.X
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m + 1) * (4 * (X + 8)) + 8)
  let common := X + X * scalar + 1
  let width := Polynomial.C (m + 4) * (X + 8)
  let mixed := (2 * X + 1) * (width + common) + 3 * X + 1
  let ambient := X + X * (2 * mixed + 4 * X + 9) + 1
  let poly := (X ^ 2 + 1) * ambient + 3 * X + Polynomial.C (2 * (q + 2)) +
    (X + Polynomial.C (q + 2) + Polynomial.C A) ^ A
  obtain ⟨K, hK, hk⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨K, hK, ?_⟩
  intro P hP
  simpa [poly, ambient, mixed, width, common, scalar, X,
    allocatedProjectedAmbientLog, allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog,
    allocatedCommonLog, allocatedScalarLog, integerInterpolationLogEnvelope,
    Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hk P hP

end Erdos3.VectorPolynomial

end

end OAI
