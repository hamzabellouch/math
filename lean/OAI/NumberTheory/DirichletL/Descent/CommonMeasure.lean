import OAI.NumberTheory.DirichletL.Descent.SlotProducts

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open MeasureTheory CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem common_measure_energy {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (b : Ω → ℂ) (φ : κ → Ω → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hb : Integrable (fun t => ‖b t‖) μ)
    (hφ : ∀ k, Integrable (fun t => b t * φ k t) μ)
    (hbound : ∀ t, (∑ k, ‖φ k t‖ ^ 2) ≤ E) :
    (∑ k, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) ≤ E * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : Ω → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t * φ k t)
  have hF (t : Ω) : ‖F t‖ ≤ ‖b t‖ * Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE]
    change (∑ k, ‖b t * φ k t‖ ^ 2) ≤ ‖b t‖ ^ 2 * E
    simp only [norm_mul, mul_pow, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫ t, F t ∂μ) = e.symm (fun k => ∫ t, b t * φ k t ∂μ) := by
    rw [show F = (fun t => e.symm (fun k => b t * φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t, b t * φ k t ∂μ)‖ ≤
      (∫ t, ‖b t‖ ∂μ) * Real.sqrt E := by
    rw [← he, ← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt hE] at hs
  simpa [e, mul_comm] using hs

theorem integrated_hybridRow_energy {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis)),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ v ∈ bset, primaryGenerator v ≠ 0 ∧ (Ideal.absNorm v : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
    ∀ (μ : Measure Ω) (b : Ω → ℂ)
      (a : Ω → Ideal Eis → ℂ) (beta : Ω → Ideal Eis → Ideal Eis → ℂ)
      (rowPhase : Ideal Eis → Ω → ℂ) (m : ℂ),
      Integrable b μ →
      (∀ P ∈ Pset, AEStronglyMeasurable (fun t => a t P) μ) →
      (∀ n ∈ nset, ∀ v ∈ bset, AEStronglyMeasurable (fun t => beta t n v) μ) →
      (∀ k ∈ rows, AEStronglyMeasurable (rowPhase k) μ) →
      (∀ t, ∀ P ∈ Pset, ‖a t P‖ ≤ 1) →
      (∀ t, ∀ n ∈ nset, ∀ v ∈ bset, ‖beta t n v‖ ≤ 1) →
      (∀ k ∈ rows, ∀ t, ‖rowPhase k t‖ ≤ 1) →
      (∑ k ∈ rows, ‖m * ∫ t, b t * (rowPhase k t *
        hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2) ≤
      ‖m‖ ^ 2 * (C * (K * N * B) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L)) * (∫ t, ‖b t‖ ∂μ) ^ 2 := by
  obtain ⟨C, hC, he⟩ := hybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset hrows hn hv hP μ b a beta phase m
    hb haM hbetaM hphaseM ha hbeta hphase
  let E := C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L)
  have hE : 0 ≤ E := by
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    dsimp only [E]
    positivity
  let φ : rows → Ω → ℂ := fun k t => phase k t * hybridRow Pset nset bset (a t) (beta t) k
  have hbound (t : Ω) : (∑ k, ‖φ k t‖ ^ 2) ≤ E := by
    calc
      _ ≤ ∑ k : rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hphase k k.property t)
      _ = ∑ k ∈ rows, ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2 := by
        exact Finset.sum_coe_sort rows (fun k : Ideal Eis => ‖hybridRow Pset nset bset (a t) (beta t) k‖ ^ 2)
      _ ≤ E := he K N B L hK hN hB rows nset bset Pset (a t) (beta t)
        hrows hn hv hP (ha t) (hbeta t)
  have hφM (k : rows) : AEStronglyMeasurable (φ k) μ := by
    apply (hphaseM k k.property).mul
    unfold hybridRow
    apply Finset.aestronglyMeasurable_fun_sum
    intro P hPS
    simp only [div_eq_mul_inv]
    apply ((haM P hPS).mul_const _ |>.mul_const _).mul
    unfold hybridInner
    apply Finset.aestronglyMeasurable_fun_sum
    intro n hns
    apply Finset.aestronglyMeasurable_fun_sum
    intro v hvs
    exact (((hbetaM n hns v hvs).mul_const _).mul_const _).mul_const _
  have hpoint (k : rows) (t : Ω) : ‖φ k t‖ ≤ Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖)
      (Finset.mem_univ k)).trans (hbound t)
  have hint (k : rows) : Integrable (fun t => b t * φ k t) μ :=
    hb.mul_bdd (hφM k) (Filter.Eventually.of_forall (hpoint k))
  have hm := mul_le_mul_of_nonneg_left
    (common_measure_energy μ b φ E hE hb.norm hint hbound) (sq_nonneg ‖m‖)
  simp only [norm_mul, mul_pow, ← Finset.mul_sum] at hm ⊢
  rw [mul_assoc]
  rw [show (∑ k : rows, ‖∫ t, b t * φ k t ∂μ‖ ^ 2) =
      ∑ k ∈ rows, ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2 from
    Finset.sum_coe_sort rows (fun k : Ideal Eis =>
      ‖∫ t, b t * (phase k t * hybridRow Pset nset bset (a t) (beta t) k) ∂μ‖ ^ 2)] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI
