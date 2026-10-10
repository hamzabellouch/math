import OAI.Analysis.TriangularHilbert.AbsCost

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatAtBounds (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (p σ : Three → ℝ) (M : ℝ) : Prop where
  energy : ∀ v, ‖heatEnergy A h u p σ v‖ ≤ M
  first : ∀ v w, ‖heatFirst A h u p σ v w‖ ≤ M
  pure : ∀ v w, ‖heatPure A h u p σ v w‖ ≤ M
  variance : ∀ v w, ‖heatVariance A h u p σ v w‖ ≤ M
  cost : ∀ v w, ‖heatCost A h u p σ v w‖ ≤ M
  mixed : ∀ v w z, w ≠ v → z ≠ v → ‖heatMixed A h u p σ v w z‖ ≤ M

lemma heatAtBounds_of_norms (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (p : Three → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    {E L Q : ℝ} (hE : 0 ≤ E) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hr : ∀ v w, ‖heatCarrier A h u p σ v w‖^3 ≤ E)
    (hl : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)‖ ≤ L)
    (hq : ∀ w, ‖heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q) :
    HeatAtBounds A h u p σ
      (‖traceRealCLM (ι := BlockSpace ι)‖ * E * (1 + (3/2:ℝ)*L + (3/4:ℝ)*L^2 + (3/2:ℝ)*Q)) := by
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  have hN : 0 ≤ N := norm_nonneg _
  have he v : ‖heatEnergy A h u p σ v‖ ≤ N * E := by
    rw [heatEnergy_eq_localGram A hh u p hσ v v, localGram_eq_carrier A hh u p hσ v v]
    exact (norm_energy_gram_le _).trans (mul_le_mul_of_nonneg_left (hr v v) hN)
  have hf v w : ‖heatFirst A h u p σ v w‖ ≤ (3/2:ℝ)*N*L*E := by
    simp only [heatFirst, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hg v w : ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ ≤
      (3/2:ℝ)*N*Q*E := by
    simp only [localGram_eq_carrier A hh u p hσ, localSecond_eq_carrier A hh u p hσ]
    apply (norm_energyGradient_inserted_gram_le _ _).trans
    gcongr
    · exact hq w
    · exact hr v w
  have hc v w : ‖heatCost A h u p σ v w‖ ≤ (3/4:ℝ)*N*L^2*E := by
    simp only [heatCost, localGram_eq_carrier A hh u p hσ, localFirst_eq_carrier A hh u p hσ]
    apply (norm_hessianCost_inserted_gram_le _ _ (heatMask_isHermitian _)).trans
    gcongr
    · exact hl w
    · exact hr v w
  have hNE := mul_nonneg hN hE
  have hNLE := mul_nonneg (mul_nonneg hN hL) hE
  have hNL2E := mul_nonneg (mul_nonneg hN (sq_nonneg L)) hE
  have hNQE := mul_nonneg (mul_nonneg hN hQ) hE
  constructor
  · intro v; dsimp only [N] at *; nlinarith [he v]
  · intro v w; dsimp only [N] at *; nlinarith [hf v w]
  · intro v w
    have hp : ‖heatPure A h u p σ v w‖ ≤ ‖heatCost A h u p σ v w‖ +
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := norm_add_le _ _
    dsimp only [N] at *; nlinarith [hc v w, hg v w]
  · intro v w
    have hv : ‖heatVariance A h u p σ v w‖ = (1/2:ℝ) *
        ‖energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)‖ := by
      simp [heatVariance, norm_mul]
    rw [hv]; dsimp only [N] at *; nlinarith [hg v w]
  · intro v w; dsimp only [N] at *; nlinarith [hc v w]
  · intro v w z hw hz
    have hx := two_abs_heatMixed_le A hh u p hσ hw hz
    rw [← Real.norm_eq_abs] at hx
    have hwle := le_abs_self (heatCost A h u p σ v w)
    have hzle := le_abs_self (heatCost A h u p σ v z)
    rw [← Real.norm_eq_abs] at hwle hzle
    dsimp only [N] at *; nlinarith [hc v w, hc v z]

lemma HeatAtBounds.mono {A : Three → Matrix ι ι ℂ} {h : ℝ} {u : ι → ℝ}
    {p σ : Three → ℝ} {M N : ℝ} (hb : HeatAtBounds A h u p σ M) (hMN : M ≤ N) :
    HeatAtBounds A h u p σ N := by
  exact ⟨fun v => (hb.energy v).trans hMN, fun v w => (hb.first v w).trans hMN,
    fun v w => (hb.pure v w).trans hMN, fun v w => (hb.variance v w).trans hMN,
    fun v w => (hb.cost v w).trans hMN, fun v w z hw hz => (hb.mixed v w z hw hz).trans hMN⟩

lemma exists_heat_uniform_majorant (A : Three → Matrix ι ι ℂ) {h a b D : ℝ}
    (hh : 0 < h) (ha : 0 < a) (hab : a ≤ b) (hD : 0 ≤ D) (u : ι → ℝ) :
    ∃ B : (ℝ × ℝ) → ℝ, Integrable B ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (i : Three) (d : ℝ) (z : ℝ × ℝ), |d| ≤ D → ∀ (σ : Three → ℝ),
      (∀ w, a ≤ σ w) → (∀ w, σ w ≤ b) → HeatAtBounds A h u (chart i d z) σ (B z) := by
  obtain ⟨R,hR,hRB⟩ := exists_heatCarrier_gaussian_bound A hh ha hab hD u
  obtain ⟨S,hS,hSB⟩ := exists_score_polynomial_bound u ha hD
  let T := entryNormConstant (BlockSpace ι)
  let L := T*S
  let Q := T*(S^2+a⁻¹)
  have hT : 0 ≤ T := entryNormConstant_nonneg
  have hL : 0 ≤ L := mul_nonneg hT hS
  have hQ : 0 ≤ Q := mul_nonneg hT (add_nonneg (sq_nonneg _) (inv_nonneg.mpr ha.le))
  let N := ‖traceRealCLM (ι := BlockSpace ι)‖
  let C := N * R^3 * (1+(3/2:ℝ)*L+(3/4:ℝ)*L^2+(3/2:ℝ)*Q)
  have hN : 0 ≤ N := norm_nonneg _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbpos : 0 < b := ha.trans_le hab
  have hb : 0 < 1/(32*b) := by positivity
  refine ⟨fun z => C * (planePoly z^2 * planeGaussian (1/(32*b)) z),
    (integrable_planePoly_sq_gaussian hb).const_mul C,
    fun z => mul_nonneg hC (mul_nonneg (sq_nonneg _) (planeGaussian_pos _ _).le), ?_⟩
  intro i d z hd σ hσa hσb
  have hσ : ∀ w, 0 < σ w := fun w => ha.trans_le (hσa w)
  let P := planePoly z
  let G := planeGaussian (1/(32*b)) z
  have hP : 0 ≤ P := planePoly_nonneg z
  have hP1 : 1 ≤ P := one_le_planePoly z
  have hG : 0 ≤ G := (planeGaussian_pos _ _).le
  have hG1 : G ≤ 1 := planeGaussian_le_one hb.le z
  have hr v w : ‖heatCarrier A h u (chart i d z) σ v w‖^3 ≤ R^3 * G := by
    calc
      _ ≤ (R*G)^3 := pow_le_pow_left₀ (norm_nonneg _) (hRB i d z hd σ hσa hσb v w) 3
      _ = R^3*G^3 := mul_pow _ _ _
      _ ≤ R^3 * G := by gcongr; nlinarith [mul_nonneg hG (sub_nonneg.mpr hG1)]
  have hl w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a) else 0)‖ ≤ L*P := by
    calc
      _ ≤ T*(S*P) := norm_heatMask_le _ (mul_nonneg hS hP) (by
        intro a j; split_ifs
        · exact (hSB i d z hd σ hσa a j).1
        · simpa using mul_nonneg hS hP)
      _ = _ := by dsimp [L]; ring
  have hq w : ‖heatMask (fun a j => if a = w then score (u j) (chart i d z a) (σ a)^2-(σ a)⁻¹ else 0)‖ ≤ Q*P^2 := by
    calc
      _ ≤ T*((S^2+a⁻¹)*P^2) := norm_heatMask_le _ (by positivity) (by
        intro k j; split_ifs
        · exact (hSB i d z hd σ hσa k j).2
        · simpa using (show 0 ≤ (S^2+a⁻¹)*P^2 by positivity))
      _ = _ := by dsimp [Q]; ring
  apply (heatAtBounds_of_norms A hh u (chart i d z) hσ
    (mul_nonneg (pow_nonneg hR _) hG) (mul_nonneg hL hP)
    (mul_nonneg hQ (sq_nonneg P)) hr hl hq).mono
  change N*(R^3*G)*(1+(3/2:ℝ)*(L*P)+(3/4:ℝ)*(L*P)^2+(3/2:ℝ)*(Q*P^2)) ≤ C*(P^2*G)
  have hP2 : P ≤ P^2 := by nlinarith
  have h1P2 : 1 ≤ P^2 := le_trans hP1 hP2
  calc
    _ = N*R^3*G*(1+(3/2:ℝ)*L*P+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by ring
    _ ≤ N*R^3*G*(P^2+(3/2:ℝ)*L*P^2+(3/4:ℝ)*L^2*P^2+(3/2:ℝ)*Q*P^2) := by gcongr
    _ = _ := by dsimp [C]; ring
end
end TriangularHilbert.Heat
end

end OAI
