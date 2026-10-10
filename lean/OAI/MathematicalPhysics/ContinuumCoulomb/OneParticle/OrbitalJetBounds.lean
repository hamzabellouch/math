import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianJetBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeJets
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFieldBounds

namespace OAI

/-! Uniform fourth-order bounds for the actual localized orbitals and
products used in the compressed nuclear coefficients. -/

noncomputable section
namespace ContinuumCoulomb

theorem fourJet_linear_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ)
    (hf : ContDiff ℝ 4 f) {B D : ℝ} (hB : 0 ≤ B) (hD : 1 ≤ D) (hL : ‖L‖ ≤ D)
    (hb : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B) {k : ℕ} (hk : k ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ B*D^4 := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  have h := (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at h
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f (L x)‖*‖L‖^k := h
    _ ≤ B*D^k := mul_le_mul (hb k hk (L x))
      (pow_le_pow_left₀ (norm_nonneg L) hL k) (pow_nonneg (norm_nonneg L) k) hB
    _ ≤ B*D^4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD hk) hB

theorem fourJet_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 4 f) (hg : ContDiff ℝ 4 g)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ A)
    (hb : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ B)
    {k : ℕ} (hk : k ≤ 4) (x : E) :
    ‖iteratedFDeriv ℝ k (fun x => f x*g x) x‖ ≤ 16*A*B := by
  apply (norm_iteratedFDeriv_mul_le hf hg x (by exact_mod_cast hk)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i (hi'.trans hk) x) (Nat.cast_nonneg _))
        (hb (k-i) ((Nat.sub_le k i).trans hk) x) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2:ℝ)^k*A*B := by
      rw [← Finset.sum_mul,← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ 16*A*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ hA
      exact (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hk).trans_eq (by norm_num)

theorem continuumLocalizedMode_jets_bounded {freq : ℝ} (hfreq : 0 < freq) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ u k, k ≤ 4 → ∀ x,
      ‖iteratedFDeriv ℝ k (continuumLocalizedMode freq u) x‖ ≤ B := by
  obtain ⟨A,hA,ha⟩ := normalized_planar_mode_jets_bounded
  obtain ⟨B,hB,hb⟩ := vertical_mode_jets_bounded hfreq
  let P := max 1 ‖wellPlanarProjection‖
  let Q := max 1 ‖wellVerticalProjection‖
  have hP : 1 ≤ P := le_max_left _ _
  have hQ : 1 ≤ Q := le_max_left _ _
  have hPA : 0 ≤ A*P^4 := by positivity
  have hQB : 0 ≤ B*Q^4 := by positivity
  refine ⟨16*(A*P^4)*(B*Q^4)+1,by nlinarith [mul_nonneg hPA hQB],?_⟩
  intro u k hk x
  let f : Position → ℝ := (fun r => normalizedPlanarMode (r-u)) ∘ wellPlanarProjection
  let g : Position → ℝ := verticalMode freq ∘ wellVerticalProjection
  have hf : ContDiff ℝ 4 f :=
    ((normalizedPlanarMode_C7.of_le (by norm_num)).comp (contDiff_id.sub contDiff_const)).comp
      wellPlanarProjection.contDiff
  have hg : ContDiff ℝ 4 g := ((verticalMode_smooth freq).of_le (by simp)).comp wellVerticalProjection.contDiff
  have hfa (j : ℕ) (hj : j ≤ 4) (y : Position) : ‖iteratedFDeriv ℝ j f y‖ ≤ A*P^4 := by
    apply fourJet_linear_comp wellPlanarProjection _
      ((normalizedPlanarMode_C7.of_le (by norm_num)).comp (contDiff_id.sub contDiff_const))
      (by linarith) hP (le_max_right _ _) _ hj y
    intro l hl r
    change ‖iteratedFDeriv ℝ l (fun x => normalizedPlanarMode (x-u)) r‖ ≤ A
    rw [iteratedFDeriv_comp_sub]
    exact ha l hl (r-u)
  have hgb (j : ℕ) (hj : j ≤ 4) (y : Position) : ‖iteratedFDeriv ℝ j g y‖ ≤ B*Q^4 :=
    fourJet_linear_comp wellVerticalProjection _ ((verticalMode_smooth freq).of_le (by simp))
      (by linarith) hQ (le_max_right _ _) hb hj y
  exact (fourJet_mul hf hg hPA hQB hfa hgb hk x).trans (by linarith)

end ContinuumCoulomb

end

end OAI
