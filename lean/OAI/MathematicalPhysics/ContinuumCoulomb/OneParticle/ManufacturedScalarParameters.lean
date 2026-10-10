import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardTolerance
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ComplementParameterBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.ComplementSmallness
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ShiftedHubbardBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCounterterms

namespace OAI

/-! A single polynomial exponent closes the numerical hypotheses of the
full-domain manufactured-grid comparison. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open HubbardGlobal

theorem manufactured_scalar_parameters {freq rho a γ δ B : ℝ}
    (hf : 1 ≤ freq) (hrho : 0 ≤ rho) (ha : 0 < a)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1/4) (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ q qG : ℕ, 1 ≤ q ∧ 1 ≤ qG ∧
    ∀ r v p k : ℕ, q+9*r+v+p ≤ k → ∀ N D : ℝ,
      2 ≤ N → 25*(k:ℝ)*Real.log N ≤ D →
    ∀ {Edge : Type} [Fintype Edge] (m : ℕ) (u : Fin (m+1) → PlanarPosition)
      (left right : Edge → Fin (m+1)) (t : Edge → ℝ),
      (m+1:ℝ) ≤ N^r → (∑ e, |t e|) ≤ N^v →
    let scale := a*(N^k)^30
    let η := localizedCountertermBound freq*N^r/scale
    let ε := ((N^k)^19)⁻¹
    let tol := (N^(2*r+p+6))⁻¹
    let Eform := localizedHubbardFormError m freq D (tol+tol)
    let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
      (localizedOffsiteCoulomb freq u) left right t-
      (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
    let K := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
      ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
    let g₀ := (γ/8)/(2*((m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+
      6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
    let g := (N^(qG+2*r))⁻¹
    0 ≤ η ∧ η ≤ 1 ∧ η ≤ δ ∧
    (m+1:ℝ)*(ε+ε^2/(γ/4)) ≤ γ/8 ∧
    Eform ≤ (N^(p+2))⁻¹ ∧ 0 < g ∧
    (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+g ≤ g₀ ∧
    scale*(3*((2*(m+1:ℝ)*ε)^2+scale⁻¹^2*(8*(m+1:ℝ)^3*K)+
      (B/(N^k)^20)^2*((m+1:ℝ)+2*K)*(m+1:ℝ))/g) ≤ (N^(p+2))⁻¹ := by
  have hfp : 0 < freq := lt_of_lt_of_le zero_lt_one hf
  let C := manufacturedKineticBudgetConstant freq rho
  let b := γ/(16*C)
  have hC : 0 < C := manufacturedKineticBudgetConstant_positive hf hrho
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨qη,hqη,heta⟩ := exists_polynomial_ratio_offset
    (localizedCountertermBound freq/a) (lt_min hδ zero_lt_one)
  obtain ⟨qR,hqR,hres⟩ := exists_residual_complement_smallness hγ
  obtain ⟨qF,hqF,hform⟩ := exists_hubbardDouble_parameter_offset freq
  obtain ⟨qG,hqG,hkin⟩ := exists_manufactured_kinetic_exponent hf hrho hγ hγ1
  obtain ⟨qA,hqA,habs⟩ := exists_shifted_hubbard_polynomial_bound hfp
  obtain ⟨qB,hqB,hsmall⟩ := exists_nuclear_complement_smallness ha hb hB
  obtain ⟨qI,hqI,herr⟩ := exists_complement_error_scale (b := B) ha
  refine ⟨qη+qR+qF+qB+qA+qI+2*qG+3,qG,by omega,hqG,?_⟩
  intro r v p k hk N D hN hD Edge _ m u left right t hm ht
  dsimp only
  let scale := a*(N^k)^30
  let η := localizedCountertermBound freq*N^r/scale
  let ε := ((N^k)^19)⁻¹
  let tol := (N^(2*r+p+6))⁻¹
  let Eform := localizedHubbardFormError m freq D (tol+tol)
  let A := hubbardFermionBottom m (localizedCoulombProfile freq 0)
    (localizedOffsiteCoulomb freq u) left right t-
    (1/2:ℝ)*(∑ i, ∑ j, localizedOffsiteCoulomb freq u i j)-Eform
  let K := (m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+6*Real.pi*rho+
    ((-1/2:ℝ)+freq/2))+2*(m+1:ℝ)*ε
  let g₀ := (γ/8)/(2*((m+1:ℝ)*(((m+1:ℝ)+η)*PlanarSobolev.wellBound+
    6*Real.pi*rho+((-1/2:ℝ)+freq/2))+γ/8+1))
  let g := (N^(qG+2*r))⁻¹
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hR0 : 0 < N^k := by positivity
  have hR1 : 1 ≤ N^k := one_le_pow₀ hN1
  have hM : 1 ≤ (m+1:ℝ) := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hM0 : 0 ≤ (m+1:ℝ) := by positivity
  have he0 : 0 ≤ ε := by dsimp [ε]; positivity
  have he1 : ε ≤ 1 := by dsimp [ε]; exact inv_le_one_of_one_le₀ (one_le_pow₀ hR1)
  have hη0 : 0 ≤ η := by
    dsimp [η,scale]
    exact div_nonneg (mul_nonneg (localizedCountertermBound_nonnegative freq) (by positivity)) (by positivity)
  have hηmin : η ≤ min δ 1 := by
    calc
      _ = (localizedCountertermBound freq/a)*N^r/(N^k)^30 := by dsimp [η,scale]; ring
      _ ≤ (localizedCountertermBound freq/a)*N^r/(N^k)^2 := by
        gcongr
        · exact mul_nonneg (div_nonneg (localizedCountertermBound_nonnegative freq) ha.le) (pow_nonneg hN0.le r)
        · decide
      _ ≤ _ := by simpa only [Nat.add_zero,pow_zero,div_one] using heta r 0 k (by omega) N hN
  have hη1 : η ≤ 1 := hηmin.trans (min_le_right _ _)
  have hE : Eform ≤ (N^(p+2))⁻¹ := hform r p k (by omega) N D hN hD m hm
  have hE1 : Eform ≤ 1 := hE.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hN1))
  have hA : |A| ≤ N^(qA+2*r+v) :=
    habs r v N hN m u left right t D (tol+tol) hm ht (by dsimp [tol]; positivity) hE1
  obtain ⟨hK,hg₀⟩ := hkin N hN r (m+1) η ε hM hm hη0 hη1 he1
  have hgap : b/N^(2*r) ≤ g₀ := by
    apply le_trans _ (manufactured_kinetic_complement_budgets hf hrho hγ hγ1 hM hη0 hη1 he1).2
    change b/N^(2*r) ≤ b/(m+1:ℝ)^2
    apply div_le_div_of_nonneg_left hb.le (by positivity)
    rw [show 2*r=r*2 by omega,pow_mul]
    exact pow_le_pow_left₀ hM0 hm 2
  have hsg := (hsmall r (qA+2*r+v) k (by omega) N (m+1) A hN hM0 hm hA).2
  have hsmall' : (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+g ≤ g₀ := by
    change 2*g ≤ g₀ at hg₀
    change (B/(N^k)^20)*(m+1:ℝ)+|A/scale|+b/(2*N^(2*r)) ≤ b/N^(2*r) at hsg
    have hid : b/(2*N^(2*r))=(b/N^(2*r))/2 := by ring
    rw [hid] at hsg
    linarith only [hsg,hgap,hg₀]
  have hK0 : 0 ≤ K := by
    have hW := PlanarSobolev.wellBound_nonnegative
    have hE0 : 0 ≤ (-1/2:ℝ)+freq/2 := by linarith
    dsimp [K]
    positivity
  refine ⟨hη0,hη1,hηmin.trans (min_le_left _ _),?_,hE,by positivity,hsmall',?_⟩
  · simpa only [one_div] using hres r k (by omega) N (m+1) hN hM0 hm
  · exact herr r (qG+2*r) (qG+2*r) (p+2) k (by omega) N hN (m+1) K g
      hM0 hm hK0 hK le_rfl

end ContinuumCoulomb

end

end OAI
