import OAI.Probability.SLE.Multipoint.MultipointFieldBounds
import OAI.Probability.SLE.Multipoint.MultipointAbsorption

namespace OAI

/-! Absorption of the actual finite-product generator. -/

noncomputable section
open scoped BigOperators

namespace SLEExactGauge.Multipoint

theorem regularized_product_relative_drift {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (D σ : ι → ℝ) (z : ι → ℂ × ℝ) (x : ℝ)
    (hD : ∀ i ∈ s, 0 < D i) (hσ : ∀ i ∈ s, σ i ≤ 1)
    (hδ : ∀ i ∈ s, branchRegulator κ (D i) (σ i) (z i) ≤ 1) :
    let p := greenExponent κ
    let ε := (negativeDrift p/2)/(4*((s.card : ℝ)+1))
    let C := driftAllowance p*driftThreshold p^(-p)
    let L := youngConstant p (angularCoefficientConstant p^2) ε
    (∑ i ∈ s, logGenerator κ (regularizedLogFactor κ (D i) (σ i)) (z i) x /
        regularizedLogFactor κ (D i) (σ i) (z i) x) +
      (1/2 : ℝ)*(∑ ij ∈ s.offDiag,
        (deriv (regularizedLogFactor κ (D ij.1) (σ ij.1) (z ij.1)) x /
          regularizedLogFactor κ (D ij.1) (σ ij.1) (z ij.1) x)*
        (deriv (regularizedLogFactor κ (D ij.2) (σ ij.2) (z ij.2)) x /
          regularizedLogFactor κ (D ij.2) (σ ij.2) (z ij.2) x)) ≤
      κ*(C*(∑ i ∈ s, branchRegulator κ (D i) (σ i) (z i)*logVelocity κ (z i) x^2) +
        L*(∑ ij ∈ s.offDiag,
          (branchRegulator κ (D ij.1) (σ ij.1) (z ij.1)*
            branchRegulator κ (D ij.2) (σ ij.2) (z ij.2))^(-exponent p)*
          (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x))) := by
  dsimp only
  let p := greenExponent κ
  let k := negativeDrift p/2
  let ε := k/(4*((s.card : ℝ)+1))
  let C := driftAllowance p*driftThreshold p^(-p)
  let L := youngConstant p (angularCoefficientConstant p^2) ε
  let δ := fun i => branchRegulator κ (D i) (σ i) (z i)
  let A := fun i => damping p (δ i) (logAngle κ (z i) x)*logVelocity κ (z i) x^2
  let H := fun i => δ i*logVelocity κ (z i) x^2
  let b := fun i => deriv (regularizedLogFactor κ (D i) (σ i) (z i)) x /
    regularizedLogFactor κ (D i) (σ i) (z i) x
  let d := fun i => logGenerator κ (regularizedLogFactor κ (D i) (σ i)) (z i) x /
    regularizedLogFactor κ (D i) (σ i) (z i) x
  let w := fun ij : ι × ι => (δ ij.1*δ ij.2)^(-exponent p)*
    (logVelocity κ (z ij.1) x*logVelocity κ (z ij.2) x)
  have hp : 0 < p := by
    dsimp [p, greenExponent]
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  have hk : 0 < k := div_pos (negativeDrift_pos hp) (by norm_num)
  have he : 0 < ε := absorption_epsilon_pos hk s.card
  have hA (i : ι) (hi : i ∈ s) : 0 ≤ A i := by
    have hδi : 0 < δ i := mul_pos (hD i hi) (Real.exp_pos _)
    have hf := angularFactor_pos (p := p) hδi (logAngle_sin_pos κ (z i) x)
    change 0 ≤ (δ i/angularFactor p (δ i) (logAngle κ (z i) x)*
      sinePower (q p-2) (logAngle κ (z i) x))*logVelocity κ (z i) x^2
    exact mul_nonneg (mul_nonneg (div_pos hδi hf).le
      (Real.rpow_nonneg (logAngle_sin_pos κ (z i) x).le _)) (sq_nonneg _)
  have hd (i : ι) (hi : i ∈ s) : d i ≤ (κ*C)*H i-(κ*k)*A i := by
    have h := regularizedLogFactor_relative_drift κ (D i) (σ i) hκ hκ8
      (hD i hi) (hσ i hi) (z i) x
    convert h using 1
    dsimp [d, C, H, k, A, δ, p]
    ring
  have hcross (ij : ι × ι) (hij : ij ∈ s.offDiag) :
      (1/2 : ℝ)*(b ij.1*b ij.2) ≤ (κ*ε)*(A ij.1+A ij.2)+(κ*L)*w ij := by
    obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
    have h := regularizedLogFactor_pair_absorption κ (D ij.1) (D ij.2) (σ ij.1) (σ ij.2)
      ε hκ hκ8 (hD _ hi) (hD _ hj) he (z ij.1) (z ij.2) x (hδ _ hi) (hδ _ hj)
    have hsmall : (1/2 : ℝ)*(b ij.1*b ij.2) ≤ |b ij.1*b ij.2| := by
      nlinarith [le_abs_self (b ij.1*b ij.2), abs_nonneg (b ij.1*b ij.2)]
    apply hsmall.trans
    convert h using 1
    dsimp [b, L, A, w, δ, p]
    ring
  have hbudget : 2*(κ*ε)*(s.card : ℝ) ≤ κ*k := by
    have h := mul_le_mul_of_nonneg_left (absorption_epsilon_budget hk.le s.card) hκ.le
    convert h using 1
    dsimp [ε]
    ring
  have h := sum_drift_absorption s d A H (fun ij => (1/2 : ℝ)*(b ij.1*b ij.2)) w
    (κ*C) (κ*k) (κ*ε) (κ*L) (mul_pos hκ he).le hA hbudget hd hcross
  rw [← Finset.mul_sum] at h
  convert h using 1
  dsimp [d, b, C, L, H, w, ε, k, δ, p]
  ring

end SLEExactGauge.Multipoint

end

end OAI
