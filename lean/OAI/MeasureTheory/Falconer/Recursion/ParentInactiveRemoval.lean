import OAI.MeasureTheory.Falconer.Recursion.ParentDiscardedForm
import OAI.MeasureTheory.Falconer.Graphs.ParentRetainedEnergy
import OAI.MeasureTheory.Falconer.Estimates.ProfileMassError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_parent_inactive_removal
    {sig κ T lam₁ lam₂ W : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (hT : 0 ≤ T) (hlam₁ : 0 ≤ lam₁) (hlam₂ : 0 ≤ lam₂) (hW : 0 ≤ W)
    (K₁ K₂ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (L n : ℕ) (a p v : ℝ), p = a+n → v-a ≤ N →
    κ*(N : ℝ) ≤ p-a → p-a ≤ v-p+2*sig*(N : ℝ) → 10*sig*(N : ℝ) ≤ v-p →
    (L : ℝ) ≤ v-p+2*sig*(N : ℝ) →
    ∀ X Y : DyadicSquare, 0 < X.side → 0 < Y.side →
    X.side ≤ (2:ℝ)^(-a) → Y.side ≤ (2:ℝ)^(-a) →
    100*(2:ℝ)^(-a) ≤ dist X.center Y.center →
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-a) →
    ∀ Ψ : ℝ → ℝ, (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
    Measurable Ψ → (∀ t, Ψ t ≤ W) →
    ∀ {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂],
    ∀ (S₁ : Finset ι₁) (b₁ : ι₁ → PolicyDescriptor) (k₁ : ι₁ → ℕ)
      (S₂ : Finset ι₂) (b₂ : ι₂ → PolicyDescriptor) (k₂ : ι₂ → ℕ),
    S₁.card ≤ (N+1)^3+1 → (∑ d ∈ S₁, k₁ d) ≤ K₁ →
    S₂.card ≤ (N+1)^3+1 → (∑ d ∈ S₂, k₂ d) ≤ K₂ →
    (∀ d ∈ S₁, descriptorLength (b₁ d) ≤ L) → (∀ d ∈ S₂, descriptorLength (b₂ d) ≤ L) →
    ∀ Q₁ Q₂ : DyadicSquare, 0 < Q₁.side → 0 < Q₂.side →
    ∀ (ρ₁ ρ₂ : Measure Plane) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂], ∀ (m₁ m₂ : ℝ → ℝ)
      (J₁ i₁ J₂ i₂ : ℕ) (h₁ h₂ : Plane → ℂ),
    Measurable h₁ → Measurable h₂ → (∀ x, ‖h₁ x‖ ≤ 1) → (∀ y, ‖h₂ y‖ ≤ 1) →
    ∀ M₁ M₂ : ℝ, 0 < M₁ → 0 < M₂ →
    (ρ₁ X.carrier).toReal/M₁ ≤ ((2:ℝ)^N)^(3*lam₁) →
    (ρ₂ Y.carrier).toReal/M₂ ≤ ((2:ℝ)^N)^(3*lam₂) →
    let β₁ := inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ h₁
    let β₂ := inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ h₂
    |sourceRadialSquareEnergy a v Ψ (sourceParentDistanceF X Y ρ₁ ρ₂ M₁ M₂ β₁ β₂) -
      sourceRadialSquareEnergy a v Ψ
        (sourceParentRetainedF N sig (p-a) X Y ρ₁ ρ₂ n M₁ M₂ β₁ β₂)| ≤ ((2:ℝ)^N)^(-T) := by
  let l := 3*lam₁+3*lam₂
  let C := symbolDerivativeConstant K₁^K₁ * symbolDerivativeConstant K₂^K₂ * sourceArcLength.real univ
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg
      (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
      (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)) ENNReal.toReal_nonneg
  obtain ⟨N₁,hN₁⟩ := uniform_parent_discarded_F (T := T+2*l+3) hsig hgap K₁ K₂
  obtain ⟨N₂,hN₂⟩ := fixed_constant_absorbed (by norm_num : (0:ℝ) < 1) (4*W*(2*C+1))
  refine ⟨max N₁ N₂,?_⟩
  intro N hN L n a p v hp hv hlow ht hu hL X Y hX hY hXa hYa hlo hhi Ψ hΨ hmΨ hΨW
    ι₁ ι₂ inst₁ inst₂ S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
    ρ₁ ρ₂ hρ₁ hρ₂ m₁ m₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ hm₁ hm₂ hb₁ hb₂ M₁ M₂ hM₁ hM₂ hmass₁ hmass₂
  dsimp only
  let β₁ := inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁
  let β₂ := inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂
  let R : ℝ := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hmeas₁ := measurable_inheritedCircleSymbol S₁ b₁ k₁ Q₁ ρ₁ m₁ N lam₁ sig J₁ i₁ hsp₁ hm₁
  have hmeas₂ := measurable_inheritedCircleSymbol S₂ b₂ k₂ Q₂ ρ₂ m₂ N lam₂ sig J₂ i₂ hsp₂ hm₂
  have hnorm₁ : ∀ x dir, ‖β₁ x dir‖ ≤ symbolDerivativeConstant K₁^K₁ := by
    intro x dir
    simpa only [one_mul] using inheritedCircleSymbol_norm_bound S₁ b₁ k₁ Q₁ hQ₁ ρ₁ m₁ N
      lam₁ sig J₁ i₁ hsp₁ 1 hb₁ K₁ hk₁ x dir
  have hnorm₂ : ∀ x dir, ‖β₂ x dir‖ ≤ symbolDerivativeConstant K₂^K₂ := by
    intro x dir
    simpa only [one_mul] using inheritedCircleSymbol_norm_bound S₂ b₂ k₂ Q₂ hQ₂ ρ₂ m₂ N
      lam₂ sig J₂ i₂ hsp₂ 1 hb₂ K₂ hk₂ x dir
  have hmass : ((ρ₁ X.carrier).toReal/M₁)*((ρ₂ Y.carrier).toReal/M₂) ≤ R^l := by
    calc
      _ ≤ R^(3*lam₁)*R^(3*lam₂) := mul_le_mul hmass₁ hmass₂ (by positivity) (by positivity)
      _ = R^l := (Real.rpow_add hRp _ _).symm
  have hfull (r : ℝ) : ‖sourceParentDistanceF X Y ρ₁ ρ₂ M₁ M₂ β₁ β₂ r‖ ≤ C*R^l := by
    have hh := sourceDistanceF_norm_le ρ₁ ρ₂ X.carrier Y.carrier hM₁ hM₂ _ β₁ β₂
      (by norm_num : (0:ℝ) ≤ 1)
      (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
      (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
      (sourceConeCircle_norm_le (sourceParentAxis X Y)) (fun x _ => hnorm₁ x) (fun y _ => hnorm₂ y) r
    apply hh.trans
    simpa only [one_mul, mul_assoc, C] using mul_le_mul_of_nonneg_left hmass hC
  have he (r : ℝ) (hr : Ψ (r/(2:ℝ)^v) ≠ 0) :
      ‖sourceParentDiscardedF N sig (p-a) X Y ρ₁ ρ₂ n M₁ M₂ β₁ β₂ r‖ ≤ R^(-(T+2*l+3))*R^l := by
    have hh := hN₁ N ((le_max_left _ _).trans hN) L n a p v r hp hlow ht hu hL X Y hX hY hXa hYa
      hlo hhi Ψ hΨ hr S₁ b₁ k₁ S₂ b₂ k₂ hc₁ hk₁ hc₂ hk₂ hl₁ hl₂ Q₁ Q₂ hQ₁ hQ₂
      ρ₁ ρ₂ m₁ m₂ lam₁ lam₂ J₁ i₁ J₂ i₂ hsp₁ hsp₂ hm₁ hm₂ hb₁ hb₂ M₁ M₂ hM₁ hM₂
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hRp.le (-(T+2*l+3)))
  have herr := parent_retained_energy_error_le N sig (p-a) a v X Y hX hY ρ₁ ρ₂ n hM₁ hM₂
    β₁ β₂ hmeas₁ hmeas₂
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le _)) _) hnorm₁ hnorm₂
    Ψ hmΨ hW hΨW (fun t ht => by
      by_contra hn
      have hh := (hΨ t hn).2
      linarith)
    (mul_nonneg hC (Real.rpow_nonneg hRp.le l)) (by positivity) hfull he
  apply herr.trans
  apply parent_error_power_bound hR hC hW (by dsimp [l]; positivity) hT (by positivity)
  · calc
      (2:ℝ)^(2*(v-a)) ≤ (2:ℝ)^(2*(N:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = R^2 := by
        rw [mul_comm (2:ℝ), Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        simp only [Real.rpow_natCast, Real.rpow_ofNat, R]
  · simpa only [Real.rpow_one] using hN₂ N ((le_max_right _ _).trans hN)

end PlanarFalconer

end OAI
