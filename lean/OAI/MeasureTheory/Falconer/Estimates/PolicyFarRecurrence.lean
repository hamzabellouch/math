import OAI.MeasureTheory.Falconer.Estimates.PolicyFarCoefficients
import OAI.MeasureTheory.Falconer.Fourier.PolicyJetChildren

namespace OAI

/-! # The near and collision successors of an actual far branch -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

theorem exists_policy_far_recurrence
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K : ℕ) {lam σ ε T : ℝ} (hlam : 0 ≤ lam)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε) (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ u, 0 ≤ Ψ u)
    (hsupp : ∀ u, Ψ u ≠ 0 → u ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ u, Ψ u ≤ W) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∃ N₀ : ℕ,
      ∀ (P : PolicyJetData m), P.lam = lam → P.σ = σ →
      N₀ ≤ P.N → ∀ hsplit : P.a < P.splitDepth, 1 ≤ P.Z →
      ∀ (w₀ : Sphere (m+3)) (M : ℝ), 0 ≤ M →
      (∀ row, ∀ hrow : row ∈
        (P.Q.descendant P.X).occupiedPaths P.ρ (P.splitDepth-P.a) ×ˢ
          (P.Q.descendant P.Y).occupiedPaths P.ρ (P.splitDepth-P.a),
        P.farWeight P.splitDepth lam σ ε *
          (P.child P.splitDepth hsplit.le row hrow).envelope K L Ψ ≤ M) →
      (∀ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
        ENNReal.ofReal (P.farWeight b lam σ ε)*
          farCollisionMaximum w₀ P.Q P.ρ (fun t => P.profile (t/P.N))
            P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a) ≤ ENNReal.ofReal M) →
      P.envelope K L Ψ ≤ 2*M+((2:ℝ)^P.N)^(-T) := by
  obtain ⟨L₀,hfar⟩ := exists_policy_far_step hgnomonic hquadratic m K hσ hσ1 hT
    hΨ hpos hsupp hW hΨW
  obtain ⟨Nnear,hnear⟩ := eventual_policy_near_coefficient m K hlam hσ.le hε
  obtain ⟨Npoly,hpoly⟩ := PlanarFalconer.fixed_polynomial_subpower 1 (half_pos hε)
  refine ⟨L₀,?_⟩
  intro L hL
  obtain ⟨B,C,Nfar,hB,hC,hstep⟩ := hfar L hL
  obtain ⟨Ncoeff,hcoeff⟩ := eventual_policy_collisionTerm_payment m K hB hC hlam hσ.le hε
  refine ⟨max 1 (max (max Nnear Npoly) (max Nfar Ncoeff)),?_⟩
  intro P hLam hσP hN hsplit hZ w₀ M hM hchildren hcollisions
  have hN1 : 1 ≤ P.N := (le_max_left _ _).trans hN
  have hNall := (le_max_right _ _).trans hN
  have hNnear : Nnear ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hNall)
  have hNpoly : Npoly ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hNall)
  have hNfar : Nfar ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans hNall)
  have hNcoeff : Ncoeff ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans hNall)
  have hweight : 0 < P.farWeight P.splitDepth lam σ ε := by
    unfold PolicyJetData.farWeight
    positivity
  have hchild : P.graphChild K L P.splitDepth Ψ ≤ M/P.farWeight P.splitDepth lam σ ε := by
    apply P.graphChild_le K L P.splitDepth hsplit.le Ψ (div_nonneg hM hweight.le)
    intro row hrow
    apply (le_div_iff₀ hweight).mpr
    simpa only [mul_comm] using hchildren row hrow
  have hweighted : P.farWeight P.splitDepth lam σ ε*P.graphChild K L P.splitDepth Ψ ≤ M := by
    simpa only [mul_comm] using (le_div_iff₀ hweight).mp hchild
  have hchild0 : 0 ≤ P.graphChild K L P.splitDepth Ψ :=
    childJetStateMaximum_nonneg (m+1) K L 1 _ P.Q P.ρ _ P.N P.σ P.J P.i P.masks P.Z
      P.X P.Y (P.splitDepth-P.a) _ P.splitDepth P.t Ψ
  have hnearM : P.nearBound K L Ψ ≤ M := by
    rw [P.nearBound_eq]
    calc
      _ = (((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
          ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
            profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
          (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2))*
            P.graphChild K L P.splitDepth Ψ := by ring
      _ ≤ P.farWeight P.splitDepth lam σ ε*P.graphChild K L P.splitDepth Ψ :=
        mul_le_mul_of_nonneg_right (hnear P hLam hNnear) hchild0
      _ ≤ M := hweighted
  let S := Finset.Icc (P.a+9) (P.splitDepth+6)
  have hcard : S.card ≤ P.N+3 := by
    dsimp [S]
    rw [Nat.card_Icc]
    have hh : P.splitDepth ≤ P.t := Nat.sub_le _ _
    have ht := P.base_right.trans P.base_N
    omega
  have hpoly' : ((P.N+3:ℕ):ℝ) ≤ ((2:ℝ)^P.N)^(ε/2) := by
    apply (show ((P.N+3:ℕ):ℝ) ≤ 4*(P.N:ℝ)+1 from ?_).trans
      (by simpa only [pow_one] using hpoly P.N hNpoly)
    push_cast
    have hh : (1:ℝ) ≤ P.N := by exact_mod_cast hN1
    linarith
  have hcardE : (S.card:ℝ≥0∞) ≤ ENNReal.ofReal (((2:ℝ)^P.N)^(ε/2)) := by
    have hh := ENNReal.ofReal_le_ofReal ((Nat.cast_le.mpr hcard).trans hpoly')
    simpa only [ENNReal.ofReal_natCast] using hh
  have hsum : (∑ b ∈ S, P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b) ≤ ENNReal.ofReal M := by
    calc
      _ ≤ ∑ _b ∈ S, ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M := by
        apply Finset.sum_le_sum
        intro b hb
        exact (hcoeff P hLam hZ hNcoeff w₀ b).trans
          (mul_le_mul' le_rfl (hcollisions b hb))
      _ = (S.card:ℝ≥0∞)*(ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M) := by simp
      _ ≤ ENNReal.ofReal (((2:ℝ)^P.N)^(ε/2))*
          (ENNReal.ofReal (((2:ℝ)^P.N)^(-ε/2))*ENNReal.ofReal M) :=
        mul_le_mul' hcardE le_rfl
      _ = ENNReal.ofReal M := by
        rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
        have hc : ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(-ε/2) = 1 := by
          rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^P.N)]
          convert Real.rpow_zero ((2:ℝ)^P.N) using 2
          ring
        rw [hc,ENNReal.ofReal_one,one_mul]
  have hbound := (hstep P hσP hNfar hsplit hZ w₀).trans
    (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hnearM) hsum) le_rfl)
  have heq : ENNReal.ofReal M+ENNReal.ofReal M+
      ENNReal.ofReal (((2:ℝ)^P.N)^(-T)) = ENNReal.ofReal (2*M+((2:ℝ)^P.N)^(-T)) := by
    rw [← ENNReal.ofReal_add hM hM,
      ← ENNReal.ofReal_add (add_nonneg hM hM) (by positivity)]
    congr 1
    ring
  rw [heq] at hbound
  have hh := (ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top).mp hbound
  simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*M+((2:ℝ)^P.N)^(-T))] using hh

end Falconer

end OAI
