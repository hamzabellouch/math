import OAI.MeasureTheory.Falconer.Estimates.FarErrorOrder

namespace OAI

/-! # The actual policy far reduction with an arbitrary-power error -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace PolicyJetData
variable {m : ℕ}

noncomputable def nearBound (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N P.splitDepth-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      childJetStateMaximum (m+1) K L 1
        (P.list.filter (fun b => P.splitDepth < PlanarFalconer.descriptorAnchor b))
        P.Q P.ρ (fun t => P.profile (t/P.N)) P.N P.σ P.J P.i P.masks P.Z
        P.X P.Y (P.splitDepth-P.a) (profileModelMass P.profile P.N P.splitDepth) P.splitDepth P.t Ψ)

noncomputable def collisionTerm (P : PolicyJetData m) (w₀ : Sphere (m+3))
    (C : ℝ) (b : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C*((2*(1100*((m+3)+1))+1)^(2*(m+3)):ℕ)*
    ((2:ℝ)^P.N)^(-2*(profileExcess (d := m+3) P.profile P.N b-
      profileExcess (d := m+3) P.profile P.N P.a)+4*(((m+3:ℕ):ℝ)+1)*P.lam))*
    (PlanarFalconer.binKernelConstant*farCollisionMaximum w₀ P.Q P.ρ
      (fun t => P.profile (t/P.N)) P.policy P.N P.σ P.J (P.i+1) P.q b P.t P.X P.Y (b-P.a))

end PolicyJetData

theorem exists_policy_far_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K : ℕ) {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ L₀ : ℕ, ∀ L ≥ L₀, ∃ (B C : ℝ) (N₀ : ℕ), 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (P : PolicyJetData m), P.σ = σ → N₀ ≤ P.N →
      P.a < P.splitDepth → 1 ≤ P.Z → ∀ w₀ : Sphere (m+3),
      ENNReal.ofReal (P.envelope K L Ψ) ≤ ENNReal.ofReal (P.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (P.a+9) (P.splitDepth+6),
          P.collisionTerm w₀ (C*(B^K*P.Z⁻¹)^4) b) +
        ENNReal.ofReal (((2:ℝ)^P.N)^(-T)) := by
  let loss := T+5*((m+3:ℕ):ℝ)+1
  have hloss : 0 ≤ loss := by dsimp [loss]; positivity
  obtain ⟨M,q,hM,hnc,horder⟩ := exists_far_truncation_orders m (loss := loss) hσ
  refine ⟨2*M+(m+2)+1,?_⟩
  intro L hML
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hstep⟩ := exists_far_envelope_step hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  obtain ⟨Nerr,herr⟩ := eventual_far_error_absorbed m K hB hCerr (by norm_num : (0:ℝ) < 1) T
  let Nscale := PolicyJetData.farThreshold B σ hB hσ hσ1 m
  refine ⟨B,C,max Nerr Nscale,hB,hC,?_⟩
  intro P hσP hN hfar hZ w₀
  have hpσ : 0 < P.σ := by simpa only [hσP] using hσ
  have hpσ1 : P.σ ≤ 1 := by simpa only [hσP] using hσ1
  have hNscale : PolicyJetData.farThreshold B P.σ hB hpσ hpσ1 m ≤ P.N := by
    simpa only [hσP] using (le_max_right Nerr Nscale).trans hN
  let D := P.farData B hB hpσ hpσ1 hNscale hfar loss hloss
  have hncD : D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) := by
    change loss ≤ (16*P.σ)*_
    simpa only [hσP] using hnc
  have horderD : -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss := by
    change -(16*P.σ)*(M:ℝ)+2*(m+3) ≤ -loss
    simpa only [hσP] using horder
  have he := herr D ((le_max_left Nerr Nscale).trans hN) hZ
    (show T+5*((m+3:ℕ):ℝ)+1 ≤ D.loss from le_refl _)
  have hresult := (hstep D hncD horderD w₀).trans (add_le_add le_rfl he)
  change ENNReal.ofReal (P.envelope K L Ψ) ≤ _ at hresult
  exact hresult

end Falconer

end OAI
