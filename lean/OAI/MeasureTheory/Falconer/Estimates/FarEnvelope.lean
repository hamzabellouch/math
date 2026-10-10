import OAI.MeasureTheory.Falconer.Angular.FarAngularStep
import OAI.MeasureTheory.Falconer.Fourier.PolicyJetData

namespace OAI

/-! # The far reduction for the full recursive symbol supremum -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def envelope (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnvelope (m+1) K L D.Dq D.F D.F D.Q D.ρ (fun t => D.profile (t/D.N))
    D.N D.σ D.J D.i D.masks D.Z
    (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
    (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a) D.a D.t Ψ

theorem envelope_le_of_energy_le (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ)
    {H : ℝ≥0∞} (h : ∀ f g : DescriptorJetSymbol (m+1) K L D.F D.Dq,
      ENNReal.ofReal (D.energy f g Ψ) ≤ H) : ENNReal.ofReal (D.envelope K L Ψ) ≤ H := by
  by_cases htop : H = ⊤
  · simp only [htop,le_top]
  apply ENNReal.ofReal_le_of_le_toReal
  apply csSup_le (show (jetStateValues (m+1) K L D.Dq D.F D.F D.Q D.ρ
      (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z
      (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
      (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a)
      D.a D.t Ψ).Nonempty from ⟨0,Or.inl rfl⟩)
  intro r hr
  rcases hr with rfl | ⟨f,g,rfl⟩
  · exact ENNReal.toReal_nonneg
  · exact (ENNReal.ofReal_le_iff_le_toReal htop).mp (h f g)

noncomputable def farError (D : JetStateFarData m B) (K : ℕ) (Cerr : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal D.prefactor *
    (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
    ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ

end JetStateFarData

theorem exists_far_envelope_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss → ∀ w₀ : Sphere (m+3),
      ENNReal.ofReal (D.envelope K L Ψ) ≤ ENNReal.ofReal (D.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        D.farError K Cerr := by
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hstep⟩ := exists_far_angular_step hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,Cerr,hB,hC,hCerr,?_⟩
  intro D hloss horder w₀
  apply D.envelope_le_of_energy_le
  intro f g
  exact hstep D hloss horder f g w₀

namespace PolicyJetData
variable {m : ℕ}

noncomputable def envelope (P : PolicyJetData m) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnvelope (m+1) K L 1 P.list P.list P.Q P.ρ (fun t => P.profile (t/P.N))
    P.N P.σ P.J P.i P.masks P.Z
    (P.ρ.restrict (P.Q.descendant P.X).carrier) (P.ρ.restrict (P.Q.descendant P.Y).carrier)
    (profileModelMass P.profile P.N P.a) (profileModelMass P.profile P.N P.a) P.a P.t Ψ

 theorem farData_envelope (P : PolicyJetData m) (B : ℝ) (hB : 1 ≤ B)
    (hσ : 0 < P.σ) (hσ1 : P.σ ≤ 1)
    (hN : farThreshold B P.σ hB hσ hσ1 m ≤ P.N)
    (hfar : P.a < P.splitDepth) (loss : ℝ) (hloss : 0 ≤ loss)
    (K L : ℕ) (Ψ : ℝ → ℝ) :
    (P.farData B hB hσ hσ1 hN hfar loss hloss).envelope K L Ψ = P.envelope K L Ψ := rfl

end PolicyJetData

end Falconer

end OAI
