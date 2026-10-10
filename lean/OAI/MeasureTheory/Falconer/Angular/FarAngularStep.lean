import OAI.MeasureTheory.Falconer.Estimates.FarDataBound

namespace OAI

/-! # The conditional angular far branch, with the actual near child

This is the analytic far step of the recursive argument. Its inputs are
geometric scale data; only the cited gnomonic and quadratic stationary
results are published hypotheses.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff

namespace JetStateFarData
variable {m : ℕ} {B : ℝ}

noncomputable def energy (D : JetStateFarData m B) {K L : ℕ}
    (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (Ψ : ℝ → ℝ) : ℝ :=
  jetStateEnergy D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z
    (D.ρ.restrict (D.Q.descendant D.X).carrier) (D.ρ.restrict (D.Q.descendant D.Y).carrier)
    (profileModelMass D.profile D.N D.a) (profileModelMass D.profile D.N D.a) D.a D.t Ψ f g

noncomputable def nearBound (D : JetStateFarData m B) (K L : ℕ) (Ψ : ℝ → ℝ) : ℝ :=
  ((2*(10*((m+3)+1))+1)^(2*(m+3)):ℕ) *
    ((2:ℝ)^D.N)^(-2*(profileExcess (d := m+3) D.profile D.N D.h-
      profileExcess (d := m+3) D.profile D.N D.a)+4*(((m+3:ℕ):ℝ)+1)*D.lam)*
    (((descriptorJetBound (m+3) K)^K)^2*((descriptorJetBound (m+3) K)^K)^2*
      childJetStateMaximum (m+1) K L D.Dq (D.F.filter (fun b => D.h < PlanarFalconer.descriptorAnchor b))
        D.Q D.ρ (fun t => D.profile (t/D.N)) D.N D.σ D.J D.i D.masks D.Z D.X D.Y (D.h-D.a)
        (profileModelMass D.profile D.N D.h) D.h D.t Ψ)

end JetStateFarData

 theorem exists_far_angular_step
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L M q : ℕ) (hM : 1 ≤ M) (hML : 2*M+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C Cerr : ℝ, 1 ≤ B ∧ 0 ≤ C ∧ 0 ≤ Cerr ∧
      ∀ (D : JetStateFarData m B), D.loss ≤ D.κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -D.κ*(M:ℝ)+2*(m+3) ≤ -D.loss →
      ∀ (f g : DescriptorJetSymbol (m+1) K L D.F D.Dq) (w₀ : Sphere (m+3)),
      ENNReal.ofReal (D.energy f g Ψ) ≤ ENNReal.ofReal (D.nearBound K L Ψ) +
        (∑ b ∈ Finset.Icc (D.a+9) (D.h+6), D.collisionTerm w₀ (C*(B^K*D.Z⁻¹)^4) b) +
        ENNReal.ofReal D.prefactor *
          (2+((Finset.Icc (D.a+9) (D.h+6)).card:ℝ≥0∞)) *
          ENNReal.ofReal (Cerr*(B^K*D.Z⁻¹)^4*((2:ℝ)^D.N)^(-D.loss))*D.originalMeasure univ := by
  obtain ⟨B,C,Cerr,hB,hC,hCerr,hfar⟩ := exists_far_data_bound hgnomonic hquadratic
    m K L M q hM hML hΨ hpos hs hW hΨW
  refine ⟨B,C,Cerr,hB,hC,hCerr,?_⟩
  intro D hloss horder f g w₀
  let := D.regular.probability
  have htail (s : ℝ) (hs4 : 4 < s) : Ψ s = 0 := by
    by_contra hn
    have hh := (hs s hn).2
    linarith
  let := PlanarFalconer.sourceAngularShellMeasure_finite (D.t:ℝ) Ψ hW hΨW htail
  have hnear := profile_near_jetState D.Q D.unit D.ρ D.regular D.N_pos D.σ D.J D.i
    D.masks D.separated D.Z_pos D.ah (show D.h ≤ D.N by have := D.ht; have := D.tN; omega)
    D.X D.Y D.X_length D.Y_length D.t Ψ f g
  have hfull := jetState_energy_near_original_far f g w₀ D.Q D.unit D.ρ D.profile D.N D.σ
    D.J D.i D.masks D.separated D.separated D.Z_pos D.ah D.X D.Y D.X_length D.Y_length D.t Ψ
  have he := hfull.trans (add_le_add (ENNReal.ofReal_le_ofReal hnear)
    (hfar D hloss horder f g w₀))
  simpa only [JetStateFarData.energy,JetStateFarData.nearBound,JetStateFarData.prefactor,
    JetStateFarData.originalMeasure,JetStateFarData.kernel,add_assoc,Nat.reduceAdd] using he

end Falconer

end OAI
