import OAI.MeasureTheory.Falconer.Estimates.OuterScalarConversion
import OAI.MeasureTheory.Falconer.Measures.SpatialRestriction
import OAI.MeasureTheory.Falconer.Recursion.TwoProfileInverseCost
import OAI.MeasureTheory.Falconer.Fourier.TwoProfileDerivatives
import OAI.MeasureTheory.Falconer.Estimates.OuterDescriptors
import OAI.MeasureTheory.Falconer.Shells.DescriptorShellRegime
import OAI.MeasureTheory.Falconer.Estimates.ScalarErrorBudget

namespace OAI

/-! # Outer scalar conversion with arbitrary measurable product restrictions -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def PolicyJetData.outerRestrictedDistance {m : ℕ} (P Q : PolicyJetData m) (c : ℕ)
    (A₁ A₂ : Set (Space (m+3))) : Measure ℝ :=
  endpointWeightedDistance
    ((P.ρ.restrict (P.Q.descendant P.X).carrier).restrict A₁)
    ((Q.ρ.restrict (Q.Q.descendant Q.X).carrier).restrict A₂)
    (profileModelMass P.profile P.N P.a) (profileModelMass Q.profile Q.N Q.a) 1
    (descriptorAmbientProduct P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i (P.outerList c) P.masks)
    (descriptorAmbientProduct Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i (Q.outerList c) Q.masks)

theorem exists_outer_restricted_scalar_conversion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσsmall : σ ≤ 1/100) (hε : 0 < ε)
    (T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
    (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) :
    ∃ K : ℕ, ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
      ∀ P Q : PolicyJetData m, P.N = Q.N → P.σ = σ → Q.σ = σ →
      P.J = Q.J → P.i = 0 → Q.i = 0 → P.Z = Z → Q.Z = Z →
      P.a = 0 → Q.a = 0 → P.t = P.N → Q.t = Q.N → N₀ ≤ P.N →
      ∀ c : ℕ, 2*c ≤ P.N →
      (∀ b ∈ P.outerList c, ∀ w ∈ P.masks b, ∀ z ∈ P.masks b, w ≠ z →
        descriptorMaskRadius P.N P.σ b/2 ≤ dist w z) →
      (∀ b ∈ Q.outerList c, ∀ w ∈ Q.masks b, ∀ z ∈ Q.masks b, w ≠ z →
        descriptorMaskRadius Q.N Q.σ b/2 ≤ dist w z) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier), δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (Q.ρ.restrict (Q.Q.descendant Q.X).carrier),
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∀ A₁ A₂ : Set (Space (m+3)), MeasurableSet A₁ → MeasurableSet A₂ →
      ∀ energy : ℝ, 0 ≤ energy →
      (∀ (f : DescriptorJetSymbol (m+1) K L (P.outerList c) 1)
        (g : DescriptorJetSymbol (m+1) K L (Q.outerList c) 1),
        independentAngularEnergy P.a P.t Ψ
          (fun z => endpointTransform (P.ρ.restrict (P.Q.descendant P.X).carrier)
            (profileModelMass P.profile P.N P.a)
            (f.value P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks P.Z) z.1 z.2)
          (fun z => endpointTransform (Q.ρ.restrict (Q.Q.descendant Q.X).carrier)
            (profileModelMass Q.profile Q.N Q.a)
            (g.value Q.Q Q.ρ (fun u => Q.profile (u/Q.N)) Q.N Q.σ Q.J Q.i Q.masks Q.Z) z.1 z.2) ≤ energy) →
      (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)),
        ‖charFun (P.outerRestrictedDistance Q c A₁ A₂) r‖^2) ≤ ((2:ℝ)^P.N)^ε*energy+((2:ℝ)^P.N)^(-T) := by
  let accuracy := (T+2)/2
  obtain ⟨k,A₀,hA₀,horder⟩ := exists_two_profile_masked_shell_order hgnomonic hquadratic m
    (κ := 16*σ) (T := accuracy) (by positivity)
  let order := 2*(k+1)+(m+2)+1
  let C : ℝ := (2:ℝ)^order
  let Cerr : ℝ := δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr,C]; positivity
  obtain ⟨Nder,hder⟩ := uniform_two_profile_derivatives (m+3) order 4 hσ
  obtain ⟨Nfreq,hfreq⟩ := eventual_descriptor_pair_shell_regime (d := m+3) hσ (by linarith) hδ Ψ hΨ hsupp
  obtain ⟨Nrad,hrad⟩ := Regularization.fixed_constant_absorbed hσ 8
  obtain ⟨Ntwo,htwo⟩ := Regularization.fixed_constant_absorbed (half_pos hε) 2
  obtain ⟨Nerr,herr⟩ := eventual_scalar_shell_error_budget T hCerr
    (show 0 ≤ 4*V by positivity)
  refine ⟨2*k,?_⟩
  intro L Z hZ
  obtain ⟨A,B,hA,hB,hshell⟩ := horder L
  obtain ⟨Ncost,hcost⟩ := eventual_two_profile_root_shell_cost m k A B Z δ W hδ hW (half_pos hε)
  refine ⟨max (max Nder Nfreq) (max (max Nrad Ntwo) (max Nerr Ncost)),?_⟩
  intro P Q hN hσP hσQ hJ hiP hiQ hZP hZQ haP haQ htP htQ hlarge c hc hsepP hsepQ hsep hnear A₁ A₂ hA₁ hA₂ energy he0 henergy
  let := P.regular.probability
  let := Q.regular.probability
  let μ₀ := P.ρ.restrict (P.Q.descendant P.X).carrier
  let ν₀ := Q.ρ.restrict (Q.Q.descendant Q.X).carrier
  let μ := μ₀.restrict A₁
  let ν := ν₀.restrict A₂
  have hdom : μ.prod ν ≤ μ₀.prod ν₀ := Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hsep' : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W :=
    (ae_mono hdom) hsep
  have hnear' : ∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
      ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 :=
    (ae_mono hdom) hnear
  let ell := max (P.outerLongest c) (Q.outerLongest c)
  have hell : 2*ell ≤ P.N := by
    have hp := P.outerLongest_half hc
    have hq := Q.outerLongest_half (by omega : 2*c ≤ Q.N)
    dsimp [ell]
    omega
  have hNd : Nder ≤ P.N := by omega
  have hNf : Nfreq ≤ P.N := by omega
  have hNr : Nrad ≤ P.N := by omega
  have hNt : Ntwo ≤ P.N := by omega
  have hNe : Nerr ≤ P.N := by omega
  have hNc : Ncost ≤ P.N := by omega
  have hsp : ∀ r, 4 < r → Ψ r = 0 := by
    intro r hr
    by_contra hn
    exact (not_lt_of_ge hr.le) (hsupp r hn).2
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.N:ℝ) Ψ hV hΨV hsp
  let E := descriptorDerivativeScale P.N σ ell
  have hE : 1 ≤ E := descriptorDerivativeScale_ge_one P.N hσ.le ell
  have hEu : E ≤ ((2:ℝ)^P.N)^2 := descriptorDerivativeScale_le_square P.N ell hσ.le (by linarith) (by omega)
  have hlengthP : ∀ b ∈ P.outerList c, PlanarFalconer.descriptorLength b ≤ ell :=
    fun b hb => (Finset.le_sup hb).trans (le_max_left _ _)
  have hlengthQ : ∀ b ∈ Q.outerList c, PlanarFalconer.descriptorLength b ≤ ell :=
    fun b hb => (Finset.le_sup hb).trans (le_max_right _ _)
  have hradP : ∀ b ∈ P.outerList c, (descriptorMaskRadius P.N σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N σ b (hlengthP b hb)).trans
    exact mul_le_mul_of_nonneg_right (hrad P.N hNr) (by positivity)
  have hradQ : ∀ b ∈ Q.outerList c, (descriptorMaskRadius P.N σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N σ b (hlengthQ b hb)).trans
    exact mul_le_mul_of_nonneg_right (hrad P.N hNr) (by positivity)
  have hgap : 20*σ*(P.N:ℝ) ≤ (P.N:ℝ)-0 := by
    have hh := mul_le_mul_of_nonneg_right hσsmall (Nat.cast_nonneg (α := ℝ) P.N)
    linarith
  have hellR : (ell:ℝ) ≤ ((P.N:ℝ)-0)/2+σ*P.N := by
    have hh : 2*(ell:ℝ) ≤ P.N := by exact_mod_cast hell
    nlinarith [mul_nonneg hσ.le (Nat.cast_nonneg (α := ℝ) P.N)]
  have hfreqP := hfreq P.N hNf ell 0 P.N (by omega) hgap hellR μ ν (by simpa using hsep'.mono (fun _ hz => hz.1))
  have hd := hder P.N hNd P.Q Q.Q P.ρ Q.ρ (fun u => P.profile (u/P.N))
    (fun u => Q.profile (u/Q.N)) P.J 0 ell (P.outerList c) (Q.outerList c) P.masks Q.masks
    (P.outerList_card c) (by simpa only [hN] using Q.outerList_card c)
    hlengthP hlengthQ (by simpa only [hσP] using hsepP) (by simpa only [hσQ,← hN] using hsepQ)
  have hM : profileModelMass P.profile P.N P.a = 1 := by simp [profileModelMass,haP,P.regular.zero]
  have hP : profileModelMass Q.profile Q.N Q.a = 1 := by simp [profileModelMass,haQ,Q.regular.zero]
  have hmass : (μ.prod ν).real univ ≤ 1 := by
    have hp : μ univ ≤ 1 := (Measure.restrict_le_self univ).trans
      ((Measure.restrict_le_self univ).trans (by simp))
    have hq : ν univ ≤ 1 := (Measure.restrict_le_self univ).trans
      ((Measure.restrict_le_self univ).trans (by simp))
    rw [measureReal_def]
    apply (ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞) ≠ ⊤) ?_).trans_eq (by norm_num)
    rw [← univ_prod_univ,Measure.prod_prod]
    simpa only [one_mul] using mul_le_mul hp hq (by positivity) (by positivity)
  have hb := hshell ((2:ℝ)^P.N) E δ W C (one_le_pow₀ (by norm_num)) hE hEu hδ hW
    (one_le_pow₀ (by norm_num)) P.Q Q.Q P.ρ Q.ρ (fun u => P.profile (u/P.N))
    (fun u => Q.profile (u/Q.N)) P.N σ P.J 0 (P.outerList c) (Q.outerList c) P.masks Q.masks
    (by simpa only [hσP] using hsepP) (by simpa only [hσQ,← hN] using hsepQ) hradP hradQ
    μ ν 1 1 1 zero_lt_one zero_lt_one zero_lt_one (by simpa using hsep') hnear'
    (fun x y l hl w => hd x y l hl w) Z hZ 0 P.N Ψ hΨ hpos hzero hone
    (by simpa using hfreqP.mono (fun _ hr => hr.2.2.1))
    (by simpa only [E,neg_mul] using hfreqP.mono (fun _ hr => hr.2.2.2)) energy
    (by
      intro f g
      have hh := henergy (f.restrictSpatial A₁ hA₁) (g.restrictSpatial A₂ hA₂)
      simp only [DescriptorJetSymbol.restrictSpatial_endpoint] at hh
      rw [hM,hP] at hh
      simpa only [haP,haQ,Nat.cast_zero,htP,hσP,hσQ,hJ,hiP,hiQ,hZP,hZQ,← hN] using hh)
  let err : ℝ := Cerr*((2:ℝ)^P.N)^(-accuracy)*(μ.prod ν).real univ
  have her0 : 0 ≤ err := by dsimp [err]; positivity
  have her : err ≤ Cerr*((2:ℝ)^P.N)^(-((T+2)/2)) := by
    simpa only [accuracy,mul_one] using mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ Cerr*((2:ℝ)^P.N)^(-accuracy))
  have he : 2*(2:ℝ)^(P.N:ℝ)*err^2*(PlanarFalconer.sourceAngularShellMeasure (P.N:ℝ) Ψ).real univ ≤ ((2:ℝ)^P.N)^(-T) := by
    apply (mul_le_mul_of_nonneg_left
      (PlanarFalconer.sourceAngularShellMeasure_real_mass_le (P.N:ℝ) Ψ hV hΨV hsp) (by positivity)).trans
    exact herr P.N hNe P.N err le_rfl her0 her
  have hcostP := hcost P.N hNc (P.outerList c) (Q.outerList c) (L+2*k)
    (P.outerList_card c) (by simpa only [hN] using Q.outerList_card c)
  have hcoeff : 2*descriptorInverseShellCost
      (descriptorRootSymbol (m+1) (P.outerList c) (L+2*k))
      (descriptorRootSymbol (m+1) (Q.outerList c) (L+2*k)) k A B 1 1 Z δ W hδ hW ≤ ((2:ℝ)^P.N)^ε := by
    calc
      _ ≤ ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(ε/2) :=
        mul_le_mul (htwo P.N hNt) hcostP (by unfold descriptorInverseShellCost; positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hb' : (∫ r in Icc ((2:ℝ)^((P.N:ℝ)-1)) ((2:ℝ)^((P.N:ℝ)+1)), ‖charFun (P.outerRestrictedDistance Q c A₁ A₂) r‖^2) ≤
      2*(descriptorInverseShellCost
        (descriptorRootSymbol (m+1) (P.outerList c) (L+2*k))
        (descriptorRootSymbol (m+1) (Q.outerList c) (L+2*k)) k A B 1 1 Z δ W hδ hW*energy)+
      2*(2:ℝ)^(P.N:ℝ)*err^2*(PlanarFalconer.sourceAngularShellMeasure (P.N:ℝ) Ψ).real univ := by
    unfold PolicyJetData.outerRestrictedDistance
    rw [hM,hP]
    simpa only [hσP,hσQ,hJ,hiP,hiQ,← hN,neg_zero,Real.rpow_zero,
      one_mul,sub_zero,inv_one,abs_one,mul_one,accuracy,err,Cerr,C,mul_assoc,μ,ν,μ₀,ν₀] using hb
  apply hb'.trans
  exact add_le_add (by nlinarith only [mul_le_mul_of_nonneg_right hcoeff he0]) he

end Falconer

end OAI
