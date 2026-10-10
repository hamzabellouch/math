import OAI.MeasureTheory.Falconer.Fourier.RotatedMaskedJetShell
import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseCost
import OAI.MeasureTheory.Falconer.Recursion.ProfilePairMass
import OAI.MeasureTheory.Falconer.Fourier.DescriptorPairDerivativeScale
import OAI.MeasureTheory.Falconer.Shells.DescriptorShellRegime
import OAI.MeasureTheory.Falconer.Estimates.ScalarErrorBudget
import OAI.MeasureTheory.Falconer.Estimates.FarEnvelope
import OAI.MeasureTheory.Falconer.Geometry.CellNorthFrame

namespace OAI

/-! # Uniform conversion of the actual positive high shell

The scale hypotheses are those supplied by the high-prefix geometry.
The original pair mass, finite inverse cost, and squared remainder are
paid before the converted energy enters the policy graph recurrence.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_policy_scalar_conversion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (lam T δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W)
    (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ r, 0 ≤ Ψ r)
    (hzero : ∀ r ≤ 0, Ψ r = 0) (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4) (minJet : ℕ := 0) :
    ∃ K : ℕ, minJet ≤ K ∧ ∀ L : ℕ, ∀ Z : ℝ, 0 < Z → ∃ N₀ : ℕ,
      ∀ P : PolicyJetData m, P.σ = σ → P.lam = lam → P.Z = Z → N₀ ≤ P.N →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      (∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^P.a ∧ dist z.1 z.2*(2:ℝ)^P.a ≤ W) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      20*P.σ*(P.N:ℝ) ≤ (P.t:ℝ)-P.a →
      (P.longest:ℝ) ≤ ((P.t:ℝ)-P.a)/2+P.σ*P.N →
      ∀ w₀ : Sphere (m+3),
      (2:ℝ)^(-(P.a:ℝ))*
        (∫ r in Icc ((2:ℝ)^((P.t:ℝ)-1)) ((2:ℝ)^((P.t:ℝ)+1)),
          ‖charFun (maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
            P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) r‖^2) ≤
      ((2:ℝ)^P.N)^ε*P.envelope K L Ψ+((2:ℝ)^P.N)^(-T) := by
  let β : ℝ := 2*((m+3:ℕ)+1)*lam
  let accuracy : ℝ := β+(T+2)/2
  obtain ⟨k,A₀,hA₀,horder⟩ := exists_rotated_masked_jet_shell_order hgnomonic hquadratic m
    (κ := 16*σ) (Z := accuracy) (by positivity)
  let order := 2*(k+1)+(m+2)+1
  let C : ℝ := (2:ℝ)^order
  let Cerr : ℝ := δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C
  have hCerr : 0 ≤ Cerr := by dsimp [Cerr,C]; positivity
  obtain ⟨Nder,hder⟩ := uniform_descriptor_pair_derivatives (m+3) order 3 hσ
  obtain ⟨Nfreq,hfreq⟩ := eventual_descriptor_pair_shell_regime (d := m+3) hσ hσ1 hδ Ψ hΨ hsupp
  obtain ⟨Nrad,hrad⟩ := Regularization.fixed_constant_absorbed hσ 8
  obtain ⟨Ntwo,htwo⟩ := Regularization.fixed_constant_absorbed (half_pos hε) 2
  obtain ⟨Nerr,herr⟩ := eventual_scalar_shell_error_budget T hCerr
    (show 0 ≤ 4*V from mul_nonneg (by norm_num) hV)
  refine ⟨max (2*k) minJet,le_max_right _ _,?_⟩
  intro L Z hZ
  obtain ⟨A,hA,hshell⟩ := horder L
  obtain ⟨Ncost,hcost⟩ := eventual_rotated_root_shell_cost m k A Z δ W hδ hW (half_pos hε)
  refine ⟨max (max Nder Nfreq) (max (max Nrad Ntwo) (max Nerr Ncost)),?_⟩
  intro P hσP hlam hZP hN hcover hsep hcenter hgap hlength w₀
  let := P.regular.probability
  obtain ⟨e,he⟩ := separated_cells_north_frame m (P.Q.descendant P.X) (P.Q.descendant P.Y)
    (P.Q.descendant_side_pos (by rw [P.unit]; norm_num) P.X)
    (by rw [P.Q.descendant_side,P.Q.descendant_side,P.X_length,P.Y_length]) hcenter
  have hnear : ∀ᵐ z : Space (m+3) × Space (m+3)
      ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod (P.ρ.restrict (P.Q.descendant P.Y).carrier),
      ‖e (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (P.Q.descendant P.X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
    exact he z.1 hx z.2 hy
  have hNd : Nder ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hNf : Nfreq ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hNr : Nrad ≤ P.N := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hNt : Ntwo ≤ P.N := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hNe : Nerr ≤ P.N := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNc : Ncost ≤ P.N := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have htN : P.t ≤ P.N := P.base_right.trans P.base_N
  have haN : P.a ≤ P.N := by
    have hp : 0 ≤ 20*P.σ*(P.N:ℝ) := by rw [hσP]; positivity
    have hat : (P.a:ℝ) ≤ P.t := by linarith
    exact (Nat.cast_le.mp hat).trans htN
  have hsp : ∀ r, 4 < r → Ψ r = 0 := by
    intro r hr
    by_contra hn
    exact (not_lt_of_ge hr.le) (hsupp r hn).2
  let := PlanarFalconer.sourceAngularShellMeasure_finite (P.t:ℝ) Ψ hV hΨV hsp
  let E := descriptorDerivativeScale P.N P.σ P.longest
  have hE : 1 ≤ E := descriptorDerivativeScale_ge_one P.N (by simpa [hσP] using hσ.le) _
  have hEupper : E ≤ ((2:ℝ)^P.N)^2 := descriptorDerivativeScale_le_square P.N P.longest
    (by simpa [hσP] using hσ.le) (by simpa [hσP] using hσ1) P.longest_le_N
  have hradius : ∀ b ∈ P.list, (descriptorMaskRadius P.N P.σ b)⁻¹ ≤ E := by
    intro b hb
    apply (descriptorMaskRadius_inv_le P.N P.σ b (Finset.le_sup hb)).trans
    change 8*max 1 _ ≤ ((2:ℝ)^P.N)^P.σ*max 1 _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [hσP] using hrad P.N hNr
  have hsep' : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
      (P.ρ.restrict (P.Q.descendant P.Y).carrier), δ ≤ dist z.1 z.2/(2:ℝ)^(-(P.a:ℝ)) := by
    simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_inv_eq_mul]
      using hsep.mono (fun _ hz => hz.1)
  have hfreqP := hfreq P.N hNf P.longest P.a P.t P.longest_le_N
    (by simpa only [hσP] using hgap) (by simpa only [hσP] using hlength)
    (P.ρ.restrict (P.Q.descendant P.X).carrier) (P.ρ.restrict (P.Q.descendant P.Y).carrier) hsep'
  have hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ,
      0 < r*((2:ℝ)^P.a)⁻¹ ∧ E^2 ≤ r*((2:ℝ)^P.a)⁻¹ ∧
        r*((2:ℝ)^P.a)⁻¹ ≤ 4*(2:ℝ)^((P.t:ℝ)-P.a) := by
    simpa only [E,hσP,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
      using hfreqP.mono (fun _ hr => hr.2.2.1)
  have hf : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ,
      ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier),
        1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ ((2:ℝ)^P.N)^(-(16*σ)) := by
    simpa only [E,hσP,neg_mul] using hfreqP.mono (fun _ hr => hr.2.2.2)
  have hd := hder P.N hNd P.Q P.ρ (fun u => P.profile (u/P.N)) P.J P.i P.longest
    P.list P.masks P.list_card (fun b hb => Finset.le_sup hb)
    (by simpa only [PolicyJetData.list,hσP] using P.separated)
  have hd' : ∀ x y l, l ≤ 2*(k+1)+(m+2)+1 → ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ l (descriptorPairAmplitude P.Q P.ρ (fun u => P.profile (u/P.N))
        P.N P.σ P.J P.i P.list P.masks x y) w‖ ≤ C*E^l := by
    simpa only [order,C,E,hσP] using fun x y l hl (w : Sphere (m+3)) => hd x y l hl w
  have hb := hshell ((2:ℝ)^P.N) E δ W C (one_le_pow₀ (by norm_num)) hE hEupper hδ hW
    (one_le_pow₀ (by norm_num)) e w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list P.masks
    (P.Q.descendant P.X) (P.Q.descendant P.Y) hcover P.separated hradius hsep hnear hd'
    Z hZ P.t Ψ hΨ hpos hzero hone hregime hf
  let η : ℝ := |(profileModelMass P.profile P.N P.a)⁻¹*(profileModelMass P.profile P.N P.a)⁻¹| *
    ((δ^(-(((m+2:ℕ):ℝ)/2))*A₀*C*((2:ℝ)^P.N)^(-accuracy))*
      ((P.ρ.restrict (P.Q.descendant P.X).carrier).prod
        (P.ρ.restrict (P.Q.descendant P.Y).carrier)).real univ)
  have hη : 0 ≤ η := by dsimp [η,C]; positivity
  have hm := regularized_pair_model_mass P.Q P.ρ P.regular haN P.X P.Y P.X_length P.Y_length
  have hηbound : η ≤ Cerr*((2:ℝ)^P.N)^(-((T+2)/2)) := by
    calc
      _ = Cerr*(|(profileModelMass P.profile P.N P.a)⁻¹*(profileModelMass P.profile P.N P.a)⁻¹| *
          ((P.ρ.restrict (P.Q.descendant P.X).carrier).prod
            (P.ρ.restrict (P.Q.descendant P.Y).carrier)).real univ)*((2:ℝ)^P.N)^(-accuracy) := by
        dsimp [η,Cerr]; ring
      _ ≤ Cerr*((2:ℝ)^P.N)^β*((2:ℝ)^P.N)^(-accuracy) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hCerr
        simpa only [hlam,β,Nat.cast_add,Nat.cast_ofNat] using hm
      _ = _ := by rw [mul_assoc,← Real.rpow_add (by positivity)]; dsimp [accuracy]; congr 2; ring
  have he : 2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2*
      (PlanarFalconer.sourceAngularShellMeasure (P.t:ℝ) Ψ).real univ ≤ ((2:ℝ)^P.N)^(-T) := by
    apply (mul_le_mul_of_nonneg_left
      (PlanarFalconer.sourceAngularShellMeasure_real_mass_le (P.t:ℝ) Ψ hV hΨV hsp)
      (by positivity : 0 ≤ 2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2)).trans
    exact herr P.N hNe _ η (by have hh : (P.t:ℝ) ≤ P.N := Nat.cast_le.mpr htN; linarith [Nat.cast_nonneg (α := ℝ) P.a]) hη hηbound
  have hcoeff : 2*rotatedInverseShellCost m k P.list A Z δ W hδ hW ≤ ((2:ℝ)^P.N)^ε := by
    calc
      _ ≤ ((2:ℝ)^P.N)^(ε/2)*((2:ℝ)^P.N)^(ε/2) :=
        mul_le_mul (htwo P.N hNt) (hcost P.N hNc P.list P.list_card)
          (by unfold rotatedInverseShellCost; positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hM : 0 < profileModelMass P.profile P.N P.a := by unfold profileModelMass; positivity
  have henv : 0 ≤ P.envelope (2*k) L Ψ :=
    le_csSup (jetStateValues_bddAbove P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i
      P.masks P.separated P.separated P.Z_pos _ _ hM hM P.a P.t Ψ) (Or.inl rfl)
  rw [← hZP] at hb
  change _ ≤ 2*(_*P.envelope (2*k) L Ψ)+2*(2:ℝ)^((P.t:ℝ)-P.a)*η^2*_ at hb
  rw [← hZP] at hcoeff
  have hmain : 2*(rotatedInverseShellCost m k P.list A P.Z δ W hδ hW *
      P.envelope (2*k) L Ψ) ≤ ((2:ℝ)^P.N)^ε*P.envelope (2*k) L Ψ := by
    nlinarith only [mul_le_mul_of_nonneg_right hcoeff henv]
  have hbase := hb.trans (add_le_add hmain he)
  have hmono : P.envelope (2*k) L Ψ ≤ P.envelope (max (2*k) minJet) L Ψ :=
    jetStateEnvelope_budget_mono (le_max_left _ _) le_rfl (by norm_num) le_rfl
      P.Q P.ρ (fun u => P.profile (u/P.N)) P.N P.σ P.J P.i P.masks
      P.separated P.separated P.Z_pos _ _ hM hM P.a P.t Ψ
  exact hbase.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmono (show 0 ≤ ((2:ℝ)^P.N)^ε by positivity)) le_rfl)

end Falconer

end OAI
