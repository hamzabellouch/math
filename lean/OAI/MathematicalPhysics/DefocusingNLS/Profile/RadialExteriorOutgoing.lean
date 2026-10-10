import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorLocalFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoingUniqueness

namespace OAI

/-! A precise outgoing class selected by the nonlinear asymptotic expansion. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem continuous_radialExterior_polynomialCorrection (P : ℂ[X]) (κ : ℝ)
    (v : ℝ →ᵇ ℂ × ℂ) :
    Continuous (fun t => radialPolynomialJet P t+radialExteriorUnweight κ v t) := by
  have hv : Continuous (fun t => v t) := v.continuous
  unfold radialPolynomialJet radialExteriorPolynomialFunction radialExteriorUnweight
  fun_prop

noncomputable def radialExteriorODEField (ν : ℂ) (n : ℕ) (t : ℝ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (z.2,-(2*ν+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*z.2-
    ν*(ν+10)*z.1+oddPowerNonlinearity n z.1)

theorem radialExteriorODEField_split (ν : ℂ) (n : ℕ) (t : ℝ) (z : ℂ × ℂ) :
    radialExteriorODEField ν n t z=
      (0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*z.2)+radialExteriorErrorMatrix ν z+
        (0,oddPowerNonlinearity n z.1) := by
  apply Prod.ext
  · simp [radialExteriorODEField,radialExteriorErrorMatrix]
  · simp [radialExteriorODEField,radialExteriorErrorMatrix]
    ring

/-- A finite but sufficiently accurate outgoing expansion, including the velocity. -/
def HasRadialOutgoingExpansion (ν : ℂ) (n : ℕ) (m : ℂ) (Z : ℝ → ℂ × ℂ) : Prop :=
  ∃ j : ℕ, ∃ v : ℝ →ᵇ ℂ × ℂ, ∃ T : ℝ,
    radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*‖m‖^(2*n) < 2*(j : ℝ) ∧
    ∀ t, T ≤ t → Z t=radialPolynomialJet (radialExteriorExpansion ν n m j) t+
      radialExteriorUnweight (2*(j : ℝ)) v t

theorem HasRadialOutgoingExpansion.tendsto {ν : ℂ} {n : ℕ} {m : ℂ} {Z : ℝ → ℂ × ℂ}
    (h : HasRadialOutgoingExpansion ν n m Z) : Tendsto Z atTop (nhds (m,0)) := by
  obtain ⟨j,v,T,hκ,heq⟩ := h
  have hκ0 : 0 < 2*(j : ℝ) := by
    have hL : 0 ≤ (2*(n : ℝ)+1)*‖m‖^(2*n) := by positivity
    linarith [radialExteriorMatrixBound_pos ν]
  have hl : Tendsto (fun t => radialPolynomialJet (radialExteriorExpansion ν n m j) t+
      radialExteriorUnweight (2*(j : ℝ)) v t) atTop (nhds (m,0)) := by
    simpa only [radialExteriorExpansion_constant] using
      radialExterior_corrected_jet_tendsto _ hκ0 (radialExteriorExpansion ν n m j) v
  apply hl.congr'
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (heq t ht).symm

theorem HasRadialOutgoingExpansion.congr {ν : ℂ} {n : ℕ} {m : ℂ} {Z W : ℝ → ℂ × ℂ}
    (h : HasRadialOutgoingExpansion ν n m Z) (he : ∀ᶠ t in atTop, Z t=W t) :
    HasRadialOutgoingExpansion ν n m W := by
  obtain ⟨j,v,T,hκ,hZ⟩ := h
  obtain ⟨U,hU⟩ := eventually_atTop.mp he
  refine ⟨j,v,max T U,hκ,?_⟩
  intro t ht
  rw [← hU t ((le_max_right _ _).trans ht)]
  exact hZ t ((le_max_left _ _).trans ht)

theorem radialExterior_outgoing_eventually_eq (ν : ℂ) (n : ℕ) (m : ℂ)
    (Z W : ℝ → ℂ × ℂ) (L : ℝ)
    (hZ : ∀ t, L ≤ t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t)
    (hW : ∀ t, L ≤ t → HasDerivAt W (radialExteriorODEField ν n t (W t)) t)
    (heZ : HasRadialOutgoingExpansion ν n m Z)
    (heW : HasRadialOutgoingExpansion ν n m W) :
    ∀ᶠ t in atTop, Z t=W t := by
  obtain ⟨j,v,T,hj,hv⟩ := heZ
  obtain ⟨k,w,U,hk,hw⟩ := heW
  let V := max L (max T U)
  have hVL : L ≤ V := le_max_left _ _
  have hVT : T ≤ V := (le_max_left T U).trans (le_max_right L _)
  have hVU : U ≤ V := (le_max_right T U).trans (le_max_right L _)
  have hz : ∀ t, V ≤ t → HasDerivAt Z
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(Z t).2)+
        radialExteriorErrorMatrix ν (Z t)+(0,oddPowerNonlinearity n (Z t).1)) t := by
    intro t ht
    simpa only [radialExteriorODEField_split] using hZ t (hVL.trans ht)
  have hw' : ∀ t, V ≤ t → HasDerivAt W
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(W t).2)+
        radialExteriorErrorMatrix ν (W t)+(0,oddPowerNonlinearity n (W t).1)) t := by
    intro t ht
    simpa only [radialExteriorODEField_split] using hW t (hVL.trans ht)
  rcases le_total j k with hjk | hkj
  · exact radialExterior_ordered_outgoing_unique ν n m j k hjk v w Z W V hz hw'
      (fun t ht => hv t (hVT.trans ht)) (fun t ht => hw t (hVU.trans ht)) hj
  · exact (radialExterior_ordered_outgoing_unique ν n m k j hkj w v W Z V hw' hz
      (fun t ht => hw t (hVU.trans ht)) (fun t ht => hv t (hVT.trans ht)) hk).mono
        (fun _ h => h.symm)

theorem exists_radialExterior_outgoing (ν m : ℂ) (n : ℕ) (hm : m ≠ 0) :
    ∃ T : ℝ, ∃ Z : ℝ → ℂ × ℂ, Continuous Z ∧ HasRadialOutgoingExpansion ν n m Z ∧
      (∀ t, T ≤ t → (Z t).1 ≠ 0) ∧
      ∀ t, T ≤ t → HasDerivAt Z (radialExteriorODEField ν n t (Z t)) t := by
  let δ := ‖m‖/2
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨S,_,hmem,T,_,j,v,_,hmargin,_,_,_,hODE⟩ :=
    exists_radialExterior_local_family ν m n δ hd (by dsimp [δ]; linarith)
  let z : S := ⟨(ν,m),hmem⟩
  let Z := fun t => radialPolynomialJet (radialExteriorExpansion ν n m j) t+
    radialExteriorUnweight (2*(j : ℝ)) (v z) t
  have hκ : radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*‖m‖^(2*n) < 2*(j : ℝ) := by
    calc
      _ ≤ radialExteriorMatrixBound ν+(2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by
        gcongr
        linarith
      _ ≤ radialExteriorMatrixBound ν+radialExteriorCutoffRate n m δ := by
        unfold radialExteriorCutoffRate
        have hpos : 0 ≤ (2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by positivity
        nlinarith
      _ < _ := hmargin z
  refine ⟨T,Z,continuous_radialExterior_polynomialCorrection _ _ _,
    ⟨j,v z,T,hκ,fun _ _ => rfl⟩,?_,?_⟩
  · intro t ht
    exact (hODE z t ht).1
  · intro t ht
    exact (hODE z t ht).2.1.prodMk (hODE z t ht).2.2

end DefocusingNLS

end OAI
