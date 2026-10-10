import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailFamily
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUniformTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailRemoval
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFreeCorrection

namespace OAI

/-! Nonvanishing nonlinear exterior solutions on a common tail for convergent parameters. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem exists_radialExterior_common_tail_data (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (δ : ℝ) (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∃ Z : ℕ → ℝ → ℂ × ℂ, ∃ Z₀ : ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z Z₀ atTop (Ici (0 : ℝ)) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      Tendsto Z₀ atTop (nhds (m₀,0)) ∧
      (∃ j : ℕ, ∃ w : ℝ →ᵇ ℂ × ℂ, radialExteriorMatrixBound ν₀ < 2*(j : ℝ) ∧
        Z₀ = fun t => radialPolynomialJet (radialFreeExpansion ν₀ m₀ j) t+
          radialExteriorUnweight (2*(j : ℝ)) w t) ∧
      (∃ j : ℕ, ∃ v : ℕ → ℝ →ᵇ ℂ × ℂ,
        (∀ n, Z n=fun t => radialPolynomialJet (radialExteriorExpansion (ν n) n (m n) j) t+
          radialExteriorUnweight (2*(j : ℝ)) (v n) t) ∧
        ∀ᶠ n in atTop, radialExteriorMatrixBound (ν n)+
          radialExteriorCutoffRate n m₀ δ < 2*(j : ℝ)) ∧
      (∀ t, S ≤ t → HasDerivAt (fun s => (Z₀ s).1) (Z₀ t).2 t ∧
        HasDerivAt (fun s => (Z₀ s).2)
          (-(2*ν₀+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z₀ t).2-
            ν₀*(ν₀+10)*(Z₀ t).1) t) ∧
      ∀ᶠ n in atTop, ∀ t, S ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (fun s => (Z n s).1) (Z n t).2 t ∧
        HasDerivAt (fun s => (Z n s).2)
          (-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  have hm01 : ‖m₀‖ < 1 := by linarith
  obtain ⟨j,hj⟩ := exists_nat_gt (radialExteriorMatrixBound ν₀/2)
  let κ : ℝ := 2*(j : ℝ)
  have hκ : radialExteriorMatrixBound ν₀ < κ := by dsimp [κ]; linarith
  have hκ0 : 0 < κ := (radialExteriorMatrixBound_pos ν₀).trans hκ
  have hB : Tendsto (fun n => radialExteriorMatrixBound (ν n)) atTop
      (nhds (radialExteriorMatrixBound ν₀)) := by
    have hc : Continuous radialExteriorMatrixBound := by unfold radialExteriorMatrixBound; fun_prop
    exact hc.continuousAt.tendsto.comp hν
  have hmargin : ∀ᶠ n in atTop, radialExteriorMatrixBound (ν n)+
      radialExteriorCutoffRate n m₀ δ < κ := by
    have hh := hB.add (radialExteriorCutoffRate_tendsto m₀ δ hδ.le hsmall)
    rw [add_zero] at hh
    exact hh.eventually (gt_mem_nhds hκ)
  let P : ℕ → ℂ[X] := fun n => radialExteriorExpansion (ν n) n (m n) j
  let Q := radialFreeExpansion ν₀ m₀ j
  obtain ⟨T,hT,R,R₀,hR,hR₀,hr⟩ :=
    exists_radialExterior_bounded_residual_family ν m ν₀ m₀ hν hm hm01 j
  let f : ℕ → ℝ → ℂ := fun n => boundedRadialPolynomialAfter T (P n)
  let r : ℕ → ℝ →ᵇ ℂ × ℂ := fun n => boundedRadialResidualAfter T (R n)
  obtain ⟨v,w,hvw,_,hwd,hv⟩ := exists_radialExterior_convergent_corrections κ ν ν₀ m₀ δ hν hδ.le
    hsmall hκ f (fun n => (boundedRadialPolynomialAfter T (P n)).continuous)
    r (boundedRadialResidualAfter T R₀) hr
  let Z : ℕ → ℝ → ℂ × ℂ := fun n t => radialPolynomialJet (P n) t+radialExteriorUnweight κ (v n) t
  let Z₀ : ℝ → ℂ × ℂ := fun t => radialPolynomialJet Q t+radialExteriorUnweight κ w t
  have hZ : TendstoUniformlyOn Z Z₀ atTop (Ici (0 : ℝ)) :=
    radialExterior_corrected_jet_uniform_limit κ hκ0.le ν m ν₀ m₀ hν hm hm01 j v w hvw
  have hZlim : ∀ n, Tendsto (Z n) atTop (nhds (m n,0)) := by
    intro n
    simpa only [P,radialExteriorExpansion_constant] using
      radialExterior_corrected_jet_tendsto κ hκ0 (P n) (v n)
  have hZ₀lim : Tendsto Z₀ atTop (nhds (m₀,0)) := by
    simpa only [Q,radialFreeExpansion_constant] using
      radialExterior_corrected_jet_tendsto κ hκ0 Q w
  have hP : TendstoUniformlyOn (fun n => radialPolynomialJet (P n)) (radialPolynomialJet Q)
      atTop (Ici (0 : ℝ)) :=
    radialPolynomialJet_uniform_limit P Q j
      (Eventually.of_forall (fun n => radialExteriorExpansion_degree _ _ _ _))
      (radialFreeExpansion_degree _ _ _)
      (fun k _ => radialExteriorExpansion_coefficient_limit ν m ν₀ m₀ hν hm hm01 j k)
  have hQlim : Tendsto (radialPolynomialJet Q) atTop (nhds (m₀,0)) := by
    simpa only [Q,radialFreeExpansion_constant] using radialPolynomialJet_tendsto Q
  obtain ⟨SP,_,hSP⟩ := radial_uniform_tail_near_limit (fun n => radialPolynomialJet (P n))
    (radialPolynomialJet Q) (m₀,0) δ hδ hP hQlim
  obtain ⟨SF,_,hSF⟩ := radial_uniform_tail_near_limit Z Z₀ (m₀,0) δ hδ hZ hZ₀lim
  let S := max T (max SP SF)
  refine ⟨S,hT.trans (le_max_left _ _),Z,Z₀,hZ,hZlim,hZ₀lim,
    ⟨j,w,hκ,rfl⟩,⟨j,v,(fun _ => rfl),hmargin⟩,?_,?_⟩
  · intro t ht
    exact radialExterior_free_tail_from_correction ν₀ T j Q R₀ hR₀ w t
      ((le_max_left T _).trans ht) (hwd t)
  filter_upwards [hv,hSP,hSF] with n hvn hpn hfn t ht
  have htT : T ≤ t := (le_max_left T _).trans ht
  have htSP : SP ≤ t := ((le_max_left SP SF).trans (le_max_right T _)).trans ht
  have htSF : SF ≤ t := ((le_max_right SP SF).trans (le_max_right T _)).trans ht
  have hpn' : ‖radialExteriorPolynomialFunction (P n) t-m₀‖ < δ := by
    exact (norm_fst_le (radialPolynomialJet (P n) t-(m₀,0))).trans_lt (hpn t htSP)
  have hfn' : ‖(Z n t).1-m₀‖ < δ :=
    (norm_fst_le (Z n t-(m₀,0))).trans_lt (hfn t htSF)
  have hne : (Z n t).1 ≠ 0 := by
    intro hz
    rw [hz,zero_sub,norm_neg] at hfn'
    exact (hδm.trans hfn').false
  refine ⟨hne,?_⟩
  have hd := radialExterior_tail_cutoff_removal (ν n) m₀ n j δ T (P n) (R n)
    (hR n) (v n) t htT hpn'.le hfn'.le (hvn.2.2 t)
  exact hd

theorem exists_radialExterior_common_tail_with_expansion (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (δ : ℝ) (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∃ Z : ℕ → ℝ → ℂ × ℂ, ∃ Z₀ : ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z Z₀ atTop (Ici (0 : ℝ)) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      Tendsto Z₀ atTop (nhds (m₀,0)) ∧
      (∃ j : ℕ, ∃ w : ℝ →ᵇ ℂ × ℂ, radialExteriorMatrixBound ν₀ < 2*(j : ℝ) ∧
        Z₀ = fun t => radialPolynomialJet (radialFreeExpansion ν₀ m₀ j) t+
          radialExteriorUnweight (2*(j : ℝ)) w t) ∧
      (∀ t, S ≤ t → HasDerivAt (fun s => (Z₀ s).1) (Z₀ t).2 t ∧
        HasDerivAt (fun s => (Z₀ s).2)
          (-(2*ν₀+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z₀ t).2-
            ν₀*(ν₀+10)*(Z₀ t).1) t) ∧
      ∀ᶠ n in atTop, ∀ t, S ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (fun s => (Z n s).1) (Z n t).2 t ∧
        HasDerivAt (fun s => (Z n s).2)
          (-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  obtain ⟨S,hS,Z,Z₀,hconv,hlim,hlim₀,hfreeExp,_,hfree,hactual⟩ :=
    exists_radialExterior_common_tail_data ν m ν₀ m₀ hν hm δ hδ hδm hsmall
  exact ⟨S,hS,Z,Z₀,hconv,hlim,hlim₀,hfreeExp,hfree,hactual⟩

theorem exists_radialExterior_common_tail (ν m : ℕ → ℂ) (ν₀ m₀ : ℂ)
    (hν : Tendsto ν atTop (nhds ν₀)) (hm : Tendsto m atTop (nhds m₀))
    (δ : ℝ) (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) :
    ∃ S : ℝ, 0 ≤ S ∧ ∃ Z : ℕ → ℝ → ℂ × ℂ, ∃ Z₀ : ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z Z₀ atTop (Ici (0 : ℝ)) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      Tendsto Z₀ atTop (nhds (m₀,0)) ∧
      (∀ t, S ≤ t → HasDerivAt (fun s => (Z₀ s).1) (Z₀ t).2 t ∧
        HasDerivAt (fun s => (Z₀ s).2)
          (-(2*ν₀+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z₀ t).2-
            ν₀*(ν₀+10)*(Z₀ t).1) t) ∧
      ∀ᶠ n in atTop, ∀ t, S ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (fun s => (Z n s).1) (Z n t).2 t ∧
        HasDerivAt (fun s => (Z n s).2)
          (-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  obtain ⟨S,hS,Z,Z₀,hconv,hlim,hlim₀,_,hfree,hactual⟩ :=
    exists_radialExterior_common_tail_with_expansion ν m ν₀ m₀ hν hm δ hδ hδm hsmall
  exact ⟨S,hS,Z,Z₀,hconv,hlim,hlim₀,hfree,hactual⟩

end DefocusingNLS

end OAI
