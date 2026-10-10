import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMildEnergy

namespace OAI

/-! # Integrated energy balance on a finite expanding torus slab -/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingLowEnergy expandingHighEnergy expandingFreeStep
  expandingFreeInverse expandingInversePath

theorem continuous_expandingLowEnergy_sq (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    Continuous (fun s : Icc (0 : ℝ) T =>
      ‖expandingLowEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL s.2.1)) (u s)‖ ^ 2) := by
  let v := expandingInversePath a b k L T ha hk hL u
  have he (s : Icc (0 : ℝ) T) :
      ‖expandingLowEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL s.2.1)) (u s)‖ ^ 2 =
        Real.exp (-a * s) * ‖expandingLowEnergy a k L hL (v s)‖ ^ 2 := by
    have hret : expandingFreeStep a b k L s ha hk hL s.2.1 (v s) = u s :=
      expandingInversePath_return a b k L T ha hk hL u s
    simpa only [hret] using expandingLowEnergy_free a b k L s ha hk hL s.2.1 (v s)
  simp_rw [he]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).mul
    (((expandingLowEnergy a k L hL).continuous.comp v.continuous).norm.pow 2)

theorem continuous_expandingHighEnergy_sq (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (u : C(Icc (0 : ℝ) T, FourierL2)) :
    Continuous (fun s : Icc (0 : ℝ) T =>
      ‖expandingHighEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL s.2.1)) (u s)‖ ^ 2) := by
  let v := expandingInversePath a b k L T ha hk hL u
  have he (s : Icc (0 : ℝ) T) :
      ‖expandingHighEnergy a k (expandingRadius L s)
        (hL.trans (expandingRadius_ge L s hL s.2.1)) (u s)‖ ^ 2 =
        Real.exp ((6 - 2 * a - k) * s) * ‖expandingHighEnergy a k L hL (v s)‖ ^ 2 := by
    have hret : expandingFreeStep a b k L s ha hk hL s.2.1 (v s) = u s :=
      expandingInversePath_return a b k L T ha hk hL u s
    simpa only [hret] using expandingHighEnergy_free a b k L s ha hk hL s.2.1 (v s)
  simp_rw [he]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).mul
    (((expandingHighEnergy a k L hL).continuous.comp v.continuous).norm.pow 2)

theorem expandingMildEnergy_balance (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (f : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r)
    (t : Icc (0 : ℝ) T) :
    ‖u t‖ ^ 2 = ‖f‖ ^ 2 + ∫ τ in (0 : ℝ)..(t : ℝ),
      (let s := projIcc 0 T hT τ;
      let hR := hL.trans (expandingRadius_ge L s hL s.2.1);
      -a * ‖expandingLowEnergy a k (expandingRadius L s) hR (u s)‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k (expandingRadius L s) hR (u s)‖ ^ 2 +
        2 * inner ℝ (u s) (r τ)) := by
  let p := fun τ => projIcc 0 T hT τ
  let F := fun τ => ‖u (p τ)‖ ^ 2
  let D := fun τ =>
    -a * ‖expandingLowEnergy a k (expandingRadius L (p τ))
      (hL.trans (expandingRadius_ge L (p τ) hL (p τ).2.1)) (u (p τ))‖ ^ 2 +
    (6 - 2 * a - k) * ‖expandingHighEnergy a k (expandingRadius L (p τ))
      (hL.trans (expandingRadius_ge L (p τ) hL (p τ).2.1)) (u (p τ))‖ ^ 2 +
    2 * inner ℝ (u (p τ)) (r τ)
  have hF : Continuous F := (u.continuous.comp continuous_projIcc).norm.pow 2
  have hD : Continuous D :=
    ((continuous_const.mul ((continuous_expandingLowEnergy_sq a b k L T ha hk hL u).comp
      continuous_projIcc)).add
      (continuous_const.mul ((continuous_expandingHighEnergy_sq a b k L T ha hk hL u).comp
        continuous_projIcc))).add
        (continuous_const.mul ((u.continuous.comp continuous_projIcc).inner hr))
  have hd (τ : ℝ) (hτ : τ ∈ Ioo 0 (t : ℝ)) : HasDerivAt F (D τ) τ :=
    hasDerivAt_expandingMildEnergy a b k L T ha hk hL hT u r hr f hu τ
      ⟨hτ.1, hτ.2.trans_le t.2.2⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.2.1 hF.continuousOn hd
    (hD.intervalIntegrable 0 t)
  have hp0 : p 0 = ⟨0, le_rfl, hT⟩ := projIcc_of_mem hT ⟨le_rfl, hT⟩
  have hpt : p t = t := projIcc_of_mem hT t.2
  have hu0 : u ⟨0, le_rfl, hT⟩ = f := by
    have h := hu ⟨0, le_rfl, hT⟩
    simpa [expandingFreeStep_zero, expandingDuhamel] using h
  change ‖u t‖ ^ 2 = ‖f‖ ^ 2 + ∫ τ in (0 : ℝ)..(t : ℝ), D τ
  dsimp only [F] at hi
  rw [hp0, hpt, hu0] at hi
  linarith

end DefocusingNLS

end OAI
