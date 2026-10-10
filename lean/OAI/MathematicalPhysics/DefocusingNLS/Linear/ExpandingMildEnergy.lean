import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingInteractionPicture
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyInner

namespace OAI

/-! # Energy differentiation for the actual expanding mild equation

The proof takes place in the free interaction picture.  The solution and
forcing need only be continuous in the exact moving Sobolev norm.
-/

open Set Filter Topology

namespace DefocusingNLS

attribute [local irreducible] expandingLowEnergy expandingHighEnergy expandingFreeStep
  expandingFreeInverse expandingInversePath expandingDuhamel

private theorem expanding_component_derivative (a b k L T c : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (J₀ : FourierL2 →L[ℝ] FourierL2)
    (J : Icc (0 : ℝ) T → FourierL2 →L[ℝ] FourierL2)
    (hnorm : ∀ s g, ‖J s (expandingFreeStep a b k L s ha hk hL s.2.1 g)‖ ^ 2 =
      Real.exp (c * s) * ‖J₀ g‖ ^ 2)
    (hinner : ∀ s g h,
      inner ℝ (J s (expandingFreeStep a b k L s ha hk hL s.2.1 g))
        (J s (expandingFreeStep a b k L s ha hk hL s.2.1 h)) =
      Real.exp (c * s) * inner ℝ (J₀ g) (J₀ h))
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (f : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun τ => ‖J (projIcc 0 T hT τ) (u (projIcc 0 T hT τ))‖ ^ 2)
      (c * ‖J (projIcc 0 T hT t) (u (projIcc 0 T hT t))‖ ^ 2 +
        2 * inner ℝ (J (projIcc 0 T hT t) (u (projIcc 0 T hT t)))
          (J (projIcc 0 T hT t) (r t))) t := by
  let v := expandingInversePath a b k L T ha hk hL u
  let p := fun τ => projIcc 0 T hT τ
  have hreturn (s : Icc (0 : ℝ) T) :
      expandingFreeStep a b k L s ha hk hL s.2.1 (v s) = u s :=
    expandingInversePath_return a b k L T ha hk hL u s
  have he (s : Icc (0 : ℝ) T) : ‖J s (u s)‖ ^ 2 =
      Real.exp (c * s) * ‖J₀ (v s)‖ ^ 2 := by
    simpa only [hreturn] using hnorm s (v s)
  have hv := hasDerivAt_expandingMild_pullback a b k L T ha hk hL hT u r hr f hu t ht
  have hJ := J₀.hasFDerivAt.comp_hasDerivAt t hv
  have hd := (((hasDerivAt_id t).const_mul c).exp).mul hJ.norm_sq
  have hsame : (fun τ => Real.exp (c * τ) * ‖J₀ (v (p τ))‖ ^ 2) =ᶠ[𝓝 t]
      (fun τ => ‖J (p τ) (u (p τ))‖ ^ 2) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    have hp : p τ = ⟨τ, hτ.1.le, hτ.2.le⟩ := projIcc_of_mem hT ⟨hτ.1.le, hτ.2.le⟩
    rw [hp]
    exact (he ⟨τ, hτ.1.le, hτ.2.le⟩).symm
  have hi : inner ℝ (J (p t) (u (p t))) (J (p t) (r t)) =
      Real.exp (c * t) * inner ℝ (J₀ (v (p t)))
        (J₀ (expandingFreeInverse a b k L t ha hk hL ht.1.le (r t))) := by
    have hi := hinner ⟨t, ht.1.le, ht.2.le⟩ (v ⟨t, ht.1.le, ht.2.le⟩)
      (expandingFreeInverse a b k L t ha hk hL ht.1.le (r t))
    rw [hreturn, expandingFreeInverse_right] at hi
    simpa only [p, projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩] using hi
  apply (hd.congr_of_eventuallyEq hsame.symm).congr_deriv
  change (Real.exp (c * t) * (c * 1)) * ‖J₀ (v (p t))‖ ^ 2 +
    Real.exp (c * t) * (2 * inner ℝ (J₀ (v (p t)))
      (J₀ (expandingFreeInverse a b k L t ha hk hL ht.1.le (r t)))) = _
  rw [he, hi]
  dsimp [p]
  rw [projIcc_of_mem hT ⟨ht.1.le, ht.2.le⟩]
  ring

theorem hasDerivAt_expandingMildEnergy (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, FourierL2)) (r : ℝ → FourierL2) (hr : Continuous r)
    (f : FourierL2)
    (hu : ∀ s : Icc (0 : ℝ) T, u s =
      expandingFreeStep a b k L s ha hk hL s.2.1 f +
        expandingDuhamel a b k L ha hk hL s r)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    let s := projIcc 0 T hT t
    let hR := hL.trans (expandingRadius_ge L s hL s.2.1)
    HasDerivAt (fun τ => ‖u (projIcc 0 T hT τ)‖ ^ 2)
      (-a * ‖expandingLowEnergy a k (expandingRadius L s) hR (u s)‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k (expandingRadius L s) hR (u s)‖ ^ 2 +
        2 * inner ℝ (u s) (r t)) t := by
  dsimp only
  have hlo := expanding_component_derivative a b k L T (-a) ha hk hL hT
    ((expandingLowEnergy a k L hL).restrictScalars ℝ)
    (fun s => (expandingLowEnergy a k (expandingRadius L s)
      (hL.trans (expandingRadius_ge L s hL s.2.1))).restrictScalars ℝ)
    (fun s g => expandingLowEnergy_free a b k L s ha hk hL s.2.1 g)
    (fun s g h => expandingLowEnergy_free_inner a b k L s ha hk hL s.2.1 g h)
    u r hr f hu t ht
  have hhi := expanding_component_derivative a b k L T (6 - 2 * a - k) ha hk hL hT
    ((expandingHighEnergy a k L hL).restrictScalars ℝ)
    (fun s => (expandingHighEnergy a k (expandingRadius L s)
      (hL.trans (expandingRadius_ge L s hL s.2.1))).restrictScalars ℝ)
    (fun s g => expandingHighEnergy_free a b k L s ha hk hL s.2.1 g)
    (fun s g h => expandingHighEnergy_free_inner a b k L s ha hk hL s.2.1 g h)
    u r hr f hu t ht
  simp only [ContinuousLinearMap.coe_restrictScalars'] at hlo hhi
  convert hlo.add hhi using 1
  · funext τ
    exact expandingEnergy_norm_sq a k _
      (hL.trans (expandingRadius_ge L _ hL (projIcc 0 T hT τ).2.1)) _
  · rw [expandingEnergy_inner a k _
      (hL.trans (expandingRadius_ge L _ hL (projIcc 0 T hT t).2.1))]
    ring

end DefocusingNLS

end OAI
