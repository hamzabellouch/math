import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.PairSpinOrbitals
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorFormCompression
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedLinearCoulomb
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedFockStates

namespace OAI

/-! The actual corrected spatial-spin Coulomb tensor differs from its
occupation-diagonal density interaction by the Gram and off-site errors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem correctedLocalizedFourIndex_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin m → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : m*localizedOverlapBound D ≤ 1/2) (i j k l : Fin m) :
    |localizedLinearFourIndex hf u (correctedLocalizedCoefficients u i)
        (correctedLocalizedCoefficients u k) (correctedLocalizedCoefficients u j)
        (correctedLocalizedCoefficients u l)-
      (if i=k ∧ j=l then localizedFourIndex freq (u i) (u i) (u j) (u j) else 0)| ≤
      (m:ℝ)^4*(32*(2*m*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  have hg := localizedLinearFourIndex_correction hf u (correctedLocalizedCoefficients u)
    (show 0 ≤ 2*(m:ℝ)*localizedOverlapBound D by
      exact mul_nonneg (by positivity) (localizedOverlapBound_nonnegative D))
    (fun a b => (correctedLocalizedCoefficients_entries u hsep hs a b).2)
    (fun a b => (correctedLocalizedCoefficients_entries u hsep hs a b).1) i k j l
  have hb : 0 ≤ localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) :=
    mul_nonneg (localizedFourIndexConstant_nonnegative freq) (Real.exp_pos _).le
  by_cases h : i=k ∧ j=l
  · obtain ⟨rfl,rfl⟩ := h
    simpa only [and_self,ite_true] using hg.trans (le_add_of_nonneg_right hb)
  · have ho : i ≠ k ∨ j ≠ l := by tauto
    have he := localizedFourIndex_offsite hf u hsep i k j l ho
    simp only [h,ite_false,sub_zero]
    have ht := abs_add_le
      (localizedLinearFourIndex hf u (correctedLocalizedCoefficients u i)
        (correctedLocalizedCoefficients u k) (correctedLocalizedCoefficients u j)
        (correctedLocalizedCoefficients u l)-localizedFourIndex freq (u i) (u k) (u j) (u l))
      (localizedFourIndex freq (u i) (u k) (u j) (u l))
    simp only [sub_add_cancel] at ht
    exact ht.trans (add_le_add hg he)

theorem localizedSpinMode_coulomb_integrable {freq : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition) (a b c d : Fin ((2*m+1)+1)) :
    Integrable (fun z => flatPairCoulomb z.1 z.2*
      ((star (Coulomb.flatSpinOrbital (localizedSpinMode freq u a) z.1)*
        Coulomb.flatSpinOrbital (localizedSpinMode freq u c) z.1)*
        (star (Coulomb.flatSpinOrbital (localizedSpinMode freq u b) z.2)*
          Coulomb.flatSpinOrbital (localizedSpinMode freq u d) z.2)))
      (Coulomb.spinSpaceMeasure.prod Coulomb.spinSpaceMeasure) := by
  let p := (HubbardGlobal.siteModes m).symm
  apply realSpin_coulomb_integrable
  convert localizedLinearFourIndex_integrable hf u
    (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
    (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) using 1
  funext z
  dsimp only [correctedLocalizedMode,p]
  ring

theorem localizedSpinMode_coulomb_tensor {freq : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition) (a b c d : Fin ((2*m+1)+1)) :
    flatCoulombTensor (localizedSpinMode freq u) a b c d =
      let p := (HubbardGlobal.siteModes m).symm
      if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then
        (localizedLinearFourIndex hf u (correctedLocalizedCoefficients u (p a).1)
          (correctedLocalizedCoefficients u (p c).1) (correctedLocalizedCoefficients u (p b).1)
          (correctedLocalizedCoefficients u (p d).1):ℂ) else 0 := by
  let p := (HubbardGlobal.siteModes m).symm
  have hI : Integrable (fun z : Position × Position => Coulomb.coulombKernel (z.1-z.2)*
      ((correctedLocalizedMode freq u (p a).1 z.1*correctedLocalizedMode freq u (p c).1 z.1)*
        (correctedLocalizedMode freq u (p b).1 z.2*correctedLocalizedMode freq u (p d).1 z.2)))
      (volume.prod volume) := by
    convert localizedLinearFourIndex_integrable hf u
      (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
      (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) using 1
    funext z
    dsimp only [correctedLocalizedMode]
    ring
  have he : (∫ z : Position × Position, Coulomb.coulombKernel (z.1-z.2)*
      ((correctedLocalizedMode freq u (p a).1 z.1*correctedLocalizedMode freq u (p c).1 z.1)*
        (correctedLocalizedMode freq u (p b).1 z.2*correctedLocalizedMode freq u (p d).1 z.2))
      ∂(volume.prod volume)) = localizedLinearFourIndex hf u
        (correctedLocalizedCoefficients u (p a).1) (correctedLocalizedCoefficients u (p c).1)
        (correctedLocalizedCoefficients u (p b).1) (correctedLocalizedCoefficients u (p d).1) := by
    rw [localizedLinearFourIndex_integral hf u]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp only [correctedLocalizedMode]
    ring
  have h := realSpin_coulomb_integral _ _ _ _ hI (p a).2 (p b).2 (p c).2 (p d).2
  change flatCoulombTensor (localizedSpinMode freq u) a b c d = _ at h
  change flatCoulombTensor (localizedSpinMode freq u) a b c d =
    if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then _ else 0
  simpa only [he] using h

def localizedDensityTensor (freq : ℝ) {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (a b c d : Fin ((2*m+1)+1)) : ℂ :=
  let p := (HubbardGlobal.siteModes m).symm
  if a=c ∧ b=d then
    (localizedFourIndex freq (u (p a).1) (u (p a).1) (u (p b).1) (u (p b).1):ℂ) else 0

theorem localizedSpinMode_coulomb_error {freq D : ℝ} (hf : 0 < freq)
    {m : ℕ} (u : Fin (m+1) → PlanarPosition)
    (hsep : ∀ i j, i ≠ j → D ≤ ‖u i-u j‖)
    (hs : (m+1:ℕ)*localizedOverlapBound D ≤ 1/2)
    (a b c d : Fin ((2*m+1)+1)) :
    ‖flatCoulombTensor (localizedSpinMode freq u) a b c d-localizedDensityTensor freq u a b c d‖ ≤
      (m+1:ℝ)^4*(32*(2*(m+1:ℝ)*localizedOverlapBound D)*localizedPotentialBound freq)+
        localizedFourIndexConstant freq*Real.exp (-(9/10:ℝ)*D) := by
  let p := (HubbardGlobal.siteModes m).symm
  have he := correctedLocalizedFourIndex_error hf u hsep hs (p a).1 (p b).1 (p c).1 (p d).1
  rw [localizedSpinMode_coulomb_tensor hf]
  change ‖(if (p a).2=(p c).2 ∧ (p b).2=(p d).2 then _ else 0)-_‖ ≤ _
  by_cases hspin : (p a).2=(p c).2 ∧ (p b).2=(p d).2
  · have heq : ((p a).1=(p c).1 ∧ (p b).1=(p d).1) ↔ (a=c ∧ b=d) := by
      constructor
      · rintro ⟨hac,hbd⟩
        exact ⟨p.injective (Prod.ext hac hspin.1),p.injective (Prod.ext hbd hspin.2)⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨rfl,rfl⟩
    rw [ite_eq_left hspin]
    dsimp only [localizedDensityTensor]
    simp only [heq] at he
    split_ifs at he ⊢ <;> simpa only [← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,Complex.ofReal_zero,sub_zero,Nat.cast_add,Nat.cast_one] using he
  · have hne : ¬(a=c ∧ b=d) := by rintro ⟨rfl,rfl⟩; exact hspin ⟨rfl,rfl⟩
    rw [ite_eq_right hspin]
    simp only [localizedDensityTensor,ite_eq_right hne,sub_self,norm_zero]
    have hp := localizedPotentialBound_nonnegative freq
    have hov := localizedOverlapBound_nonnegative D
    exact add_nonneg (by positivity)
      (mul_nonneg (localizedFourIndexConstant_nonnegative freq) (Real.exp_pos _).le)

end ContinuumCoulomb

end

end OAI
