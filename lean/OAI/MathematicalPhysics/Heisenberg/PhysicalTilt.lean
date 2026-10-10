import OAI.MathematicalPhysics.Heisenberg.CubeSurface

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.Selection
open SlotTensor

lemma matrix_tilt_mean {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Matrix I I ℝ) (hA : A.transpose=A) (m : I → ℝ) (V b L : ℝ)
    (hV : 0≤V) (hb : 0≤b) (hL : 0<L) (hm : ∀ i,-V/2≤ m i)
    (htail : L*Matrix.trace (NormedSpace.exp A)≤
      Matrix.trace (NormedSpace.exp A*Matrix.diagonal (fun i=>if V/4≤ m i then (1:ℝ) else 0)))
    (hsmall : L⁻¹*Real.exp (-(b*V/16))≤1/11) :
    V/8≤(∑ i,NormedSpace.exp A i i*Real.exp (b*m i)*m i)/
      tiltPartition (fun i=>NormedSpace.exp A i i) m b := by
  have hw : ∀ i,0≤NormedSpace.exp A i i:=fun i=>(exp_diagonal_pos A hA i).le
  have hp : 0<∑ i,NormedSpace.exp A i i:=exp_trace_pos A hA
  rw [trace_spectral_tail] at htail
  have ht:=tilt_tail_bound _ m hw hp hb hL htail (a:=3*V/16)
  have he : b*(3*V/16-V/4)= -(b*V/16):=by ring
  rw [he] at ht
  have hbnd :=ht.trans hsmall
  have hl:=tilt_mean_lower _ m hw hp b (3*V/16) (V/2) (by simpa only [neg_div] using hm)
  nlinarith [mul_le_mul_of_nonneg_left hbnd (show 0≤3*V/16+V/2 by positivity)]

lemma physical_field_mean {d ℓ : ℕ} (Λ : Finset (Site d))
    (τ : State d ℓ) (hτ : ∀ A B,τ.functional (A*B)=τ.functional (B*A))
    (β h L : ℝ) (hb : 0≤β*h) (hL : 0<L)
    (htail : L*Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ))≤
      Matrix.trace (NormedSpace.exp ((β/2) • spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ)*
        Matrix.diagonal (fun k : Λ → SpinSlots.Level ℓ=>if (Λ.card:ℝ)*ℓ/4≤physicalMagnetization ℓ k then (1:ℝ) else 0)))
    (hsmall : L⁻¹*Real.exp (-((β*h)*((Λ.card:ℝ)*ℓ)/16))≤1/11) :
    (Λ.card:ℝ)*ℓ/8≤((gibbsState τ (shiftedField Λ h) β).functional (totalZ Λ)).re := by
  rw [shiftedField_gibbs_totalZ Λ τ hτ]
  apply matrix_tilt_mean _ _ _ _ _ _ (by positivity) hb hL _ htail hsmall
  · rw [Matrix.transpose_smul,spinGenerator_transpose _
      (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he))]
  · intro k
    simpa only [Fintype.card_coe,neg_mul] using (physicalMagnetization_bounds ℓ k).1

end Heisenberg.Selection
end
end

end OAI
