import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoing

namespace OAI

/-! The local fixed-power construction takes values in the unique outgoing class. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialExterior_local_outgoing (ν m : ℂ) (n : ℕ) (hm : m ≠ 0) :
    ∃ S : Set (ℂ × ℂ), IsOpen S ∧ (ν,m) ∈ S ∧
      ∃ T : ℝ, ∃ Y : S → ℝ → ℂ × ℂ,
        (∀ z, Continuous (Y z) ∧ HasRadialOutgoingExpansion z.val.1 n z.val.2 (Y z)) ∧
        (∀ t, T ≤ t → Continuous (fun z => Y z t)) ∧
        ∀ z t, T ≤ t → (Y z t).1 ≠ 0 ∧
          HasDerivAt (Y z) (radialExteriorODEField z.val.1 n t (Y z t)) t := by
  let δ := ‖m‖/2
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨S,hS,hp,T,_,j,v,_,hmargin,hnear,hcont,_,hODE⟩ :=
    exists_radialExterior_local_family ν m n δ hδ (by dsimp [δ]; linarith)
  let Y := fun (z : S) t => radialPolynomialJet
    (radialExteriorExpansion z.val.1 n z.val.2 j) t+
      radialExteriorUnweight (2*(j : ℝ)) (v z) t
  refine ⟨S,hS,hp,T,Y,?_,hcont,?_⟩
  · intro z
    refine ⟨continuous_radialExterior_polynomialCorrection _ _ _,j,v z,T,?_,fun _ _ => rfl⟩
    have hz : ‖z.val.2‖ ≤ ‖m‖+2*δ := by
      have hh := norm_add_le (z.val.2-m) m
      rw [sub_add_cancel] at hh
      linarith [hnear z]
    calc
      _ ≤ radialExteriorMatrixBound z.val.1+(2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by
        gcongr
      _ ≤ radialExteriorMatrixBound z.val.1+radialExteriorCutoffRate n m δ := by
        unfold radialExteriorCutoffRate
        have hp : 0 ≤ (2*(n : ℝ)+1)*(‖m‖+2*δ)^(2*n) := by positivity
        nlinarith
      _ < _ := hmargin z
  · intro z t ht
    exact ⟨(hODE z t ht).1,(hODE z t ht).2.1.prodMk (hODE z t ht).2.2⟩

end DefocusingNLS

end OAI
