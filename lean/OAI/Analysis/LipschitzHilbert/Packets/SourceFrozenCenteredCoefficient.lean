import OAI.Analysis.LipschitzHilbert.Packets.SourceFrozenSpectrum
import OAI.Analysis.LipschitzHilbert.Trees.SourceCenteredMaskedVariation

namespace OAI

/-! Freezing a selector commutes with the actual physical centered
coefficient. This is an identity of totalized integrals, so no extra
integrability or boundary-level hypothesis is needed. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

theorem frozenProfile_physicalCoefficient (s : ℝ) (d : Fin N → ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalCoefficient s d v g j u k =
      conj (c j u k)*P.physicalCoefficient s d v g j u k := by
  have h := P.frozenProfile_mainCoefficient c hc d
    (fun z => v (sourceReferenceToPhysical s z))
    (fun z => g (sourceReferenceToPhysical s z)) j u k
  rw [(P.frozenProfile c hc).family_mainCoefficient_physical,
    P.family_mainCoefficient_physical] at h
  exact h

theorem frozenProfile_physicalCenteredWave (s t : ℝ) (d : Fin N → ℝ)
    (v : ℝ×ℝ → ℝ) (q : Σ j, ι j) (k : κ) (z : ℝ×ℝ) :
    (P.frozenProfile c hc).physicalCenteredWave s t d v q k z =
      c q.1 q.2 k*P.physicalCenteredWave s t d v q k z := by
  unfold physicalCenteredWave
  rw [P.frozenProfile_physicalPacket]
  by_cases h : |v z-t| ≤ d q.1 <;> simp [h,smul_apply,smul_eq_mul]

/-- The frozen selector contributes its conjugate to the analyzing
coefficient, including when it is zero and on cutoff boundaries. -/
theorem frozenProfile_physicalCenteredCoefficient (s t : ℝ) (d : Fin N → ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalCenteredCoefficient s t d v g j u k =
      conj (c j u k)*P.physicalCenteredCoefficient s t d v g j u k := by
  simp only [physicalCenteredCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change (↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj ((P.frozenProfile c hc).physicalCenteredWave s t d v ⟨j,u⟩ k z)
        ∂volume.prod volume) =
    conj (c j u k)*((↑(P.length j*P.width):ℂ)⁻¹*
      (∫ z, g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z)
        ∂volume.prod volume))
  have heq : (fun z => g z k*conj
      ((P.frozenProfile c hc).physicalCenteredWave s t d v ⟨j,u⟩ k z)) =
      fun z => conj (c j u k)*(g z k*conj (P.physicalCenteredWave s t d v ⟨j,u⟩ k z)) := by
    funext z
    rw [P.frozenProfile_physicalCenteredWave,map_mul]
    ring
  rw [heq,integral_const_mul]
  ring

/-- The centered masked band is the original alternate synthesis with
the genuine centered coefficient of the frozen analyzing packet. -/
theorem physicalCenteredMaskedBand_eq_frozen
    (alt : ∀ j, ι j → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)
    (d : Fin N → ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j, ι j → SlopeBox) (L A t y : ℝ) (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand c alt hAlt d v g T L A t y j x =
      WithLp.toLp 2 (fun k => ∑ u : ι j,
        (P.frozenProfile c hc).physicalCenteredCoefficient t t d v g j u k*
          ((T j u).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j u k (x,y+t*x)) := by
  ext k
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp,
    P.frozenProfile_physicalCenteredCoefficient]

end LipschitzHilbert.SourceLatticePacket

end

end OAI
