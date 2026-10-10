import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedOneBodyMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbardTensor
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockGraphEntries

namespace OAI

/-! From the actual spatial one-body error to the full spinful Hubbard
coefficient error. The off-site counterterm is kept exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb
open HubbardGlobal

section Entries
variable {Edge : Type*} [Fintype Edge]
variable {m : ℕ} {rho H S freq scale δ ε η : ℝ}
variable (hrho : 0 ≤ rho) (hH : 0 ≤ H) (hS : 0 ≤ S) (hf : 0 < freq)
variable (u : Fin (m+1) → PlanarPosition) (hδ : 0 ≤ δ)
variable (hcoeff : ∀ i, 0 ≤ localizedCounterterm freq u i/scale ∧
  localizedCounterterm freq u i/scale ≤ δ)
variable (F : Position → ℝ)
variable (hI : ∀ i j, Integrable (fun x => F x*correctedLocalizedMode freq u i x*
  correctedLocalizedMode freq u j x))
variable (left right : Edge → Fin (m+1)) (t : Edge → ℝ)
variable (hε : 0 ≤ ε) (hη : 0 ≤ η)
variable (hmatrix : ∀ i j, |scale*correctedNuclearOneBodyMatrix rho H S freq scale u F i j-
  localizedOneBodyTarget scale freq u i j| ≤ ε)
variable (hgraph : ∀ i j, ‖(scale*planarHoppingMatrix u i j:ℂ)-
  graphHoppingMatrix m left right (fun e => (t e:ℂ)) i j‖ ≤ η)
include hrho hH hS hf hδ hcoeff hI hε hη hmatrix hgraph

theorem localizedSpin_hubbard_oneBody_error (a b : Fin ((2*m+1)+1)) :
    ‖(scale:ℂ)*(flatResidualMatrix (localizedSpinMode freq u)
        (localizedSpinResidual rho H S freq scale u) a b+
        flatNuclearMatrix (localizedSpinMode freq u) F a b)-
      hubbardOneBodyMatrix m (localizedOffsiteCoulomb freq u) left right t a b‖ ≤ ε+η := by
  rw [localizedSpin_oneBody_matrix hrho hH hS hf scale u hδ hcoeff F hI]
  let p := (siteModes m).symm
  change ‖(scale:ℂ)*(if (p a).2=(p b).2 then _ else 0)-
    (if (p a).2=(p b).2 then _ else 0)‖ ≤ _
  by_cases hs : (p a).2=(p b).2
  · simp only [hs,ite_true]
    have he := hmatrix (p a).1 (p b).1
    have hg := hgraph (p a).1 (p b).1
    have hc : localizedOffsiteSum freq u (p a).1 =
        ∑ j, localizedOffsiteCoulomb freq u (p a).1 j := by
      rfl
    have ht : ((localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℝ):ℂ)-
        (graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1-
          if (p a).1=(p b).1 then ((∑ j, localizedOffsiteCoulomb freq u (p a).1 j:ℝ):ℂ) else 0) =
        (scale*planarHoppingMatrix u (p a).1 (p b).1:ℂ)-
          graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1 := by
      unfold localizedOneBodyTarget
      rw [hc]
      split_ifs <;> push_cast <;> ring
    calc
      _ ≤ ‖(scale:ℂ)*(correctedNuclearOneBodyMatrix rho H S freq scale u F (p a).1 (p b).1:ℂ)-
          (localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℂ)‖+
          ‖(localizedOneBodyTarget scale freq u (p a).1 (p b).1:ℂ)-
          (graphHoppingMatrix m left right (fun e => (t e:ℂ)) (p a).1 (p b).1-
          if (p a).1=(p b).1 then ((∑ j, localizedOffsiteCoulomb freq u (p a).1 j:ℝ):ℂ) else 0)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε+η := by
        rw [ht]
        apply add_le_add _ hg
        simpa only [← Complex.ofReal_mul,← Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs] using he
  · simp only [hs,ite_false,mul_zero,sub_self,norm_zero]
    exact add_nonneg hε hη
end Entries

end ContinuumCoulomb

end

end OAI
