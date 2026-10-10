import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixSKGuerra
import OAI.Probability.SKBarriers.Scalar.VectorMultiplier

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

theorem matrixConstrainedPressure_quadratic_gap {N d r k : ℕ} (hN : 0<N)
    (hr : 0<r) (β : ℝ) (D A : Fin d → Fin d → ℝ)
    (hD : Nonempty (MatrixStates N d D))
    (B : Fin (k+1) → Fin r → Fin d → ℝ)
    (w : Fin (k+1) → ℝ) (hw : ∀ b, 0 ≤ w b) (hs : ∑ b, w b=1)
    (hO : ∀ s : Config d, |matrixSiteWeight A (fun a u => spin (a u)) s|≤1) :
    let V := matrixSiteVector β B (fun (a : Config d) u => spin (a u))
    let O := matrixSiteWeight A (fun (a : Config d) u => spin (a u))
    let f := siteValueTerminal (fun _ : Config d => 0)
    let g := vectorHierarchyAverage ((k+1)*r) (siteBlockMass r k w) V f
      (affineMoment (fun _ : Config d => 0) (fun s => ContinuousLinearMap.proj s) O) 0
    matrixConstrainedPressure N d β D ≤
      vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V f 0+
        (β^2/4)*(matrixSquare d D-2*matrixInner d (factorPath d r k B (Fin.last k)) D+
          ∑ j, w j*matrixSquare d (factorPath d r k B j))-
        (g-matrixInner d A D)^2/2 := by
  dsimp only
  let V := matrixSiteVector β B (fun (a : Config d) u => spin (a u))
  let O := matrixSiteWeight A (fun (a : Config d) u => spin (a u))
  let f := siteValueTerminal (fun _ : Config d => 0)
  let g := vectorHierarchyAverage ((k+1)*r) (siteBlockMass r k w) V f
    (affineMoment (fun _ : Config d => 0) (fun s => ContinuousLinearMap.proj s) O) 0
  let L := matrixInner d A D-g
  have hm (i : Fin ((k+1)*r)) : siteBlockMass r k w i∈Icc (0:ℝ) 1 := by
    refine ⟨Finset.sum_nonneg (fun b _ => ?_),?_⟩
    · split_ifs; exact hw b; rfl
    · calc
        siteBlockMass r k w i ≤ ∑ b, w b := Finset.sum_le_sum (fun b _ => by
          change (if _ then w b else 0) ≤ w b
          split_ifs; rfl; exact hw b)
        _ = 1 := hs
  have HB := matrixConstrainedPressure_le hN hr β D (fun u t => L*A u t) hD B w hw hs
  have he : matrixSiteWeight (fun u t => L*A u t) (fun (a : Config d) u => spin (a u))=
      fun s => 0+L*O s := by
    funext s
    simp only [O,matrixSiteWeight,zero_add,Finset.mul_sum,mul_assoc]
  have hi : matrixInner d (fun u t => L*A u t) D=L*matrixInner d A D := by
    simp only [matrixInner,Finset.mul_sum,mul_assoc]
  rw [he,hi] at HB
  have HM := vectorHierarchy_bounded_multiplier ((k+1)*r) (siteBlockMass r k w) hm
    V (fun _ : Config d => 0) O hO L
  change _ ≤ vectorHierarchy ((k+1)*r) (siteBlockMass r k w) V f 0+L*g+L^2/2 at HM
  change matrixConstrainedPressure N d β D ≤ _
  dsimp only [L] at HB HM
  dsimp only [V,f,g] at HB HM ⊢
  nlinarith

end SK.Analytic

end
end

end OAI
