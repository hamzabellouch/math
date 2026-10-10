import OAI.MeasureTheory.Falconer.Estimates.ScalarForwardRegularization
import OAI.MeasureTheory.Falconer.Measures.ScalarSubsetMass
import OAI.MeasureTheory.Falconer.Estimates.ScalarLossAbsorption

namespace OAI

/-! Quantitative projection growth before the initial regularization.
 Both nonporous and porous alternatives are compared to the original set. -/
namespace Falconer
open scoped Pointwise

def scalarBinaryCopies (B C : ℕ) : ℕ :=
  (2*scalarBinaryCopyBound B C+1)*scalarBinaryBranchCount B C

namespace Regularization

 theorem scalar_initial_projection_growth {B C P M : ℕ} {K K0 κ : ℝ}
    (hC : 7 ≤ C) (hCB : 2*C ≤ B) (hP : 18 ≤ P) (hM : 0 < M)
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hK : 0 < K) (hK0 : 0 < K0)
    (hCbudget : Real.log (64*K)+κ*Real.log (5/4:ℝ)+4000*(P:ℝ)*Real.log 2 ≤
      κ*(C:ℝ)*Real.log 2)
    (hBbudget : 800*(P:ℝ) ≤ κ*(B:ℝ)) (hCmargin : 8*(C:ℝ) ≤ κ*(B:ℝ))
    (hloss : Real.log (2050*(B+1)^2:ℝ) ≤ κ*(P:ℝ)*Real.log 2/200)
    (hscale : 40*Real.log K0 ≤ (κ*(B:ℝ)-2*(P:ℝ))*κ*(M:ℝ)*Real.log 2)
    (hsmall : Real.log ((scalarCells ((1/2:ℝ)^(B*M))
      (scalarBinaryCopies B C • L.image scalarPathCenter)).card:ℝ) ≤
        (1-3*κ/4)*(B:ℝ)*(M:ℝ)*Real.log 2)
    (hpoint : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K0*t^κ*((L.image scalarPathCenter).card:ℝ))
    (A : Finset ℝ) (hA : A.Nonempty) (hAb : ∀ t ∈ A, 1/3 ≤ t ∧ t ≤ 1)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass A u t ≤ K*t^κ*(A.card:ℝ)) :
    ∃ t ∈ A, Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*(L.card:ℝ) <
      ((scalarCells ((1/2:ℝ)^(B*M)) ((L.image scalarPathCenter)+
        (L.image scalarPathCenter).image (fun x => t*x))).card:ℝ) := by
  have hBpos : 0 < B := by omega
  obtain ⟨Q,k,n,hQne,hQL,hsize,hlevels⟩ := scalar_forward_regularization hBpos L hL hne
  have hsizeR : (L.card:ℝ) ≤ (2050*(B+1)^2:ℝ)^(M+1)*(Q.card:ℝ) := by
    exact_mod_cast hsize
  have hpointQ := scalar_pruned_ball_bound hL hQL hK0.le hsizeR hpoint
  have hscaleQ := scalar_regularization_scale_budget hM hκ hK0 hBbudget hloss hscale
  have hJ : 0 < scalarBinaryBranchCount B C := by
    unfold scalarBinaryBranchCount
    positivity
  obtain ⟨t,ht,hgain⟩ := scalar_projection_growth_of_sumset (by omega) (by omega) hP hM
    hBpos Q (hQL.trans hL) hQne k n hlevels (le_refl (18*(2:ℝ)^C)) hJ
    (scalar_binary_parameter_contract hC hCB)
    (scalar_binary_parameter_copy_bound B C).le (le_refl (scalarBinaryCopies B C))
    (L.image scalarPathCenter) (Finset.image_subset_image (f := scalarPathCenter) hQL) hκ hκ1
    (scalar_binary_parameter_log hCB hCmargin) hsmall hK (by positivity)
    hCbudget hBbudget hscaleQ hpointQ A hA hAb hball
  refine ⟨t,ht,?_⟩
  calc
    _ ≤ Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*
        ((2050*(B+1)^2:ℝ)^(M+1)*(Q.card:ℝ)) :=
      mul_le_mul_of_nonneg_left hsizeR (Real.exp_pos _).le
    _ = (Real.exp ((κ/25)*(P:ℝ)*(M:ℝ)*Real.log 2)*
        (2050*(B+1)^2:ℝ)^(M+1))*(Q.card:ℝ) := by ring
    _ ≤ Real.exp ((κ/20)*(P:ℝ)*(M:ℝ)*Real.log 2)*(Q.card:ℝ) :=
      mul_le_mul_of_nonneg_right (scalar_regularization_gain hM hκ.le hloss) (Nat.cast_nonneg _)
    _ < _ := hgain
    _ ≤ _ := by
      exact_mod_cast scalar_projection_cover_mono
        (Finset.image_subset_image (f := scalarPathCenter) hQL) ((1/2:ℝ)^(B*M)) t

end Regularization
end Falconer

end OAI
