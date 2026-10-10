import OAI.MeasureTheory.Falconer.Recursion.ProfileLowerBound
import OAI.MeasureTheory.Falconer.Recursion.ProfileDecomposition

namespace OAI

/-! Select structured scale intervals for the actual regularized planar
branching profile from its finite prefix-count bounds. -/
namespace Falconer.Regularization

theorem planar_profile_scale_selection {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (N : ℕ), 0 < N → ∀ L : Finset (CellPath 2),
      L ⊆ cubePaths 2 N → ∀ (F : CellPath 2 → List ℕ) (B : ℕ), 0 < B →
      ∀ (p : CellPath 2) (ε s t : ℝ), 0 ≤ ε → s < t →
      (∀ i ≤ N/B+1,
        (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
          (2 : ℝ)^(ε*(N : ℝ)-t*(blockDepth N B i : ℝ))) →
      ∃ R : List (ℝ × ℝ),
        StructuredProfilePieces (fun x => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x))
          τ (2*η) s 1 R ∧
        1-η^2-η-ε/(t-s) ≤ (R.map Prod.snd).sum := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_profile_slope_decomposition hη hη1
  refine ⟨τ,hτ,?_⟩
  intro N hN L hL F B hB p ε s t hε hst hcounts
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlo : ∀ x ∈ Set.Icc (0 : ℝ) 1, t*x-ε*1 ≤
      regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x) := by
    intro x hx
    have hh := regularizedProfile_lower_from_ratios hN hL F hB p hcounts hx
    simpa only [mul_div_cancel_right₀ ε hNR,mul_one] using hh
  have hz : (fun x : ℝ => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x)) 0 = 0 := by
    simp [regularizedProfile_zero]
  have hd := ht (fun x => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x))
    (planarProfile_lipschitz hN hL F B (N/B+1) p) 1 ε s t (by norm_num) hε hst hz hlo
  simpa only [mul_one,one_mul] using hd

end Falconer.Regularization

end OAI
