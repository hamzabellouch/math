import OAI.MeasureTheory.Falconer.Geometry.ScalarRationalProjection

namespace OAI

/-! Small projections survive the precise coefficient density zoom.
 The budget is explicit and uses only a fixed number of scalar operations. -/
namespace Falconer
open scoped Pointwise

def scalarNormalizedBaseBudget (M : ℕ) (K : ℝ) : ℝ :=
  1+K+45*(2*K)^7+(2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3

def scalarNormalizedProjectionBudget (M : ℕ) (K : ℝ) : ℝ :=
  scalarCoefficientBudget (M+2) (scalarNormalizedBaseBudget M K) 5

 theorem scalar_normalized_projection_bound {δ K z R : ℝ} (hδ : 0 < δ) (hK : 1 ≤ K)
    (X E : Finset ℝ) (hX : X.Nonempty) (hz : z ∈ E)
    (hE : ∀ a ∈ E, |a| ≤ 1)
    (hcandidate : (z,R) ∈ scalarBallCandidates δ E) (hRδ : δ < R)
    (M : ℕ) (hM : |R⁻¹| ≤ M)
    (hdoubling : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (hproj : ∀ a ∈ E, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      K*(scalarCells δ X).card) :
    ∀ t ∈ scalarZoom (z-3*R) (6*R) (E.filter fun x => |x-z| ≤ R),
      ((scalarCells δ (X+X.image (fun x => t*x))).card:ℝ) ≤
        scalarNormalizedProjectionBudget M K*(scalarCells δ X).card := by
  have hK0 : 0 ≤ K := by linarith
  let S0 := E ∪ {1}
  have hS0 : ∀ a ∈ S0, |a| ≤ (1:ℝ) := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hE a ha
    · have ha1 : a = 1 := Finset.mem_singleton.mp ha
      simp [ha1]
  have hproj0 : ∀ a ∈ S0, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      K*(scalarCells δ X).card := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hproj a ha
    · have he : a = 1 := Finset.mem_singleton.mp ha
      subst a
      simpa using hdoubling
  have hRmem := scalar_density_radius_mem E hcandidate hRδ
  have hRproj := scalar_closure_projections hδ hK X S0 hX 1 (by simpa only [Nat.cast_one] using hS0) hdoubling hproj0 3 R hRmem
  have hinv0 : ((scalarCells δ (X+X.image (fun x => R⁻¹*x))).card:ℝ) ≤
      (2*(M:ℝ)+3)*((scalarCells δ (X+X.image (fun x => R*x))).card:ℝ) := by
    exact_mod_cast scalar_inverse_coefficient_cells hδ (hδ.trans hRδ).ne' X M hM
  have hinv := hinv0.trans (mul_le_mul_of_nonneg_left hRproj (by positivity))
  have hhalf0 : ((scalarCells δ (X+X.image (fun x => (1/2:ℝ)*x))).card:ℝ) ≤
      25*(2*K)^3*(scalarCells δ X).card := by
    convert scalar_reciprocal_integer_projection hδ X hX hdoubling 2 (by omega) using 1 <;> norm_num
  have hhalf : ((scalarCells δ (X+X.image (fun x => (1/2:ℝ)*x))).card:ℝ) ≤
      45*(2*K)^7*(scalarCells δ X).card := by
    have hp := pow_le_pow_right₀ (show 1 ≤ 2*K by linarith) (show 3 ≤ (7:ℕ) by omega)
    apply hhalf0.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    nlinarith [pow_nonneg (show 0 ≤ 2*K by positivity) 3]
  have hsix : ((scalarCells δ (X+X.image (fun x => (1/6:ℝ)*x))).card:ℝ) ≤
      45*(2*K)^7*(scalarCells δ X).card := by
    convert scalar_reciprocal_integer_projection hδ X hX hdoubling 6 (by omega) using 1 <;> norm_num
  let L := scalarNormalizedBaseBudget M K
  have hH : 0 ≤ scalarCoefficientBudget 1 K 3 :=
    (by norm_num : (0:ℝ) ≤ 1).trans (scalarCoefficientBudget_one_le 1 hK 3)
  have hrat0 : 0 ≤ 45*(2*K)^7 := by positivity
  have hinvnonneg : 0 ≤ (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 := by positivity
  have hL1 : 1 ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLK : K ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLrat : 45*(2*K)^7 ≤ L := by dsimp [L,scalarNormalizedBaseBudget]; linarith
  have hLinv : (2*(M:ℝ)+3)*scalarCoefficientBudget 1 K 3 ≤ L := by
    dsimp [L,scalarNormalizedBaseBudget]
    linarith
  let S := E ∪ {1,1/2,1/6,R⁻¹}
  have hS : ∀ a ∈ S, |a| ≤ (M+2:ℕ) := by
    intro a ha
    simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with ha | rfl | rfl | rfl | rfl
    · exact (hE a ha).trans (by push_cast; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))])
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · push_cast; norm_num; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]
    · exact hM.trans (by push_cast; linarith)
  have hprojS : ∀ a ∈ S, ((scalarCells δ (X+X.image (fun x => a*x))).card:ℝ) ≤
      L*(scalarCells δ X).card := by
    intro a ha
    simp only [S,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with ha | rfl | rfl | rfl | rfl
    · exact (hproj a ha).trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
    · have hh : ((scalarCells δ (X+X.image (fun x => (1:ℝ)*x))).card:ℝ) ≤
          K*(scalarCells δ X).card := by simpa using hdoubling
      exact hh.trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
    · exact hhalf.trans (mul_le_mul_of_nonneg_right hLrat (Nat.cast_nonneg _))
    · exact hsix.trans (mul_le_mul_of_nonneg_right hLrat (Nat.cast_nonneg _))
    · exact hinv.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right hLinv (Nat.cast_nonneg (scalarCells δ X).card))
  have hD := hdoubling.trans (mul_le_mul_of_nonneg_right hLK (Nat.cast_nonneg _))
  intro t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  have hamem : a ∈ S := Finset.mem_union_left _ (Finset.mem_filter.mp ha).1
  have hzmem : z ∈ S := Finset.mem_union_left _ hz
  have hexpr := scalar_normalized_expression_mem (R := R) hamem hzmem
    (by simp [S]) (by simp [S]) (by simp [S])
  exact scalar_closure_projections hδ hL1 X S hX (M+2) hS hD hprojS 5 _ hexpr

end Falconer

end OAI
