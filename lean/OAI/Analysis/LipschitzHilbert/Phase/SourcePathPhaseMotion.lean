import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionMotion
import OAI.Analysis.LipschitzHilbert.Phase.ScalarPhase

namespace OAI

/-! Removal of the actual path phase in §9, `pred:path-errors`.
The scalar phase costs only the off-path mass, including when it is zero. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

/-- Sum the individual numerator errors before removing the moving path
phase. The two errors may have different sizes. -/
theorem finite_rotated_off_path_motion {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (l : ι → ℝ) (W W' : ι → E)
    {lam lam' : ℂ} {q η K u : ℝ}
    (hlam : lam ≠ 0) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hweight : ‖lam'-lam‖ ≤ q*‖lam‖)
    (hsum : ∑ i ∈ s, l i ≤ u)
    (hW : ∀ i ∈ s, ‖W i‖ ≤ K*l i)
    (hmove : ∀ i ∈ s, ‖W' i-W i‖ ≤ η*K*l i) :
    ‖(scalarPhase lam')⁻¹ • (∑ i ∈ s, W' i) -
      (scalarPhase lam)⁻¹ • (∑ i ∈ s, W i)‖ ≤ (η+2*q)*K*u := by
  have hlam' := (scalarPhase_relative_motion hlam hq1 hweight).1
  have hphase := scalarPhase_inverse_motion hlam hq1 hweight
  have hsumW : ‖∑ i ∈ s, W i‖ ≤ K*u := by
    calc
      _ ≤ ∑ i ∈ s, ‖W i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, K*l i := Finset.sum_le_sum hW
      _ = K*(∑ i ∈ s, l i) := (Finset.mul_sum ..).symm
      _ ≤ K*u := mul_le_mul_of_nonneg_left hsum hK
  have hsumMove : ‖(∑ i ∈ s, W' i)-(∑ i ∈ s, W i)‖ ≤ η*K*u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ s, ‖W' i-W i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, η*K*l i := Finset.sum_le_sum hmove
      _ = (η*K)*(∑ i ∈ s, l i) := (Finset.mul_sum ..).symm
      _ ≤ η*K*u := mul_le_mul_of_nonneg_left hsum (mul_nonneg hη hK)
  have heq : (scalarPhase lam')⁻¹ • (∑ i ∈ s, W' i) -
      (scalarPhase lam)⁻¹ • (∑ i ∈ s, W i) =
      (scalarPhase lam')⁻¹ • ((∑ i ∈ s, W' i)-(∑ i ∈ s, W i)) +
      ((scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹) • (∑ i ∈ s, W i) := by
    simp only [smul_sub,sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(scalarPhase lam')⁻¹ • ((∑ i ∈ s, W' i)-(∑ i ∈ s, W i))‖ +
        ‖((scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹) • (∑ i ∈ s, W i)‖ :=
      norm_add_le _ _
    _ = ‖(∑ i ∈ s, W' i)-(∑ i ∈ s, W i)‖ +
        ‖(scalarPhase lam')⁻¹-(scalarPhase lam)⁻¹‖*‖∑ i ∈ s, W i‖ := by
      rw [norm_smul,norm_inv,norm_scalarPhase hlam',inv_one,one_mul,norm_smul]
    _ ≤ η*K*u+(2*q)*(K*u) := add_le_add hsumMove
      (mul_le_mul hphase hsumW (norm_nonneg _) (by positivity))
    _ = _ := by ring

/-- Quotient form, matching the actual transition-product motion theorem. -/
theorem finite_rotated_off_path_motion_of_quotient {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset ι) (l : ι → ℝ) (W W' : ι → E)
    {lam lam' : ℂ} {q η K u : ℝ}
    (hlam : lam ≠ 0) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hweight : ‖lam'/lam-1‖ ≤ q)
    (hsum : ∑ i ∈ s, l i ≤ u)
    (hW : ∀ i ∈ s, ‖W i‖ ≤ K*l i)
    (hmove : ∀ i ∈ s, ‖W' i-W i‖ ≤ η*K*l i) :
    ‖(scalarPhase lam')⁻¹ • (∑ i ∈ s, W' i) -
      (scalarPhase lam)⁻¹ • (∑ i ∈ s, W i)‖ ≤ (η+2*q)*K*u :=
  finite_rotated_off_path_motion s l W W' hlam hq0 hq1 hη hK
    (complex_relative_motion_to_sub hlam hweight) hsum hW hmove

namespace AngularGrid

/-- The actual source transition product supplies the phase estimate needed
by the finite off-path sum lemma. No displaced good-point hypothesis enters. -/
theorem source_block_scalar_phase_motion {ι : Type*}
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox)
    (w B K D : ℝ) (hw : 0 < w) (hB : 1 ≤ B) (hK : 0 < K) (hD : 0 ≤ D)
    (hwidth : ∀ t ∈ tops, B^2*w ≤ (T t).width)
    {Kb : ℕ} (hKb : 0 < Kb) (gap : ℕ → ℝ) (phase : ℕ → ℂ)
    (h lower upper : ℕ) (hbase : h ≤ lower)
    (hgap : ∀ j ∈ Finset.Ico lower upper, 0 ≤ gap j ∧ gap j ≤ g.width h)
    (top : ι) (htop : top ∈ tops)
    (he : g.eligible (g.rootWidth/B^2) (w/(T top).length) upper)
    (sR : ℝ) (hs : g.index h (T top).slope = g.index h sR)
    (child : ℝ) (hchild : 0 < child) (hblock : g.width h ≤ B*child)
    (b : ℝ) (hb : |b| ≤ w/(child*Real.sqrt (g.branching:ℝ))) (z : ℝ × ℝ)
    (Z : ℝ) (hZ : 0 ≤ Z) (hphase : ∀ j ∈ Finset.Ico lower upper, ‖phase j‖ ≤ Z) :
    let weight := fun t x => (T t).weight K D x
    let lam := fun x => g.packetPathProduct (g.sourceTransition tops (fun t => (T t).slope)
      (fun t => w/(T t).length) (g.rootWidth/B^2) weight Kb gap phase x)
      lower upper (T top).slope
    let e := (upper-lower:ℕ)*Z*(2*((5*D/K)/Real.sqrt (g.branching:ℝ)))
    let q := Real.exp e*e
    q < 1 →
    ‖scalarPhase (lam (SlopeBox.lineShift sR b z))-scalarPhase (lam z)‖ ≤ 2*q ∧
      ‖(scalarPhase (lam (SlopeBox.lineShift sR b z)))⁻¹-
        (scalarPhase (lam z))⁻¹‖ ≤ 2*q := by
  dsimp only
  intro hq
  have hrel := g.source_block_transition_relative_motion tops T w B K D hw hB hK hD hwidth
    hKb gap phase h lower upper hbase hgap top htop he sR hs child hchild hblock b hb z Z hZ hphase
  have hlam := g.source_path_product_ne_zero tops (fun t => (T t).slope)
    (fun t => w/(T t).length) (g.rootWidth/B^2) (fun t x => (T t).weight K D x)
    Kb gap phase z lower upper (T top).slope
  have hmove := complex_relative_motion_to_sub hlam hrel
  exact ⟨(scalarPhase_relative_motion hlam hq hmove).2,
    scalarPhase_inverse_motion hlam hq hmove⟩

end AngularGrid
end LipschitzHilbert

end

end OAI
