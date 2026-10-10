import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.QuantumSectorNearMinimizer
import OAI.Analysis.CoulombIonization.FormDomain.LipschitzResidualBase

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace

namespace CoulombAtom

lemma continuous_form_re_le {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (G : V) :
    (⟪G,B G⟫_ℂ).re ≤ ‖B‖*‖G‖^2 := by
  calc
    _ ≤ ‖⟪G,B G⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖G‖*‖B G‖ := norm_inner_le_norm _ _
    _ ≤ ‖G‖*(‖B‖*‖G‖) := mul_le_mul_of_nonneg_left (B.le_opNorm G) (norm_nonneg _)
    _ = _ := by ring

lemma positive_form_residual_bound {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (F G : V) {η C K : ℝ} (hη : 0 ≤ η)
    (hF : (⟪F,B F⟫_ℂ).re ≤ η) (hG : ‖G‖^2 ≤ C*K) :
    (⟪G,B F⟫_ℂ).re^2 ≤ η*(‖B‖*C*K) := by
  have hGn : 0 ≤ (⟪G,B G⟫_ℂ).re := hB.re_inner_nonneg_right G
  calc
    _ ≤ (⟪F,B F⟫_ℂ).re*(⟪G,B G⟫_ℂ).re := positive_map_cauchy_re B hB F G
    _ ≤ η*(⟪G,B G⟫_ℂ).re := mul_le_mul_of_nonneg_right hF hGn
    _ ≤ η*(‖B‖*(C*K)) := mul_le_mul_of_nonneg_left
      ((continuous_form_re_le B G).trans (mul_le_mul_of_nonneg_left hG (norm_nonneg _))) hη
    _ = _ := by ring

lemma approximate_positive_form {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (B : V →L[ℂ] V) (hB : B.IsPositive)
    (p : V → V) (hpB : ∃ C : ℝ, 0 ≤ C ∧ ∀ F, ‖p F‖^2 ≤ C*‖F‖^2)
    (Q : V → Prop) {K : ℝ} (hK : 0 ≤ K)
    (hne : ∀ η : ℝ, 0 < η → ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪F,B F⟫_ℂ).re ≤ η)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ F, Q F ∧ ‖F‖^2 ≤ K ∧ (⟪p F,B F⟫_ℂ).re ≤ δ := by
  obtain ⟨C,hC,hp⟩ := hpB
  let A : ℝ := ‖B‖*C*K
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let η : ℝ := δ^2/(A+1)
  have hη : 0 < η := div_pos (sq_pos_of_pos hδ) (by linarith)
  have hηA : η*(A+1)=δ^2 := div_mul_cancel₀ _ (by linarith : A+1 ≠ 0)
  obtain ⟨F,hQ,hFK,hq⟩ := hne η hη
  refine ⟨F,hQ,hFK,?_⟩
  have hG : ‖p F‖^2 ≤ C*K := (hp F).trans (mul_le_mul_of_nonneg_left hFK hC)
  have hr := positive_form_residual_bound B hB F (p F) hη.le hq hG
  change (⟪p F,B F⟫_ℂ).re^2 ≤ η*A at hr
  nlinarith

attribute [local irreducible] graphComponent graphFormVector FermionLipschitzMultiplier.apply
  coulombFormOperator fermionGraph weakGraph fermionGraphValue formEnergy energy
  sectorExcessOperator

lemma quantum_sector_excess_near_minimizer {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2=1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪F,sectorExcessOperator Z N F⟫_ℂ).re ≤ η := by
  have hm : 0 < min 1 η := lt_min zero_lt_one hη
  have hex := quantum_sector_near_minimizer Z N hm
  rcases hex with ⟨F,hn,hF⟩
  have hb : formEnergy Z (graphFormVector F) ≤ energy Z N+1 :=
    hF.le.trans (add_le_add le_rfl (min_le_left _ _))
  have hk := near_minimizer_graph_bound hZ F hn hb
  refine ⟨F,hn,hk,?_⟩
  have he := sectorExcessOperator_diagonal Z F
  have hp : formEnergy Z (graphFormVector F) ≤ energy Z N+η :=
    hF.le.trans (add_le_add le_rfl (min_le_right _ _))
  have hev : energy Z N * ‖fermionGraphValue N F‖^2 = energy Z N :=
    (congrArg (fun t : ℝ => energy Z N*t) hn).trans (mul_one _)
  exact he.le.trans ((sub_le_sub_left hev.ge _).trans (sub_le_iff_le_add.mpr (by linarith only [hp])))

theorem quantum_approximate_lipschitz_multiplier {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ)
    (p : FermionLipschitzMultiplier N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N, ‖fermionGraphValue N F‖^2=1 ∧
      ‖F‖^2 ≤ 4*(|energy Z N|+(N:ℝ)*Z^2+2) ∧
      (⟪p.apply F,sectorExcessOperator Z N F⟫_ℂ).re ≤ δ := by
  exact approximate_positive_form (sectorExcessOperator Z N)
    (sectorExcessOperator_positive hZ N) p.apply (FermionLipschitzMultiplier.graph_bound p)
    (fun F => ‖fermionGraphValue N F‖^2=1) (by positivity)
    (fun _ hη => quantum_sector_excess_near_minimizer hZ N hη) hδ

end CoulombAtom

end

end OAI
