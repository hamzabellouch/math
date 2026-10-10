import Mathlib
import OAI.Analysis.SymmetricDomains.BishopPathInterior

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
namespace Release061
open scoped Topology
open Set Filter Metric

lemma norm_affine_one (x : Affine 1) : ‖x‖ = ‖x 0‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [Subsingleton.elim i (0 : Fin 1)] using le_refl ‖x 0‖
  · exact norm_le_pi_norm x 0

def affineClosedDiscCoordinate (x : closedBall (0 : Affine 1) 1) : Wiener.ClosedDisc :=
  ⟨x.val 0,by
    have hx := mem_closedBall_zero_iff.mp x.property
    rw [norm_affine_one] at hx
    exact mem_closedBall_zero_iff.mpr hx⟩

lemma affineClosedDiscCoordinate_continuous : Continuous affineClosedDiscCoordinate := by
  apply Continuous.subtype_mk
  exact (continuous_apply 0).comp continuous_subtype_val

theorem bounded_cocompact_chart_disc_continuity {n k : ℕ} {Γ : Type*}
    (V U : Set (Affine n)) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    {ε : ℝ} (Φ : Affine k → Affine n)
    (hΦ : AnalyticOnNhd ℂ Φ (ball 0 ε)) (hΦV : MapsTo Φ (ball 0 ε) V) :
    Wiener.DiscContinuityWithin k (Φ ⁻¹' U) ε := by
  intro A hA hAh hsmall hbd hstart
  let B : Icc (0 : ℝ) 1 → closedBall (0 : Affine 1) 1 → V :=
    fun s x => ⟨Φ (A s (affineClosedDiscCoordinate x)),hΦV (by simpa only [mem_ball,dist_zero_right] using hsmall s (affineClosedDiscCoordinate x))⟩
  have hAc : Continuous (fun p : Icc (0 : ℝ) 1 × closedBall (0 : Affine 1) 1 =>
      A p.1 (affineClosedDiscCoordinate p.2)) :=
    hA.comp (continuous_fst.prodMk (affineClosedDiscCoordinate_continuous.comp continuous_snd))
  have hB : Continuous (Function.uncurry B) := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (hΦ _ (by simpa only [mem_ball,dist_zero_right] using hsmall p.1 (affineClosedDiscCoordinate p.2))).continuousAt.comp hAc.continuousAt
  have hBh (s : Icc (0 : ℝ) 1) : HolomorphicOnSubset (ball (0 : Affine 1) 1)
      (fun x => (B s ⟨x.val,ball_subset_closedBall x.property⟩).val) := by
    obtain ⟨g,hg,he⟩ := hAh s
    have hcoord : AnalyticOnNhd ℂ (fun x : Affine 1 => x 0) (ball 0 1) :=
      fun _ _ => (ContinuousLinearMap.proj 0 : Affine 1 →L[ℂ] ℂ).analyticAt _
    have hgP : AnalyticOnNhd ℂ (fun x : Affine 1 => g (x 0)) (ball 0 1) :=
      hg.comp hcoord (fun x hx => by
        simpa only [mem_ball,dist_zero_right,norm_affine_one] using hx)
    have hcomp : AnalyticOnNhd ℂ (fun x : Affine 1 => Φ (g (x 0))) (ball 0 1) := by
      apply hΦ.comp hgP
      intro x hx
      have hh := hsmall s (affineClosedDiscCoordinate ⟨x,ball_subset_closedBall hx⟩)
      rw [he] at hh
      simpa only [mem_ball,dist_zero_right,affineClosedDiscCoordinate] using hh
    intro p
    refine ⟨ball 0 1,isOpen_ball,p.property,fun x => Φ (g (x 0)),hcomp,?_⟩
    intro q _
    change Φ (g (q.val 0)) = Φ (A s (affineClosedDiscCoordinate ⟨q.val,ball_subset_closedBall q.property⟩))
    rw [he]; rfl
  have hall := bounded_cocompact_disc_continuity V U hUV hU hbounded hhol K hK hrep B hB hBh
    (fun s x hx => hbd s (affineClosedDiscCoordinate x) (by
      change ‖x.val 0‖ = 1; rwa [norm_affine_one] at hx))
    (fun x => hstart (affineClosedDiscCoordinate x))
  intro s z
  let x : closedBall (0 : Affine 1) 1 := ⟨fun _ => z.val,by
    rw [mem_closedBall,dist_zero_right,norm_affine_one]
    exact mem_closedBall_zero_iff.mp z.property⟩
  exact hall s x

end Release061

end

end OAI
