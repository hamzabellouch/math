import Mathlib.Topology.UniformSpace.HeineCantor
import OAI.Geometry.NodalSets.Charts.MetricNormalizationBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

def weightedHessianValue (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ) (p t : Coord) : ℝ :=
  H p p/(g p p+4)+H t t

lemma weightedHessianValue_normalized (g H : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (p t : Coord) (hp : 0 < g p p) :
    weightedHessianValue g H p t =
      (g p p/(g p p+4))*H (metricNormalize g p) (metricNormalize g p)+H t t := by
  have hs := Real.sq_sqrt hp.le
  have hs0 := (Real.sqrt_pos.mpr hp).ne'
  have hd : g p p+4 ≠ 0 := by positivity
  unfold weightedHessianValue metricNormalize
  simp only [map_smul,smul_apply,smul_eq_mul]
  field_simp
  rw [hs]
  ring

theorem weightedHessianValue_uniform_continuity
    (g H : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {D : Set Coord} (hD : IsCompact D) (hg : ContinuousOn g D) (hH : ContinuousOn H D)
    (hp : ∀ x ∈ D, ∀ v, 0 ≤ g x v v) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ D, ∀ y ∈ D, ∀ p q t u : Coord,
      ‖p‖ ≤ K → ‖q‖ ≤ K → ‖t‖ ≤ K → ‖u‖ ≤ K →
      ‖x-y‖ < δ → ‖p-q‖ < δ → ‖t-u‖ < δ →
      |weightedHessianValue (g x) (H x) p t-weightedHessianValue (g y) (H y) q u| < ε := by
  let E : Set (Coord × (Coord × Coord)) := D ×ˢ (Metric.closedBall 0 K ×ˢ Metric.closedBall 0 K)
  have hE : IsCompact E := hD.prod ((isCompact_closedBall 0 K).prod (isCompact_closedBall 0 K))
  let F : Coord × (Coord × Coord) → ℝ := fun z ↦ weightedHessianValue (g z.1) (H z.1) z.2.1 z.2.2
  have hgc : ContinuousOn (fun z : Coord × (Coord × Coord) ↦ g z.1) E :=
    hg.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)
  have hHc : ContinuousOn (fun z : Coord × (Coord × Coord) ↦ H z.1) E :=
    hH.comp continuous_fst.continuousOn (fun z hz ↦ hz.1)
  have hpc : ContinuousOn (fun z : Coord × (Coord × Coord) ↦ z.2.1) E :=
    (continuous_fst.comp continuous_snd).continuousOn
  have htc : ContinuousOn (fun z : Coord × (Coord × Coord) ↦ z.2.2) E :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hF : ContinuousOn F E := by
    apply ContinuousOn.add
    · exact ((hHc.clm_apply hpc).clm_apply hpc).div
        (((hgc.clm_apply hpc).clm_apply hpc).add continuousOn_const)
        (fun z hz ↦ by have h := hp z.1 hz.1 z.2.1; positivity)
    · exact (hHc.clm_apply htc).clm_apply htc
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuousOn_iff.mp (hE.uniformContinuousOn_of_continuous hF) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy p q t u hpb hqb htb hub hxy hpq htu
  have hxE : (x,(p,t)) ∈ E := ⟨hx,by simpa using hpb,by simpa using htb⟩
  have hyE : (y,(q,u)) ∈ E := ⟨hy,by simpa using hqb,by simpa using hub⟩
  have hdxy : dist (x,(p,t)) (y,(q,u)) < δ := by
    change max (dist x y) (max (dist p q) (dist t u)) < δ
    simpa only [max_lt_iff,dist_eq_norm] using And.intro hxy (And.intro hpq htu)
  have hr := hd (x,(p,t)) hxE (y,(q,u)) hyE hdxy
  simpa only [Real.dist_eq,F] using hr

end
end Yau.Geometry

end OAI
