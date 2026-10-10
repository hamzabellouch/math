import OAI.Analysis.LienardCycles.CharacteristicScaling

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus

lemma mixed_z_radius {f fr : (ℝ × ℝ) × ℝ → ℝ} {z k r b : ℝ}
    (hf : ∀ q, 0 < q.2 → ContDiffAt ℝ ω f q) (hr : 0 < r)
    (hfr : ∀ a, HasDerivAt (fun s => f ((a,k),s)) (fr ((a,k),r)) r)
    (hb : HasDerivAt (fun a => fr ((a,k),r)) b z) :
    HasDerivAt (fun s => direction ((1,0),0) f ((z,k),s)) b r := by
  have he : (fun a => direction ((0,0),1) f ((a,k),r)) = (fun a => fr ((a,k),r)) := by
    ext a
    exact (slice_r ((hf ((a,k),r) hr).differentiableAt (by simp))).unique (hfr a)
  have hcross := (slice_d ((direction_contDiffAt (hf ((z,k),r) hr) ((0,0),1)).differentiableAt
    (by simp))).unique (he ▸ hb)
  have hh := slice_r ((direction_contDiffAt (hf ((z,k),r) hr) ((1,0),0)).differentiableAt (by simp))
  rw [←direction_comm (hf ((z,k),r) hr) ((1,0),0) ((0,0),1),hcross] at hh
  exact hh

lemma mixed_k_radius {f fr : (ℝ × ℝ) × ℝ → ℝ} {z k r b : ℝ}
    (hf : ∀ q, 0 < q.2 → ContDiffAt ℝ ω f q) (hr : 0 < r)
    (hfr : ∀ a, HasDerivAt (fun s => f ((z,a),s)) (fr ((z,a),r)) r)
    (hb : HasDerivAt (fun a => fr ((z,a),r)) b k) :
    HasDerivAt (fun s => direction ((0,1),0) f ((z,k),s)) b r := by
  have he : (fun a => direction ((0,0),1) f ((z,a),r)) = (fun a => fr ((z,a),r)) := by
    ext a
    exact (slice_r ((hf ((z,a),r) hr).differentiableAt (by simp))).unique (hfr a)
  have hcross := (slice_k ((direction_contDiffAt (hf ((z,k),r) hr) ((0,0),1)).differentiableAt
    (by simp))).unique (he ▸ hb)
  have hh := slice_r ((direction_contDiffAt (hf ((z,k),r) hr) ((0,1),0)).differentiableAt (by simp))
  rw [←direction_comm (hf ((z,k),r) hr) ((0,1),0) ((0,0),1),hcross] at hh
  exact hh

end QuinticLienard.QuadraticCoordinates

end OAI
