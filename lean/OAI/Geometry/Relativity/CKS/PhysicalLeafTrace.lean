import OAI.Geometry.Relativity.CKS.FoliationFrameRegularity
import OAI.Geometry.Relativity.CKS.PhysicalNormalFrame

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix CKSCalculus Filter
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise

def angularFrame (U : ℝ) (γ : Mat) (s : Point) : Mat :=
  fun a b => adaptedFrame U γ s a.succ b.succ

lemma angularFrame_gram {U : ℝ} {γ : Mat} {s : Point}
    (hU : U ≠ 0) (hγ : γ.PosDef) :
    (angularFrame U γ s).transpose * angularFrame U γ s = γ⁻¹ := by
  let e := angularFrame U γ s
  have horth : e*(γ*e.transpose)=1 := by
    ext a b
    change (∑ i, e a i*(∑ j, γ i j*e b j)) = if a=b then 1 else 0
    have ho := adaptedFrame_orthonormal hU hγ s a.succ b.succ
    rw [metricPair_tangential_slots _ _ _ (adaptedFrame_radial U γ s a)
      (adaptedFrame_radial U γ s b)] at ho
    have hmm : (∑ i : Fin 2, ∑ j : Fin 2,
        foliationMetric U γ s i.succ j.succ * adaptedFrame U γ s a.succ i.succ *
          adaptedFrame U γ s b.succ j.succ) =
        ∑ i, ∑ j, γ i j*e a i*e b j := rfl
    rw [hmm] at ho
    simp only [Fin.succ_inj] at ho
    rw [← ho]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.mul_assoc]
  exact mul_eq_one_comm.mp horth

lemma angular_trace_transform (k e : Mat) :
    (∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, k i j*e a i*e a j)=
      (e*k*e.transpose).trace := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma physical_chi_representation {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) (a b : Fin 2) :
    CKSFrame.chi (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) a b =
    ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
      angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) b j := by
  have ha := (foliation_actualAdaptedAt hU hγ hs h0.ne' hp).self_of_nhds
  rw [← CKSFrame.connection_normal,frame_connection_actual ha]
  exact leaf_frame_chi (hU.differentiableAt (by simp))
    (hγ.differentiableAt (by simp)) (hs.differentiableAt (by simp)) h0 hp a b

theorem physical_mean_curvature {U : PhysicalPoint → ℝ}
    {γ : PhysicalPoint → Mat} {s : PhysicalPoint → Point} {x : PhysicalPoint}
    (hU : ContDiffAt ℝ ∞ U x) (hγ : ContDiffAt ℝ ∞ γ x)
    (hs : ContDiffAt ℝ ∞ s x) (h0 : 0 < U x)
    (hp : ∀ᶠ y in 𝓝 x, (γ y).PosDef) :
    CKSFrame.mean (frameConnectionField
      (fun y => foliationMetric (U y) (γ y) (s y))
      (fun i y => adaptedFrame (U y) (γ y) (s y) i) x) =
      ((γ x)⁻¹*sourceChi U γ s x).trace := by
  let c := frameConnectionField (fun y => foliationMetric (U y) (γ y) (s y))
    (fun i y => adaptedFrame (U y) (γ y) (s y) i) x
  have ht : CKSFrame.mean c = ∑ a : Fin 2, CKSFrame.chi c a a := by
    simp [CKSFrame.mean,CKSFrame.chi,Fin.sum_univ_two]
  change CKSFrame.mean c = _
  rw [ht]
  calc
    _ = ∑ a : Fin 2, ∑ i : Fin 2, ∑ j : Fin 2, sourceChi U γ s x i j *
        angularFrame (U x) (γ x) (s x) a i * angularFrame (U x) (γ x) (s x) a j := by
      apply Finset.sum_congr rfl
      intro a _
      exact physical_chi_representation hU hγ hs h0 hp a a
    _ = _ := by
      rw [angular_trace_transform,Matrix.trace_mul_comm,
        ← Matrix.mul_assoc,angularFrame_gram h0.ne' hp.self_of_nhds]

end
end CKSAngularGeometry

end

end OAI
