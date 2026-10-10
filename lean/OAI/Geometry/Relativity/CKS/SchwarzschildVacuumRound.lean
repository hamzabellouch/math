import OAI.Geometry.Relativity.CKS.SchwarzschildProfile
import OAI.Geometry.Relativity.CKS.LocalConstraints

namespace OAI

noncomputable section
open Set Filter CKSLorentz CKSCalculus CKSRound CKSRealizedRound CKSAngularGeometry
open scoped ContDiff Topology
namespace CKSSchwarzschild

lemma radial_round_vacuum {m : ℝ} {v : ℝ → ℝ} {x : PhysicalPoint}
    (hv : ContDiffAt ℝ ∞ v (x 0)) (hr : x 0 ≠ 0)
    (hs : Real.sin (x 1) ≠ 0) (hp : 0 < CKSRealizedRound.radicand (fun _ => m) v x) :
    let g := metricJet (CKSRealizedRound.lapse (fun _ => m) v) x
    let k := tensorJet (CKSRealizedRound.lapse (fun _ => m) v) v
      (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
    g.energy k = 0 ∧ g.momentum k = 0 := by
  dsimp only
  have hu := contDiffAt_lapse (contDiffAt_const (c := m)) hv hr hp
  have hu0 := (CKSRealizedRound.lapse_pos hp).ne'
  have hvd : DifferentiableAt ℝ (deriv v) (x 0) :=
    (hv.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hL : DifferentiableAt ℝ (radial (deriv v)) x := hvd.comp x (coord 0).differentiableAt
  rw [constructed_metricJet (contDiffAt_const (c := m)) (hv.of_le (by change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hr hs hp,
    tensorJet_eq_round _ _ _ _ _ _ (hu.differentiableAt (by simp))
      (hv.differentiableAt (by simp)) hL (differentiableAt_const 0) hu0,
    lapseJet_eq_mass (contDiffAt_const (c := m)) (hv.of_le (by change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top)) hr hp]
  let f := massJet (fun _ : PhysicalPoint => m) x
  let k := roundTensor v (radial (deriv v)) (fun _ => 0) (fun _ => 0) x
  have hf : f.Fr = 0 ∧ f.Ft = 0 ∧ f.Fp = 0 ∧ f.Ftt = 0 ∧ f.Fpp = 0 := by
    simp [f,massJet,D_const,D_D_const]
  have hmass : (CKSRealizedRound.lapse (fun _ => m) v x)^2 =
      1+k.v^2-2*f.F/x 0 := CKSRealizedRound.lapse_sq hp
  let j := f.lapse (x 0) (CKSRealizedRound.lapse (fun _ => m) v x) k.v k.vp (deriv (deriv v) (x 0))
  change (j.roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1))).energy
    (k.jet j (x 0) (Real.sin (x 1)) (Real.cos (x 1))) = 0 ∧
    (j.roundMetric (x 0) (Real.sin (x 1)) (Real.cos (x 1))).momentum
    (k.jet j (x 0) (Real.sin (x 1)) (Real.cos (x 1))) = 0
  constructor
  · rw [MassJet.energy_mass_form f k (c := Real.cos (x 1)) (vpp := deriv (deriv v) (x 0)) hr hu0 hs hmass]
    simp [k,roundTensor,radial,f,massJet,MassJet.laplace,MassJet.gradientSq,D_const,D_D_const]
  · funext i
    fin_cases i
    all_goals dsimp only [Pi.zero_apply]
    · have h := RoundTensor.normal_momentum_round k
        j (c := Real.cos (x 1)) hr hs hu0
      have hz : k.L-k.vp = 0 := by simp [k,roundTensor,radial]
      rw [hz,mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hu0
    · apply (RoundTensor.theta_momentum_round k j (c := Real.cos (x 1)) hr hs hu0).trans
      simp [k,roundTensor,radial,j,MassJet.lapse,f,massJet,D_const,D_radial 1 hvd]
    · apply (RoundTensor.phi_momentum_round k j (c := Real.cos (x 1)) hr hs hu0).trans
      simp [k,roundTensor,radial,j,MassJet.lapse,f,massJet,D_const,D_radial 2 hvd]
end CKSSchwarzschild

end

end OAI
