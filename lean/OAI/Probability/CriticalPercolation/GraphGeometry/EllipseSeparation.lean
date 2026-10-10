import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseGrid
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseAngles
import OAI.Probability.CriticalPercolation.GraphGeometry.EllipseLinear

namespace OAI

section
section
noncomputable section
open Set Function

namespace CriticalPercolation.EuclideanEllipse

theorem separated_neighboring_ellipses (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta)
    (chooseCenter : (ℂ → ℂ) → Circle)
    (hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (normalize U W (Circle.exp phi)) : ℂ)).re|<1/8) :
    ∃ p∈parameterDisk, ∃ q∈parameterDisk,
      (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
      (1 : ℝ)/4≤|EllipseLinear.det
        (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
        (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
  obtain ⟨N,K,hN,hK,hangle,hcomp⟩ := exists_grid_comparison W U zeta hW hWU hzeta
  have hNr : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hKr : (K : ℝ)≠0 := (Nat.cast_pos.mpr hK).ne'
  let phi : ℕ → ℝ := fun k => (k : ℝ)*Real.pi/K
  let centers : ℕ → ℕ → Circle := fun i k => chooseCenter (diskNormalize W U (gridPoint N K i k))
  let F : ℕ → ℕ → Real.Angle := fun i k => lineAngle (centers i k)
  have hp0 : phi 0=0 := by simp [phi]
  have hpK : phi K=Real.pi := by dsimp [phi]; field_simp
  have hn : ∀ k, diskNormalize W U (gridPoint N K N k)=normalize U W (Circle.exp (phi k)) := by
    intro k
    simp only [diskNormalize,gridPoint,div_self hNr,diskRadius,mul_one,add_sub_cancel,phi]
  have hc : ∀ k≤K, F 0 k=F 0 0 := by
    intro k _hk
    dsimp [F,centers,gridPoint]
    simp only [Nat.cast_zero,zero_div,zero_mul]
    rw [diskNormalize_center W U ((k : ℝ)*Real.pi/K)]
  have hs : ∀ i≤N, F i K=F i 0 := by
    intro i _hi
    have he : gridPoint N K i K=((i : ℝ)/N,Real.pi) := by
      simp only [gridPoint]
      congr 1
    have he0 : gridPoint N K i 0=((i : ℝ)/N,0) := by simp [gridPoint]
    dsimp [F,centers]
    rw [he,he0,diskNormalize_seam]
  let err : ℕ → ℝ := fun k => boundaryError (phi k) (centers N k)
  let b : ℕ → ℝ := fun k => 2*phi k+Real.pi+err k
  have herr : ∀ k≤K, |err k|<Real.pi/8 := by
    intro k _hk
    apply boundary_error_lt
    simpa only [centers,hn] using hboundary (phi k)
  have hlift : ∀ k≤K, F N k=(b k : Real.Angle) := by
    intro k _hk
    exact boundary_lift (phi k) (centers N k)
  have hmesh : ∀ k<K, |phi (k+1)-phi k|<Real.pi/32 := by
    intro k _hk
    have he := gridPoint_angular_step N K k hK
    exact he.trans_lt hangle
  have hstep := DiskWinding.boundary_mesh_lifts phi err K hmesh herr
  have hturn : b K-b 0=2*Real.pi := by
    have hcseam : centers N K=centers N 0 := by
      dsimp [centers]
      rw [hn,hn,hpK,hp0,circle_exp_pi]
      congr 1
      funext z
      exact normalize_neg U W (Circle.exp 0) z
    have heseam : err K=err 0 := by
      dsimp [err]
      rw [hpK,hp0,hcseam,boundary_error_seam]
    dsimp [b]
    rw [hpK,hp0,heseam]
    ring
  have hex := DiskWinding.exists_large_edge F N K b hc hs hlift hstep hturn
  have edge : ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K →
      Real.pi/4≤|DiskWinding.increment (F i k) (F (i+a) (k+b))| →
      ∃ p∈parameterDisk, ∃ q∈parameterDisk,
        (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
        (1 : ℝ)/4≤|EllipseLinear.det
          (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
          (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
    intro i hi k hk a ha b hb hia hkb hsep
    refine ⟨gridPoint N K i k,gridPoint_mem hN hK hi hk,
      gridPoint N K (i+a) (k+b),gridPoint_mem hN hK hia hkb,hcomp i hi k hk a ha b hb hia hkb,?_⟩
    have hd := EllipseLinear.det_lower_of_separation (centers i k : ℂ).arg (centers (i+a) (k+b) : ℂ).arg hsep
    simpa only [circle_arg_re,circle_arg_im] using hd
  rcases hex with ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩
  · exact edge i hi k (by omega) 0 (by omega) 1 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k hk 1 (by omega) 0 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k (by omega) 1 (by omega) 1 (by omega) (by omega) (by omega) hik

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
