import Mathlib
import OAI.Analysis.Conductivity.Fourier.PureModeWall
import OAI.Analysis.Conductivity.Walls.CriticalWallRegion

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_pure_mode_wall_region
    {v : P×Box3 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (hz : ∀ q z,wallDerivative (fun y => v (q,y)) (z,0)=0)
    {σ lam k : ℝ} (hσ : σ≠0) (hlam : lam≠0) (hk : k≠0)
    (hbase : ∀ y,v (p,y)=pureWallMode σ lam k y)
    {W : Set Coord3} (hW : IsOpen W) {x : Coord3} (hx : x∈W) (hxz : x 2=0) :
    ∃ B : VanishingCorrectionRegion (fun z => wallCoordinatePair (fun y => v (z.1,y)) z.2) p W,
      x∈B.region := by
  have hstrip : IsOpen {y : Coord3 | |k*y 2|<Real.pi} :=
    isOpen_lt (continuous_const.mul (continuous_apply 2)).abs continuous_const
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp (hW.inter hstrip) x
    ⟨hx,by simp only [mem_ofPred_eq,hxz,mul_zero,abs_zero]; exact Real.pi_pos⟩
  let U := Metric.ball x δ
  have hproj : ∀ y∈U,boxCoordinates.symm ((boxCoordinates y).1,0)∈U := by
    intro y hy
    rw [Metric.mem_ball,dist_pi_lt_iff hδ] at hy ⊢
    intro i
    fin_cases i
    · exact hy 0
    · exact hy 1
    · change dist (0:ℝ) (x 2)<δ
      simpa only [hxz,dist_self] using hδ
  have hrect : ∀ z∈Icc (x 0-δ/2) (x 0+δ/2)×ˢIcc (x 1-δ/2) (x 1+δ/2),
      boxCoordinates.symm (z,0)∈U := by
    intro z hz
    rw [Metric.mem_ball,dist_pi_lt_iff hδ]
    intro i
    fin_cases i
    · change dist z.1 (x 0)<δ
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.1.1,hz.1.2]
    · change dist z.2 (x 1)<δ
      rw [Real.dist_eq,abs_lt]
      constructor <;> linarith [hz.2.1,hz.2.2]
    · change dist (0:ℝ) (x 2)<δ
      simpa only [hxz,dist_self] using hδ
  have hcp : Convex ℝ {y : Coord3 | 0<y 2} :=
    convex_halfSpace_gt ⟨fun _ _ => rfl,fun _ _ => rfl⟩ 0
  have hcn : Convex ℝ {y : Coord3 | y 2<0} :=
    convex_halfSpace_lt ⟨fun _ _ => rfl,fun _ _ => rfl⟩ 0
  have hnb : ∀ y∈U,wallQuotient (wallDerivative (fun z => v (p,z))) (boxCoordinates y)≠0 := by
    intro y hy
    rw [show (fun z => v (p,z))=pureWallMode σ lam k from funext hbase]
    exact pureWallMode_quotient_nonzero hσ hk _ (hball hy).2
  let B := criticalWallRegion hv p hz Metric.isOpen_ball Metric.isBounded_ball
    (fun y hy => (hball hy).1) (Metric.nonempty_ball.mpr hδ)
    (((convex_ball x δ).inter hcp).isPreconnected)
    (((convex_ball x δ).inter hcn).isPreconnected) hproj hnb
    (show x 0-δ/2<x 0+δ/2 by linarith)
    (show x 1-δ/2<x 1+δ/2 by linarith) hσ hlam hrect
    (fun z => (hbase (z,0)).trans (pureWallMode_wall_value σ lam k z))
  exact ⟨B,Metric.mem_ball_self hδ⟩

end ScalarConductivity

end
end

end OAI
