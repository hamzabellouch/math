import Mathlib
import OAI.Analysis.Conductivity.Geometry.ParametricCorrectionRegionPiola

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_transported_vanishing_region
    {u v : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (p : P)
    (Y : OpenPartialHomeomorph (P×Coord3) (P×Coord3))
    (hY : ∀ q x,(Y (q,x)).1=q)
    (hsm : ContDiff ℝ (↑(⊤:ℕ∞)) Y)
    (hinv : ContDiffOn ℝ (↑(⊤:ℕ∞)) Y.symm Y.target)
    {U : Set Coord3} (hYU : Y.source⊆univ×ˢU)
    {x : Coord3} (hx : (p,x)∈Y.source)
    (hpot : ∀ z∈Y.source,v (z.1,(Y z).2)=u z)
    (hlocal : ∀ A : Set Coord3,IsOpen A → (Y (p,x)).2∈A →
      ∃ B : VanishingCorrectionRegion v p A,(Y (p,x)).2∈B.region) :
    ∃ B : VanishingCorrectionRegion u p U,x∈B.region := by
  let z := (Y (p,x)).2
  have hpz : (p,z)∈Y.target := by
    have he : (p,z)=Y (p,x) := Prod.ext (hY p x).symm rfl
    rw [he]
    exact Y.map_source hx
  obtain ⟨V₀,A₀,hV₀,hA₀,hp₀,hz₀,hprod₀⟩ := exists_open_product_inside Y.open_target hpz
  obtain ⟨δ,hδ,hδball⟩ := Metric.isOpen_iff.mp hV₀ p hp₀
  obtain ⟨η,hη,hηball⟩ := Metric.isOpen_iff.mp hA₀ z hz₀
  let Kp := Metric.closedBall p (δ/2)
  let Ka := Metric.closedBall z (η/2)
  let A := Metric.ball z (η/2)
  have hpK : Kp⊆V₀ := fun q hq => hδball
    (lt_of_le_of_lt hq (by linarith : δ/2<δ))
  have haK : Ka⊆A₀ := fun y hy => hηball
    (lt_of_le_of_lt hy (by linarith : η/2<η))
  have hjoint : Kp×ˢKa⊆Y.target := fun q hq => hprod₀ ⟨hpK hq.1,haK hq.2⟩
  obtain ⟨C,hC,hbound⟩ := parametric_chart_compact_bounds Y hY hsm hinv
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)) hjoint
  obtain ⟨B,hzB⟩ := hlocal A Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
  obtain ⟨τ,hτ,hτball⟩ := Metric.isOpen_iff.mp B.region_open z hzB
  let K := Metric.closedBall z (τ/2)
  have hKB : K⊆B.region := fun y hy => hτball
    (lt_of_le_of_lt hy (by linarith : τ/2<τ))
  let O : Set (P×Coord3) := Y.source∩{q | (Y q).2∈Metric.ball z (τ/2)}
  have hO : IsOpen O := Y.open_source.inter
    (Metric.isOpen_ball.preimage (continuous_snd.comp hsm.continuous))
  have hxO : (p,x)∈O := ⟨hx,Metric.mem_ball_self (by positivity)⟩
  obtain ⟨V₁,W₁,hV₁,hW₁,hp₁,hx₁,hprod₁⟩ := exists_open_product_inside hO hxO
  let V := Metric.ball p (δ/2)∩V₁
  let W := W₁∩Metric.ball x 1
  have hVp : p∈V := ⟨Metric.mem_ball_self (by positivity),hp₁⟩
  have hWx : x∈W := ⟨hx₁,Metric.mem_ball_self zero_lt_one⟩
  have hWU : W⊆U := fun y hy => (hYU (hprod₁ (show (p,y)∈V₁×ˢW₁ from ⟨hp₁,hy.1⟩)).1).2
  have hVA : V×ˢA⊆Y.target := fun q hq => hjoint
    ⟨Metric.ball_subset_closedBall hq.1.1,Metric.ball_subset_closedBall hq.2⟩
  have hW : ∀ q∈V,W⊆(fiberSlice Y hY q).symm '' K := by
    intro q hq y hy
    have hh := hprod₁ (show (q,y)∈V₁×ˢW₁ from ⟨hq.2,hy.1⟩)
    exact ⟨(Y (q,y)).2,Metric.ball_subset_closedBall hh.2,(fiberSlice Y hY q).left_inv hh.1⟩
  have himage : ∀ q∈V,(fiberSlice Y hY q).symm '' A⊆U := by
    rintro q hq _ ⟨y,hy,rfl⟩
    exact (hYU ((fiberSlice Y hY q).map_target (hVA ⟨hq,hy⟩))).2
  have hpot' : ∀ q∈V,∀ y∈A,u (q,(fiberSlice Y hY q).symm y)=v (q,y) := by
    intro q hq y hy
    have hyt := hVA (show (q,y)∈V×ˢA from ⟨hq,hy⟩)
    have hys := (fiberSlice Y hY q).map_target hyt
    have hh := hpot (q,(fiberSlice Y hY q).symm y) hys
    rw [show (Y (q,(fiberSlice Y hY q).symm y)).2=y from
      (fiberSlice Y hY q).right_inv hyt] at hh
    exact hh.symm
  let D := VanishingCorrectionRegion.piola hu hv p Y hY hsm hinv
    (Metric.isOpen_ball.inter hV₁) hVp (Metric.isBounded_ball.subset inter_subset_left)
    Metric.isOpen_ball B (isCompact_closedBall _ _) hKB hVA hW
    (hW₁.inter Metric.isOpen_ball) ⟨x,hWx⟩
    (Metric.isBounded_ball.subset inter_subset_right) hWU himage hpot' hC
    (fun q hq y hy => (hbound (q,y)
      ⟨Metric.ball_subset_closedBall hq.1,Metric.ball_subset_closedBall hy⟩).2.2.2)
  exact ⟨D,hWx⟩

end ScalarConductivity

end
end

end OAI
