import OAI.Geometry.NodalSets.Elliptic.RealZeroBallExpansion

namespace OAI

namespace Yau.Geometry
open Metric Filter Set
open scoped ContDiff Topology
noncomputable section

theorem real_weak_unique_continuation (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (U : Set Yau.Jets.Coord) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hEq : ∀ x ∈ U, realEllipticResidual gamma potential B W x = 0)
    (y : Yau.Jets.Coord) (hyU : y ∈ U) (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) :
    ∀ x ∈ U, W x = 0 := by
  let Z := (tsupport W)ᶜ
  have hopen : IsOpen Z := (isClosed_tsupport W).isOpen_compl
  have hnon : (U ∩ Z).Nonempty := ⟨y,hyU,notMem_tsupport_iff_eventuallyEq.mpr hy⟩
  have hclosed : closure Z ∩ U ⊆ Z := by
    intro x hx
    obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU x hx.2
    obtain ⟨z,hz,hxz⟩ := Metric.mem_closure_iff.mp hx.1 (R/16) (by positivity)
    have hsub : ball z (R/2) ⊆ U := by
      intro w hw
      apply hRU
      apply mem_ball.mpr
      have hh := dist_triangle w z x
      rw [dist_comm z x] at hh
      have hw' := mem_ball.mp hw
      linarith
    have hzero := real_zero_germ_expands gamma potential W B hg hgp hpot hB hsym hW hpos
      z (R/2) (by positivity) (fun w hw ↦ hEq w (hsub hw))
      (notMem_tsupport_iff_eventuallyEq.mp hz)
    have he : W =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [ball_mem_nhds x (by positivity : 0 < R/16)] with w hw
      apply hzero
      apply mem_ball.mpr
      have hh := dist_triangle w x z
      have hw' := mem_ball.mp hw
      linarith
    exact notMem_tsupport_iff_eventuallyEq.mpr he
  have hall := hconn.subset_of_closure_inter_subset hopen hnon hclosed
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (hall hx)

theorem real_global_unique_continuation (gamma potential W : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgp : ∀ x, 0 < gamma x)
    (hpot : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hsym : ∀ x i j, B x i j = B x j i)
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ x, (B x).PosDef)
    (hEq : ∀ x, realEllipticResidual gamma potential B W x = 0)
    (y : Yau.Jets.Coord) (hy : W =ᶠ[𝓝 y] (fun _ ↦ 0)) : W = 0 := by
  funext x
  exact real_weak_unique_continuation gamma potential W B hg hgp hpot hB hsym hW hpos
    univ isOpen_univ isPreconnected_univ (fun x _ ↦ hEq x) y (mem_univ _) hy x (mem_univ _)

end
end Yau.Geometry

end OAI
