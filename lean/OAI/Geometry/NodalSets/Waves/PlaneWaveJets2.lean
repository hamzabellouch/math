import OAI.Geometry.NodalSets.Elliptic.ProductErrorJets
import OAI.Geometry.NodalSets.Elliptic.RescaledJetDecay
import OAI.Geometry.NodalSets.Waves.PlaneWaveJets

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_main_coefficient_jets (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (R : ℝ) (hR : 0 ≤ R) (d0 : ℕ) (e : ℝ) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ t x s, 1 ≤ s →
      sourceEuclideanNorm (x-y t.1) ≤ (n:ℝ)^(-5/12:ℝ) →
      ∀ (sigma : ℝ) (v : Coord), ‖v‖ ≤ R → ∀ k, k ≤ d0 →
      ‖iteratedFDeriv ℝ k (fun z ↦ normalizedRescaling (b.wave n t) S n s sigma x z -
        (b.wave n t x/(sigma:ℂ))*planeWave (g (y t.1) (d.q t.1 t.2)) s z) v‖ ≤
        e*‖b.wave n t x/(sigma:ℂ)‖ := by
  have hq : Continuous (fun t : T × Fin 3 ↦ d.q t.1 t.2) :=
    continuous_prod_of_discrete_right.mpr (fun j ↦ (continuous_apply j).comp d.continuous_q)
  have hK : Continuous (fun t : T × Fin 3 ↦ g (y t.1) (d.q t.1 t.2)) :=
    (hg.continuous.comp (hy.comp continuous_fst)).clm_apply hq
  obtain ⟨B,hB,hplane⟩ := uniform_planeWave_jets _ hK d0
  let cost : ℝ := 2^d0*B*(2^d0+2)
  have hcost : 0 < cost := by dsimp [cost]; positivity
  let q := min 1 (e/cost)
  have hqpos : 0 < q := lt_min zero_lt_one (div_pos he hcost)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hqcost : cost*q ≤ e := by
    have := (le_div_iff₀ hcost).mp (min_le_right 1 (e/cost))
    nlinarith
  obtain ⟨delta,hdelta,hexp⟩ := small_exp_jet_threshold d0 q hqpos
  have hmin : 0 < min delta q := lt_min hdelta hqpos
  filter_upwards [b.uniform_rescaled_factor_jets hg hp hS hy hp0 (R+1) (by linarith) d0
    (min delta q) hmin,b.uniform_main_amplitude_ratio hg hp hy (R+1) 1 zero_lt_one]
    with n hfactors hgerms
  intro t x s hs hnear sigma v hv k hk
  let U := ball (0:Coord) (R+1)
  have hU : IsOpen U := isOpen_ball
  have hvU : v ∈ U := by simpa only [U,mem_ball,dist_zero_right] using (show ‖v‖ < R+1 by linarith)
  have hnorm (z : Coord) (hz : z ∈ U) : ‖z‖ ≤ R+1 := (by simpa only [U,mem_ball,dist_zero_right] using hz : ‖z‖ < R+1).le
  let L := frozenPhaseCovector (fderiv ℝ S x) (g (y t.1) (d.q t.1 t.2))
  let E := rescaledPhaseDefect (b.phase t) L n s x
  let A := rescaledAmplitudeRatio (b.amplitude n t) n s x
  let P := planeWave (g (y t.1) (d.q t.1 t.2)) s
  let alpha := b.wave n t x/(sigma:ℂ)
  have hEs : ContDiffOn ℝ ∞ E U := fun z hz ↦ (hfactors t x s hs hnear z (hnorm z hz)).1.contDiffWithinAt
  have hAs : ContDiffOn ℝ ∞ A U := fun z hz ↦ (hfactors t x s hs hnear z (hnorm z hz)).2.1.contDiffWithinAt
  have hPs : ContDiff ℝ ∞ P := planeWave_smooth _ _
  have hBs : ContDiffOn ℝ ∞ (fun z ↦ Complex.exp (E z)) U := Complex.contDiff_exp.comp_contDiffOn hEs
  have hEa (j : ℕ) (hj : j ≤ d0) : ‖iteratedFDeriv ℝ j E v‖ ≤ delta :=
    ((hfactors t x s hs hnear v (hv.trans (by linarith))).2.2 j hj).1.trans (min_le_left _ _)
  have hAa (j : ℕ) (hj : j ≤ d0) : ‖iteratedFDeriv ℝ j (fun z ↦ A z-1) v‖ ≤ q :=
    ((hfactors t x s hs hnear v (hv.trans (by linarith))).2.2 j hj).2.trans (min_le_right _ _)
  have hExp (j : ℕ) (hj : j ≤ d0) : ‖iteratedFDeriv ℝ j (fun z ↦ Complex.exp (E z)-1) v‖ ≤ q :=
    hexp U hU E hEs v hvU hEa j hj
  have hprod (j : ℕ) (hj : j ≤ d0) :
      ‖iteratedFDeriv ℝ j (fun z ↦ A z*Complex.exp (E z)-1) v‖ ≤ (2^d0+2)*q :=
    near_one_product_jet_bound hU A (fun z ↦ Complex.exp (E z)) hAs hBs hvU d0 hqpos.le hq1 hAa hExp j hj
  have hrel := local_mul_jet_bound hU P (fun z ↦ A z*Complex.exp (E z)-1)
    hPs.contDiffOn ((hAs.mul hBs).sub contDiffOn_const) hvU k hB.le
    (fun j hj ↦ hplane t s hs v j (hj.trans hk)) (fun j hj ↦ hprod j (hj.trans hk))
  have hsmall : ‖iteratedFDeriv ℝ k (fun z ↦ P z*(A z*Complex.exp (E z)-1)) v‖ ≤ e := by
    apply hrel.trans
    have hpow : (2:ℝ)^k ≤ 2^d0 := pow_le_pow_right₀ (by norm_num) hk
    calc
      _ ≤ 2^d0*B*((2^d0+2)*q) := by gcongr
      _ = cost*q := by dsimp [cost]; ring
      _ ≤ e := hqcost
  have heq : (fun z ↦ normalizedRescaling (b.wave n t) S n s sigma x z-alpha*P z) =ᶠ[𝓝 v]
      (fun z ↦ alpha • (P z*(A z*Complex.exp (E z)-1))) := by
    filter_upwards [hU.mem_nhds hvU] with z hz
    obtain ⟨hax,_,hbase,hshift⟩ := hgerms t x s hs hnear z (hnorm z hz)
    rw [normalizedWave_factorization _ _ _ S (g (y t.1) (d.q t.1 t.2)) n s sigma x z
      hax hbase.self_of_nhds hshift.self_of_nhds]
    dsimp [alpha,P,A,E,L,rescaledAmplitudeRatio]
    ring
  rw [(heq.iteratedFDeriv (𝕜 := ℝ) k).self_of_nhds,
    iteratedFDeriv_const_smul_apply' (((hPs.contDiffOn.mul ((hAs.mul hBs).sub contDiffOn_const)).contDiffAt
      (hU.mem_nhds hvU)).of_le (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))),norm_smul]
  exact (mul_le_mul_of_nonneg_left hsmall (norm_nonneg alpha)).trans_eq (mul_comm _ _)

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
