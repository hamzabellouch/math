import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.InterpolationUniform
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialAlgebra
import OAI.Probability.CriticalPercolation.Clusters.ClusterTail
import OAI.Probability.CriticalPercolation.Criticality.InfiniteNearbyPair
import OAI.Probability.CriticalPercolation.Criticality.MinimalInterpolation
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes
import OAI.Probability.CriticalPercolation.GraphGeometry.AdjacentLog
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteAdjacent
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialRadius

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma eventually_no_superpolynomial_band
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hsub : G.SubexponentialGrowth)
    (hsuper : G.SuperpolynomialGrowth) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℕ in atTop, ∀ (p : unitInterval) (z : V), ε≤p → ε≤1-(p:ℝ) →
      (Real.log s)⁻¹^2 ≤ (G.law p).real (G.clusterBand z s) →
      (∀ v, θ/2≤(G.law p).real (G.clusterTail v s)) → False := by
  obtain ⟨A,hA,hAbound⟩ := G.subexponential_adjacent_bound hconnected hlocal hquasi hsub
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  let c := θ^2/8
  have hc : 0<c := by dsimp [c]; positivity
  have hcθ : c≤θ/4 := by dsimp [c]; nlinarith
  let C := max 1 (interpolationConstant (c/2) ε)
  have hC1 : 1≤C := le_max_left _ _
  have hC : 0<C := by linarith
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M,hM⟩ := exists_nat_gt (16*C/Real.log 2+1)
  have hM1 : 1≤M := by
    have hn : 0≤16*C/Real.log 2 := by positivity
    have hh : (1:ℝ)<M := by linarith
    exact_mod_cast hh.le
  have hMp : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  have hMs : 16*C≤(M:ℝ)*Real.log 2 := by
    have hh : 16*C/Real.log 2≤(M:ℝ) := by linarith
    exact (div_le_iff₀ hlog2).mp hh
  have hslope : C*(4/(M:ℝ)/Real.log 2)≤1/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [show C*(4/(M:ℝ)/Real.log 2)*4=16*C/((M:ℝ)*Real.log 2) by ring]
    exact (div_le_one (mul_pos hMp hlog2)).mpr hMs
  obtain ⟨R,hR,hRadius⟩ := G.superpolynomial_radius_log hsuper M hM1
  let B := Real.log (1/c)+R/Real.log 2+2+Real.log (2*A/ε)/C
  have hslow := CriticalPercolation.eventually_log_dominates C B hC.le
  have hscale : ∀ᶠ s : ℕ in atTop, 4*((D:ℝ)+1)≤θ*s := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    filter_upwards [hh.eventually (eventually_ge_atTop (4*((D:ℝ)+1)/θ))] with s hs
    have := (div_le_iff₀ hθ).mp hs
    nlinarith
  filter_upwards [hslow,hscale,eventually_ge_atTop 2] with s hslow hscale hs
  intro p z hεp hεq hband htail
  have hp : (p:ℝ)∈Set.Ioo 0 1 := ⟨hε.trans_le hεp,by linarith⟩
  obtain ⟨r,hr,hrV,hrlog⟩ := hRadius s (by omega)
  let BF := G.vertexBall_finite hlocal z r
  let Bv := BF.toFinset
  have hBn : Bv.Nonempty := ⟨z,BF.mem_toFinset.mpr (G.mem_vertexBall_self z r)⟩
  have hcost : (s^2+D*s^3:ℕ)≤θ/4*(Bv.card:ℝ) := by
    calc
      _ ≤ θ/4*(s:ℝ)^4 := CriticalPercolation.deletion_cost_le_quarter θ hθ D s (by omega) hscale
      _ ≤ θ/4*(Bv.card:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := hrV z
        rw [Set.ncard_eq_toFinset_card _ BF] at hh
        exact_mod_cast hh
  obtain ⟨y,hy,hyprob⟩ := G.exists_nearby_large_pair hconnected hlocal p Bv hBn z s D hD θ
    (fun v _ => htail v) hcost
  let f := (G.law p).real (G.clusterBand z s)
  have hf : 0≤f := measureReal_nonneg
  have hf1 : f≤1 := measureReal_le_one
  obtain ⟨haf,halog⟩ := CriticalPercolation.band_log_bound hc s hs hband
  have hex : ∃ u v, v∈G.vertexBall u r ∧ c*f≤(G.law p).real (G.twoClusterEvent u v s) := by
    refine ⟨y,z,G.vertexBall_comm.mp (BF.mem_toFinset.mp hy),?_⟩
    exact (mul_le_mul_of_nonneg_right hcθ hf).trans hyprob
  obtain ⟨u,v,huv,hprob,hupper⟩ := G.maximal_interpolation_pair p hp s r haf hc
    (by positivity : 0≤θ/2) hε hεp hεq
    (by nlinarith : c*f≤c) (by dsimp [c]; nlinarith : 2*c≤(θ/2)^2) htail hex
  obtain ⟨e,he⟩ := G.twoClusterEvent_of_adj huv
  rw [he s] at hprob hupper
  have hlower := G.adjacent_log_lower A ε hA hε p hεp s (by omega) e (hAbound p hp e) hprob
  have hclog := CriticalPercolation.clog_two_le_log r hr
  have hlogsr : Real.log r/Real.log 2≤(4/(M:ℝ)*Real.log s+R)/Real.log 2 :=
    div_le_div_of_nonneg_right hrlog hlog2.le
  have hlogs : 0≤Real.log s := Real.log_nonneg (by exact_mod_cast (show 1 ≤ s by omega))
  have hterm : C*((4/(M:ℝ)*Real.log s+R)/Real.log 2) ≤
      Real.log s/4+C*(R/Real.log 2) := by
    have hh := mul_le_mul_of_nonneg_right hslope hlogs
    convert add_le_add hh (le_refl (C*(R/Real.log 2))) using 1 <;> first | rfl | ring
  have hupper' : -Real.log ((G.law p).real
      (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) ≤
      C*(Real.log (1/c)+2*Real.log (Real.log s)+(Nat.clog 2 r:ℝ)+1) := by
    exact hupper.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at *; linarith) hC.le)
  have hg := mul_le_mul_of_nonneg_left (hclog.trans (add_le_add hlogsr (le_refl 1))) hC.le
  have hB : C*(2*Real.log (Real.log s)+B) =
      C*(2*Real.log (Real.log s)+Real.log (1/c)+R/Real.log 2+2)+Real.log (2*A/ε) := by
    dsimp [B]
    field_simp
    ring
  rw [hB] at hslow
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
