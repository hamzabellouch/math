import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodDriverEstimate
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodDriverVariation

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem reflected_driver_continuity (B : Body E) (x₀ c : E) (r R : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hball : Metric.closedBall c r⊆B.carrier)
    (hR : ∀x∈B.carrier,‖x-c‖ ≤ R) (w : ℝ → E) (hw : ContinuousOn w (Icc 0 1)) :
    ∃u : ℝ → E, ContinuousOn u (Icc 0 1) ∧
      (∀t∈Icc (0:ℝ) 1,u t∈B.carrier) ∧
      TendstoUniformlyOn (fun n => mesh B x₀ w (n+1)) u atTop (Icc 0 1) ∧
      ∀ε : ℝ,0 < ε → ∃δ : ℝ,0 < δ ∧ ∀v : ℝ → E,
        ContinuousOn v (Icc 0 1) → (∀t∈Icc (0:ℝ) 1,‖v t-w t‖ < δ) →
        ∃z : ℝ → E,ContinuousOn z (Icc 0 1) ∧
          (∀t∈Icc (0:ℝ) 1,z t∈B.carrier) ∧
          TendstoUniformlyOn (fun n => mesh B x₀ v (n+1)) z atTop (Icc 0 1) ∧
          ∀t∈Icc (0:ℝ) 1,
            ‖z t-u t‖ + ‖(z t-x₀-(v t-v 0))-(u t-x₀-(w t-w 0))‖ < ε := by
  obtain ⟨u,k,μ,hu,hk,hu₀,hk₀,hBu,hconv,hrest⟩ :=
    reflected_equation B x₀ c r R hx₀ hr hball hR w hw
  obtain ⟨M,hM,hvar⟩ := mesh_nearby_variation B x₀ c r R hx₀ hr hball hR w hw
  let C := (M:ℝ)*(R^2/r)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg M) (div_nonneg (sq_nonneg R) hr.le)
  refine ⟨u,hu,fun t ht => (hBu t ht).1,hconv,fun ε hε => ?_⟩
  have hg : ContinuousAt (fun a : ℝ => 6*a+2*Real.sqrt (8*a*C)) 0 := by fun_prop
  obtain ⟨d,hd,hgd⟩ := Metric.continuousAt_iff.mp hg ε hε
  let δ := min (r/8) (d/2)
  have hδ : 0 < δ := lt_min (by positivity) (half_pos hd)
  have hδr : δ ≤ r/8 := min_le_left _ _
  have hδd : δ < d := (min_le_right _ _).trans_lt (half_lt_self hd)
  have hsmall : 6*δ+2*Real.sqrt (8*δ*C) < ε := by
    have h := hgd (x:=δ) (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδd)
    simpa only [mul_zero,zero_mul,Real.sqrt_zero,add_zero,Real.dist_eq,sub_zero,
      abs_of_nonneg (by positivity : 0 ≤ 6*δ+2*Real.sqrt (8*δ*C))] using h
  refine ⟨δ,hδ,fun v hv hc => ?_⟩
  obtain ⟨z,l,ν,hz,hl,hz₀,hl₀,hBz,hzconv,hrestz⟩ :=
    reflected_equation B x₀ c r R hx₀ hr hball hR v hv
  refine ⟨z,hz,fun t ht => (hBz t ht).1,hzconv,fun t ht => ?_⟩
  have hb : ‖z t-u t‖ ≤ 2*δ+Real.sqrt (8*δ*C) := by
    apply le_of_tendsto (((hzconv.tendsto_at ht).sub (hconv.tendsto_at ht)).norm)
    filter_upwards [eventually_ge_atTop M] with n hn
    apply mesh_driver_estimate B x₀ C δ hx₀ hδ.le w v (fun s hs => (hc s hs).le)
      (n+1) (Nat.succ_pos _) _ _ t ht
    · exact hvar w (fun s hs => by simpa using (by positivity : (0:ℝ) ≤ r/8))
        (n+1) (hn.trans (Nat.le_succ _))
    · exact hvar v (fun s hs => (hc s hs).le.trans hδr)
        (n+1) (hn.trans (Nat.le_succ _))
  have he : (z t-x₀-(v t-v 0))-(u t-x₀-(w t-w 0))=
      (z t-u t)-((v t-w t)-(v 0-w 0)) := by abel
  have hnorm : ‖(z t-x₀-(v t-v 0))-(u t-x₀-(w t-w 0))‖ ≤ ‖z t-u t‖+2*δ := by
    rw [he]
    have ha := hc t ht
    have hb₀ := hc 0 ⟨le_rfl,zero_le_one⟩
    have hc₀ := norm_sub_le (v t-w t) (v 0-w 0)
    have hd₀ := norm_sub_le (z t-u t) ((v t-w t)-(v 0-w 0))
    linarith
  linarith

end ConvexSkorokhod

end OAI
