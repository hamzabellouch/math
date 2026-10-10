import OAI.Geometry.NodalSets.Charts.ChartDerivativeTransfer
import OAI.Geometry.NodalSets.Charts.ChartNormComparison
import OAI.Geometry.NodalSets.Charts.UniformInverseChartBounds
import OAI.Geometry.NodalSets.Coefficients.LocalCoordinateResidual
import OAI.Geometry.NodalSets.Elliptic.OperatorLocality
import OAI.Geometry.NodalSets.Waves.ConstructedCoordinateWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Filter Set Metric
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem uniform_chart_wave_transfer
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (w : Coord → ℝ) (hw : ContDiff ℝ ∞ w)
    (p : T → QuadParam Coord) (hpc : Continuous p)
    (F : T → OpenPartialHomeomorph Coord Coord)
    (hF : ∀ t, (F t : Coord → Coord) = rawQuadratic (p t))
    (r : ℝ) (hr : 0 < r) (hsource : ∀ t, (F t).source = ball 0 r)
    (hInv : ∀ t, ContDiffOn ℝ ∞ (F t).symm (F t).target)
    (hJ : ∀ t, ∀ x ∈ (F t).source, ∃ J : Coord ≃L[ℝ] Coord,
      fderiv ℝ (rawQuadratic (p t)) x = J.toContinuousLinearMap)
    (hwp : ∀ t, ∀ z ∈ (F t).target, 0 < w z)
    (S : Coord → ℝ) (u : ℕ → T → Coord → ℂ)
    (hu : ∀ n t, ContDiff ℝ ∞ (u n t))
    (hsupport : ∀ n, 0 < n → ∀ t, tsupport (u n t) ⊆ closedBall 0 (2*(n:ℝ)^(-1/3:ℝ)))
    (k0 K : ℕ) (c Cr : ℝ) (Cs : Fin (k0+1) → ℝ)
    (hc : 0 < c) (hCr : 0 < Cr) (hCs : ∀ k, 0 < Cs k)
    (hest : ∀ᶠ n : ℕ in atTop, ∀ t x,
      (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (u n t) x‖ ≤
        Cs k*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2)) ∧
      DerivativeBound k0 (fun z ↦ smoothSecondOrder (fun i j ↦ complexPrincipal g i j (p t))
        (fun j ↦ complexDrift g w j (p t)) (u n t) z +
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*u n t z) x
        (Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)))) :
    ∃ c' Cw Cr' R : ℝ, 0 < c' ∧ 0 < Cw ∧ 0 < Cr' ∧ 0 < R ∧
      ∀ᶠ n : ℕ in atTop, ∀ t,
        ContDiff ℝ ∞ (chartPushforward (F t) (u n t)) ∧
        HasCompactSupport (chartPushforward (F t) (u n t)) ∧
        tsupport (chartPushforward (F t) (u n t)) ⊆ closedBall (p t).1 (R*(n:ℝ)^(-1/3:ℝ)) ∧
        ∀ z : Coord,
          (∀ k : Fin (k0+1), ‖iteratedFDeriv ℝ k.val (chartPushforward (F t) (u n t)) z‖ ≤
            Cw*(n:ℝ)^k.val*Real.exp ((n:ℝ)*S z-c'*(n:ℝ)*‖z-(p t).1‖^2)) ∧
          DerivativeBound k0 (fun z ↦ sourceWeightedOperator g w (chartPushforward (F t) (u n t)) z +
            ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))*chartPushforward (F t) (u n t) z) z
              (Cr'*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S z)) := by
  have hR (t : T) : closedBall (0:Coord) (r/2) ⊆ (F t).source := by
    rw [hsource t]
    exact closedBall_subset_ball (by linarith)
  obtain ⟨D,hD,hDb⟩ := compact_inverse_derivative_bounds isCompact_univ p hpc F
    (fun t _ ↦ hF t) (fun t _ ↦ hInv t) (fun t _ ↦ hJ t) (r/2) (fun t _ ↦ hR t) k0
  obtain ⟨L,hL,hLb⟩ := compact_chart_norm_bound isCompact_univ p hpc (r/2) (by positivity)
  let Ct : ℝ := ∑ k, Cs k
  have hCt : 0 < Ct := Finset.sum_pos (fun k _ ↦ hCs k) Finset.univ_nonempty
  have hCi (k : Fin (k0+1)) : Cs k ≤ Ct :=
    Finset.single_le_sum (fun j _ ↦ (hCs j).le) (Finset.mem_univ k)
  let Q : ℝ := (k0.factorial : ℝ)*D^k0
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQk (k : ℕ) (hk : k ≤ k0) : (k.factorial:ℝ)*D^k ≤ Q := by
    have hf : (k.factorial:ℝ) ≤ k0.factorial := by exact_mod_cast Nat.factorial_le hk
    have hd := pow_le_pow_right₀ hD hk
    dsimp [Q]
    gcongr
  refine ⟨c/L^2,Q*Ct,Q*Cr,2*L,by positivity,mul_pos hQ hCt,mul_pos hQ hCr,by positivity,?_⟩
  have hsmall : ∀ᶠ n : ℕ in atTop, 2*(n:ℝ)^(-1/3:ℝ) < r/2 := by
    apply eventually_nat_frequency (P := fun N : ℝ ↦ 2*N^(-1/3:ℝ) < r/2)
    have ht : Tendsto (fun N : ℝ ↦ 2*N^(-1/3:ℝ)) atTop (𝓝 0) := by
      simpa only [neg_div,mul_zero] using
        (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul 2
    exact ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hest,hsmall,eventually_ge_atTop (1:ℕ)] with n hn hsmall hn1
  have hnpos : 0 < n := by omega
  have hN : (1:ℝ) ≤ n := by exact_mod_cast hn1
  intro t
  have hus := hsupport n hnpos t
  have huR : tsupport (u n t) ⊆ closedBall (0:Coord) (r/2) :=
    hus.trans (closedBall_subset_closedBall hsmall.le)
  have huSource := huR.trans (hR t)
  have huComp : HasCompactSupport (u n t) :=
    (isCompact_closedBall (0:Coord) (r/2)).of_isClosed_subset isClosed_closure huR
  obtain ⟨hVs,hVc,hVsup⟩ := chartPushforward_smooth (F t) (hInv t) (u n t) (hu n t) huComp huSource
  refine ⟨hVs,hVc,?_,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := hVsup hz
    have hnorm := hLb t (mem_univ t) x (huR hx)
    have hxN : ‖x‖ ≤ 2*(n:ℝ)^(-1/3:ℝ) := by simpa using hus hx
    rw [mem_closedBall,dist_eq_norm,hF t]
    calc
      _ ≤ L*‖x‖ := hnorm
      _ ≤ L*(2*(n:ℝ)^(-1/3:ℝ)) := mul_le_mul_of_nonneg_left hxN (by positivity)
      _ = _ := by ring
  · intro z
    by_cases hz : z ∈ tsupport (chartPushforward (F t) (u n t))
    · obtain ⟨x,hx,rfl⟩ := hVsup hz
      have hxS := huSource hx
      have hxt := (F t).map_source hxS
      have hinv : (F t).symm (F t x) = x := (F t).left_inv hxS
      have hFx : rawQuadratic (p t) x = F t x := congrFun (hF t).symm x
      have hdi (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k0) := hDb t (mem_univ t) x (huR hx) i hi hik
      have hnorm : ‖F t x-(p t).1‖ ≤ L*‖x‖ := by rw [hF t]; exact hLb t (mem_univ t) x (huR hx)
      have hgauss : Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2) ≤
          Real.exp ((n:ℝ)*S (F t x)-(c/L^2)*(n:ℝ)*‖F t x-(p t).1‖^2) := by
        apply Real.exp_le_exp.mpr
        rw [hFx]
        have hh := gaussian_chart_norm_bound c (n:ℝ) L ‖x‖ ‖F t x-(p t).1‖ hc.le
          (by positivity) (by positivity) (norm_nonneg _) (norm_nonneg _) hnorm
        linarith
      refine ⟨?_,?_⟩
      · intro k
        have hk : k.val ≤ k0 := by omega
        have hb := chart_wave_size_transfer (F t) (hInv t) (u n t) (hu n t) (F t x) hxt k.val
          Ct D (Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2)) (n:ℝ)
          hCt.le (by positivity) hN (fun i hi ↦ by
            rw [hinv]
            have hh := (hn t x).1 ⟨i,by omega⟩
            exact hh.trans (by gcongr; exact hCi ⟨i,by omega⟩))
          (fun i hi hik ↦ hdi i hi (hik.trans hk))
        apply hb.trans
        have hq := hQk k.val hk
        calc
          _ = ((k.val.factorial:ℝ)*D^k.val)*Ct*(n:ℝ)^k.val*
              Real.exp ((n:ℝ)*S (rawQuadratic (p t) x)-c*(n:ℝ)*‖x‖^2) := by ring
          _ ≤ _ := by gcongr
      · intro k hk
        rw [transported_residual_derivative g hg hp w hw (p t) (F t) (hF t) (hInv t) (hJ t)
          (hwp t) (u n t) (hu n t) huComp huSource _ (F t x) hxt k]
        have hrs := actual_coordinate_residual_smoothOn g hg hp w hw (p t) (F t).source (hJ t)
          (fun x hx ↦ by rw [← hF t]; exact hwp t (F t x) ((F t).map_source hx)) (u n t) (hu n t)
          ((4:ℂ)*(n:ℂ)^2+6*(n:ℂ))
        have hb := chart_residual_bound_transfer (F t) (hInv t) _ hrs (F t x) hxt k
          Cr D (Real.exp ((n:ℝ)*S (rawQuadratic (p t) x))) (n:ℝ) (K:ℝ)
          (fun i hi ↦ by rw [hinv]; exact (hn t x).2 i (hi.trans hk))
          (fun i hi hik ↦ hdi i hi (hik.trans hk))
        apply hb.trans
        rw [hFx]
        have hq := hQk k hk
        calc
          _ = ((k.factorial:ℝ)*D^k)*Cr*(n:ℝ)^(-(K:ℝ))*Real.exp ((n:ℝ)*S (F t x)) := by ring
          _ ≤ _ := by gcongr
    · have he : chartPushforward (F t) (u n t) =ᶠ[𝓝 z] (fun _ ↦ 0) :=
        notMem_tsupport_iff_eventuallyEq.mp hz
      refine ⟨?_,?_⟩
      · intro k
        rw [(he.iteratedFDeriv ℝ k.val).self_of_nhds]
        have hzder : iteratedFDeriv ℝ k.val (fun _ : Coord ↦ (0:ℂ)) z = 0 := by simp
        rw [hzder,norm_zero]
        positivity
      · intro k _
        rw [source_residual_derivative_zero g w _ _ z hz k]
        simp only [norm_zero]
        positivity

end
end Yau.Geometry

end OAI
