import OAI.Geometry.Riemannian.HarmonicCore.SobolevOrder

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

theorem weak_forced_cutoff_all_orders (n : ℕ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (r S T : ℝ) (hr : 0 < r) (hrS : r < S)
    (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A) (C L Q c : ℝ)
    (hc : 0 < c) (hC : ∀ x, ‖A x‖ ≤ C) (hL0 : 0 ≤ L) (hQ : 0 ≤ Q)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (hcompact : ∀ a : E3, HasCompactSupport (fun x ↦ fderiv ℝ A x a))
    (u : ZeroSobolev T) (F : DerivativeL2)
    (hF : ∀ i, CompactSobolev (n+1) (componentL2 (b i) F))
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = ⟪F,sobolevDerivative S v⟫_ℝ)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 r)
    (K : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) :
    CompactSobolev (n+2) (scalarFieldCLM χ hχ.continuous K hK (sobolevValue T u)) := by
  classical
  induction n generalizing r S T u F χ K with
  | zero =>
    obtain ⟨N,wF,hwF⟩ := CompactSobolev.exists_common_graph _ hF
    have hsχ : HasCompactSupport χ := Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_tsupport χ,Metric.isBounded_ball.subset hsupp⟩
    obtain ⟨D,hD⟩ := continuous_compact_bound (gradient χ) (gradient_continuous hχ) (gradient_compact hsχ)
    refine ⟨r,cutoffSobolev r T χ hχ hsupp K D hK hD u,rfl,fun a ↦ ?_⟩
    obtain ⟨w,hw⟩ := weak_forced_cutoff_H2 b r S T N hrS A C L c hc hL0 hA.continuous
      hC hL hpos u F wF hwF hu χ hχ hsupp K D hK hD a
    exact ⟨r,w,hw,fun _ ↦ trivial⟩
  | succ n ih =>
    obtain ⟨R1,hr1,h1S⟩ := exists_between hrS
    obtain ⟨R2,h12,h2S⟩ := exists_between h1S
    obtain ⟨R3,h23,h3S⟩ := exists_between h2S
    obtain ⟨ψ',Dψ',hψ',hsψ',hKψ',hDψ',hψ'1,hdψ'⟩ := smooth_ball_cutoff R2 R3 (hr.trans (hr1.trans h12)) h23
    let Kψ' : ℝ := 1
    let w := cutoffSobolev R3 T ψ' hψ' hsψ' Kψ' Dψ' hKψ' hDψ' u
    have hwreg : CompactSobolev (n+2) (sobolevValue R3 w) :=
      ih R3 S T (hr.trans (hr1.trans (h12.trans h23))) h3S u F
        (fun i ↦ (hF i).lower) hu ψ' hψ' hsψ' Kψ' hKψ'
    have hwweak : ∀ v : ZeroSobolev R2,
        ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative R3 w),sobolevDerivative R2 v⟫_ℝ = ⟪F,sobolevDerivative R2 v⟫_ℝ := by
      have hh (v : ZeroSobolev R3) :
          ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative R3 v⟫_ℝ = ⟪F,sobolevDerivative R3 v⟫_ℝ :=
        hu (includeSobolev h3S.le v)
      exact weak_forced_cutoff_restrict R2 R3 T h23.le A C hA.continuous.aestronglyMeasurable hC
        u F hh ψ' hψ' hsψ' Kψ' Dψ' hKψ' hDψ' hψ'1 hdψ'
    obtain ⟨N,v,hv⟩ := CompactSobolev.exists_common_graph
      (fun i ↦ componentL2 (b i) (sobolevDerivative R3 w))
      (fun i ↦ (hwreg.gradient R3 w rfl (b i)).mono (by omega))
    obtain ⟨M,z,hz⟩ := CompactSobolev.exists_common_graph
      (fun i ↦ componentL2 (b i) F) (fun i ↦ (hF i).mono (by omega))
    have hsχ : HasCompactSupport χ := Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_tsupport χ,Metric.isBounded_ball.subset hsupp⟩
    obtain ⟨D,hD⟩ := continuous_compact_bound (gradient χ) (gradient_continuous hχ) (gradient_compact hsχ)
    have hwχ : CompactSobolev (n+3) (scalarFieldCLM χ hχ.continuous K hK (sobolevValue R3 w)) := by
      refine ⟨r,cutoffSobolev r R3 χ hχ hsupp K D hK hD w,rfl,fun a ↦ ?_⟩
      obtain ⟨q,hq,hqe⟩ := weak_direction_equation b b R1 R2 R3 N M h12 A hA C L Q hC hL0 hQ hL hQbound
        w F hwweak v hv z hz a
      let B : E3 → E3 →L[ℝ] E3 := fun x ↦ fderiv ℝ A x a
      have hB : ContDiff ℝ ∞ B := (hA.fderiv_right (by simp)).clm_apply contDiff_const
      have hBbound : ∀ x, ‖B x‖ ≤ L*‖a‖ := coefficientDirection_bound A L hL0 hL a
      let G : DerivativeL2 := (∑ i,vectorizeL2 (b i) (componentL2 a (sobolevDerivative M (z i))))-
        coefficientDirectionCLM A hA L hL0 hL a (sobolevDerivative R3 w)
      have hGreg (i) : CompactSobolev (n+1) (componentL2 (b i) G) := by
        change CompactSobolev (n+1) (componentL2 (b i) (_-_))
        rw [map_sub,sub_eq_add_neg]
        apply CompactSobolev.add
        · exact CompactSobolev.vector_sum b _
            (fun j ↦ (hF j).gradient M (z j) (hz j) a) (b i)
        · have hh := CompactSobolev.coefficient b (sobolevDerivative R3 w)
              (fun j ↦ hwreg.gradient R3 w rfl (b j)) B hB (hcompact a) (L*‖a‖) hBbound (b i)
          simpa only [coefficientDirectionCLM,B,neg_one_smul] using hh.smul (-1)
      have hqχ : CompactSobolev (n+2)
          (scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative R3 w))) := by
        rw [←hq]
        exact ih r R1 (R3+1) hr hr1 q G hGreg hqe χ hχ hsupp K hK
      let θ : E3 → ℝ := fun x ↦ fderiv ℝ χ x a
      have hθ : ContDiff ℝ ∞ θ := (hχ.fderiv_right (by simp)).clm_apply contDiff_const
      obtain ⟨Ka,hKa⟩ := continuous_compact_bound θ hθ.continuous (hsχ.fderiv_apply ℝ a)
      rw [cutoffSobolev_direction r R3 χ hχ hsupp K D hK hD w a Ka hKa]
      exact hqχ.add (hwreg.smooth_mul θ hθ (hsχ.fderiv_apply ℝ a) Ka hKa)
    have he (x : E3) : χ x*ψ' x=χ x := by
      by_cases hx : x ∈ tsupport χ
      · rw [hψ'1 x (Metric.ball_subset_closedBall (hsupp hx) |> Metric.closedBall_subset_closedBall (hr1.trans h12).le),mul_one]
      · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    change CompactSobolev (n+3) _
    change CompactSobolev (n+3) (scalarFieldCLM χ hχ.continuous K hK
      (scalarFieldCLM ψ' hψ'.continuous Kψ' hKψ' (sobolevValue T u))) at hwχ
    rw [scalarFieldCLM_mul χ ψ' hχ.continuous hψ'.continuous K Kψ' hK hKψ' he] at hwχ
    exact hwχ



theorem CompactSobolev.classical {n : ℕ} {f : ValueL2} (hf : CompactSobolev (n+2) f) :
    ∃ U : E3 →ᵇ ℝ, ContDiff ℝ n (U:E3 → ℝ) ∧ (U:E3 → ℝ) =ᵐ[volume] (f:E3 → ℝ) := by
  classical
  let b := stdOrthonormalBasis ℝ E3
  induction n generalizing f with
  | zero =>
    obtain ⟨R,u,hu,hd⟩ := hf
    obtain ⟨N,w,hw⟩ := CompactSobolev.exists_common_graph _ (fun i ↦ hd (b i))
    obtain ⟨U,hU⟩ := graph_H2_continuous b R N u w hw
    exact ⟨U,contDiff_zero.mpr U.continuous,by simpa only [hu] using hU⟩
  | succ n ih =>
    have hlow : CompactSobolev (n+2) f := hf.lower
    obtain ⟨U,hUdiff,hU⟩ := ih hlow
    obtain ⟨R,u,hu,hd⟩ := hf
    choose V hVdiff hV using fun i ↦ ih (hd (b i))
    let W : E3 → E3 := fun x ↦ ∑ i,V i x • b i
    have hWd : ContDiff ℝ n W := ContDiff.sum (fun i _ ↦ (hVdiff i).smul contDiff_const)
    have hWa : W =ᵐ[volume] (sobolevDerivative R u : E3 → E3) := by
      have hall : ∀ᵐ x ∂volume, ∀ i, V i x = ⟪b i,(sobolevDerivative R u) x⟫_ℝ := by
        rw [ae_all_iff]
        intro i
        exact (hV i).trans (componentL2_coe (b i) _)
      filter_upwards [hall] with x hx
      simpa only [W,hx] using b.sum_repr' ((sobolevDerivative R u) x)
    refine ⟨U,?_,hU⟩
    rw [show ((n+1:ℕ):WithTop ℕ∞) = (n:WithTop ℕ∞)+1 by simp,contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x ↦ InnerProductSpace.toDual ℝ E3 (W x),?_,fun x ↦ ?_⟩
    · exact (InnerProductSpace.toDual ℝ E3).toContinuousLinearMap.contDiff.comp hWd
    · exact sobolev_continuous_hasFDerivAt R u U W U.continuous hWd.continuous
        (by simpa only [hu] using hU) hWa x

theorem CompactSobolev.smooth {f : ValueL2} (hf : ∀ n, CompactSobolev n f) :
    ∃ U : E3 →ᵇ ℝ, ContDiff ℝ ∞ (U:E3 → ℝ) ∧ (U:E3 → ℝ) =ᵐ[volume] (f:E3 → ℝ) := by
  obtain ⟨U,_,hU⟩ := CompactSobolev.classical (n:=0) (hf 2)
  refine ⟨U,contDiff_infty.mpr (fun n ↦ ?_),hU⟩
  obtain ⟨V,hVd,hV⟩ := CompactSobolev.classical (n:=n) (hf (n+2))
  have he : (U:E3 → ℝ) = (V:E3 → ℝ) := (volume : Measure E3).eq_of_ae_eq (hU.trans hV.symm) U.continuous V.continuous
  rw [he]
  exact hVd



theorem metric_weak_smooth (g : SmoothMetric3) (r S T : ℝ)
    (hr : 0 < r) (hrS : r < S) (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T u) x),
        (sobolevDerivative S v) x⟫_ℝ) = 0) :
    ∃ U : E3 →ᵇ ℝ, ContDiff ℝ ∞ (U:E3 → ℝ) ∧
      (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)] (sobolevValue T u : E3 → ℝ) := by
  obtain ⟨A,C,L,Q,c,hA,hC0,hL0,hQ0,hc,hC,hL,hQ,hpos,hAg,hcomp⟩ :=
    g.smooth_energy_extension_higher S (hr.trans hrS).le
  obtain ⟨R,hrR,hRS⟩ := exists_between hrS
  obtain ⟨χ,D,hχ,hsχ,hK,hD,hχ1,hdχ⟩ := smooth_ball_cutoff r R hr hrR
  have hweak (v : ZeroSobolev S) :
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪(0:DerivativeL2),sobolevDerivative S v⟫_ℝ := by
    rw [inner_zero_left,coefficient_ball_energy_eq g S A C hA.continuous.aestronglyMeasurable hC hAg]
    exact hu v
  let f := scalarFieldCLM χ hχ.continuous 1 hK (sobolevValue T u)
  have hf (n : ℕ) : CompactSobolev n f := by
    apply (weak_forced_cutoff_all_orders n (stdOrthonormalBasis ℝ E3) R S T (hr.trans hrR) hRS
      A hA C L Q c hc hC hL0 hQ0 hL hQ hpos hcomp u 0 _ hweak χ hχ hsχ 1 hK).mono (by omega)
    intro i
    simpa only [map_zero] using CompactSobolev.zero (n+1)
  obtain ⟨U,hUd,hUa⟩ := CompactSobolev.smooth hf
  refine ⟨U,hUd,?_⟩
  filter_upwards [hUa.filter_mono ae_restrict_le,
    (scalarFieldCLM_coe χ hχ.continuous 1 hK (sobolevValue T u)).filter_mono ae_restrict_le,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hy hz
  rw [hx]
  change f x = _
  rw [hy,hχ1 x (Metric.ball_subset_closedBall hz),one_smul]

theorem metric_affine_weak_smooth (g : SmoothMetric3) (R : ℝ) (hR : 0 < R)
    {F : E3 → ℝ} (hF : ContDiff ℝ ∞ F) (hcompact : HasCompactSupport F) :
    ∃ u : ZeroSobolev R,
      (∀ v : ZeroSobolev R,
        (∫ x, ⟪g.energyOperator x (gradient F x+(sobolevDerivative R u) x),
          (sobolevDerivative R v) x⟫_ℝ) = 0) ∧
      ∀ r : ℝ, 0 < r → r < R → ∃ U : E3 →ᵇ ℝ,
        ContDiff ℝ ∞ (U:E3 → ℝ) ∧
        (U:E3 → ℝ) =ᵐ[volume.restrict (Metric.ball 0 r)]
          (fun x ↦ F x+(sobolevValue R u) x) := by
  obtain ⟨u,hu,_⟩ := g.metric_affine_weak_dirichlet R hR.le hF hcompact
  obtain ⟨T,hRT,hTs⟩ := compact_test_extension hF hcompact R
  let φ : DirichletTest T := ⟨F,hF,hcompact,hTs⟩
  let w : ZeroSobolev T := testSobolev T φ+includeSobolev hRT u
  have hw : ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.energyOperator x ((sobolevDerivative T w) x),(sobolevDerivative R v) x⟫_ℝ) = 0 := by
    intro v
    rw [←hu v]
    apply integral_congr_ae
    filter_upwards [affineSobolev_derivative hRT φ u] with x hx
    rw [hx]
  refine ⟨u,hu,fun r hr hrR ↦ ?_⟩
  obtain ⟨U,hUd,hU⟩ := g.metric_weak_smooth r R T hr hrR w hw
  exact ⟨U,hUd,hU.trans ((affineSobolev_value hRT φ u).filter_mono ae_restrict_le)⟩

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
