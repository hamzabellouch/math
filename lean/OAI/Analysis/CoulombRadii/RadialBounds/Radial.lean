import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

def IsRadial (w : Position → ℝ) : Prop := ∀ x y, ‖x‖ = ‖y‖ → w x = w y

theorem potentialOf_isometry {w : Position → ℝ} (hw : IsRadial w)
    (T : Position ≃ₗᵢ[ℝ] Position) (x : Position) :
    potentialOf w (T x) = potentialOf w x := by
  unfold potentialOf
  rw [← T.measurePreserving.integral_comp T.toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← T.map_sub]
  simp only [coulombKernel, T.norm_map]
  rw [hw (T y) y (T.norm_map y)]

theorem potentialOf_radial {w : Position → ℝ} (hw : IsRadial w) :
    IsRadial (potentialOf w) := by
  intro x y hxy
  let T : Position ≃ₗᵢ[ℝ] Position := (ℝ ∙ (x-y))ᗮ.reflection
  have hT : T x = y := Submodule.reflection_sub hxy
  rw [← hT]
  exact (potentialOf_isometry hw T x).symm

theorem radial_potential_le_center {w : Position → ℝ} {A : ℝ}
    (hi : Integrable w) (hp : ∀ x, 0 ≤ w x) (hb : ∀ x, w x ≤ A)
    (hr : IsRadial w) (x : Position) : potentialOf w x ≤ potentialOf w 0 := by
  by_cases hx : x = 0
  · simp [hx]
  have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hcont := potentialOf_continuous hi hp hb
  have hrad := potentialOf_radial hr
  have hw : WeakLaplacianLower (fun y => potentialOf w x-potentialOf w y)
      (Metric.ball 0 ‖x‖ ∩ {y | 0 < potentialOf w x-potentialOf w y}) 0 := by
    intro φ hφ hc _ hpos
    have hL : Continuous (coordinateLaplacian φ) :=
      continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
    have hLc := hasCompactSupport_coordinateLaplacian hc
    have hiP : Integrable (fun y => potentialOf w y*coordinateLaplacian φ y) :=
      integrable_mul_compact_of_continuousAt (fun _ _ => hcont.continuousAt) hL hLc
    simp_rw [sub_mul]
    rw [integral_sub ((hL.integrable_of_hasCompactSupport hLc).const_mul _) hiP,
      integral_const_mul, integral_coordinateLaplacian hφ hc,
      potentialOf_weakLaplacian hi φ hφ hc (Set.subset_univ _)]
    simp only [zero_mul, mul_zero, zero_sub, neg_mul, integral_neg, neg_neg]
    exact integral_nonneg (fun y => mul_nonneg (mul_nonneg (by positivity) (hp y)) (hpos y))
  have hh := weak_maximum_principle_closedBall hR
    (continuous_const.sub hcont).continuousOn
    (fun y hy => by
      change potentialOf w x-potentialOf w y ≤ 0
      rw [hrad y x hy, sub_self]) hw
    (0 : Position) (by simp [hR.le])
  change potentialOf w x-potentialOf w 0 ≤ 0 at hh
  linarith

theorem integrable_coulomb_pairing {ρ w : Position → ℝ} {C : ℝ}
    (hρ : Integrable ρ) (hw : Integrable w) (hb : ∀ x, ‖w x‖ ≤ C) :
    Integrable (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*w z.1)
      (volume.prod volume) := by
  let k : Position → ℝ := (Metric.ball 0 1).indicator coulombKernel
  have hk : Integrable k :=
    (coulombKernel_integrableOn_ball 1).integrable_indicator measurableSet_ball
  have hn : Integrable (fun z : Position × Position => ‖ρ z.2‖*k (z.1-z.2))
      (volume.prod volume) := by
    simpa using hρ.norm.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hk
  have hf : Integrable (fun z : Position × Position => ‖w z.1‖*‖ρ z.2‖)
      (volume.prod volume) := hw.norm.mul_prod hρ.norm
  have hm : AEStronglyMeasurable
      (fun z : Position × Position => coulombKernel (z.1-z.2)*ρ z.2*w z.1)
      (volume.prod volume) := by
    have hh := hρ.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) measurable_coulombKernel.aestronglyMeasurable
    have hh' : AEStronglyMeasurable
        (fun z : Position × Position => ρ z.2*coulombKernel (z.1-z.2)*w z.1)
        (volume.prod volume) := hh.mul hw.aestronglyMeasurable.comp_fst
    convert hh' using 1
    ext z
    ring
  refine Integrable.mono' ((hn.const_mul C).add hf) hm (Filter.Eventually.of_forall ?_)
  intro z
  have hK : coulombKernel (z.1-z.2) ≤ k (z.1-z.2)+1 := by
    by_cases hz : z.1-z.2 ∈ Metric.ball (0 : Position) 1
    · simp only [k, Set.indicator_of_mem hz]
      linarith
    · have hl : 1 ≤ ‖z.1-z.2‖ := by simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz
      have hh : ‖z.1-z.2‖⁻¹ ≤ (1:ℝ) := by simpa using inv_anti₀ (by norm_num : (0:ℝ)<1) hl
      simpa only [k, Set.indicator_of_notMem hz, zero_add, coulombKernel] using hh
  have hkpos : 0 ≤ k (z.1-z.2) := Set.indicator_nonneg (fun y _ => coulombKernel_nonneg y) _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg (coulombKernel_nonneg _)]
  calc
    coulombKernel (z.1-z.2)*‖ρ z.2‖*‖w z.1‖ ≤
        (k (z.1-z.2)+1)*‖ρ z.2‖*‖w z.1‖ := by gcongr
    _ = ‖ρ z.2‖*k (z.1-z.2)*‖w z.1‖+‖w z.1‖*‖ρ z.2‖ := by ring
    _ ≤ C*(‖ρ z.2‖*k (z.1-z.2))+‖w z.1‖*‖ρ z.2‖ := by
      nlinarith [mul_nonneg (norm_nonneg (ρ z.2)) hkpos,
        mul_le_mul_of_nonneg_left (hb z.1) (mul_nonneg (norm_nonneg (ρ z.2)) hkpos)]

theorem coulomb_pairing_comm {ρ w : Position → ℝ} {C : ℝ}
    (hρ : Integrable ρ) (hw : Integrable w) (hb : ∀ x, ‖w x‖ ≤ C) :
    (∫ x, potentialOf ρ x*w x) = ∫ y, potentialOf w y*ρ y := by
  calc
    (∫ x, potentialOf ρ x*w x) = ∫ x, ∫ y, coulombKernel (x-y)*ρ y*w x := by
      simp only [potentialOf, integral_mul_const]
    _ = ∫ y, ∫ x, coulombKernel (x-y)*ρ y*w x :=
      integral_integral_swap (integrable_coulomb_pairing hρ hw hb)
    _ = ∫ y, potentialOf w y*ρ y := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [potentialOf, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [coulombKernel, norm_sub_rev x y]
      ring

theorem neutral_radial_average_nonneg {σ w : Position → ℝ} {lam Aσ Aw : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam)
    (hw : Integrable w) (hwpos : ∀ x, 0 ≤ w x) (hwbd : ∀ x, w x ≤ Aw)
    (hwrad : IsRadial w) :
    0 ≤ ∫ x, (lam*coulombKernel x-potentialOf σ x)*w x := by
  have hwabs : ∀ x, ‖w x‖ ≤ Aw := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwpos x)]
    exact hwbd x
  have hiK : Integrable (fun x => coulombKernel x*w x) := by
    have hh := (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ h => coulombKernel_le_one h)
      hw hwpos hwbd (0 : Position)).1
    simpa [coulombKernel] using hh
  have hiP : Integrable (fun x => potentialOf σ x*w x) := by
    have hh := (integrable_coulomb_pairing hσ hw hwabs).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hiPw : Integrable (fun x => potentialOf w x*σ x) := by
    have hh := (integrable_coulomb_pairing hw hσ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hσpos x)]
      exact hσbd x)).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hmax : ∀ x, potentialOf w x*σ x ≤ potentialOf w 0*σ x := fun x =>
    mul_le_mul_of_nonneg_right (radial_potential_le_center hw hwpos hwbd hwrad x) (hσpos x)
  have hle := integral_mono hiPw (hσ.const_mul (potentialOf w 0)) hmax
  rw [integral_const_mul, hmass] at hle
  have hzero : potentialOf w 0 = ∫ x, coulombKernel x*w x := by
    simp only [potentialOf, coulombKernel, zero_sub, norm_neg]
  simp_rw [sub_mul]
  have hilam : Integrable (fun x => lam*coulombKernel x*w x) := by
    simpa only [mul_assoc] using hiK.const_mul lam
  rw [integral_sub hilam hiP, coulomb_pairing_comm hσ hw hwabs]
  simp_rw [mul_assoc lam, integral_const_mul]
  rw [← hzero]
  nlinarith

theorem neutral_weighted_lone_bound {σ w : Position → ℝ} {lam Aσ Aw B : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam)
    (hw : Integrable w) (hwpos : ∀ x, 0 ≤ w x) (hwbd : ∀ x, w x ≤ Aw)
    (hwrad : IsRadial w) (hB : 0 ≤ B)
    (hcap : ∀ x, w x ≠ 0 → lam*coulombKernel x-potentialOf σ x ≤ B) :
    (∫ x, |lam*coulombKernel x-potentialOf σ x| *w x) ≤ 2*B*(∫ x, w x) := by
  let F (x : Position) := lam*coulombKernel x-potentialOf σ x
  have hwabs : ∀ x, ‖w x‖ ≤ Aw := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hwpos x)]
    exact hwbd x
  have hiK : Integrable (fun x => coulombKernel x*w x) := by
    have hh := (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ h => coulombKernel_le_one h)
      hw hwpos hwbd (0 : Position)).1
    simpa [coulombKernel] using hh
  have hiP : Integrable (fun x => potentialOf σ x*w x) := by
    have hh := (integrable_coulomb_pairing hσ hw hwabs).integral_prod_left
    simpa only [potentialOf, integral_mul_const] using hh
  have hiF : Integrable (fun x => F x*w x) := by
    simpa only [Pi.sub_def, F, sub_mul, mul_assoc] using (hiK.const_mul lam).sub hiP
  have hiabs : Integrable (fun x => |F x| *w x) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hwpos _)] using hiF.norm
  have hle : ∀ x, |F x| *w x ≤ 2*B*w x-F x*w x := by
    intro x
    by_cases hx : w x = 0
    · simp [hx]
    · have hh := hcap x hx
      have hh' : |F x| ≤ 2*B-F x := by
        rw [abs_le]
        constructor <;> dsimp [F] <;> linarith
      nlinarith [mul_le_mul_of_nonneg_right hh' (hwpos x)]
  have hh := integral_mono hiabs ((hw.const_mul (2*B)).sub hiF) hle
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (hw.const_mul (2*B)) hiF, integral_const_mul] at hh
  have hmean := neutral_radial_average_nonneg hσ hσpos hσbd hmass hw hwpos hwbd hwrad
  change 0 ≤ ∫ x, F x*w x at hmean
  linarith

theorem neutral_annulus_lone_bound {σ : Position → ℝ} {lam Aσ C a b : ℝ}
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hmass : (∫ x, σ x) = lam) (ha : 0 < a) (hC : 0 ≤ C)
    (hcap : ∀ x : Position, a ≤ ‖x‖ → ‖x‖ ≤ b →
      lam*coulombKernel x-potentialOf σ x ≤ C/(‖x‖^4)) :
    (∫ x in {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b},
      |lam*coulombKernel x-potentialOf σ x|) ≤
    2*(C/a^4)*(volume {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}).toReal := by
  let s : Set Position := {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b}
  let w : Position → ℝ := s.indicator (fun _ => 1)
  have hs : IsCompact s := by
    have hs' : s = Metric.closedBall (0 : Position) b ∩ {x | a ≤ ‖x‖} := by
      ext x
      simp only [s, Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
        dist_zero_right, and_comm]
    rw [hs']
    exact (isCompact_closedBall (0 : Position) b).inter_right (isClosed_le continuous_const continuous_norm)
  have hw : Integrable w := by
    apply (integrable_indicator_iff hs.measurableSet).mpr
    exact integrableOn_const hs.measure_ne_top
  have hwpos : ∀ x, 0 ≤ w x := fun x => Set.indicator_nonneg (fun _ _ => by norm_num) x
  have hwbd : ∀ x, w x ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [w, hx]
  have hwrad : IsRadial w := by
    intro x y hxy
    by_cases hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ b
    · have hy : a ≤ ‖y‖ ∧ ‖y‖ ≤ b := by simpa only [hxy] using hx
      simp [w, s, hx, hy]
    · have hy : ¬(a ≤ ‖y‖ ∧ ‖y‖ ≤ b) := by simpa only [hxy] using hx
      simp [w, s, hx, hy]
  have hB : 0 ≤ C/a^4 := div_nonneg hC (by positivity)
  have hcap' : ∀ x, w x ≠ 0 → lam*coulombKernel x-potentialOf σ x ≤ C/a^4 := by
    intro x hx
    have hxs : x ∈ s := by
      by_contra h
      exact hx (Set.indicator_of_notMem h _)
    exact (hcap x hxs.1 hxs.2).trans
      (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ ha.le hxs.1 4))
  have hh := neutral_weighted_lone_bound hσ hσpos hσbd hmass hw hwpos hwbd hwrad hB hcap'
  have heq : (fun x => |lam*coulombKernel x-potentialOf σ x| *w x) =
      s.indicator (fun x => |lam*coulombKernel x-potentialOf σ x|) := by
    ext x
    by_cases hx : x ∈ s <;> simp [w, hx]
  rw [heq, integral_indicator hs.measurableSet] at hh
  have hiw : (∫ x, w x) = (volume s).toReal := by
    rw [show w = s.indicator (fun _ => (1:ℝ)) from rfl,
      integral_indicator hs.measurableSet, integral_const]
    simp only [Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def]
  rw [hiw] at hh
  exact hh

theorem locallyUniform_subsequence_of_equicontinuous
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X]
    (F : ℕ → C(X, ℝ))
    (heq : Equicontinuous (fun n x => F n x))
    (hbd : ∀ x, ∃ M : ℝ, ∀ n, ‖F n x‖ ≤ M) :
    ∃ f : C(X, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => F (φ n) x) f atTop := by
  let : T2Space (UniformOnFun X ℝ {K : Set X | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_sUnion_of_mem (Set.mem_singleton x) isCompact_singleton)
  let S := Set.range F
  have hs : IsCompact (closure S) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun f : C(X, ℝ) => (f : X → ℝ))
      (𝔖 := {K : Set X | IsCompact K}) (fun _ hK => hK)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K _
      let pick : S → ℕ := fun f => Classical.choose f.property
      have hp (f : S) : F (pick f) = f.val := Classical.choose_spec f.property
      have hh := (heq.comp pick).equicontinuousOn K
      convert hh using 1
      ext f x
      exact congrArg (fun u : C(X, ℝ) => u x) (hp f).symm
    · intro K _ x _
      obtain ⟨M, hM⟩ := hbd x
      refine ⟨Set.Icc (-M) M, isCompact_Icc, ?_⟩
      rintro f ⟨n, rfl⟩
      exact abs_le.mp (hM n)
  obtain ⟨f, _, φ, hφ, ht⟩ := hs.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨f, φ, hφ, ?_⟩
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht

theorem equicontinuous_of_eventual_local_lipschitz
    {X : Type*} [PseudoMetricSpace X] (F : ℕ → X → ℝ)
    (hc : ∀ n, Continuous (F n))
    (hl : ∀ x, ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ C ∧
      ∀ n, N ≤ n → ∀ y ∈ Metric.ball x r, ‖F n x-F n y‖ ≤ C*dist y x) :
    Equicontinuous F := by
  intro x
  obtain ⟨r, C, N, hr, hC, hN⟩ := hl x
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  have hf : EquicontinuousAt (fun n : Fin N => F n) x :=
    equicontinuousAt_finite.mpr (fun n => (hc n).continuousAt)
  obtain ⟨δ, hδ, hd⟩ := Metric.equicontinuousAt_iff.mp hf ε hε
  refine ⟨min r (min δ (ε/(C+1))), lt_min hr (lt_min hδ (div_pos hε (by linarith))), ?_⟩
  intro y hy n
  have hyr : dist y x < r := lt_of_lt_of_le hy (min_le_left _ _)
  have hyδ : dist y x < δ := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have hyε : dist y x < ε/(C+1) :=
    lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
  by_cases hn : n < N
  · exact hd y hyδ ⟨n, hn⟩
  · have hh := hN n (le_of_not_gt hn) y hyr
    rw [dist_eq_norm]
    have hmul := (lt_div_iff₀ (by linarith : 0 < C+1)).mp hyε
    nlinarith [dist_nonneg (x := y) (y := x)]

theorem norm_bounded_of_eventually_bounded (a : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ n in atTop, ‖a n‖ ≤ C) : ∃ M : ℝ, ∀ n, ‖a n‖ ≤ M := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨C+∑ j ∈ Finset.range N, ‖a j‖, ?_⟩
  intro n
  have hs : 0 ≤ ∑ j ∈ Finset.range N, ‖a j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  by_cases hn : n < N
  · have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range N) => norm_nonneg (a j))
      (Finset.mem_range.mpr hn)
    linarith
  · have hh := hN n (le_of_not_gt hn)
    linarith

theorem locallyUniform_subsequence_of_eventual_ball_estimates
    {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (F : ℕ → X → ℝ)
    (hc : ∀ n, Continuous (F n))
    (he : ∀ x, ∃ (r C : ℝ) (N : ℕ), 0 < r ∧ 0 ≤ C ∧
      ∀ n, N ≤ n → ‖F n x‖ ≤ C ∧
        ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
          ‖F n y-F n z‖ ≤ C*dist y z) :
    ∃ f : C(X, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun n x => F (φ n) x) f atTop ∧
      LocallyLipschitzOn Set.univ f := by
  let G : ℕ → C(X, ℝ) := fun n => ⟨F n, hc n⟩
  have hEq : Equicontinuous (fun n x => G n x) := by
    apply equicontinuous_of_eventual_local_lipschitz F hc
    intro x
    obtain ⟨r, C, N, hr, hC, hN⟩ := he x
    refine ⟨r, C, N, hr, hC, ?_⟩
    intro n hn y hy
    simpa only [dist_comm x y] using (hN n hn).2 x (Metric.mem_ball_self hr) y hy
  have hBd : ∀ x, ∃ M : ℝ, ∀ n, ‖G n x‖ ≤ M := by
    intro x
    obtain ⟨r, C, N, _, hC, hN⟩ := he x
    exact norm_bounded_of_eventually_bounded (fun n => F n x) hC
      (eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).1⟩)
  obtain ⟨f, φ, hφ, hu⟩ := locallyUniform_subsequence_of_equicontinuous G hEq hBd
  refine ⟨f, φ, hφ, hu, ?_⟩
  intro x _
  obtain ⟨r, C, N, hr, _, hN⟩ := he x
  refine ⟨C.toNNReal, Metric.ball x r, ?_, ?_⟩
  · simpa only [nhdsWithin_univ] using Metric.ball_mem_nhds x hr
  · apply LipschitzOnWith.of_dist_le'
    intro y hy z hz
    have ht (w : X) : Tendsto (fun n => F (φ n) w) atTop (𝓝 (f w)) :=
      hu.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ w)
    have hn : ∀ᶠ n : ℕ in atTop, N ≤ φ n := hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
    have hl := le_of_tendsto ((ht y).sub (ht z)).norm (hn.mono (fun n hn => (hN (φ n) hn).2 y hy z hz))
    simpa only [dist_eq_norm] using hl

def screenedField (lam : ℝ) (σ : Position → ℝ) (x : Position) : ℝ :=
  lam*coulombKernel x-potentialOf σ x

theorem screenedField_continuousOn {lam A : ℝ} {σ : Position → ℝ}
    (hi : Integrable σ) (hp : ∀ x, 0 ≤ σ x) (hb : ∀ x, σ x ≤ A) :
    ContinuousOn (screenedField lam σ) {x | x ≠ 0} := by
  intro x hx
  have hk : ContinuousAt coulombKernel x :=
    continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)
  exact ((continuousAt_const.mul hk).sub
    (potentialOf_continuous hi hp hb).continuousAt).continuousWithinAt

theorem screenedField_weakLaplacian {lam A : ℝ} {σ : Position → ℝ}
    (hi : Integrable σ) (hp : ∀ x, 0 ≤ σ x) (hb : ∀ x, σ x ≤ A) :
    HasWeakLaplacian (screenedField lam σ) {x | x ≠ 0} (fun x => 4*Real.pi*σ x) := by
  intro φ hφ hc ht
  have hLc : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLs := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hLc hLs
  have hiP : Integrable (fun x => potentialOf σ x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun _ _ => (potentialOf_continuous hi hp hb).continuousAt)
      hLc hLs
  have hzero : φ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hx => ht hx rfl)
  calc
    (∫ x, screenedField lam σ x*coordinateLaplacian φ x) =
        lam*(∫ x, coulombKernel x*coordinateLaplacian φ x)-
        ∫ x, potentialOf σ x*coordinateLaplacian φ x := by
      simp only [screenedField, sub_mul, mul_assoc]
      rw [integral_sub (hiK.const_mul lam) hiP, integral_const_mul]
    _ = ∫ x, (4*Real.pi*σ x)*φ x := by
      rw [integral_coulombKernel_laplacian hφ hc, hzero,
        potentialOf_weakLaplacian hi φ hφ hc (Set.subset_univ _)]
      simp only [mul_zero, neg_zero, zero_sub, ← integral_neg]
      congr 1
      ext x
      ring

theorem isCompact_closedNormAnnulus (a b : ℝ) :
    IsCompact {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} := by
  have he : {x : Position | a ≤ ‖x‖ ∧ ‖x‖ ≤ b} =
      Metric.closedBall (0 : Position) b ∩ {x | a ≤ ‖x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right, and_comm]
  rw [he]
  exact (isCompact_closedBall (0 : Position) b).inter_right (isClosed_le continuous_const continuous_norm)

end NeutralAtom
end
end

end OAI
