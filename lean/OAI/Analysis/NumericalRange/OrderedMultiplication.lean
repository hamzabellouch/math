import OAI.Analysis.NumericalRange.HilbertSchmidt

namespace OAI

noncomputable section

universe u_54 u_55 u_56 u_57 u_58 u_59 u_60

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
open scoped ComplexConjugate InnerProductSpace
open Set Metric Filter Complex
open scoped Topology
open MeasureTheory Set Complex
open scoped Topology
open MeasureTheory Set Complex Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace CompleteCrouzeix

section

section

section

section
variable {E : Type u_54} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace FourierResolution
variable (D : FourierResolution E)
variable (J : E ≃ₗᵢ⋆[ℂ] E)
    (hJJ : Function.Involutive J)
    (hJ0 : ∀ u, J (D.proj 0 u) = D.proj 0 (J u))
    (hJ1 : ∀ u, J (D.proj 1 u) = D.proj 2 (J u))

include hJJ hJ1 in
lemma star_negative (u : E) : J (D.proj 2 u) = D.proj 1 (J u) := by
  have h := congrArg J (hJ1 (J u))
  simpa only [hJJ u, hJJ (D.proj 1 (J u))] using h.symm

lemma nonnegative_decompose (v : E) (hv : D.proj 2 v = 0) :
    D.proj 0 v + D.proj 1 v = v := by
  simpa only [hv, add_zero] using D.decompose v

include hJ1 in

lemma hermitian_fourier_norm (v : E) (hv : D.proj 2 v = 0)
    (hv0 : J (D.proj 0 v) = D.proj 0 v) :
    ‖v + J v‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖D.proj 0 v‖ ^ 2) := by
  have hvd := D.nonnegative_decompose v hv
  have hjd : J v = D.proj 0 v + D.proj 2 (J v) := by
    calc
      J v = J (D.proj 0 v + D.proj 1 v) := congrArg J hvd.symm
      _ = _ := by rw [map_add, hv0, hJ1]
  have hn1 : ‖D.proj 2 (J v)‖ = ‖D.proj 1 v‖ := by
    rw [← hJ1, J.norm_map]
  have hsum : v + J v = (2 : ℂ) • D.proj 0 v + D.proj 1 v + D.proj 2 (J v) := by
    calc
      _ = (D.proj 0 v + D.proj 1 v) + (D.proj 0 v + D.proj 2 (J v)) :=
        congrArg₂ (· + ·) hvd.symm hjd
      _ = _ := by simp only [two_smul]; abel
  have ho1 : inner ℂ ((2 : ℂ) • D.proj 0 v) (D.proj 1 v) = 0 := by
    rw [inner_smul_left, D.orthogonal 0 1 (by decide)]
    simp
  have ho2 : inner ℂ ((2 : ℂ) • D.proj 0 v + D.proj 1 v)
      (D.proj 2 (J v)) = 0 := by
    rw [inner_add_left, inner_smul_left,
      D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp
  rw [hsum, norm_sq_add_orthogonal _ _ ho2, norm_sq_add_orthogonal _ _ ho1,
    norm_smul, hn1]
  have hn := D.norm_decompose v
  rw [hv, norm_zero, zero_pow (by decide), add_zero] at hn
  norm_num
  nlinarith

lemma adjoint_module_apply (M L : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (r : E) :
    D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) =
      D.cauchyAdjoint M (L.adjoint r) := by
  have h := congrArg ContinuousLinearMap.adjoint hmod
  simp only [ContinuousLinearMap.adjoint_comp, D.adjoint_cauchy M hswap] at h
  exact congrArg (fun T : E →L[ℂ] E => T r) h

include hJ0 hJ1 in
lemma hermitian_diagonal_bound (M L : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmod : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (p r : E) (hp : p = L.adjoint r) (hpJ : J p = p) :
    ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
  have hdiag := D.hermitian_fourier_norm J hJ1 (D.cauchyAdjoint M p)
    (D.negative_adjoint M hswap p)
    (by rw [D.mean_adjoint M hswap, hJ0, hpJ])
  have heq : D.cauchyAdjoint M p =
      D.cauchyAdjoint M (L.adjoint (D.cauchyAdjoint M r)) := by
    rw [D.adjoint_module_apply M L hswap hmod, hp]
  have hw := D.weighted_adjoint_bound M hM hswap (L.adjoint (D.cauchyAdjoint M r))
  have hnorm : ‖L.adjoint (D.cauchyAdjoint M r)‖ ≤ ‖D.cauchyAdjoint M r‖ := by
    calc _ ≤ ‖L.adjoint‖ * ‖D.cauchyAdjoint M r‖ := L.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.cauchyAdjoint M r‖ := by gcongr; simpa using hL
      _ = _ := one_mul _
  rw [hdiag, heq, D.mean_adjoint M hswap]
  nlinarith [norm_nonneg (L.adjoint (D.cauchyAdjoint M r)),
    norm_nonneg (D.cauchyAdjoint M r)]

include hJ0 hJ1 in
lemma opposite_adjoint_orthogonal (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (r : E) (hr : D.proj 0 r = 0) :
    inner ℂ (D.cauchyAdjoint M r) (J (D.cauchyAdjoint M (J r))) = 0 := by
  have hpos : D.proj 1 (D.cauchyAdjoint M r) = D.cauchyAdjoint M r := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M r)
      (D.negative_adjoint M hswap r)
    simpa only [D.mean_adjoint M hswap, hr, zero_add] using h
  have hjr : D.proj 0 (J r) = 0 := by rw [← hJ0, hr]; simp
  have hjpos : D.proj 1 (D.cauchyAdjoint M (J r)) = D.cauchyAdjoint M (J r) := by
    have h := D.nonnegative_decompose (D.cauchyAdjoint M (J r))
      (D.negative_adjoint M hswap (J r))
    simpa only [D.mean_adjoint M hswap, hjr, zero_add] using h
  have hneg : D.proj 2 (J (D.cauchyAdjoint M (J r))) =
      J (D.cauchyAdjoint M (J r)) := by rw [← hJ1, hjpos]
  conv_lhs => lhs; rw [← hpos]
  conv_lhs => rhs; rw [← hneg]
  exact D.orthogonal 1 2 (by decide) _ _

include hJ0 hJ1 in

theorem density_comparison_core (M L R : E →L[ℂ] E)
    (hM : ‖M‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M)
    (hmodL : (D.cauchy M).comp (L.comp (D.cauchy M)) = L.comp (D.cauchy M))
    (hmodR : (D.cauchy M).comp (R.comp (D.cauchy M)) = R.comp (D.cauchy M))
    (p q r : E) (hp : p = L.adjoint r) (hq : q = R.adjoint r)
    (hpJ : J p = p) (hqJ : J q = q) (hr : D.proj 0 r = 0)
    (hp0 : D.proj 0 p ≠ 0) (κ : ℝ) (hκ : 0 < κ)
    (hblock : 2 * ‖(κ : ℂ) • D.cauchyAdjoint M r +
        ((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖ ^ 2 ≤
      ‖D.cauchyAdjoint M p + J (D.cauchyAdjoint M p)‖ ^ 2 +
      ‖D.cauchyAdjoint M q + J (D.cauchyAdjoint M q)‖ ^ 2) : κ ≤ 2 := by
  have hg : D.cauchyAdjoint M r ≠ 0 := by
    intro hz
    apply hp0
    have hc : D.cauchyAdjoint M p = 0 := by
      rw [hp, ← D.adjoint_module_apply M L hswap hmodL, hz]
      simp
    rw [← D.mean_adjoint M hswap p, hc]
    simp
  have hgp : 0 < ‖D.cauchyAdjoint M r‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hg)
  have hdiag1 := D.hermitian_diagonal_bound J hJ0 hJ1 M L hM hL hswap hmodL p r hp hpJ
  have hdiag2 := D.hermitian_diagonal_bound J hJ0 hJ1 M R hM hR hswap hmodR q r hq hqJ
  have hortho := D.opposite_adjoint_orthogonal J hJ0 hJ1 M hswap r hr
  have hscaled : inner ℂ ((κ : ℂ) • D.cauchyAdjoint M r)
      (((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))) = 0 := by
    rw [inner_smul_left, inner_smul_right, hortho]
    simp
  rw [norm_sq_add_orthogonal _ _ hscaled] at hblock
  have hnorm : ‖(κ : ℂ) • D.cauchyAdjoint M r‖ ^ 2 =
      κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, mul_pow]
  rw [hnorm] at hblock
  have hmul : κ ^ 2 * ‖D.cauchyAdjoint M r‖ ^ 2 ≤
      4 * ‖D.cauchyAdjoint M r‖ ^ 2 := by
    nlinarith [sq_nonneg (‖((κ⁻¹ : ℝ) : ℂ) • J (D.cauchyAdjoint M (J r))‖)]
  have hs : κ ^ 2 ≤ 4 := le_of_mul_le_mul_right hmul hgp
  nlinarith

end FourierResolution
end

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
lemma scalarFourier_star_zero (u : CircleL2) :
    star (scalarFourier.proj 0 u) = scalarFourier.proj 0 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n <;> by_cases hm : n < 0 <;>
      simp [frequencyPart, hn, hneg, hp, hm]

lemma scalarFourier_star_positive (u : CircleL2) :
    star (scalarFourier.proj 1 u) = scalarFourier.proj 2 (star u) := by
  apply circle_fourier_ext
  intro n
  rw [circle_fourier_star, scalarFourier_coefficient, scalarFourier_coefficient,
    circle_fourier_star]
  by_cases hn : n = 0
  · subst n; simp [frequencyPart]
  · have hneg : -n ≠ 0 := neg_ne_zero.mpr hn
    by_cases hp : 0 < n
    · have hm : ¬ n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]
    · have hm : n < 0 := by omega
      simp [frequencyPart, hn, hneg, hp, hm]

variable {m : Type u_55} [Fintype m] [DecidableEq m]
abbrev MatrixCircleL2 := Lp (HSMatrix m) 2 (@AddCircle.haarAddCircle 1 inferInstance)

def matrixFourier : FourierResolution (MatrixCircleL2 (m := m)) :=
  vectorResolution scalarFourier

lemma coordinate_matrixStar (i j : m) (u : MatrixCircleL2 (m := m)) :
    l2Coordinate (i,j) (l2Star u) = star (l2Coordinate (j,i) u) := by
  apply Lp.ext
  filter_upwards [l2Coordinate_ae (i,j) (l2Star u), l2Coordinate_ae (j,i) u,
    l2StarL_ae u, Lp.coeFn_star (l2Coordinate (j,i) u)] with t hl hr hs hc
  rw [hl, hc, Pi.star_apply, hr]
  change l2StarL u t (i,j) = _
  rw [hs]
  rfl

lemma coordinate_matrixFourier (j : Fin 3) (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (matrixFourier.proj j u) = scalarFourier.proj j (l2Coordinate i u) :=
  coordinate_entrywise _ _ _

lemma matrixFourier_star_zero (u : MatrixCircleL2 (m := m)) :
    l2Star (matrixFourier.proj 0 u) = matrixFourier.proj 0 (l2Star u) := by
  apply l2Coordinate_injective
  rintro ⟨i,j⟩
  rw [coordinate_matrixStar, coordinate_matrixFourier, coordinate_matrixFourier,
    coordinate_matrixStar, scalarFourier_star_zero]

lemma matrixFourier_star_positive (u : MatrixCircleL2 (m := m)) :
    l2Star (matrixFourier.proj 1 u) = matrixFourier.proj 2 (l2Star u) := by
  apply l2Coordinate_injective
  rintro ⟨i,j⟩
  rw [coordinate_matrixStar, coordinate_matrixFourier, coordinate_matrixFourier,
    coordinate_matrixStar, scalarFourier_star_positive]

end

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)
variable {m : Type u_56} [Fintype m] [instDecidableEqM : DecidableEq m]

def matrixM : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m) :=
  K.toMarkovKernel.toCLM

lemma matrixM_norm_le
    (K : CompleteCrouzeix.AnalyticBidiskKernel) {m : Type u_56} [Fintype m] [DecidableEq m] :
    ‖(K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _)‖ ≤ 1 :=
  K.toMarkovKernel.toCLM_norm_le

lemma coordinate_matrixM (u : MatrixCircleL2 (m := m)) (i : m × m) :
    l2Coordinate i (K.matrixM u) = K.scalarM (l2Coordinate i u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (l2Coordinate i u),
    K.toMarkovKernel.applyLp_ae u, l2Coordinate_ae i (K.matrixM u)] with t h1 h2 h3
  rw [h3]
  change (K.toMarkovKernel.applyLp u t) i = K.toMarkovKernel.applyLp (l2Coordinate i u) t
  rw [h1,h2]
  unfold MarkovKernel.applyFun
  change (EuclideanSpace.proj (𝕜 := ℂ) i) (∫ y, K.toMarkovKernel.kernel t y • u y ∂AddCircle.haarAddCircle) = _
  rw [← (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm
    (K.toMarkovKernel.integrable_row_smul u t)]
  apply integral_congr_ae
  filter_upwards [l2Coordinate_ae i u] with s hs
  rw [hs]
  rfl

lemma matrixM_swap : (K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _).comp
    (matrixFourier.proj 1) = (matrixFourier.proj 2).comp K.matrixM := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,
    coordinate_matrixM,coordinate_matrixFourier,coordinate_matrixFourier,coordinate_matrixM]
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L (l2Coordinate i u)) K.scalarM_swap

lemma matrixM_star (u : MatrixCircleL2 (m := m)) :
    K.matrixM (l2Star u) = l2Star (K.matrixM u) := by
  apply l2Coordinate_injective
  rintro ⟨i,j⟩
  rw [coordinate_matrixM,coordinate_matrixStar,coordinate_matrixStar,coordinate_matrixM,
    K.scalarM_star]

end AnalyticBidiskKernel
end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
variable {ι : Type u_57} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

lemma l2_sum_embedding_coordinate (u : V) :
    ∑ i, l2Embedding i (l2Coordinate i u) = u := by
  apply l2Coordinate_injective
  intro j
  simp only [map_sum,coordinate_embedding]
  simp

lemma entrywise_embedding (C : CircleL2 →L[ℂ] CircleL2) (j : ι) (u : CircleL2) :
    entrywiseL2 C (l2Embedding j u) = l2Embedding j (C u) := by
  apply l2Coordinate_injective
  intro i
  rw [coordinate_entrywise,coordinate_embedding,coordinate_embedding]
  split_ifs <;> simp

lemma entrywise_module_of_blocks (C : CircleL2 →L[ℂ] CircleL2) (T : V →L[ℂ] V)
    (h : ∀ i j : ι, C.comp (((l2Coordinate i).comp (T.comp (l2Embedding j))).comp C) =
      ((l2Coordinate i).comp (T.comp (l2Embedding j))).comp C) :
    (entrywiseL2 C).comp (T.comp (entrywiseL2 C)) = T.comp (entrywiseL2 C) := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  change l2Coordinate i (entrywiseL2 C (T (entrywiseL2 C u))) =
    l2Coordinate i (T (entrywiseL2 C u))
  rw [coordinate_entrywise]
  rw [← l2_sum_embedding_coordinate u]
  simp only [map_sum,entrywise_embedding]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun L : CircleL2 →L[ℂ] CircleL2 => L (l2Coordinate j u)) (h i j)

theorem actualExteriorCauchy_vector_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {B : ℂ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : AnalyticOnNhd ℂ B (closure Ω))
    (T : V →L[ℂ] V)
    (hT : ∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => B (exteriorMap a b h t.toCircle) (u t)) :
    (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)).comp
      (T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM))) =
      T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) := by
  apply entrywise_module_of_blocks
  intro i j
  let φ : (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →L[ℂ] ℂ :=
    (EuclideanSpace.proj i).comp ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ ι))
      (EuclideanSpace.single j 1))
  have hφ : AnalyticOnNhd ℂ (fun z => φ (B z)) (closure Ω) :=
    (φ.analyticOnNhd univ).comp hB (mapsTo_univ _ _)
  apply actualExteriorCauchy_module hR ha hh hi hd hsupport hΩ hcv hboundary houtside hinner hφ
  intro u
  filter_upwards [l2Coordinate_ae i (T (l2Embedding j u)),hT (l2Embedding j u),
    l2Embedding_ae j u] with t hcoord hTt hemb
  change l2Coordinate i (T (l2Embedding j u)) t = _
  rw [hcoord,hTt,hemb]
  have he : EuclideanSpace.single j (u t) = u t • EuclideanSpace.single j (1:ℂ) := by
    ext k
    simp only [PiLp.single_apply,PiLp.smul_apply,smul_eq_mul]
    split_ifs <;> simp
  rw [he,map_smul]
  change u t * φ (B (exteriorMap a b h t.toCircle)) = _
  exact mul_comm _ _

end

open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma matrixCauchy_eq_entrywise {m : Type u_58} [Fintype m] [DecidableEq m]
    (K : AnalyticBidiskKernel) :
    (matrixFourier.cauchy K.matrixM : MatrixCircleL2 (m := m) →L[ℂ] _) =
      entrywiseL2 (scalarFourier.cauchy K.scalarM) := by
  ext1 u
  apply l2Coordinate_injective
  intro i
  simp only [FourierResolution.cauchy,add_apply,ContinuousLinearMap.comp_apply,
    map_add,coordinate_matrixFourier,K.coordinate_matrixM,coordinate_entrywise]

section ActualFields
variable {ι : Type u_59} [Fintype ι] [DecidableEq ι]
local notation "V" => VectorL2 (μ := @AddCircle.haarAddCircle 1 inferInstance) (ι := ι)

theorem actualExteriorCauchy_field_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {B : ℂ → EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι}
    (hB : AnalyticOnNhd ℂ B (closure Ω))
    (hn : ∀ t : UnitAddCircle, ‖B (exteriorMap a b h t.toCircle)‖ ≤ 1) :
    ∃ T : V →L[ℂ] V, ‖T‖ ≤ 1 ∧
      (∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
        fun t => B (exteriorMap a b h t.toCircle) (u t)) ∧
      (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)).comp
        (T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM))) =
        T.comp (entrywiseL2 (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) := by
  have hb : MapsTo (exteriorMap a b h) (sphere 0 1) (closure Ω) := by
    intro t ht
    apply frontier_subset_closure
    rw [← hboundary]
    exact mem_image_of_mem _ ht
  have hBcont : Continuous (fun t : UnitAddCircle => B (exteriorMap a b h t.toCircle)) :=
    (hB.comp (exteriorMap_circle_analytic hR hh) hb).continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)
  let T : V →L[ℂ] V := pointwiseL2L (fun t : UnitAddCircle => B (exteriorMap a b h t.toCircle))
    hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  have hT : ∀ u : V, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => B (exteriorMap a b h t.toCircle) (u t) :=
    fun u => pointwiseL2_ae _ hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn) u
  exact ⟨T,pointwiseL2L_norm _ hBcont.aestronglyMeasurable (Filter.Eventually.of_forall hn),hT,
    actualExteriorCauchy_vector_module hR ha hh hi hd hsupport hΩ hcv hboundary houtside hinner hB T hT⟩

end ActualFields

theorem actualExteriorCauchy_ordered_modules {m : Type u_60} [Fintype m] [DecidableEq m]
    {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    (hboundary : exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (hinner : MapsTo (exteriorMap a b h) ({t | R⁻¹ < ‖t‖} ∩ ball 0 1) (closure Ω))
    {F : ℂ → Matrix m m ℂ} (hF : AnalyticOnNhd ℂ F (closure Ω))
    (hn : ∀ t : UnitAddCircle, ‖F (exteriorMap a b h t.toCircle)‖ ≤ 1) :
    let C : MatrixCircleL2 (m := m) →L[ℂ] _ :=
      matrixFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).matrixM
    ∃ L R : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m),
      ‖L‖ ≤ 1 ∧ ‖R‖ ≤ 1 ∧
      (∀ u, L u =ᵐ[AddCircle.haarAddCircle]
        fun t => toHS (F (exteriorMap a b h t.toCircle)*fromHS (u t))) ∧
      (∀ u, R u =ᵐ[AddCircle.haarAddCircle]
        fun t => toHS (fromHS (u t)*F (exteriorMap a b h t.toCircle))) ∧
      C.comp (L.comp C) = L.comp C ∧ C.comp (R.comp C) = R.comp C := by
  let BL := fun z => hsLeft (F z)
  let BR := fun z => hsRight (F z)
  have hBL : AnalyticOnNhd ℂ BL (closure Ω) :=
    ((hsLeftL (m := m)).analyticOnNhd univ).comp hF (mapsTo_univ _ _)
  have hBR : AnalyticOnNhd ℂ BR (closure Ω) :=
    ((hsRightL (m := m)).analyticOnNhd univ).comp hF (mapsTo_univ _ _)
  obtain ⟨L,hLn,hLa,hLC⟩ := actualExteriorCauchy_field_module hR ha hh hi hd hsupport
    hΩ hcv hboundary houtside hinner hBL (fun t => hsLeft_norm (hn t))
  obtain ⟨T,hTn,hTa,hTC⟩ := actualExteriorCauchy_field_module hR ha hh hi hd hsupport
    hΩ hcv hboundary houtside hinner hBR (fun t => hsRight_norm (hn t))
  refine ⟨L,T,hLn,hTn,hLa,hTa,?_,?_⟩
  · simpa only [matrixCauchy_eq_entrywise] using hLC
  · simpa only [matrixCauchy_eq_entrywise] using hTC

end CompleteCrouzeix

end

end OAI
