import OAI.Analysis.NumericalRange.MarkovOperator

namespace OAI

noncomputable section

universe u_40 u_41 u_42 u_43

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace

open scoped ComplexConjugate InnerProductSpace
namespace CompleteCrouzeix

section

section

variable {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

structure FourierResolution (E : Type u_41) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  proj : Fin 3 → E →L[ℂ] E
  selfAdjoint : ∀ i, (proj i).adjoint = proj i
  product : ∀ i j, (proj i).comp (proj j) = if i = j then proj i else 0
  total : proj 0 + proj 1 + proj 2 = ContinuousLinearMap.id ℂ E

lemma norm_sq_add_orthogonal
    {E : Type u_40} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (x y : E)
    (h : inner ℂ x y = 0) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h

namespace FourierResolution
variable (D : FourierResolution E)

lemma decompose (u : E) : D.proj 0 u + D.proj 1 u + D.proj 2 u = u := by
  exact congrArg (fun T : E →L[ℂ] E => T u) D.total

@[simp] lemma proj_proj (i j : Fin 3) (u : E) :
    D.proj i (D.proj j u) = if i = j then D.proj i u else 0 := by
  have h := congrArg (fun T : E →L[ℂ] E => T u) (D.product i j)
  split_ifs with hij <;> simpa [hij] using h

lemma orthogonal (i j : Fin 3) (hij : i ≠ j) (u v : E) :
    inner ℂ (D.proj i u) (D.proj j v) = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, D.selfAdjoint, D.proj_proj]
  simp [hij]

lemma norm_decompose (u : E) :
    ‖u‖ ^ 2 = ‖D.proj 0 u‖ ^ 2 + ‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2 := by
  conv_lhs => rw [← D.decompose u]
  rw [norm_sq_add_orthogonal]
  · rw [norm_sq_add_orthogonal]
    exact D.orthogonal 0 1 (by decide) u u
  · rw [inner_add_left, D.orthogonal 0 2 (by decide), D.orthogonal 1 2 (by decide)]
    simp

def cauchy (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.comp (D.proj 1)

def cauchyAdjoint (M : E →L[ℂ] E) : E →L[ℂ] E :=
  D.proj 0 + D.proj 1 + M.adjoint.comp (D.proj 2)

lemma adjoint_cauchy (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.cauchy M).adjoint = D.cauchyAdjoint M := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simp only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] at h
  simp only [cauchy, cauchyAdjoint, map_add, ContinuousLinearMap.adjoint_comp,
    D.selfAdjoint, h]

lemma adjoint_markov_swap (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) :
    (D.proj 1).comp M.adjoint = M.adjoint.comp (D.proj 2) := by
  have h := congrArg ContinuousLinearMap.adjoint hswap
  simpa only [ContinuousLinearMap.adjoint_comp, D.selfAdjoint] using h

lemma adjoint_apply (M : E →L[ℂ] E) (u : E) :
    D.cauchyAdjoint M u = D.proj 0 u + D.proj 1 u + M.adjoint (D.proj 2 u) := rfl

lemma adjoint_positive (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    M.adjoint (D.proj 2 u) = D.proj 1 (M.adjoint u) := by
  exact (congrArg (fun T : E →L[ℂ] E => T u) (D.adjoint_markov_swap M hswap)).symm

lemma mean_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 0 (D.cauchyAdjoint M u) = D.proj 0 u := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp

lemma negative_adjoint (M : E →L[ℂ] E)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    D.proj 2 (D.cauchyAdjoint M u) = 0 := by
  rw [D.adjoint_apply, D.adjoint_positive M hswap]
  simp only [map_add, D.proj_proj]
  simp [Fin.ext_iff]

theorem weighted_adjoint_bound (M : E →L[ℂ] E) (hM : ‖M‖ ≤ 1)
    (hswap : M.comp (D.proj 1) = (D.proj 2).comp M) (u : E) :
    ‖D.cauchyAdjoint M u‖ ^ 2 + ‖D.proj 0 u‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 := by
  have hd : ‖M.adjoint (D.proj 2 u)‖ ≤ ‖D.proj 2 u‖ := by
    calc _ ≤ ‖M.adjoint‖ * ‖D.proj 2 u‖ := M.adjoint.le_opNorm _
      _ ≤ 1 * ‖D.proj 2 u‖ := by
        gcongr
        simpa using hM
      _ = _ := one_mul _
  have hadd : ‖D.proj 1 u + M.adjoint (D.proj 2 u)‖ ^ 2 ≤
      2 * (‖D.proj 1 u‖ ^ 2 + ‖D.proj 2 u‖ ^ 2) := by
    have htri := norm_add_le (D.proj 1 u) (M.adjoint (D.proj 2 u))
    have h1 := norm_nonneg (D.proj 1 u)
    have h2 := norm_nonneg (M.adjoint (D.proj 2 u))
    have h3 := norm_nonneg (D.proj 2 u)
    have h4 := norm_nonneg (D.proj 1 u + M.adjoint (D.proj 2 u))
    nlinarith [sq_nonneg (‖D.proj 1 u‖ - ‖D.proj 2 u‖)]
  have horth : inner ℂ (D.proj 0 u)
      (D.proj 1 u + M.adjoint (D.proj 2 u)) = 0 := by
    rw [D.adjoint_positive M hswap, inner_add_right,
      D.orthogonal 0 1 (by decide), D.orthogonal 0 1 (by decide)]
    simp
  rw [D.adjoint_apply, add_assoc,
    norm_sq_add_orthogonal _ _ horth,
    D.norm_decompose u]
  linarith

end FourierResolution
end

open scoped lp
variable {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

def modeMask (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) : ℓ²(ι, ℂ) :=
  ⟨fun n => if c n = j then u n else 0, (lp.memℓp u).mono' (by
    intro n; split_ifs <;> simp)⟩

@[simp] lemma modeMask_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMask c j u n = if c n = j then u n else 0 := rfl

lemma modeMask_norm (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) :
    ‖modeMask c j u‖ ≤ ‖u‖ := by
  apply lp.norm_mono (by norm_num)
  intro n
  simp only [modeMask_apply]
  split_ifs <;> simp

def modeMaskL (c : ι → Fin 3) (j : Fin 3) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  LinearMap.mkContinuous
  { toFun := modeMask c j
    map_add' u v := by ext n; simp only [modeMask_apply, lp.coeFn_add, Pi.add_apply]; split_ifs <;> simp
    map_smul' a u := by ext n; simp only [modeMask_apply, lp.coeFn_smul, Pi.smul_apply]; split_ifs <;> simp }
    1 (by intro u; simpa using modeMask_norm c j u)

@[simp] lemma modeMaskL_apply (c : ι → Fin 3) (j : Fin 3) (u : ℓ²(ι, ℂ)) (n : ι) :
    modeMaskL c j u n = if c n = j then u n else 0 := rfl

lemma modeMaskL_adjoint (c : ι → Fin 3) (j : Fin 3) :
    (modeMaskL c j).adjoint = modeMaskL c j := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [modeMaskL_apply]
  split_ifs <;> simp

def basisProjection (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) (j : Fin 3) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((modeMaskL c j).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] lemma basisProjection_repr
    {ι : Type u_42} {E : Type u_43} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u : E) (n : ι) :
    b.repr (basisProjection b c j u) n = if c n = j then b.repr u n else 0 := by
  simp [basisProjection]

lemma basisProjection_inner (b : HilbertBasis ι ℂ E) (c : ι → Fin 3)
    (j : Fin 3) (u v : E) :
    inner ℂ (basisProjection b c j u) v = inner ℂ u (basisProjection b c j v) := by
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map]
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [basisProjection_repr]
  split_ifs <;> simp

def basisResolution (b : HilbertBasis ι ℂ E) (c : ι → Fin 3) : FourierResolution E where
  proj := basisProjection b c
  selfAdjoint i := by
    symm
    exact (ContinuousLinearMap.eq_adjoint_iff _ _).mpr (basisProjection_inner b c i)
  product i j := by
    ext u
    apply b.repr.injective
    ext n
    by_cases hij : i = j
    · subst j
      simp only [ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i <;> simp [hc]
    · simp only [ite_eq_right hij, zero_apply, map_zero, lp.coeFn_zero, Pi.zero_apply,
        ContinuousLinearMap.comp_apply, basisProjection_repr]
      by_cases hc : c n = i
      · simp [hc, hij]
      · simp [hc]

  total := by
    ext u
    apply b.repr.injective
    ext n
    simp only [add_apply, map_add, lp.coeFn_add, Pi.add_apply,
      basisProjection_repr, ContinuousLinearMap.id_apply]
    have h : c n = 0 ∨ c n = 1 ∨ c n = 2 := by omega
    rcases h with h | h | h <;> simp [h]

def frequencyPart (n : ℤ) : Fin 3 := if n = 0 then 0 else if 0 < n then 1 else 2

open MeasureTheory
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
abbrev CircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle 1 inferInstance)

def scalarFourier : FourierResolution CircleL2 :=
  basisResolution fourierBasis frequencyPart

lemma scalarFourier_coefficient (j : Fin 3) (u : CircleL2) (n : ℤ) :
    fourierCoeff (scalarFourier.proj j u) n =
      if frequencyPart n = j then fourierCoeff u n else 0 := by
  simpa only [← fourierBasis_repr, scalarFourier, basisResolution] using
    basisProjection_repr (E := CircleL2) fourierBasis frequencyPart j u n

end

open MeasureTheory ComplexConjugate
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma circle_fourier_ext {u v : CircleL2}
    (h : ∀ n : ℤ, fourierCoeff u n = fourierCoeff v n) : u = v := by
  apply fourierBasis.repr.injective
  apply lp.ext
  funext n
  simpa only [fourierBasis_repr] using h n

lemma circle_fourier_star (u : CircleL2) (n : ℤ) :
    fourierCoeff (star u : CircleL2) n = star (fourierCoeff u (-n)) := by
  rw [fourierCoeff, fourierCoeff]
  change _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  simp only [ht, Pi.star_apply, smul_eq_mul, map_mul, neg_neg,
    fourier_neg, RCLike.star_def]

lemma integral_fourier_nonzero (n : ℤ) (hn : n ≠ 0) :
    (∫ t : UnitAddCircle, fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simpa [fourierCoeff, Pi.single_eq_of_ne hn.symm] using h

lemma scalarFourier_fourier (j : Fin 3) (n : ℤ) :
    scalarFourier.proj j (fourierLp 2 n) =
      if frequencyPart n = j then fourierLp 2 n else 0 := by
  apply circle_fourier_ext
  intro k
  rw [scalarFourier_coefficient]
  have hf : fourierCoeff (fourierLp 2 n : CircleL2) k = (Pi.single n (1 : ℂ) : ℤ → ℂ) k := by
    rw [fourierCoeff_congr_ae (coeFn_fourierLp 2 n), fourierCoeff_fourier]
  by_cases h : frequencyPart n = j
  · simp only [h, ite_true, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]
  · have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    simp only [h, ite_false, hz, hf]
    by_cases hkn : k = n
    · subst k; simp [h]
    · simp [Pi.single_eq_of_ne hkn]

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

def scalarM : CircleL2 →L[ℂ] CircleL2 := K.toMarkovKernel.toCLM

lemma kernel_complex (w t : UnitAddCircle) :
    (K.kernel w t : ℂ) = 1 + K.circleB w t + conj (K.circleB w t) := by
  apply Complex.ext <;> simp [kernel, Complex.add_re, Complex.add_im]; ring

lemma scalarM_fourier_ae (n : ℤ) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, (K.kernel w t : ℂ) * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.toMarkovKernel.applyLp_ae (fourierLp 2 n : CircleL2)] with w hw
  refine hw.trans ?_
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 n] with t ht
  rw [ht]
  rfl

lemma scalarM_fourier_positive_ae (n : ℤ) (hn : 0 < n) :
    K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => ∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle := by
  filter_upwards [K.scalarM_fourier_ae n] with w hw
  rw [hw]
  simp_rw [K.kernel_complex, add_mul, one_mul]
  have hB : Continuous (fun t => K.circleB w t * fourier n t) :=
    (K.continuous_circleB.comp (continuous_const.prodMk continuous_id)).mul
      (fourier n).continuous
  have hBc : Continuous (fun t => conj (K.circleB w t) * fourier n t) :=
    (Complex.continuous_conj.comp
      (K.continuous_circleB.comp (continuous_const.prodMk continuous_id))).mul
      (fourier n).continuous
  have hint (f : UnitAddCircle → ℂ) (hf : Continuous f) :
      Integrable f AddCircle.haarAddCircle :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he₁ : (∫ t, fourier n t + K.circleB w t * fourier n t +
      conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add ((hint _ (fourier n).continuous).add (hint _ hB)) (hint _ hBc)
  have he₂ : (∫ t, fourier n t + K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) =
      (∫ t, fourier n t ∂AddCircle.haarAddCircle) +
      (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) :=
    integral_add (hint _ (fourier n).continuous) (hint _ hB)
  rw [he₁, he₂,
    integral_fourier_nonzero n (ne_of_gt hn),
    K.conj_circleB_right_nonneg_fourier w n (le_of_lt hn), zero_add, add_zero]

lemma scalarM_fourier_positive_coefficient (n k : ℤ) (hn : 0 < n) (hk : 0 ≤ k) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  rw [fourierCoeff_congr_ae (K.scalarM_fourier_positive_ae n hn), fourierCoeff]
  simp only [smul_eq_mul]
  simp_rw [← integral_const_mul]
  have hc : Continuous (fun p : UnitAddCircle × UnitAddCircle =>
      fourier (-k) p.1 * (K.circleB p.1 p.2 * fourier n p.2)) :=
    ((fourier (-k)).continuous.comp continuous_fst).mul
      (K.continuous_circleB.mul ((fourier n).continuous.comp continuous_snd))
  rw [integral_integral_swap
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have hz (t : UnitAddCircle) :
      (∫ w, fourier (-k) w * (K.circleB w t * fourier n t)
        ∂AddCircle.haarAddCircle) = 0 := by
    simp_rw [show ∀ w, fourier (-k) w * (K.circleB w t * fourier n t) =
      (K.circleB w t * fourier (-k) w) * fourier n t from fun w => by ring]
    rw [integral_mul_const, K.circleB_left_nonpos_fourier t (-k) (by omega), zero_mul]
  simp_rw [hz, integral_zero]

lemma scalarM_star (u : CircleL2) : K.scalarM (star u) = star (K.scalarM u) := by
  apply Lp.ext
  filter_upwards [K.toMarkovKernel.applyLp_ae (star u),
    K.toMarkovKernel.applyLp_ae u, Lp.coeFn_star (K.scalarM u)] with w hs hu hstar
  change K.toMarkovKernel.applyLp (star u) w = _
  rw [hs,hstar]
  change K.toMarkovKernel.applyFun (star u) w = conj (K.toMarkovKernel.applyLp u w)
  rw [hu]
  unfold MarkovKernel.applyFun
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star u] with t ht
  rw [ht]
  change (K.kernel w t : ℂ) * conj (u t) = conj ((K.kernel w t : ℂ) * u t)
  simp

lemma star_fourierLp (n : ℤ) :
    star (fourierLp 2 n : CircleL2) = fourierLp 2 (-n) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (fourierLp 2 n : CircleL2),
    coeFn_fourierLp 2 n, coeFn_fourierLp 2 (-n)] with t hs hn hneg
  simp only [hs,Pi.star_apply,hn,hneg,fourier_neg,RCLike.star_def]

lemma scalarM_fourier_negative_coefficient (n k : ℤ) (hn : n < 0) (hk : k ≤ 0) :
    fourierCoeff (K.scalarM (fourierLp 2 n)) k = 0 := by
  have he : (fourierLp 2 n : CircleL2) = star (fourierLp 2 (-n) : CircleL2) := by
    simpa only [neg_neg] using (star_fourierLp (-n)).symm
  rw [he,K.scalarM_star,circle_fourier_star,
    K.scalarM_fourier_positive_coefficient (-n) (-k) (by omega) (by omega),star_zero]

lemma scalarM_fourier_zero : K.scalarM (fourierLp 2 0) = fourierLp 2 0 := by
  have he : (fourierLp 2 0 : CircleL2) = Lp.const 2 AddCircle.haarAddCircle 1 := by
    apply Lp.ext
    filter_upwards [coeFn_fourierLp 2 0,
      Lp.coeFn_const (p := 2) (μ := AddCircle.haarAddCircle) (1 : ℂ)] with t hf hc
    rw [hf,hc]
    simp
  rw [he]
  exact K.toMarkovKernel.toCLM_const 1

lemma scalarM_fourier_swap (n : ℤ) :
    K.scalarM (scalarFourier.proj 1 (fourierLp 2 n)) =
      scalarFourier.proj 2 (K.scalarM (fourierLp 2 n)) := by
  rw [scalarFourier_fourier]
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hfn : frequencyPart n ≠ 1 := by simp [frequencyPart,hn.ne,not_lt.mpr hn.le]
    simp only [hfn,ite_false,map_zero]
    apply circle_fourier_ext
    intro k
    have hz : fourierCoeff (0 : CircleL2) k = 0 := by
      rw [fourierCoeff_congr_ae (Lp.coeFn_zero _ _ _)]
      simp [fourierCoeff]
    rw [hz,scalarFourier_coefficient]
    split_ifs with hfk
    · have hk : k < 0 := by
        unfold frequencyPart at hfk
        split_ifs at hfk with h0 hp <;> simp_all
        omega
      exact (K.scalarM_fourier_negative_coefficient n k hn hk.le).symm
    · rfl
  · subst n
    rw [K.scalarM_fourier_zero,scalarFourier_fourier]
    simp [frequencyPart]
  · have hfn : frequencyPart n = 1 := by simp [frequencyPart,hn.ne',hn]
    simp only [hfn,ite_true]
    apply circle_fourier_ext
    intro k
    rw [scalarFourier_coefficient]
    split_ifs with hfk
    · rfl
    · have hk : 0 ≤ k := by
        by_contra hk
        have hk' : k < 0 := by omega
        exact hfk (by simp [frequencyPart,hk'.ne,not_lt.mpr hk'.le])
      exact K.scalarM_fourier_positive_coefficient n k hn hk

lemma scalarM_swap : K.scalarM.comp (scalarFourier.proj 1) =
    (scalarFourier.proj 2).comp K.scalarM := by
  apply ContinuousLinearMap.ext_on (s := Set.range (fourierLp (T := 1) 2))
  · change ∀ x, x ∈ closure (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2)) : Set CircleL2)
    change ∀ x, x ∈ (Submodule.span ℂ (Set.range (fourierLp (T := 1) 2))).topologicalClosure
    rw [span_fourierLp_closure_eq_top (by norm_num : (2 : ENNReal) ≠ ∞)]
    intro x; trivial
  · rintro _ ⟨n,rfl⟩
    exact K.scalarM_fourier_swap n

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
