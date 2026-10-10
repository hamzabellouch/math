import OAI.Analysis.NumericalRange.ExteriorProjection

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_46 u_47

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

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem physicalCauchy_extension {G : ℂ → ℂ} {U Ω : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hΩ : IsOpen Ω) (hboundary : frontier Ω ⊆ G '' sphere 0 1)
    (houtside : ∀ t ∈ U, G t ∈ Ω → t ∈ ball 0 1)
    (hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω)
    {u : UnitAddCircle → ℂ} (hu : Continuous u) {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q U)
    (he : ∀ w ∈ U ∩ ball 0 1, physicalCauchy G u (G w) =
      q w + cauchyCorrectionIntegral G u w) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy G u) Ω ∧
      ∀ t ∈ sphere (0:ℂ) 1, v (G t) = q t + cauchyCorrectionIntegral G u t := by
  obtain ⟨ho,g,hg,hgU,hgf,hfg⟩ := noncritical_holomorphic_inverse hU hG hi hd
  have hp : AnalyticOnNhd ℂ (physicalCauchy G u) Ω :=
    physicalCauchy_analytic (hG.mono hTU) hu hΩ (by
      intro z hz t he
      exact hdis t.toCircle t.toCircle.property (he ▸ hz))
  have hc := cauchyCorrectionIntegral_analytic hU hG hi hd hTU hu
  let f := fun z => q (g z) + cauchyCorrectionIntegral G u (g z)
  have hf : AnalyticOnNhd ℂ f (G '' U) := (hq.comp hg hgU).add (hc.comp hg hgU)
  obtain ⟨v,hv,hvp,hvf⟩ := analytic_open_gluing hΩ ho hp hf (by
    intro z hz
    have hw := hgU hz.2
    have hgz := hfg z hz.2
    have hwi : g z ∈ ball 0 1 := houtside (g z) hw (by rw [hgz]; exact hz.1)
    dsimp [f]
    rw [← he (g z) ⟨hw,hwi⟩,hgz])
  refine ⟨v,hv.mono ?_,hvp,?_⟩
  · intro z hz
    by_cases hi : z ∈ Ω
    · exact Or.inl hi
    · have hz' : z ∈ frontier Ω := by
        rw [frontier,Set.mem_sdiff]
        exact ⟨hz,by simpa only [hΩ.interior_eq] using hi⟩
      obtain ⟨t,ht,rfl⟩ := hboundary hz'
      exact Or.inr ⟨t,hTU ht,rfl⟩
  · intro t ht
    rw [hvf ⟨t,hTU ht,rfl⟩]
    dsimp [f]
    rw [hgf t (hTU ht)]

theorem physicalCauchy_fourier_extension {G : ℂ → ℂ} {U Ω : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) (hi : InjOn G U)
    (hd : ∀ w ∈ U, deriv G w ≠ 0) (hTU : sphere 0 1 ⊆ U)
    (hΩ : IsOpen Ω) (hboundary : frontier Ω ⊆ G '' sphere 0 1)
    (houtside : ∀ t ∈ U, G t ∈ Ω → t ∈ ball 0 1)
    (hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω) (n : ℤ) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy G (fourier n)) Ω ∧
      ∀ t : UnitAddCircle, v (G t.toCircle) =
        (if 0 ≤ n then fourier n t else 0) +
          cauchyCorrectionIntegral G (fourier n) t.toCircle := by
  have he : ∃ q : ℂ → ℂ, AnalyticOnNhd ℂ q U ∧
      (∀ w ∈ U ∩ ball 0 1, physicalCauchy G (fourier n) (G w) =
        q w + cauchyCorrectionIntegral G (fourier n) w) ∧
      ∀ t : UnitAddCircle, q t.toCircle = if 0 ≤ n then fourier n t else 0 := by
    rcases n with n | n
    · refine ⟨fun w => w^n,analyticOnNhd_id.pow n,?_,?_⟩
      · intro w hw
        have hf : (fourier (Int.ofNat n) : UnitAddCircle → ℂ) =
            (fun t => (t.toCircle : ℂ)^n) := funext (fourier_natCast_toCircle n)
        rw [hf]
        exact physicalCauchy_pow hU hG hi hd hTU n hw.1 hw.2
      · intro t
        change (t.toCircle : ℂ)^n = if 0 ≤ (n:ℤ) then fourier (n:ℤ) t else 0
        rw [ite_eq_left (Int.natCast_nonneg n),fourier_natCast_toCircle]
    · refine ⟨fun _ => 0,analyticOnNhd_const,?_,?_⟩
      · intro w hw
        have hn : Int.negSucc n = -((n+1 : ℕ) : ℤ) := by omega
        rw [hn]
        have hf : (fourier (-((n+1:ℕ):ℤ)) : UnitAddCircle → ℂ) =
            (fun t => ((t.toCircle : ℂ)⁻¹)^(n+1)) :=
          funext (fourier_neg_natCast_toCircle (n+1))
        rw [hf,zero_add]
        exact physicalCauchy_inv_pow hU hG hi hd hTU (Nat.succ_ne_zero n) hw.1 hw.2
      · intro t
        rw [ite_eq_right (by omega : ¬0 ≤ Int.negSucc n)]
  obtain ⟨q,hq,he,hqt⟩ := he
  obtain ⟨v,hv,hvp,hvt⟩ := physicalCauchy_extension hU hG hi hd hTU hΩ hboundary
    houtside hdis (map_continuous (fourier n)) hq he
  exact ⟨v,hv,hvp,fun t => by rw [hvt t.toCircle t.toCircle.property,hqt t]⟩

end

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma scalarCauchy_fourier_ae (K : AnalyticBidiskKernel) (n : ℤ) :
    scalarFourier.cauchy K.scalarM (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
      fun w => (if 0 ≤ n then fourier n w else 0) +
        ∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle := by
  let u : CircleL2 := fourierLp 2 n
  have hlo : scalarFourier.proj 0 u + scalarFourier.proj 1 u =
      if 0 ≤ n then u else 0 := by
    dsimp [u]
    rw [scalarFourier_fourier,scalarFourier_fourier]
    rcases lt_trichotomy n 0 with hn | hn | hn
    · simp [frequencyPart,hn.ne,not_lt.mpr hn.le,not_le.mpr hn]
    · simp [hn,frequencyPart]
    · simp [frequencyPart,hn.ne',hn,hn.le]
  have he : scalarFourier.cauchy K.scalarM u =
      (if 0 ≤ n then u else 0) + K.scalarM (scalarFourier.proj 1 u) := by
    change scalarFourier.proj 0 u + scalarFourier.proj 1 u + _ = _
    rw [hlo]
    rfl
  rw [show fourierLp 2 n = u from rfl,he]
  filter_upwards [Lp.coeFn_add (if 0 ≤ n then u else 0)
    (K.scalarM (scalarFourier.proj 1 u)),coeFn_fourierLp 2 n,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := AddCircle.haarAddCircle),
    K.scalarM_positive_ae u] with w hadd hu hz hM
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hM]
  congr 1
  · split_ifs <;> assumption
  · apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 n] with t ht
    rw [show u t = fourier n t from ht]

def physicalAnalyticTrace {G : ℂ → ℂ} {Ω : Set ℂ}
    (hG : AnalyticOnNhd ℂ G (sphere 0 1))
    (hboundary : MapsTo G (sphere 0 1) (closure Ω))
    (v : ℂ → ℂ) (hv : AnalyticOnNhd ℂ v (closure Ω)) : C(UnitAddCircle,ℂ) :=
  ⟨fun t => v (G t.toCircle), (hv.comp hG hboundary).continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)⟩

theorem actualExteriorCauchy_fourier_trace {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (ha : a ≠ 0) (hh : AnalyticOnNhd ℂ h (ball 0 R))
    (hi : InjOn (exteriorMap a b h) {t | R⁻¹ < ‖t‖})
    (hd : ∀ t, R⁻¹ < ‖t‖ → deriv (exteriorMap a b h) t ≠ 0)
    (hsupport : ∀ w t : Circle,
      0 ≤ (conj ((t : ℂ)*deriv (exteriorMap a b h) t)*
        (exteriorMap a b h t-exteriorMap a b h w)).re)
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (hboundary :
      exteriorMap a b h '' sphere 0 1 = frontier Ω)
    (houtside : ∀ t, R⁻¹ < ‖t‖ → exteriorMap a b h t ∈ Ω → t ∈ ball 0 1)
    (n : ℤ) :
    ∃ v : ℂ → ℂ, AnalyticOnNhd ℂ v (closure Ω) ∧
      EqOn v (physicalCauchy (exteriorMap a b h) (fourier n)) Ω ∧
      scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
        (fourierLp 2 n) =ᵐ[AddCircle.haarAddCircle]
          fun t => v (exteriorMap a b h t.toCircle) := by
  let G := exteriorMap a b h
  let U : Set ℂ := {t | R⁻¹ < ‖t‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hG : AnalyticOnNhd ℂ G U := analyticOnNhd_exteriorMap (lt_trans zero_lt_one hR) hh
  have hTU : sphere (0:ℂ) 1 ⊆ U := by
    intro t ht
    change R⁻¹ < ‖t‖
    rw [mem_sphere_zero_iff_norm.mp ht]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR
  have hdis : ∀ t ∈ sphere (0:ℂ) 1, G t ∉ Ω := by
    intro t ht
    have hm : G t ∈ frontier Ω := hboundary ▸ mem_image_of_mem G ht
    simpa only [frontier,hΩ.interior_eq,Set.mem_sdiff] using hm.2
  obtain ⟨v,hv,hvp,hvt⟩ := physicalCauchy_fourier_extension hU hG hi hd hTU hΩ
    (by rw [← hboundary]) houtside hdis n
  refine ⟨v,hv,hvp,?_⟩
  filter_upwards [scalarCauchy_fourier_ae (actualExteriorKernel hR ha hh hi hd hsupport) n]
    with w hw
  rw [hw,hvt]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with point
  rw [actualExteriorKernel_circleB hR ha hh hi hd hsupport]
  exact mul_comm _ _

end

section
open Set Metric Complex MeasureTheory
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

lemma exteriorMap_circle_analytic {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
    (hR : 1 < R) (hh : AnalyticOnNhd ℂ h (ball 0 R)) :
    AnalyticOnNhd ℂ (exteriorMap a b h) (sphere 0 1) := by
  apply (analyticOnNhd_exteriorMap (a := a) (b := b) (lt_trans zero_lt_one hR) hh).mono
  intro t ht
  change R⁻¹ < ‖t‖
  rw [mem_sphere_zero_iff_norm.mp ht]
  exact (inv_lt_one₀ (lt_trans zero_lt_one hR)).mpr hR

theorem actualExteriorCauchy_module {a b : ℂ} {h : ℂ → ℂ} {R : ℝ}
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
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closure Ω))
    (T : CircleL2 →L[ℂ] CircleL2)
    (hT : ∀ u : CircleL2, T u =ᵐ[AddCircle.haarAddCircle]
      fun t => f (exteriorMap a b h t.toCircle)*u t) :
    (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM).comp
      (T.comp (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM)) =
      T.comp (scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM) := by
  let G := exteriorMap a b h
  let C := scalarFourier.cauchy (actualExteriorKernel hR ha hh hi hd hsupport).scalarM
  have hG : AnalyticOnNhd ℂ G (sphere 0 1) := exteriorMap_circle_analytic hR hh
  have hb : MapsTo G (sphere 0 1) (closure Ω) := by
    intro t ht
    apply frontier_subset_closure
    rw [← hboundary]
    exact mem_image_of_mem G ht
  apply circleCLM_ext
  intro n
  change C (T (C (fourierLp 2 n))) = T (C (fourierLp 2 n))
  obtain ⟨v,hv,_,hvt⟩ := actualExteriorCauchy_fourier_trace hR ha hh hi hd hsupport
    hΩ hboundary houtside n
  let u := physicalAnalyticTrace hG hb (fun z => f z*v z) (hf.mul hv)
  have hTu : T (C (fourierLp 2 n)) = ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ u := by
    apply Lp.ext
    filter_upwards [hT (C (fourierLp 2 n)),hvt,
      ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (p := 2) (𝕜 := ℂ) u]
      with t hTt hvt hut
    rw [hTt,hvt,hut]
    rfl
  rw [hTu]
  exact actualExteriorCauchy_fix_trace hR ha hh hi hd hsupport hcv.closure hb hinner
    (hf.mul hv) u (fun _ => rfl)

end

open MeasureTheory
variable {α : Type u_46} {ι : Type u_47} [MeasurableSpace α] {μ : Measure α}
  [Fintype ι] [instDecidableEqΙ : DecidableEq ι]

abbrev VectorL2 := Lp (EuclideanSpace ℂ ι) 2 μ

def l2Coordinate (i : ι) : VectorL2 (μ := μ) (ι := ι) →L[ℂ] Lp ℂ 2 μ :=
  (EuclideanSpace.proj i).compLpL 2 μ

def singleCLM (i : ι) : ℂ →L[ℂ] EuclideanSpace ℂ ι :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single i 1)

@[simp] lemma singleCLM_apply (i : ι) (z : ℂ) :
    singleCLM i z = EuclideanSpace.single i z := by
  ext k
  by_cases h : k = i <;> simp [singleCLM, h]

def l2Embedding (i : ι) : Lp ℂ 2 μ →L[ℂ] VectorL2 (μ := μ) (ι := ι) :=
  (singleCLM i).compLpL 2 μ

lemma l2Coordinate_ae
    {α : Type u_46} {ι : Type u_47} [MeasurableSpace α] {μ : Measure α}
    [Fintype ι] [DecidableEq ι] (i : ι) (u : VectorL2 (μ := μ) (ι := ι)) :
    l2Coordinate i u =ᵐ[μ] fun t => u t i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL u

lemma l2Embedding_ae (i : ι) (u : Lp ℂ 2 μ) :
    l2Embedding i u =ᵐ[μ] fun t => EuclideanSpace.single i (u t) := by
  simpa only [l2Embedding, singleCLM_apply] using (singleCLM i).coeFn_compLpL u

lemma l2Coordinate_injective {u v : VectorL2 (μ := μ) (ι := ι)}
    (h : ∀ i, l2Coordinate i u = l2Coordinate i v) : u = v := by
  apply Lp.ext
  have hh : ∀ᵐ t ∂μ, ∀ i, (u t) i = (v t) i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [l2Coordinate_ae i u, l2Coordinate_ae i v] with t hu hv
    rw [← hu, ← hv, h i]
  filter_upwards [hh] with t ht
  exact PiLp.ext ht

@[simp] lemma coordinate_embedding (i j : ι) (u : Lp ℂ 2 μ) :
    l2Coordinate i (l2Embedding j u) = if i = j then u else 0 := by
  by_cases hij : i = j
  · subst j; rw [ite_eq_left rfl]
    apply Lp.ext
    filter_upwards [l2Coordinate_ae i (l2Embedding i u), l2Embedding_ae i u]
      with t ht hu
    simp [ht, hu]
  · rw [ite_eq_right hij]
    apply Lp.ext
    filter_upwards [l2Coordinate_ae i (l2Embedding j u), l2Embedding_ae j u,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with t ht hu hz
    rw [ht, hu]
    simp only [PiLp.single_apply, ite_eq_right hij]
    exact hz.symm

lemma embedding_inner (i : ι) (u : Lp ℂ 2 μ) (v : VectorL2 (μ := μ) (ι := ι)) :
    inner ℂ (l2Embedding i u) v = inner ℂ u (l2Coordinate i v) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [l2Embedding_ae i u, l2Coordinate_ae i v] with t ht hv
  rw [ht, hv, EuclideanSpace.inner_single_left]
  simp [RCLike.inner_apply, mul_comm]

lemma coordinate_inner (i : ι) (u : VectorL2 (μ := μ) (ι := ι)) (v : Lp ℂ 2 μ) :
    inner ℂ (l2Coordinate i u) v = inner ℂ u (l2Embedding i v) := by
  have h := congrArg (starRingEnd ℂ) (embedding_inner i v u)
  simpa only [inner_conj_symm] using h.symm

def entrywiseL2 (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    VectorL2 (μ := μ) (ι := ι) →L[ℂ] VectorL2 (μ := μ) (ι := ι) :=
  ∑ i : ι, (l2Embedding i).comp (T.comp (l2Coordinate i))

@[simp] lemma coordinate_entrywise (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u : VectorL2 (μ := μ) (ι := ι)) (i : ι) :
    l2Coordinate i (entrywiseL2 T u) = T (l2Coordinate i u) := by
  simp [entrywiseL2, sum_apply, map_sum]

lemma entrywise_inner (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (u v : VectorL2 (μ := μ) (ι := ι)) :
    inner ℂ (entrywiseL2 T u) v = inner ℂ u (entrywiseL2 T.adjoint v) := by
  simp only [entrywiseL2, sum_apply, ContinuousLinearMap.comp_apply,
    sum_inner, inner_sum, embedding_inner, ← coordinate_inner]
  apply Finset.sum_congr rfl
  intro i hi
  exact (ContinuousLinearMap.adjoint_inner_right T _ _).symm

def vectorResolution (D : FourierResolution (Lp ℂ 2 μ)) :
    FourierResolution (VectorL2 (μ := μ) (ι := ι)) where
  proj j := entrywiseL2 (D.proj j)
  selfAdjoint j := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro u v
    rw [entrywise_inner, D.selfAdjoint]
  product i j := by
    ext1 u
    apply l2Coordinate_injective
    intro k
    by_cases hij : i = j
    · subst j
      simp [coordinate_entrywise, D.proj_proj]
    · simp [hij, coordinate_entrywise, D.proj_proj]
  total := by
    ext1 u
    apply l2Coordinate_injective
    intro k
    simpa using D.decompose (l2Coordinate k u)


end CompleteCrouzeix

end

end OAI
