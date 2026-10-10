import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.CompactMetricAllJets

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma chartGradientField_sub_const (g : SmoothMetric E M) (w : M → ℝ) (p : M) (c : ℝ) :
    chartGradientField g (fun z => w z-c) p=chartGradientField g w p := by
  funext i y
  simp only [chartGradientField,coordinateFlux,Function.comp_def,fderiv_sub_const]

theorem weightedLaplacian_small_jets_on_compact (g : SmoothMetric E M) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b w : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w →
      ∀ (x : E), x ∈ K → ∀ B ε : ℝ, 0 ≤ B → 0 ≤ ε →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (b ∘ (chartAt E p).symm) x‖ ≤ B) →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (fun y => w ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j ((weightedLaplacian g b w) ∘ (chartAt E p).symm) x‖ ≤ C*B*ε := by
  obtain ⟨A,hA,ha,hρ,hρi⟩ := compact_metric_scalar_coefficient_bounds g p hK hKt h
  let S := ∑ i : CoordIndex E, ‖Module.finBasis ℝ E i‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let C1 := 2^(h+1)*A*S
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  let C2 := 2^(2*h+1)*A*A*S
  have hC2 : 0 ≤ C2 := by dsimp [C2]; positivity
  let C := C2*2^(h+1)*C1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C+1,by positivity,?_⟩
  intro b w hb hw x hx B ε hB hε hbJ hwJ
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hxO : x ∈ O := hKt hx
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hb p hy).contDiffWithinAt
  have hX (i : CoordIndex E) : ContDiffOn ℝ ∞ (chartGradientField g w p i) O :=
    chartGradientField_smooth hw g p i
  have hgj : ∀ i : CoordIndex E, ∀ k ≤ h+1,
      ‖iteratedFDeriv ℝ k (chartGradientField g w p i) x‖ ≤ C1*ε := by
    have hg := chartGradientField_sharp_jet_bound (hw.sub (contMDiff_const (c := (1:ℝ)))) g p hxO (h+1)
      (n:=1) (W:=1) (C:=ε) (A:=A) le_rfl zero_lt_one hε (zero_le_one.trans hA)
      (fun i j k hk => ha i j k hk x hx)
      (fun k hk => by simpa only [Function.comp_def,one_pow,mul_one] using hwJ k (by omega))
    rw [chartGradientField_sub_const] at hg
    intro i k hk
    exact (hg i k hk).trans_eq (by dsimp [C1,S]; simp only [one_pow,mul_one]; ring)
  let Z := fun i y => b ((chartAt E p).symm y)*chartGradientField g w p i y
  have hZ (i : CoordIndex E) : ContDiffOn ℝ ∞ (Z i) O := hb'.mul (hX i)
  have hzj : ∀ i : CoordIndex E, ∀ k ≤ h+1,
      ‖iteratedFDeriv ℝ k (Z i) x‖ ≤ (2^(h+1)*C1)*B*ε := by
    intro i k hk
    have hh := geometric_product_jet_bound_on hO hxO hb' (hX i) k hB
      (mul_nonneg hC1 hε) zero_le_one zero_le_one
      (fun j hj => by simpa using hbJ j (hj.trans hk))
      (fun j hj => by simpa using hgj i j (hj.trans hk))
    calc
      _ ≤ B*(C1*ε)*(1+1)^k := hh
      _ ≤ B*(C1*ε)*2^(h+1) := mul_le_mul_of_nonneg_left
        (by norm_num only [one_add_one_eq_two]; exact pow_le_pow_right₀ (by norm_num) hk) (by positivity)
      _ = _ := by ring
  have hdiv := coordinate_divergence_jet_bound_on (Module.finBasis ℝ E)
    (fun y => Real.sqrt (metricCoefficients g p y).det) Z hO hxO
    (contDiffOn_metricDensity g p) (fun y hy => Real.sqrt_pos.mpr (metricCoefficients_det_pos g p hy))
    hZ h (zero_le_one.trans hA) (show 0 ≤ (2^(h+1)*C1)*B*ε by positivity)
    (fun k hk => hρ k hk x hx) (fun k hk => hρi k hk x hx) hzj
  have he : ((weightedLaplacian g b w) ∘ (chartAt E p).symm) =ᶠ[𝓝 x]
      coordinateDivergence (Module.finBasis ℝ E) (fun y => Real.sqrt (metricCoefficients g p y).det) Z := by
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact weightedLaplacian_chartGradient hb hw g p hy
  intro j hj
  rw [(he.iteratedFDeriv ℝ j).self_of_nhds]
  calc
    _ ≤ (2^(2*h+1)*A*A*S)*((2^(h+1)*C1)*B*ε) := hdiv j hj
    _ = C*B*ε := by dsimp [C,C2]; ring
    _ ≤ (C+1)*B*ε := by nlinarith [mul_nonneg hB hε]

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma constant_product_jet_bound_on {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h : ℕ) {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤ 2^h*F*G := by
  intro j hj
  have hh := geometric_product_jet_bound_on hO hx hf hg j hF hG zero_le_one zero_le_one
    (fun k hk => by simpa only [one_pow,mul_one] using hfj k (hk.trans hj))
    (fun k hk => by simpa only [one_pow,mul_one] using hgj k (hk.trans hj))
  calc
    _ ≤ F*G*(1+1)^j := hh
    _ ≤ F*G*2^h := mul_le_mul_of_nonneg_left
      (by norm_num only [one_add_one_eq_two]; exact pow_le_pow_right₀ (by norm_num) hj) (mul_nonneg hF hG)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
lemma raw_jets_of_near_one {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (h : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y-1) x‖ ≤ ε) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ 1+ε := by
  intro j hj
  by_cases hj0 : j=0
  · subst j
    simp only [norm_iteratedFDeriv_zero] at hJ ⊢
    have hv := hJ 0 (Nat.zero_le h)
    simp only [norm_iteratedFDeriv_zero] at hv
    rw [Real.norm_eq_abs] at hv ⊢
    apply (sq_le_sq₀ (abs_nonneg _) (add_nonneg zero_le_one hε)).mp
    rw [sq_abs]
    have hbound := (sq_le_sq₀ (abs_nonneg (f x-1)) hε).mpr hv
    rw [sq_abs] at hbound
    have hupper := (abs_le.mp hv).2
    nlinarith
  · have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have hb := hJ j hj
    rw [fun_iteratedFDeriv_sub_apply ((hf.contDiffAt (hO.mem_nhds hx)).of_le hle)
      contDiffAt_const,iteratedFDeriv_const_of_ne hj0,Pi.zero_apply,sub_zero] at hb
    linarith

theorem cutoff_density_small_jets (g : SmoothMetric E M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (p : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (chartAt E p).target) (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (b s v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v → ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ x ∈ K, ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E p).symm y)-1) x‖ ≤ ε) →
      let w := cutoffFactor χ v
      ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1) x‖ ≤ C*ε ∧
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)-1) x‖ ≤ C*ε := by
  let O := (chartAt E p).target
  have hO : IsOpen O := (chartAt E p).open_target
  have hχ' : ContDiffOn ℝ ∞ (χ ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart hχ p hy).contDiffWithinAt
  obtain ⟨A,hA,hAj⟩ := compact_raw_jet_bound hO hK hKt hχ' (h+2)
  obtain ⟨L,hL,hLJ⟩ := weightedLaplacian_small_jets_on_compact g p hK hKt h
  let α := max 1 (2^(h+2)*A)
  have hα : 1 ≤ α := le_max_left _ _
  have hα0 : 0 < α := zero_lt_one.trans_le hα
  let β := (2^h+2)*α
  have hαβ : α ≤ β := by dsimp [β]; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) h]
  have hβ : 0 < β := hα0.trans_le hαβ
  let Q := (2^h+2)*β
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let R := 2^h*2*(L*2*α)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨min 1 (1/β),Q+R+1,lt_min zero_lt_one (by positivity),by positivity,?_⟩
  intro b s v hb hs hv Λ hΛ x hx ε hε hεδ hbJ hsJ hvJ w
  have hxO : x ∈ O := hKt hx
  have hε1 : ε ≤ 1 := hεδ.trans (min_le_left _ _)
  have hβε : β*ε ≤ 1 := by have := (le_div_iff₀ hβ).mp (hεδ.trans (min_le_right _ _)); nlinarith
  have hαε : α*ε ≤ 1 := (mul_le_mul_of_nonneg_right hαβ hε).trans hβε
  have heα : ε ≤ α*ε := by nlinarith
  have heβ : ε ≤ β*ε := heα.trans (mul_le_mul_of_nonneg_right hαβ hε)
  have hb' : ContDiffOn ℝ ∞ (b ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hb p hy).contDiffWithinAt
  have hs' : ContDiffOn ℝ ∞ (s ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hs p hy).contDiffWithinAt
  have hv' : ContDiffOn ℝ ∞ (v ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hv p hy).contDiffWithinAt
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w := contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hw' : ContDiffOn ℝ ∞ (w ∘ (chartAt E p).symm) O := fun y hy => (contDiffAt_inChart hw p hy).contDiffWithinAt
  simp only [Function.comp_def] at hb' hs' hv' hw'
  have hwJ : ∀ j ≤ h+2,
      ‖iteratedFDeriv ℝ j (fun y => w ((chartAt E p).symm y)-1) x‖ ≤ α*ε := by
    have hp := constant_product_jet_bound_on hO hxO hχ' (hv'.sub contDiffOn_const) (h+2)
      (zero_le_one.trans hA) hε (fun k hk => hAj k hk x hx) hvJ
    intro j hj
    have he : (fun y => w ((chartAt E p).symm y)-1)=
        (fun y => χ ((chartAt E p).symm y)*(v ((chartAt E p).symm y)-1)) := by
      funext y; dsimp [w,cutoffFactor]; ring
    rw [he]
    exact (hp j hj).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  have hw2J : ∀ j ≤ h, ‖iteratedFDeriv ℝ j
      (fun y => w ((chartAt E p).symm y)^2-1) x‖ ≤ β*ε := by
    intro j hj
    have hp := near_one_product_jet_bound_on hO hxO hw' hw' j (mul_nonneg hα0.le hε) hαε
      (fun k hk => hwJ k (by omega)) (fun k hk => hwJ k (by omega))
    calc
      _ ≤ (2^j+2)*(α*ε) := by simpa only [pow_two,Function.comp_apply] using hp
      _ ≤ (2^h+2)*(α*ε) := mul_le_mul_of_nonneg_right
        (add_le_add (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) le_rfl) (by positivity)
      _ = β*ε := by dsimp [β]; ring
  have hbwJ (f : M → ℝ) (hf : ContDiffOn ℝ ∞ (f ∘ (chartAt E p).symm) O)
      (hfJ : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f ((chartAt E p).symm y)-1) x‖ ≤ ε) :
      ∀ j ≤ h, ‖iteratedFDeriv ℝ j
        (fun y => f ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1) x‖ ≤ Q*ε := by
    intro j hj
    have hp := near_one_product_jet_bound_on hO hxO hf (hw'.pow 2) j (by positivity : 0 ≤ β*ε) hβε
      (fun k hk => (hfJ k (hk.trans hj)).trans heβ) (fun k hk => hw2J k (hk.trans hj))
    calc
      _ ≤ (2^j+2)*(β*ε) := hp
      _ ≤ (2^h+2)*(β*ε) := mul_le_mul_of_nonneg_right
        (add_le_add (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) le_rfl) (by positivity)
      _ = Q*ε := by dsimp [Q]; ring
  have hbraw := raw_jets_of_near_one hO hxO hb' (h+1) hε hbJ
  have hwraw := raw_jets_of_near_one hO hxO hw' (h+2) (mul_nonneg hα0.le hε) hwJ
  have hlapJ := hLJ b w hb hw x hx 2 (α*ε) (by norm_num) (by positivity)
    (fun j hj => (hbraw j hj).trans (by linarith)) hwJ
  have hlap' : ContDiffOn ℝ ∞ ((weightedLaplacian g b w) ∘ (chartAt E p).symm) O :=
    fun y hy => (contDiffAt_inChart (contMDiff_weightedLaplacian hb hw g) p hy).contDiffWithinAt
  simp only [Function.comp_def] at hlap'
  have hprod := constant_product_jet_bound_on hO hxO hw' hlap' h (by norm_num : (0:ℝ) ≤ 2)
    (show 0 ≤ L*2*(α*ε) by positivity) (fun j hj => (hwraw j (by omega)).trans (by linarith)) hlapJ
  have hprod' (j : ℕ) (hj : j ≤ h) : ‖iteratedFDeriv ℝ j
      (fun y => Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)) x‖ ≤ R*ε := by
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    have he : (fun y => Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y))=
        (fun y => Λ⁻¹ • (w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y))) := by
      funext y; simp only [smul_eq_mul]; ring
    rw [he,iteratedFDeriv_const_smul_apply' (a:=Λ⁻¹) (((hw'.mul hlap').contDiffAt (hO.mem_nhds hxO)).of_le hle),norm_smul,
      Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hΛ))]
    calc
      _ ≤ 1*(2^h*2*(L*2*(α*ε))) := mul_le_mul ((inv_le_one₀ (zero_lt_one.trans_le hΛ)).mpr hΛ)
        (hprod j hj) (norm_nonneg _) zero_le_one
      _ = R*ε := by dsimp [R]; ring
  intro j hj
  constructor
  · exact (hbwJ b hb' (fun k hk => hbJ k (by omega)) j hj).trans (by nlinarith [mul_nonneg hR hε])
  · have he : (fun y => s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)-1)=
        (fun y => (s ((chartAt E p).symm y)*w ((chartAt E p).symm y)^2-1)+
          Λ⁻¹*w ((chartAt E p).symm y)*weightedLaplacian g b w ((chartAt E p).symm y)) := by funext y; ring
    have hle : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
    rw [he,fun_iteratedFDeriv_add_apply
      ((((hs'.mul (hw'.pow 2)).sub (contDiffOn_const (c:=(1:ℝ)))).contDiffAt (hO.mem_nhds hxO)).of_le hle)
      (((((contDiffOn_const (c:=Λ⁻¹)).mul hw').mul hlap').contDiffAt (hO.mem_nhds hxO)).of_le hle)]
    exact (norm_add_le _ _).trans (by have := hbwJ s hs' hsJ j hj; have := hprod' j hj; nlinarith)

end

section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix

lemma list_positive_common_lower_bound {α : Type*} (l : List α) (f : α → ℝ)
    (hf : ∀ a ∈ l, 0 < f a) : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ l, δ ≤ f a := by
  induction l with
  | nil => exact ⟨1, by norm_num, by simp⟩
  | cons a l ih =>
    obtain ⟨δ,hδ,hd⟩ := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    refine ⟨min (f a) δ,lt_min (hf a (List.mem_cons_self)) hδ,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hd b hb)

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem cutoff_density_small_jets_finite (g : SmoothMetric E M) (χ : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) (tests : List (CoordinateTest E M)) (h : ℕ) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ (b s v : M → ℝ),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v → ∀ Λ : ℝ, 1 ≤ Λ →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      let w := cutoffFactor χ v
      ∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)*w ((chartAt E t.center).symm y)^2-1) x‖ ≤ C*ε ∧
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)*w ((chartAt E t.center).symm y)^2+
          Λ⁻¹*w ((chartAt E t.center).symm y)*weightedLaplacian g b w ((chartAt E t.center).symm y)-1) x‖ ≤ C*ε := by
  classical
  choose d C hd hC hJ using fun t : CoordinateTest E M =>
    cutoff_density_small_jets g χ hχ t.center t.isCompact t.inTarget h
  obtain ⟨δ,hδ,hδd⟩ := list_positive_common_lower_bound tests d (fun t _ => hd t)
  let A := 1+∑ t ∈ tests.toFinset, C t
  have hA : 0 < A := by
    dsimp [A]
    have hs : 0 ≤ ∑ t ∈ tests.toFinset, C t := Finset.sum_nonneg (fun t _ => (hC t).le)
    linarith
  have hCA (t : CoordinateTest E M) (ht : t ∈ tests) : C t ≤ A := by
    have hb := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) => (hC t).le)
      (List.mem_toFinset.mpr ht)
    dsimp [A]
    linarith
  refine ⟨δ,A,hδ,hA,?_⟩
  intro b s v hb hs hv Λ hΛ ε hε hεδ hbJ hsJ hvJ w t ht x hx j hj
  have hh := hJ t b s v hb hs hv Λ hΛ x hx ε hε (hεδ.trans (hδd t ht))
    (hbJ t ht x hx) (hsJ t ht x hx) (hvJ t ht x hx) j hj
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right (hCA t ht) hε),
    hh.2.trans (mul_le_mul_of_nonneg_right (hCA t ht) hε)⟩

end

open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
open Set Filter Module
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
open Set Filter
open scoped Topology
open Set Filter Function MeasureTheory FourierTransform TemperedDistribution
open scoped Topology SchwartzMap ENNReal Real Laplacian BoundedContinuousFunction
open Set Filter Function
open scoped Topology ContDiff Manifold
open Set Filter Manifold Bundle Matrix
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff Manifold Matrix
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

theorem cutoff_exactification_in_smooth_neighborhood
    (hdim : Module.finrank ℝ E=3) (g : SmoothMetric E M)
    (N : Set (SmoothMetric E M)) (hN : IsSmoothNeighborhood g N)
    (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ) :
    ∃ tests : List (CoordinateTest E M), ∃ h : ℕ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (b s U v : M → ℝ) (Λ : ℝ) (O F : Set M),
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s →
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ U → ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v →
      1 ≤ Λ → (∀ x, 0 < b x) → (∀ x, χ x ∈ Icc (0:ℝ) 1) →
      (∀ x, |v x-1| ≤ 1/2) → (∀ x, |s x-1| ≤ 1/2) →
      (∀ x, weightedLaplacian g b U x+Λ*s x*U x=0) →
      (∀ x, weightedLaplacian g b v x=Λ*b x^3*v x^5-Λ*s x*v x) →
      IsOpen O → IsOpen F → (∀ x ∈ O, χ x=1) → (∀ x ∈ F, χ x=0) →
      (∀ x ∈ F, b x=1 ∧ s x=1) →
      (∀ x, |Λ⁻¹*cutoffFactor χ v x*weightedLaplacian g b (cutoffFactor χ v) x| ≤ 1/16) →
      (∀ x ∉ O ∪ F,
        U x^2*coordinateGradientPair g (cutoffFactor χ v) (cutoffFactor χ v) x <
          cutoffFactor χ v x^2*coordinateGradientPair g U U x) →
      ∀ ε C n : ℝ, 0 ≤ ε → ε ≤ δ → 0 ≤ C → 1 ≤ n → ε*(1+C)*n^h < δ →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (fun y => b ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => s ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, ∀ j ≤ h+2,
        ‖iteratedFDeriv ℝ j (fun y => v ((chartAt E t.center).symm y)-1) x‖ ≤ ε) →
      (∀ t ∈ tests, ∀ x ∈ t.compactSet, (chartAt E t.center).symm x ∉ O ∪ F →
        ∀ i j : CoordIndex E, ∀ k ≤ h,
          ‖iteratedFDeriv ℝ k (chartGradientProjection g (fun z => U z/cutoffFactor χ v z) t.center i j) x‖ ≤ C*n^k) →
      ∃ ĝ ∈ N, ∃ u : M → ℝ,
        ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ u ∧
        (∀ x, -laplaceBeltrami ĝ u x=Λ*u x) ∧
        (∀ x, u x=U x/cutoffFactor χ v x) ∧
        (∀ x, u x=0 ↔ U x=0) ∧ (∀ x, 0 < u x ↔ 0 < U x) ∧
        (∀ x ∈ F, (∀ a c, ĝ.inner x a c=g.inner x a c) ∧ u x=U x) := by
  classical
  obtain ⟨tests,h,η,hη,hReal⟩ := conductivity_metric_in_smooth_neighborhood hdim g N hN
  obtain ⟨δ₀,A,hδ₀,hA,hDall⟩ := cutoff_density_small_jets_finite g χ hχ tests h
  refine ⟨tests,h,min δ₀ (η/A),lt_min hδ₀ (div_pos hη hA),?_⟩
  intro b s U v Λ O F hb hs hU hv hΛ1 hbpos hχrange hvsmall hssmall hweighted hfactor
    hO hF hχO hχF hext hsmall hmargin ε C n hε hεδ hC hn hεn hbJ hsJ hvJ hPJ
  have hΛ : Λ ≠ 0 := (zero_lt_one.trans_le hΛ1).ne'
  let w := cutoffFactor χ v
  have hw : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ w :=
    contMDiff_const.add (hχ.mul (hv.sub contMDiff_const))
  have hwsmall (x : M) : |w x-1| ≤ 1/2 := by
    change |1+χ x*(v x-1)-1| ≤ _
    rw [add_sub_cancel_left,abs_mul,abs_of_nonneg (hχrange x).1]
    calc
      χ x*|v x-1| ≤ 1*|v x-1| := mul_le_mul_of_nonneg_right (hχrange x).2 (abs_nonneg _)
      _ ≤ 1/2 := by simpa using hvsmall x
  have hwge (x : M) : 1/2 ≤ w x := by have h := (abs_le.mp (hwsmall x)).1; linarith
  have hwpos (x : M) : 0 < w x := by linarith [hwge x]
  let q := fun x => b x*w x^2
  let d := fun x => s x*w x^2+Λ⁻¹*w x*weightedLaplacian g b w x
  have hq : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ q := hb.mul (hw.pow 2)
  have hd : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ d :=
    (hs.mul (hw.pow 2)).add ((contMDiff_const.mul hw).mul (contMDiff_weightedLaplacian hb hw g))
  have hqpos (x : M) : 0 < q x := mul_pos (hbpos x) (sq_pos_of_pos (hwpos x))
  have hdpos (x : M) : 0 < d x := by
    have hsge : 1/2 ≤ s x := by have h := (abs_le.mp (hssmall x)).1; linarith
    have hw2 : 1/4 ≤ w x^2 := by nlinarith [hwge x]
    have hsw : 1/8 ≤ s x*w x^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hsge) (sq_nonneg (w x))]
    have hz := (abs_le.mp (hsmall x)).1
    change -(1/16) ≤ Λ⁻¹*w x*weightedLaplacian g b w x at hz
    dsimp only [d]
    linarith
  have hwO {x : M} (hx : x ∈ O) : w =ᶠ[𝓝 x] v := by
    filter_upwards [hO.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχO y hy]
  have hwF {x : M} (hx : x ∈ F) : w =ᶠ[𝓝 x] (fun _ => 1) := by
    filter_upwards [hF.mem_nhds hx] with y hy
    simp [w,cutoffFactor,hχF y hy]
  have hcompat {x : M} (hx : x ∈ O) : d x=q x^3 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwO hx)
    dsimp only [d,q]
    rw [he,(hwO hx).eq_of_nhds,hfactor x]
    field_simp [hΛ]
    ring
  have hde {x : M} (hx : x ∈ F) : d x=1 ∧ q x=1 := by
    have he := weightedLaplacian_congr_nhds g (Filter.EventuallyEq.rfl (f:=b)) (hwF hx)
    rw [weightedLaplacian_const] at he
    dsimp only [d,q]
    rw [he,(hwF hx).eq_of_nhds,(hext x hx).1,(hext x hx).2]
    simp
  have hsupp : tsupport (fun x => d x-q x^3) ⊆ (O ∪ F)ᶜ := by
    apply closure_minimal _ (hO.union hF).isClosed_compl
    intro x hx
    rw [mem_compl_iff,mem_union]
    rintro (hxo|hxf)
    · exact hx (sub_eq_zero.mpr (hcompat hxo))
    · obtain ⟨hde,hqe⟩ := hde hxf
      exact hx (by change d x-q x^3=0; rw [hde,hqe]; norm_num)
  let u := fun x => U x/w x
  have hu := hU.div₀ hw (fun x => (hwpos x).ne')
  have hsupp' : tsupport (fun x => d x-q x^3) ⊆
      {x | coordinateGradientPair g u u x ≠ 0} := by
    intro x hx
    exact conjugate_gradient_nonzero hU hw g (fun y => (hwpos y).ne') x (hmargin x (hsupp hx))
  have hD := hDall b s v hb hs hv Λ hΛ1 ε hε (hεδ.trans (min_le_left _ _)) hbJ hsJ hvJ
  have hAε : A*ε ≤ η := by
    have he := (le_div_iff₀ hA).mp (hεδ.trans (min_le_right _ _))
    nlinarith
  have hAεn : (A*ε)*(1+C)*n^h < η := by
    have he := (lt_div_iff₀ hA).mp (hεn.trans_le (min_le_right _ _))
    nlinarith
  obtain ⟨ĝ,hĝN,heq,hmetric⟩ := hReal u d q hu hd hq hdpos hqpos hsupp'
    (A*ε) C n (mul_nonneg hA.le hε) hAε hC hn hAεn
    (fun t ht x hx j hj => (hD t ht x hx j hj).2)
    (fun t ht x hx j hj => (hD t ht x hx j hj).1)
    (fun t ht x hx hdX i j k hk => hPJ t ht x hx (hsupp hdX) i j k hk)
  refine ⟨ĝ,hĝN,u,hu,?_,fun _ => rfl,?_,?_,?_⟩
  · intro x
    have hz := intrinsic_conjugated_equation hb hU hw g hΛ (fun x => (hwpos x).ne') hweighted x
    change weightedLaplacian g q u x+Λ*d x*u x=0 at hz
    rw [heq]
    have hdn := (hdpos x).ne'
    field_simp
    nlinarith [hz]
  · intro x
    change U x/w x=0 ↔ U x=0
    simp [(hwpos x).ne']
  · intro x
    exact div_pos_iff_of_pos_right (hwpos x)
  · intro x hx
    obtain ⟨hdx,hqx⟩ := hde hx
    refine ⟨hmetric x hdx hqx,?_⟩
    change U x/w x=U x
    rw [(hwF hx).eq_of_nhds,div_one]


end YauCounterexamples
end

end OAI
