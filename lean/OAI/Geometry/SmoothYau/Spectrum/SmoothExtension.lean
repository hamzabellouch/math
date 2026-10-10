import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.FlowInitialFderiv
import OAI.Geometry.SmoothYau.Smoothness.NormIteratedFDerivScalarDirection

namespace OAI

noncomputable section
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
namespace YauCounterexamples

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

lemma smooth_extension_at {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ F : E → F, ContDiff ℝ ∞ F ∧ f =ᶠ[𝓝 x] F := by
  obtain ⟨F,hF,he⟩ := smooth_extension_near_compact isCompact_singleton hO
    (singleton_subset_iff.mpr hx) hf
  exact ⟨F,hF,he.filter_mono (nhds_le_nhdsSet (mem_singleton x))⟩

lemma positive_smooth_extension_at {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hfx : 0 < f x) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ (∀ y, 0 < F y) ∧ f =ᶠ[𝓝 x] F := by
  have hp : {y | 0 < f y} ∈ 𝓝 x :=
    (hf.continuousOn.continuousAt (hO.mem_nhds hx)).eventually (isOpen_Ioi.mem_nhds hfx)
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hp
  obtain ⟨F,hF,he⟩ := smooth_extension_at (hO.inter hVo) ⟨hx,hxV⟩
    ((hf.mono inter_subset_left).log (fun y hy => (hV hy.2).ne'))
  refine ⟨fun y => Real.exp (F y), hF.exp,fun _ => Real.exp_pos _,?_⟩
  filter_upwards [he, hp] with y hy hpy
  rw [← hy,Real.exp_log hpy]

omit [FiniteDimensional ℝ E] in
lemma coordinateDivergence_eventuallyEq (e : ι → E) {ρ σ : E → ℝ}
    {X Y : ι → E → ℝ} {x : E} (hρ : ρ =ᶠ[𝓝 x] σ)
    (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    coordinateDivergence e ρ X =ᶠ[𝓝 x] coordinateDivergence e σ Y := by
  have hd (i : ι) := (hρ.mul (hX i)).fderiv (𝕜:=ℝ)
  filter_upwards [hρ,eventually_all.mpr hd] with y hy hdy
  simp only [coordinateDivergence,hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : E →L[ℝ] ℝ => L (e i)) (hdy i)

omit [FiniteDimensional ℝ E] in
lemma scalarCorrectionDenominator_eventuallyEq (e : ι → E) (n : ℝ)
    {U V : E → ℝ} {X Y : ι → E → ℝ} {x : E}
    (hU : U =ᶠ[𝓝 x] V) (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    scalarCorrectionDenominator e n U X =ᶠ[𝓝 x] scalarCorrectionDenominator e n V Y := by
  filter_upwards [hU,hU.fderiv (𝕜:=ℝ),eventually_all.mpr hX] with y hy hdy hxy
  simp only [scalarCorrectionDenominator,hy,hdy,hxy]

omit [FiniteDimensional ℝ E] in
lemma scalarCorrectionRatio_eventuallyEq (e : ι → E) (n Λ : ℝ)
    {ρ σ U V : E → ℝ} {X Y : ι → E → ℝ} {x : E}
    (hρ : ρ =ᶠ[𝓝 x] σ) (hU : U =ᶠ[𝓝 x] V) (hX : ∀ i, X i =ᶠ[𝓝 x] Y i) :
    scalarCorrectionRatio e ρ n Λ U X =ᶠ[𝓝 x] scalarCorrectionRatio e σ n Λ V Y := by
  exact ((coordinateDivergence_eventuallyEq e hρ hX).add
    (EventuallyEq.rfl.mul hU)).div (scalarCorrectionDenominator_eventuallyEq e n hU hX)

lemma contDiffOn_coordinateDivergence (e : ι → E) {O : Set E} (hO : IsOpen O)
    {ρ : E → ℝ} {X : ι → E → ℝ} (hρ : ContDiffOn ℝ ∞ ρ O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hρp : ∀ y ∈ O, 0 < ρ y) :
    ContDiffOn ℝ ∞ (coordinateDivergence e ρ X) O := by
  intro x hx
  obtain ⟨σ,hσ,hσp,hσe⟩ := positive_smooth_extension_at hO hx hρ (hρp x hx)
  choose Y hY hYe using fun i => smooth_extension_at hO hx (hX i)
  exact ((contDiff_coordinateDivergence e σ Y hσ hY (fun y => (hσp y).ne')).contDiffAt.congr_of_eventuallyEq
    (coordinateDivergence_eventuallyEq e hσe hYe)).contDiffWithinAt

lemma contDiffOn_scalarCorrectionDenominator (e : ι → E) (n : ℝ)
    {O : Set E} (hO : IsOpen O) {U : E → ℝ} {X : ι → E → ℝ}
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) :
    ContDiffOn ℝ ∞ (scalarCorrectionDenominator e n U X) O := by
  intro x hx
  obtain ⟨V,hV,hVe⟩ := smooth_extension_at hO hx hU
  choose Y hY hYe using fun i => smooth_extension_at hO hx (hX i)
  exact ((contDiff_scalarCorrectionDenominator e n V Y hV hY).contDiffAt.congr_of_eventuallyEq
    (scalarCorrectionDenominator_eventuallyEq e n hVe hYe)).contDiffWithinAt

lemma contDiffOn_scalarCorrectionRatio (e : ι → E) (n Λ : ℝ)
    {O : Set E} (hO : IsOpen O) {ρ U : E → ℝ} {X : ι → E → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ O) (hU : ContDiffOn ℝ ∞ U O)
    (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hden : ∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0) :
    ContDiffOn ℝ ∞ (scalarCorrectionRatio e ρ n Λ U X) O := by
  exact ((contDiffOn_coordinateDivergence e hO hρ hX hρp).add
    (contDiffOn_const.mul hU)).div (contDiffOn_scalarCorrectionDenominator e n hO hU hX) hden

theorem frequency_weighted_quotient_uniform_on
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f d : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hd : ContDiffOn ℝ ∞ d O)
    (h B a D : ℕ) {n W F C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F)
    (hx : W^2/(2*n^(2*B)) ≤ d x)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W^2)
    (hdj : ∀ j : ℕ, 1 ≤ j → j ≤ h → ‖iteratedFDeriv ℝ j d x‖ ≤ C*n^(j+10)*W^2) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y/d y) x‖ ≤
      (2*F*(h.factorial:ℝ)^2*(1+max 1 (2*C))^h)*
        n^(a+2*B+(2*B+11)*h)/(n^D) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨d',hd',hdp,hde⟩ := positive_smooth_extension_at hO hxO hd
    ((show 0 < W^2/(2*n^(2*B)) by positivity).trans_le hx)
  have hq := frequency_weighted_quotient_uniform hf' hd' (fun y => (hdp y).ne') x h B a D
    hn hW hF (hde.self_of_nhds ▸ hx)
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj hjh => (hde.iteratedFDeriv ℝ j).self_of_nhds ▸ hdj j hj hjh)
  intro j hj
  change ‖iteratedFDeriv ℝ j (f/d) x‖ ≤ _
  rw [(hfe.div hde).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem frequency_weighted_product_bound_on
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    {f g : E → ℝ} (hf : ContDiffOn ℝ ∞ f O) (hg : ContDiffOn ℝ ∞ g O)
    (h a b D : ℕ) {n W F G : ℝ}
    (hn : 1 ≤ n) (hW : 0 < W) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j f x‖ ≤ F*n^(a+j)/(n^D)*W)
    (hgj : ∀ j ≤ h, ‖iteratedFDeriv ℝ j g x‖ ≤ G*n^(b+j)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => f y*g y) x‖ ≤
      (2^h*F*G)*n^(a+b+j)/(n^D)*W^2 := by
  obtain ⟨f',hf',hfe⟩ := smooth_extension_at hO hxO hf
  obtain ⟨g',hg',hge⟩ := smooth_extension_at hO hxO hg
  have hq := frequency_weighted_product_bound hf' hg' x h a b D hn hW hF hG
    (fun j hj => (hfe.iteratedFDeriv ℝ j).self_of_nhds ▸ hfj j hj)
    (fun j hj => (hge.iteratedFDeriv ℝ j).self_of_nhds ▸ hgj j hj)
  intro j hj
  change ‖iteratedFDeriv ℝ j (f*g) x‖ ≤ _
  rw [(hfe.mul hge).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem scalar_denominator_jet_bound_on (e : ι → E) (U : E → ℝ) (X : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O)
    (h : ℕ) {n W C : ℝ} (hn : 1 ≤ n) (hW : 0 < W) (hC : 0 ≤ C)
    (hUj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W)
    (hXj : ∀ i, ∀ j ≤ h, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (scalarCorrectionDenominator e n U X) x‖ ≤
      (2^h*C*C*(1+∑ i, ‖e i‖))*n^(j+10)*W^2 := by
  obtain ⟨V,hV,hVe⟩ := smooth_extension_at hO hxO hU
  choose Y hY hYe using fun i => smooth_extension_at hO hxO (hX i)
  have hq := scalar_denominator_jet_bound e V Y hV hY x h hn hW hC
    (fun j hj => (hVe.iteratedFDeriv ℝ j).self_of_nhds ▸ hUj j hj)
    (fun i j hj => ((hYe i).iteratedFDeriv ℝ j).self_of_nhds ▸ hXj i j hj)
  intro j hj
  rw [(scalarCorrectionDenominator_eventuallyEq e n hVe hYe).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem coordinate_divergence_jet_bound_on (e : ι → E) (ρ : E → ℝ) (Z : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) O)
    (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hZj : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (Z i) x‖ ≤ F) :
    ∀ j ≤ h, ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖ ≤
      (2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  obtain ⟨σ,hσ,hσp,hσe⟩ := positive_smooth_extension_at hO hxO hρ (hρp x hxO)
  choose Y hY hYe using fun i => smooth_extension_at hO hxO (hZ i)
  have hq := coordinate_divergence_jet_bound e σ Y hσ (fun y => (hσp y).ne') hY x h hC hF
    (fun j hj => (hσe.iteratedFDeriv ℝ j).self_of_nhds ▸ hρj j hj)
    (fun j hj => (hσe.inv.iteratedFDeriv ℝ j).self_of_nhds ▸ hρij j hj)
    (fun i j hj => ((hYe i).iteratedFDeriv ℝ j).self_of_nhds ▸ hZj i j hj)
  intro j hj
  rw [(coordinateDivergence_eventuallyEq e hσe hYe).iteratedFDeriv ℝ j |>.self_of_nhds]
  exact hq j hj

theorem scalar_correction_error_from_quotients_on
    (e : ι → E) (ρ U : E → ℝ) (X : ι → E → ℝ)
    {O : Set E} (hO : IsOpen O) {x : E} (hxO : x ∈ O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (hU : ContDiffOn ℝ ∞ U O) (hX : ∀ i, ContDiffOn ℝ ∞ (X i) O)
    {n : ℝ} (hn : 1 ≤ n)
    (hden : ∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0)
    (h : ℕ) {C F : ℝ} (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hρj : ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C)
    (hρij : ∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C)
    (hqU : ∀ j ≤ h, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F)
    (hqX : ∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F) :
    ∀ j ≤ h,
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
      ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      (2+2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
  let f := scalarCorrectionRatio e ρ n (n*(n+2)) U X
  have hf : ContDiffOn ℝ ∞ f O := contDiffOn_scalarCorrectionRatio e n (n*(n+2)) hO
    hρ hU hX hρp hden
  let Z : ι → E → ℝ := fun i y => f y*X i y
  have hZ (i : ι) : ContDiffOn ℝ ∞ (Z i) O := hf.mul (hX i)
  have hd := contDiffOn_coordinateDivergence e hO hρ hZ hρp
  have hq := hf.mul hU
  have hdiv := coordinate_divergence_jet_bound_on e ρ Z hO hxO hρ hρp hZ h hC hF hρj hρij hqX
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hΛ : 0 < n*(n+2) := by positivity
  have hΛ1 : 1 ≤ n*(n+2) := by nlinarith
  have hnratio : (n*(n+2))⁻¹*n^2 ≤ 1 := by
    rw [← div_eq_inv_mul,div_le_one hΛ]
    nlinarith
  have hΛinv : (n*(n+2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ1
  have hCb : 0 ≤ 2^(2*h+1)*C*C*(∑ i, ‖e i‖) := by positivity
  intro j hj
  have hj' : (j:ℕ∞ω) ≤ (∞ : ℕ∞ω) := le_of_lt (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have heb : (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) =
      fun y => -(f y*U y) := by funext y; dsimp only [scalarCorrectionB,f]; ring
  have hes : (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) =
      fun y => -((n*(n+2))⁻¹ • (n^2 • (f y*U y)-coordinateDivergence e ρ Z y)) := by
    funext y; dsimp only [scalarCorrectionS,f,Z,smul_eq_mul]; ring
  have hb : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ ≤ F := by
    rw [heb]
    change ‖iteratedFDeriv ℝ j (-(fun y => f y*U y)) x‖ ≤ F
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact hqU j hj
  have hs : ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
      F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F := by
    have hz : ContDiffOn ℝ ∞ (fun y => n^2 • (f y*U y)-coordinateDivergence e ρ Z y) O :=
      (hq.const_smul (n^2)).sub hd
    rw [hes]
    change ‖iteratedFDeriv ℝ j (-(fun y => (n*(n+2))⁻¹ •
      (n^2 • (f y*U y)-coordinateDivergence e ρ Z y))) x‖ ≤ _
    rw [iteratedFDeriv_neg_apply,norm_neg,iteratedFDeriv_const_smul_apply' ((hz.contDiffAt (hO.mem_nhds hxO)).of_le hj'),
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΛ),
      fun_iteratedFDeriv_sub_apply (((hq.const_smul (n^2)).contDiffAt (hO.mem_nhds hxO)).of_le hj') ((hd.contDiffAt (hO.mem_nhds hxO)).of_le hj')]
    calc
      _ ≤ (n*(n+2))⁻¹*(‖iteratedFDeriv ℝ j (fun y => n^2 • (f y*U y)) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hΛ.le)
      _ = (n*(n+2))⁻¹*(n^2*‖iteratedFDeriv ℝ j (fun y => f y*U y) x‖+
          ‖iteratedFDeriv ℝ j (coordinateDivergence e ρ Z) x‖) := by
        rw [iteratedFDeriv_const_smul_apply' ((hq.contDiffAt (hO.mem_nhds hxO)).of_le hj'),norm_smul,
          Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ (n*(n+2))⁻¹*(n^2*F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left (hqU j hj) (sq_nonneg _)) (hdiv j hj))
          (inv_nonneg.mpr hΛ.le)
      _ = ((n*(n+2))⁻¹*n^2)*F + (n*(n+2))⁻¹*((2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := by ring
      _ ≤ _ := add_le_add
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnratio hF)
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hΛinv (mul_nonneg hCb hF))
  calc
    _ ≤ F+(F+(2^(2*h+1)*C*C*(∑ i, ‖e i‖))*F) := add_le_add hb hs
    _ = _ := by ring

theorem quantitative_scalar_correction_jets_on
    (e : ι → E) (ρ : E → ℝ) {O : Set E} (hO : IsOpen O)
    (hρ : ContDiffOn ℝ ∞ ρ O) (hρp : ∀ y ∈ O, 0 < ρ y)
    (h B : ℕ) {C : ℝ} (hC : 0 < C) :
    ∃ K > 0, ∀ (n : ℝ), 1 ≤ n → ∀ (D : ℕ) (U : E → ℝ) (X : ι → E → ℝ),
      ContDiffOn ℝ ∞ U O → (∀ i, ContDiffOn ℝ ∞ (X i) O) →
      (∀ y ∈ O, scalarCorrectionDenominator e n U X y ≠ 0) →
      ∀ x ∈ O, ∀ (W : ℝ), 0 < W →
      W^2/(2*n^(2*B)) ≤ scalarCorrectionDenominator e n U X x →
      (∀ j ≤ h+2, ‖iteratedFDeriv ℝ j U x‖ ≤ C*n^(j+4)*W) →
      (∀ i, ∀ j ≤ h+1, ‖iteratedFDeriv ℝ j (X i) x‖ ≤ C*n^(j+5)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j
        (fun y => coordinateDivergence e ρ X y+n*(n+2)*U y) x‖ ≤ C*n^4/(n^D)*W) →
      (∀ j ≤ h+1, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C) →
      (∀ j ≤ h, ‖iteratedFDeriv ℝ j (fun y => (ρ y)⁻¹) x‖ ≤ C) →
      ∀ j ≤ h,
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionB e ρ n (n*(n+2)) U X y-1) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => scalarCorrectionS e ρ n (n*(n+2)) U X y-1) x‖ ≤
        K*n^((2*B+21)*(h+2)+10)/(n^D) := by
  let Cd : ℝ := 2^(h+1)*C*C*(1+∑ i, ‖e i‖)
  let A : ℝ := 2^(h+1)*C*C
  let Kq : ℝ := 2*A*((h+1).factorial:ℝ)^2*(1+max 1 (2*Cd))^(h+1)
  let Kv : ℝ := 2+2^(2*h+1)*C*C*(∑ i, ‖e i‖)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hKq : 0 < Kq := by
    have hc : 0 < (1+max 1 (2*Cd)) := by have := le_max_left (1:ℝ) (2*Cd); linarith
    dsimp only [Kq]
    positivity
  have hKv : 0 < Kv := by dsimp only [Kv]; positivity
  refine ⟨Kv*Kq, mul_pos hKv hKq, ?_⟩
  intro n hn D U X hU hX hden x hxO W hW hx hUj hXj hRj hρj hρij j hj
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  let R : E → ℝ := fun y => coordinateDivergence e ρ X y+n*(n+2)*U y
  let d := scalarCorrectionDenominator e n U X
  have hR : ContDiffOn ℝ ∞ R O :=
    (contDiffOn_coordinateDivergence e hO hρ hX hρp).add (contDiffOn_const.mul hU)
  have hd : ContDiffOn ℝ ∞ d O := contDiffOn_scalarCorrectionDenominator e n hO hU hX
  have hRj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k R x‖ ≤ C*n^(4+k)/(n^D)*W := by
    intro k hk
    apply (hRj k hk).trans
    gcongr
    omega
  have hUj' : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k U x‖ ≤ C*n^(4+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hUj k (by omega)
  have hXj' (i : ι) : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k (X i) x‖ ≤ C*n^(5+k)*W := by
    intro k hk
    simpa only [Nat.add_comm] using hXj i k hk
  have hdj : ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k d x‖ ≤ Cd*n^(k+10)*W^2 :=
    scalar_denominator_jet_bound_on e U X hO hxO hU hX (h+1) hn hW hC.le
      (fun k hk => hUj k (by omega)) hXj
  have hRU := frequency_weighted_product_bound_on hO hxO hR hU (h+1) 4 4 D hn hW hC.le hC.le hRj' hUj'
  have hRX (i : ι) := frequency_weighted_product_bound_on hO hxO hR (hX i) (h+1) 4 5 D hn hW hC.le hC.le hRj' (hXj' i)
  have hqU := frequency_weighted_quotient_uniform_on hO hxO (hR.mul hU) hd (h+1) B 8 D hn hW hA.le hx hRU
    (fun k _ hk => hdj k hk)
  have hqX (i : ι) := frequency_weighted_quotient_uniform_on hO hxO (hR.mul (hX i)) hd (h+1) B 9 D hn hW hA.le hx (hRX i)
    (fun k _ hk => hdj k hk)
  let T : ℕ := 9+2*B+(2*B+11)*(h+1)
  let F : ℝ := Kq*n^T/(n^D)
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hqu : ∀ k ≤ h, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) x‖ ≤ F := by
    intro k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*U y) =
        fun y => (R y*U y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    apply (hqU k (by omega)).trans
    change Kq*n^(8+2*B+(2*B+11)*(h+1))/(n^D) ≤ Kq*n^T/(n^D)
    gcongr
    dsimp only [T]; omega
  have hqx : ∀ i, ∀ k ≤ h+1, ‖iteratedFDeriv ℝ k
      (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) x‖ ≤ F := by
    intro i k hk
    have he : (fun y => scalarCorrectionRatio e ρ n (n*(n+2)) U X y*X i y) =
        fun y => (R y*X i y)/d y := by
      funext y
      dsimp only [scalarCorrectionRatio,R,d]
      ring
    rw [he]
    exact hqX i k hk
  have hb := scalar_correction_error_from_quotients_on e ρ U X hO hxO hρ hρp hU hX hn hden h hC.le hF hρj hρij hqu hqx j hj
  apply hb.trans
  change Kv*(Kq*n^T/(n^D)) ≤ Kv*Kq*n^((2*B+21)*(h+2)+10)/(n^D)
  rw [show Kv*(Kq*n^T/(n^D))=Kv*Kq*n^T/(n^D) by ring]
  gcongr
  dsimp only [T]; nlinarith

end YauCounterexamples

end

end OAI
