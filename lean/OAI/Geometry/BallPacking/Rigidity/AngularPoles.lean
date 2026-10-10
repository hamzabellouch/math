import Mathlib
import OAI.Geometry.BallPacking.Rigidity.Correction

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

theorem planarCurl_congr {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (he : α =ᶠ[𝓝 z] β) : planarCurl α z = planarCurl β z := by
  simp only [planarCurl,he.fderiv_eq]

theorem planarCurl_sub {α β : Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : DifferentiableAt ℝ α z) (hβ : DifferentiableAt ℝ β z) :
    planarCurl (fun y => α y - β y) z = planarCurl α z - planarCurl β z := by
  simp only [planarCurl,fderiv_fun_sub hα hβ,sub_apply]
  ring

theorem planarCurl_const_smul (α : Plane → Plane →L[ℝ] ℝ) (c : ℝ) (z : Plane) :
    planarCurl (fun y => c • α y) z = c * planarCurl α z := by
  have he : fderiv ℝ (fun y => c • α y) z = c • fderiv ℝ α z :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := α) c) z
  simp only [planarCurl,he,smul_apply,smul_eq_mul]
  ring

theorem planarCurl_sum {ι : Type*} (P : Finset ι) {α : ι → Plane → Plane →L[ℝ] ℝ} {z : Plane}
    (hα : ∀ i ∈ P, DifferentiableAt ℝ (α i) z) :
    planarCurl (fun y => ∑ i ∈ P, α i y) z = ∑ i ∈ P, planarCurl (α i) z := by
  rw [planarCurl,fderiv_fun_sum hα]
  simp only [sum_apply,planarCurl]
  simp only [Finset.sum_sub_distrib]

theorem planarCurl_translate {α : Plane → Plane →L[ℝ] ℝ} (p z : Plane)
    (hα : DifferentiableAt ℝ α (z-p)) :
    planarCurl (fun y => α (y-p)) z = planarCurl α (z-p) := by
  have hh := hα.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const p)
  change HasFDerivAt (fun y => α (y-p)) _ z at hh
  simp only [planarCurl,hh.fderiv,ContinuousLinearMap.comp_id]

theorem angularOneForm_curl {z : Plane} (hz : z ≠ 0) : planarCurl angularOneForm z = 0 := by
  have h := cutoffAngular_curl (point := z) (differentiableAt_const (1:ℝ)) (radiusSq_pos hz).ne'
  simpa only [one_smul,deriv_const,mul_zero] using h

def angularPole (p : Plane) (z : Plane) : Plane →L[ℝ] ℝ := angularOneForm (z-p)

theorem angularPole_smoothAt {p z : Plane} (hz : z ≠ p) : ContDiffAt ℝ ∞ (angularPole p) z :=
  (angularOneForm_contDiffAt (radiusSq_pos (sub_ne_zero.mpr hz)).ne').comp z
    (contDiffAt_id.sub contDiffAt_const)

theorem angularPole_curl {p z : Plane} (hz : z ≠ p) : planarCurl (angularPole p) z = 0 := by
  unfold angularPole
  rw [planarCurl_translate p z
    ((angularOneForm_contDiffAt (radiusSq_pos (sub_ne_zero.mpr hz)).ne').differentiableAt (by simp))]
  exact angularOneForm_curl (sub_ne_zero.mpr hz)

theorem angularOneForm_rotation {z : Plane} (hz : z ≠ 0) :
    angularOneForm z (planeRotation z) = 1 := by
  change (radiusSq z)⁻¹ * (z.1*z.1-z.2*(-z.2)) = 1
  have he : z.1*z.1-z.2*(-z.2) = radiusSq z := by unfold radiusSq; ring
  rw [he,inv_mul_cancel₀ (radiusSq_pos hz).ne']

theorem angularPole_tendsto_fixed (p v : Plane) :
    Tendsto (fun z => angularPole p z v) (cocompact Plane) (𝓝 0) := by
  have ht : Tendsto (fun z : Plane => Complex.equivRealProdCLM.symm (z-p))
      (cocompact Plane) (cocompact ℂ) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact.comp
      (Homeomorph.subRight p).isClosedEmbedding.tendsto_cocompact
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hl : Tendsto (fun z : Plane =>
      ((Complex.equivRealProdCLM.symm (z-p))⁻¹ * Complex.equivRealProdCLM.symm v).im)
      (cocompact Plane) (𝓝 0) := by
    simpa only [zero_mul,Complex.zero_im,Function.comp_def] using
      (Complex.continuous_im.continuousAt.tendsto.comp ((hi.comp ht).mul_const
        (Complex.equivRealProdCLM.symm v)))
  apply hl.congr'
  filter_upwards [(isCompact_singleton (x := p)).compl_mem_cocompact] with z hz
  have hz' : z ≠ p := hz
  exact complex_winding_eq_angular (sub_ne_zero.mpr hz') v

theorem angularPole_tendsto_rotation (p : Plane) :
    Tendsto (fun z => angularPole p z (planeRotation z)) (cocompact Plane) (𝓝 1) := by
  have hl : Tendsto (fun z => 1 + angularPole p z (planeRotation p)) (cocompact Plane) (𝓝 1) := by
    simpa using (angularPole_tendsto_fixed p (planeRotation p)).const_add 1
  apply hl.congr'
  filter_upwards [(isCompact_singleton (x := p)).compl_mem_cocompact] with z hz
  have hz' : z ≠ p := hz
  have he : planeRotation z = planeRotation (z-p) + planeRotation p := by
    ext <;> simp [planeRotation]
    ring
  rw [he,map_add]
  change 1 + angularOneForm (z-p) (planeRotation p) =
    angularOneForm (z-p) (planeRotation (z-p)) + angularOneForm (z-p) (planeRotation p)
  rw [angularOneForm_rotation (sub_ne_zero.mpr hz')]

def poleSum (P : Finset Plane) (c : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  ∑ p ∈ P, c p • angularPole p z

theorem poleSum_smoothAt {P : Finset Plane} (c : Plane → ℝ) {z : Plane} (hz : z ∉ P) :
    ContDiffAt ℝ ∞ (poleSum P c) z := by
  apply ContDiffAt.sum
  intro p hp
  exact (contDiffAt_const (c := c p)).smul (angularPole_smoothAt (by rintro rfl; exact hz hp))

theorem poleSum_curl {P : Finset Plane} (c : Plane → ℝ) {z : Plane} (hz : z ∉ P) :
    planarCurl (poleSum P c) z = 0 := by
  unfold poleSum
  rw [planarCurl_sum P (α := fun p z => c p • angularPole p z) (fun p hp =>
    ((contDiffAt_const (c := c p)).smul (angularPole_smoothAt
      (by rintro rfl; exact hz hp))).differentiableAt (by simp))]
  apply Finset.sum_eq_zero
  intro p hp
  rw [planarCurl_const_smul,angularPole_curl (by rintro rfl; exact hz hp),mul_zero]

theorem poleSum_tendsto_rotation (P : Finset Plane) (c : Plane → ℝ) :
    Tendsto (fun z => poleSum P c z (planeRotation z)) (cocompact Plane) (𝓝 (∑ p ∈ P, c p)) := by
  have hl := tendsto_finsetSum P (fun p _ => (angularPole_tendsto_rotation p).const_mul (c p))
  simpa only [poleSum,sum_apply,smul_apply,smul_eq_mul,mul_one] using hl




theorem smooth_fill_finite (P : Finset Plane) (α : Plane → Plane →L[ℝ] ℝ)
    (hα : ∀ z, z ∉ P → ContDiffAt ℝ ∞ α z)
    (hlocal : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β p ∧ α =ᶠ[𝓝[≠] p] β) :
    ∃ F : Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ F ∧ ∀ z, z ∉ P → F z = α z := by
  classical
  choose β hβs hβe using hlocal
  let F : Plane → Plane →L[ℝ] ℝ := fun z => if hz : z ∈ P then β z hz z else α z
  refine ⟨F,contDiff_iff_contDiffAt.mpr ?_,fun z hz => dite_eq_right hz⟩
  intro p
  by_cases hp : p ∈ P
  · have hP : ∀ᶠ z in 𝓝 p, z ∈ P → z = p := by
      have hn : p ∈ ((P.erase p : Finset Plane) : Set Plane)ᶜ := by simp
      filter_upwards [(P.erase p).finite_toSet.isClosed.isOpen_compl.mem_nhds hn] with z hz hzP
      by_contra hzp
      exact hz (Finset.mem_erase.mpr ⟨hzp,hzP⟩)
    have he : F =ᶠ[𝓝 p] β p hp := by
      filter_upwards [hP,eventually_nhdsWithin_iff.mp (hβe p hp)] with z hz hez
      by_cases hzp : z = p
      · subst z
        simp only [F,dite_eq_left hp]
      · have hzP : z ∉ P := fun h => hzp (hz h)
        simp only [F,dite_eq_right hzP]
        exact hez hzp
    exact (hβs p hp).congr_of_eventuallyEq he
  · have he : F =ᶠ[𝓝 p] α := by
      filter_upwards [P.finite_toSet.isClosed.isOpen_compl.mem_nhds hp] with z hz
      exact dite_eq_right hz
    exact (hα p hp).congr_of_eventuallyEq he

theorem finite_residues_le_infinity (P : Finset Plane) (c : Plane → ℝ)
    (α : Plane → Plane →L[ℝ] ℝ)
    (hα : ∀ z, z ∉ P → ContDiffAt ℝ ∞ α z)
    (hcurl : ∀ z, z ∉ P → 0 ≤ planarCurl α z)
    (hres : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β p ∧
      α =ᶠ[𝓝[≠] p] fun z => c p • angularPole p z + β z)
    {k : ℝ} (hlim : Tendsto (fun z => α z (planeRotation z)) (cocompact Plane) (𝓝 k)) :
    (∑ p ∈ P, c p) ≤ k := by
  classical
  let γ : Plane → Plane →L[ℝ] ℝ := fun z => α z - poleSum P c z
  have hγs : ∀ z, z ∉ P → ContDiffAt ℝ ∞ γ z := fun z hz =>
    (hα z hz).sub (poleSum_smoothAt c hz)
  have hγlocal : ∀ p ∈ P, ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β p ∧ γ =ᶠ[𝓝[≠] p] β := by
    intro p hp
    obtain ⟨β,hβs,hβe⟩ := hres p hp
    refine ⟨fun z => β z - poleSum (P.erase p) c z,
      hβs.sub (poleSum_smoothAt c (by simp)),?_⟩
    filter_upwards [hβe] with z hz
    have hsum : poleSum P c z = c p • angularPole p z + poleSum (P.erase p) c z :=
      (Finset.add_sum_erase P (fun q => c q • angularPole q z) hp).symm
    dsimp only [γ]
    rw [hz,hsum]
    abel
  obtain ⟨F,hFs,hFe⟩ := smooth_fill_finite P γ hγs hγlocal
  have hFnear (z : Plane) (hz : z ∉ P) : F =ᶠ[𝓝 z] γ := by
    filter_upwards [P.finite_toSet.isClosed.isOpen_compl.mem_nhds hz] with y hy
    exact hFe y hy
  have hFc : ∀ z, z ∉ P → 0 ≤ planarCurl F z := by
    intro z hz
    rw [planarCurl_congr (hFnear z hz)]
    change 0 ≤ planarCurl (fun y => α y - poleSum P c y) z
    rw [planarCurl_sub ((hα z hz).differentiableAt (by simp))
      ((poleSum_smoothAt c hz).differentiableAt (by simp)),poleSum_curl c hz,sub_zero]
    exact hcurl z hz
  have hFcAll : ∀ z, 0 ≤ planarCurl F z := by
    have hd : Dense ((P : Set Plane)ᶜ) := by
      convert dense_univ.sdiff_finset P using 1
      ext z
      simp only [mem_compl_iff,Set.mem_sdiff,mem_univ,true_and,Finset.mem_coe]
    have hc : IsClosed {z : Plane | 0 ≤ planarCurl F z} :=
      isClosed_le continuous_const (planarCurl_contDiff hFs).continuous
    have hs : closure ((P : Set Plane)ᶜ) ⊆ {z : Plane | 0 ≤ planarCurl F z} :=
      closure_minimal (fun z hz => hFc z hz) hc
    intro z
    apply hs
    rw [hd.closure_eq]
    exact mem_univ z
  have hFlim : Tendsto (fun z => F z (planeRotation z)) (cocompact Plane)
      (𝓝 (k - ∑ p ∈ P, c p)) := by
    apply (hlim.sub (poleSum_tendsto_rotation P c)).congr'
    filter_upwards [P.finite_toSet.isCompact.compl_mem_cocompact] with z hz
    rw [hFe z hz]
    rfl
  exact sub_nonneg.mp (nonneg_angular_limit_of_nonneg_curl hFs hFcAll hFlim)


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)

theorem realCurve_translate {n : ℕ} (v : ℂ → Phase n) (a : ℂ) :
    realCurve (fun z => v (z+a)) = fun z => realCurve v (z+Complex.equivRealProdCLM a) := by
  funext z
  simp only [realCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

theorem planarPullback_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α : E → E →L[ℝ] ℝ) (a z : Plane) :
    planarPullback (fun y => v (y+a)) α z = planarPullback v α (z+a) := by
  simp only [planarPullback,fderiv_comp_add_right]

theorem tendsto_sub_punctured (p : Plane) :
    Tendsto (fun z : Plane => z-p) (𝓝[≠] p) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht : Tendsto (fun z : Plane => z-p) (𝓝 p) (𝓝 (p-p)) :=
      (continuous_id.sub continuous_const).continuousAt.tendsto
    simpa only [sub_self] using ht.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact sub_ne_zero.mpr hz

theorem blowup_branch_residue_at {n : ℕ} {v h : ℂ → Phase n} {m : ℕ} {a : ℂ}
    (hm : 0 < m) (hh : AnalyticAt ℂ h a) (hh0 : h a ≠ 0)
    (he : v =ᶠ[𝓝 a] fun z : ℂ => (z-a)^m • h z)
    {σ τ : ℝ} (hσ : 0 < σ) (hστ : σ < τ) :
    ∃ β : Plane → Plane →L[ℝ] ℝ, ContDiffAt ℝ ∞ β (Complex.equivRealProdCLM a) ∧
      ∀ᶠ z in 𝓝[≠] (Complex.equivRealProdCLM a),
        planarPullback (realCurve v) (blowupPrimitive σ τ) z =
          ((blowupSize σ τ * (m:ℝ)) / (2 * Real.pi)) • angularPole (Complex.equivRealProdCLM a) z + β z := by
  have ht : Tendsto (fun z : ℂ => z+a) (𝓝 0) (𝓝 a) := by
    have ht : Tendsto (fun z : ℂ => z+a) (𝓝 0) (𝓝 (0+a)) :=
      (continuous_id.add continuous_const).continuousAt.tendsto
    simpa only [zero_add] using ht
  have hh' : AnalyticAt ℂ (fun z : ℂ => h (z+a)) 0 := by
    have hh1 : AnalyticAt ℂ h (0+a) := by simpa only [zero_add] using hh
    exact hh1.comp (f := fun z : ℂ => z+a) (analyticAt_id.add analyticAt_const)
  have hh0' : (fun z : ℂ => h (z+a)) 0 ≠ 0 := by simpa using hh0
  have he' : (fun z : ℂ => v (z+a)) =ᶠ[𝓝 0] fun z : ℂ => z^m • h (z+a) := by
    filter_upwards [ht.eventually he] with z hz
    simpa only [add_sub_cancel_right] using hz
  obtain ⟨β,hβs,hβe⟩ := blowup_branch_residue hm hh' hh0' he' hσ hστ
  let p := Complex.equivRealProdCLM a
  refine ⟨fun z => β (z-p),?_,?_⟩
  · have hh : ContDiffAt ℝ ∞ β (p-p) := by simpa only [sub_self] using hβs
    have hs : ContDiffAt ℝ ∞ (fun z : Plane => z-p) p :=
      contDiffAt_id.sub contDiffAt_const
    exact hh.comp p (f := fun z : Plane => z-p) hs
  · filter_upwards [(tendsto_sub_punctured p).eventually hβe] with z hz
    rw [realCurve_translate,planarPullback_translate,sub_add_cancel] at hz
    exact hz


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)

def correctedPrimitive {n : ℕ} (S T : ℝ) (U : Fin 2 → Set (Phase n))
    (f : Fin 2 → Phase n → Phase n) (σ τ : Fin 2 → ℝ) (y : Phase n) : Phase n →L[ℝ] ℝ :=
  radialPrimitiveCLM S T y + chartCorrection (U 0) (f 0) (σ 0) (τ 0) y +
    chartCorrection (U 1) (f 1) (σ 1) (τ 1) y

theorem correctedPrimitive_smoothAt {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) :
    ContDiffAt ℝ ∞ (correctedPrimitive S T U f σ τ) y :=
  ((radialPrimitiveCLM_smooth hST).contDiffAt.add
    (chartCorrection_smoothAt (hf 0) (hτ 0) (hστ 0) (hsub 0) (hy 0))).add
    (chartCorrection_smoothAt (hf 1) (hτ 1) (hστ 1) (hsub 1) (hy 1))

theorem chartCorrection_extDeriv_zero {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f) {σ τ : ℝ}
    (hτ : 0 < τ) (hστ : σ < τ) (hsub : closedBall n τ ⊆ U)
    {y : Phase n} (hy : y ∉ f '' closedBall n τ) (v w : Phase n) :
    extDeriv (oneForm (chartCorrection U f σ τ)) y ![v,w] = 0 := by
  rw [oneForm_extDeriv_congr (chartCorrection_zero_near hf hτ hστ hsub hy)]
  change extDeriv (oneForm (fun _ : Phase n => (0 : Phase n →L[ℝ] ℝ))) y ![v,w] = 0
  rw [oneForm_extDeriv_apply (differentiableAt_const _)]
  simp

theorem correctedPrimitive_extDeriv {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) (v w : Phase n) :
    extDeriv (oneForm (correctedPrimitive S T U f σ τ)) y ![v,w] =
      radialForm S T y v w +
      extDeriv (oneForm (chartCorrection (U 0) (f 0) (σ 0) (τ 0))) y ![v,w] +
      extDeriv (oneForm (chartCorrection (U 1) (f 1) (σ 1) (τ 1))) y ![v,w] := by
  have hr := (radialPrimitiveCLM_smooth hST).differentiable (by simp) y
  have hc (i : Fin 2) :=
    (chartCorrection_smoothAt (hf i) (hτ i) (hστ i) (hsub i) (hy i)).differentiableAt (by simp)
  unfold correctedPrimitive
  rw [oneForm_extDeriv_add (hr.fun_add (hc 0)) (hc 1),
    oneForm_extDeriv_add hr (hc 0)]
  have he : oneForm (@radialPrimitiveCLM n S T) = radialPrimitive S T := rfl
  rw [he,radialForm_extDeriv hST]

theorem radialForm_adapted_nonneg {n : ℕ} {S T : ℝ} (hST : S < T) (hT : T < 1)
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n) (x v : Phase n) :
    0 ≤ radialForm S T x v (J x v) := by
  by_cases hv : v = 0
  · subst v
    simp [radialForm,standardForm,stdDot]
  · exact (radialForm_adapted_pos hST hT hJ hout x hv).le

theorem correctedPrimitive_extDeriv_nonneg {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    {y : Phase n} (hy : ∀ i, y ≠ f i 0) (v : Phase n) :
    0 ≤ extDeriv (oneForm (correctedPrimitive S T U f σ τ)) y ![v,J y v] := by
  rw [correctedPrimitive_extDeriv hST hf hτ hστ hsub hy]
  have hloc (i : Fin 2) (hi : y ∈ f i '' closedBall n (τ i)) :
      radialForm S T y v (J y v) +
        extDeriv (oneForm (chartCorrection (U i) (f i) (σ i) (τ i))) y ![v,J y v] ≥ 0 := by
    have hU : y ∈ f i '' U i := image_mono (hsub i) hi
    have hσy : y ∈ closedBall n S := by
      obtain ⟨x,hx,rfl⟩ := hi
      exact hcap i hx
    have hx : invFunOn (f i) (U i) y ≠ 0 := by
      intro he
      have hi := invFunOn_eq hU
      rw [he] at hi
      exact hy i hi.symm
    rw [radialForm_standard hST hσy,chartCorrection_extDeriv (hf i) hU (hy i),
      hJi i y hi,inverse_fderiv_intertwines (hf i) hU]
    have hn := blowupPrimitive_extDeriv_nonneg (hστ i) hx
      (fderiv ℝ (invFunOn (f i) (U i)) y v)
    linarith only [hn]
  by_cases h0 : y ∈ f 0 '' closedBall n (τ 0)
  · have h1 : y ∉ f 1 '' closedBall n (τ 1) := fun h => disjoint_left.mp hdis h0 h
    rw [chartCorrection_extDeriv_zero (hf 1) (hτ 1) (hστ 1) (hsub 1) h1,add_zero]
    exact hloc 0 h0
  · rw [chartCorrection_extDeriv_zero (hf 0) (hτ 0) (hστ 0) (hsub 0) h0,add_zero]
    by_cases h1 : y ∈ f 1 '' closedBall n (τ 1)
    · exact hloc 1 h1
    · rw [chartCorrection_extDeriv_zero (hf 1) (hτ 1) (hστ 1) (hsub 1) h1,add_zero]
      exact radialForm_adapted_nonneg hST hT hJ hout y v

theorem correctedCurve_curl_nonneg {n : ℕ} {S T : ℝ}
    (hST : S < T) (hT : T < 1)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hdis : Disjoint (f 0 '' closedBall n (τ 0)) (f 1 '' closedBall n (τ 1)))
    (hcap : ∀ i, MapsTo (f i) (closedBall n (τ i)) (closedBall n S))
    {J : Phase n → End n} (hJ : ∀ x, Compatible (J x))
    (hout : ∀ x, S < capacity x → J x = standardJ n)
    (hJi : ∀ i, ∀ y ∈ f i '' closedBall n (τ i), J y = imageJ (U i) (f i) y)
    {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (hCR : ∀ z, PseudoHolomorphicAt J u z)
    {z : Plane} (hz : ∀ i, realCurve u z ≠ f i 0) :
    0 ≤ planarCurl (planarPullback (realCurve u) (correctedPrimitive S T U f σ τ)) z := by
  rw [planarPullback_curlAt (realCurve_smooth hu).contDiffAt
    (correctedPrimitive_smoothAt hST hf hτ hστ hsub hz),realCurve_CR (hCR _)]
  exact correctedPrimitive_extDeriv_nonneg hST hT hf hτ hστ hsub hdis hcap hJ hout hJi hz _


end

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem inversePullback_sub {n : ℕ} (U : Set (Phase n)) (f : Phase n → Phase n)
    (α β : Phase n → Phase n →L[ℝ] ℝ) (y : Phase n) :
    inversePullback U f (fun x => α x - β x) y =
      inversePullback U f α y - inversePullback U f β y := by
  simp only [inversePullback,ContinuousLinearMap.sub_comp]

theorem correctedPrimitive_centre_remainder {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hτ : ∀ i, 0 < τ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hne : f 0 0 ≠ f 1 0) (i : Fin 2) :
    ∃ γ : Phase n → Phase n →L[ℝ] ℝ, ContDiffAt ℝ ∞ γ (f i 0) ∧
      correctedPrimitive S T U f σ τ =ᶠ[𝓝 (f i 0)]
        fun y => inversePullback (U i) (f i) (blowupPrimitive (σ i) (τ i)) y + γ y := by
  have h0 (j : Fin 2) : (0 : Phase n) ∈ U j := hsub j (by simpa [closedBall,capacity] using (hτ j).le)
  have hmem (j : Fin 2) : f j 0 ∈ f j '' U j := mem_image_of_mem _ (h0 j)
  have hs (j : Fin 2) : ContDiffAt ℝ ∞ (inversePullback (U j) (f j) stdPrimitive) (f j 0) :=
    inversePullback_smoothAt (hf j) (hmem j) (stdPrimitive_smooth n).contDiffAt
  fin_cases i
  · refine ⟨fun y => radialPrimitiveCLM S T y + chartCorrection (U 1) (f 1) (σ 1) (τ 1) y -
        inversePullback (U 0) (f 0) stdPrimitive y,?_,?_⟩
    · exact ((radialPrimitiveCLM_smooth hST).contDiffAt.add
        (chartCorrection_smoothAt (hf 1) (hτ 1) (hστ 1) (hsub 1) hne)).sub (hs 0)
    · filter_upwards [chartCorrection_eq_near (hf 0) (hmem 0) (σ 0) (τ 0)] with y hy
      simp only [Fin.mk_zero,correctedPrimitive,hy,inversePullback_sub]
      ext w
      simp only [add_apply,sub_apply]
      ring
  · refine ⟨fun y => radialPrimitiveCLM S T y + chartCorrection (U 0) (f 0) (σ 0) (τ 0) y -
        inversePullback (U 1) (f 1) stdPrimitive y,?_,?_⟩
    · exact ((radialPrimitiveCLM_smooth hST).contDiffAt.add
        (chartCorrection_smoothAt (hf 0) (hτ 0) (hστ 0) (hsub 0) hne.symm)).sub (hs 1)
    · filter_upwards [chartCorrection_eq_near (hf 1) (hmem 1) (σ 1) (τ 1)] with y hy
      simp only [Fin.mk_one,correctedPrimitive,hy,inversePullback_sub]
      ext w
      simp only [add_apply,sub_apply]
      ring

theorem planarPullback_inverse {n : ℕ} {U : Set (Phase n)}
    {f : Phase n → Phase n} (hf : SymplecticOn U f)
    {u : ℂ → Phase n} {z : Plane} (hu : DifferentiableAt ℝ (realCurve u) z)
    (hz : realCurve u z ∈ f '' U) (α : Phase n → Phase n →L[ℝ] ℝ) :
    planarPullback (realCurve u) (inversePullback U f α) z =
      planarPullback (realCurve (invFunOn f U ∘ u)) α z := by
  have hd := ((symplecticOn_inverse_smooth hf).contDiffAt
    ((symplecticOn_open_image hf).mem_nhds hz)).differentiableAt (by simp)
  have hc : realCurve (invFunOn f U ∘ u) = invFunOn f U ∘ realCurve u := rfl
  rw [hc]
  unfold planarPullback inversePullback
  rw [fderiv_comp z hd hu]
  rfl

theorem planarPullback_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : Plane → E) (α β : E → E →L[ℝ] ℝ) (z : Plane) :
    planarPullback v (fun y => α y + β y) z = planarPullback v α z + planarPullback v β z := by
  simp only [planarPullback,ContinuousLinearMap.add_comp]

theorem correctedPrimitive_centre_residue {n : ℕ} {S T : ℝ} (hST : S < T)
    {U : Fin 2 → Set (Phase n)} {f : Fin 2 → Phase n → Phase n} {σ τ : Fin 2 → ℝ}
    (hf : ∀ i, SymplecticOn (U i) (f i)) (hσ : ∀ i, 0 < σ i)
    (hστ : ∀ i, σ i < τ i) (hsub : ∀ i, closedBall n (τ i) ⊆ U i)
    (hne : f 0 0 ≠ f 1 0)
    {J : Phase n → End n} {p q : Phase n} {u : ℂ → Phase n}
    (hu : AffineLineCurve J p q u)
    (hJ : ∀ i, ∀ᶠ y in 𝓝 (f i 0), J y = imageJ (U i) (f i) y)
    (i : Fin 2) {a : ℂ} (ha : u a = f i 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ β : Plane → Plane →L[ℝ] ℝ,
      ContDiffAt ℝ ∞ β (Complex.equivRealProdCLM a) ∧
      ∀ᶠ z in 𝓝[≠] (Complex.equivRealProdCLM a),
        planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z =
          ((blowupSize (σ i) (τ i) * (m:ℝ)) / (2 * Real.pi)) •
            angularPole (Complex.equivRealProdCLM a) z + β z := by
  have hτ (j : Fin 2) : 0 < τ j := (hσ j).trans (hστ j)
  have h0 (j : Fin 2) : (0 : Phase n) ∈ U j := hsub j (by simpa [closedBall,capacity] using (hτ j).le)
  obtain ⟨m,v,hm,hvs,hv0,hve⟩ := chart_centre_positive_order (hf i) (h0 i) hu.2.1
    (hu.not_constant _) (hJ i) ha
  obtain ⟨β,hβs,hβe⟩ := blowup_branch_residue_at hm hvs hv0 hve (hσ i) (hστ i)
  obtain ⟨γ,hγs,hγe⟩ := correctedPrimitive_centre_remainder hST hf hτ hστ hsub hne i
  let b := Complex.equivRealProdCLM a
  have hb : realCurve u b = f i 0 := by
    change u (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM a)) = f i 0
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ha
  have hus := realCurve_smooth hu.1
  have hpbγ : ContDiffAt ℝ ∞ (planarPullback (realCurve u) γ) b :=
    planarPullback_smoothAt hus.contDiffAt (hb.symm ▸ hγs)
  refine ⟨m,hm,fun z => β z + planarPullback (realCurve u) γ z,hβs.add hpbγ,?_⟩
  have hut : Tendsto (realCurve u) (𝓝 b) (𝓝 (f i 0)) := hb ▸ hus.continuous.tendsto b
  have him : ∀ᶠ z in 𝓝 b, realCurve u z ∈ f i '' U i := hut.eventually
    ((symplecticOn_open_image (hf i)).mem_nhds (mem_image_of_mem _ (h0 i)))
  filter_upwards [hβe,(hut.eventually hγe).filter_mono nhdsWithin_le_nhds,
    him.filter_mono nhdsWithin_le_nhds] with z hzz hγz hiz
  have he : planarPullback (realCurve u) (correctedPrimitive S T U f σ τ) z =
      planarPullback (realCurve u) (inversePullback (U i) (f i) (blowupPrimitive (σ i) (τ i))) z +
      planarPullback (realCurve u) γ z := by
    unfold planarPullback
    rw [hγz,ContinuousLinearMap.add_comp]
  rw [he,planarPullback_inverse (hf i) (hus.differentiable (by simp) z) hiz,hzz]
  abel


end

open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian (Plane)

theorem complex_inv_fderiv_real {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y⁻¹) z w = -(z^2)⁻¹ * w := by
  rw [((hasDerivAt_inv hz).hasFDerivAt.restrictScalars ℝ).fderiv]
  change w * (-(z^2)⁻¹) = _
  ring

theorem infinity_curve_fderiv {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (w : ℂ) :
    fderiv ℝ (fun y : ℂ => y • h y⁻¹) z w =
      w • h z⁻¹ + z • fderiv ℝ h z⁻¹ (-(z^2)⁻¹ * w) := by
  have hi : DifferentiableAt ℝ (fun y : ℂ => y⁻¹) z :=
    (hasDerivAt_inv hz).differentiableAt.restrictScalars ℝ
  have hid : DifferentiableAt ℝ (fun y : ℂ => y) z := differentiableAt_id
  have hcomp : DifferentiableAt ℝ (fun y : ℂ => h y⁻¹) z := hh.comp z hi
  rw [fderiv_fun_smul hid hcomp]
  simp only [add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,fderiv_fun_id,
    ContinuousLinearMap.id_apply]
  have hder : HasFDerivAt (fun y : ℂ => h y⁻¹)
      ((fderiv ℝ h z⁻¹).comp (fderiv ℝ (fun y : ℂ => y⁻¹) z)) z :=
    hh.hasFDerivAt.comp z hi.hasFDerivAt
  rw [hder.fderiv,ContinuousLinearMap.comp_apply,complex_inv_fderiv_real hz]
  module

theorem normalizedPrimitive_infinity_curve {n : ℕ} {h : ℂ → Phase n} {z : ℂ}
    (hz : z ≠ 0) (hh : DifferentiableAt ℝ h z⁻¹) (hh0 : h z⁻¹ ≠ 0) :
    normalizedPrimitive (z • h z⁻¹) (fderiv ℝ (fun y : ℂ => y • h y⁻¹) z (Complex.I*z)) =
      1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)) := by
  rw [infinity_curve_fderiv hz hh,normalizedPrimitive_smul hz hh0]
  have h1 : z⁻¹ * (Complex.I*z) = Complex.I := by field_simp
  have h2 : -(z^2)⁻¹ * (Complex.I*z) = -Complex.I*z⁻¹ := by field_simp
  rw [h1,h2,Complex.I_im]

theorem infinityGerm_curve_eventuallyEq {n : ℕ} (u : ℂ → Phase n) (v : Phase n) :
    u =ᶠ[cocompact ℂ] fun z : ℂ => z • infinityGerm u v z⁻¹ := by
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz' : z ≠ 0 := hz
  simp only [infinityGerm,inv_ne_zero hz',ite_false,inv_inv,smul_smul,
    mul_inv_cancel₀ hz',one_smul]

theorem normalizedPrimitive_infinity_limit {n : ℕ} {u : ℂ → Phase n} {v : Phase n}
    (hv : v ≠ 0) (hh : AnalyticAt ℂ (infinityGerm u v) 0) :
    Tendsto (fun z : ℂ => normalizedPrimitive (u z) (fderiv ℝ u z (Complex.I*z)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
  let h := infinityGerm u v
  have hh0 : h 0 ≠ 0 := by simpa [h,infinityGerm] using hv
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa only [←Metric.cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))
  have hc : ContDiffAt ℝ ∞ h 0 := hh.contDiffAt.restrict_scalars ℝ
  have hdh : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹) (cocompact ℂ) (𝓝 (fderiv ℝ h 0)) :=
    (hc.fderiv_right (m := 0) (by simp)).continuousAt.tendsto.comp hi
  have harg : Tendsto (fun z : ℂ => -Complex.I*z⁻¹) (cocompact ℂ) (𝓝 0) := by
    simpa using hi.const_mul (-Complex.I)
  have hvec : Tendsto (fun z : ℂ => fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹))
      (cocompact ℂ) (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hdh.prodMk_nhds harg)
  have hprim : Tendsto (fun z : ℂ => normalizedPrimitive (h z⁻¹))
      (cocompact ℂ) (𝓝 (normalizedPrimitive (h 0))) :=
    (normalizedPrimitive_smoothAt hh0).continuousAt.tendsto.comp (hc.continuousAt.tendsto.comp hi)
  have hl : Tendsto (fun z : ℂ => 1 / (2 * Real.pi) +
      normalizedPrimitive (h z⁻¹) (fderiv ℝ h z⁻¹ (-Complex.I*z⁻¹)))
      (cocompact ℂ) (𝓝 (1 / (2 * Real.pi))) := by
    simpa only [Function.comp_def,map_zero,add_zero] using ((continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (hprim.prodMk_nhds hvec)).const_add (1 / (2 * Real.pi))
  apply hl.congr'
  have he := infinityGerm_curve_eventuallyEq u v
  have hnear : ∀ᶠ z in cocompact ℂ, u =ᶠ[𝓝 z] fun y : ℂ => y • h y⁻¹ := by
    filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with y hy
    have hy' : y ≠ 0 := hy
    simp only [h,infinityGerm,inv_ne_zero hy',ite_false,inv_inv,smul_smul,
      mul_inv_cancel₀ hy',one_smul]
  have hn : ∀ᶠ w in 𝓝 (0:ℂ), h w ≠ 0 :=
    hc.continuousAt.eventually (isClosed_singleton.isOpen_compl.mem_nhds hh0)
  have hd : ∀ᶠ w in 𝓝 (0:ℂ), DifferentiableAt ℝ h w :=
    hh.eventually_analyticAt.mono fun _ hx => hx.differentiableAt.restrictScalars ℝ
  filter_upwards [hnear,hi.eventually hn,hi.eventually hd,
    (isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hez hnz hdz hz
  rw [hez.self_of_nhds,hez.fderiv_eq]
  exact (normalizedPrimitive_infinity_curve hz hdz hnz).symm

theorem equivRealProd_rotation (z : Plane) :
    Complex.equivRealProdCLM.symm (planeRotation z) =
      Complex.I * Complex.equivRealProdCLM.symm z := by
  apply Complex.ext <;> simp [planeRotation,Complex.equivRealProdCLM_symm_apply]



end HigherDimensionalBallPacking.Rigidity
end

end OAI
