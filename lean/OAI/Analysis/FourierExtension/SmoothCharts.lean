import Mathlib
import OAI.Analysis.FourierExtension.Surface

namespace OAI

/-! Smooth regular levels and positively curved charts. -/

open MeasureTheory
open scoped NNReal ENNReal ContDiff
noncomputable section

open Filter
open scoped Topology ContDiff

namespace DiagonalExtension.SmoothLevel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_height [CompleteSpace E] {F : E → ℝ} {a : E}
    (hF : ContDiffAt ℝ ∞ F a) (hreg : fderiv ℝ F a ≠ 0) :
    ∃ (n : E) (h : (fderiv ℝ F a).ker → ℝ),
      fderiv ℝ F a n = -1 ∧ ContDiffAt ℝ ∞ h 0 ∧ h 0 = 0 ∧
      fderiv ℝ h 0 = 0 ∧
      (∀ᶠ (v : (fderiv ℝ F a).ker) in 𝓝 0,
        F (a + (v : E) + h v • n) = F a) ∧
      (∀ᶠ (z : (fderiv ℝ F a).ker × ℝ) in 𝓝 0,
        F (a + (z.1 : E) + z.2 • n) = F a ↔ h z.1 = z.2) := by
  let K := (fderiv ℝ F a).ker
  have hnz : (fderiv ℝ F a).toLinearMap ≠ 0 := by
    intro hh
    apply hreg
    ext x
    exact DFunLike.congr_fun hh x
  obtain ⟨n,hn⟩ := (LinearMap.range_eq_top.mp
    (Module.Dual.range_eq_top_of_ne_zero hnz)) (-1)
  change fderiv ℝ F a n = -1 at hn
  let L : K × ℝ →L[ℝ] E :=
    K.subtypeL.comp (ContinuousLinearMap.fst ℝ K ℝ) +
      (ContinuousLinearMap.snd ℝ K ℝ).smulRight n
  let f : K × ℝ → ℝ := fun z => F (a + L z)
  have hL : ∀ z : K × ℝ, L z = (z.1 : E) + z.2 • n := by intro z; rfl
  have hf : ContDiffAt ℝ ∞ f 0 := by
    have hg : ContDiffAt ℝ ∞ (fun z : K × ℝ => a + L z) 0 := by fun_prop
    have hh : ContDiffAt ℝ ∞ F (a + L 0) := by simpa using hF
    exact hh.comp 0 hg
  have hdf : fderiv ℝ f 0 = (fderiv ℝ F a).comp L := by
    have hh : HasFDerivAt F (fderiv ℝ F a) (a + L 0) := by
      simpa using (hF.differentiableAt (by simp)).hasFDerivAt
    exact (hh.comp 0 (L.hasFDerivAt.const_add a)).fderiv
  have hdvert : fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ K ℝ =
      -(ContinuousLinearMap.id ℝ ℝ) := by
    rw [hdf]
    ext
    simp [L, hn]
  have hdin : fderiv ℝ f 0 ∘L ContinuousLinearMap.inl ℝ K ℝ = 0 := by
    rw [hdf]
    ext v
    simp [L]
  have hv : (fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ K ℝ).IsInvertible := by
    rw [hdvert]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := -(ContinuousLinearMap.id ℝ ℝ)) <;>
      ext <;> simp
  let h := hf.implicitFunction (by simp) hv
  refine ⟨n,h,hn,hf.contDiffAt_implicitFunction (by simp) hv,
    hf.implicitFunction_apply_self (by simp) hv,?_,?_,?_⟩
  · simpa [hdin] using (hf.hasStrictFDerivAt_implicitFunction (by simp) hv).hasFDerivAt.fderiv
  · simpa [f,h,hL, add_assoc] using
      hf.eventually_apply_implicitFunction (by simp) hv
  · simpa [f,h,hL, add_assoc] using
      hf.eventually_apply_eq_iff_implicitFunction (by simp) hv

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma second_level_equation {F : E → ℝ} {g : V → E} {b : V} {c : ℝ}
    (hF : ContDiffAt ℝ ∞ F (g b)) (hg : ContDiffAt ℝ ∞ g b)
    (he : (fun y => F (g y)) =ᶠ[𝓝 b] fun _ => c) (v w : V) :
    fderiv ℝ F (g b) ((fderiv ℝ (fderiv ℝ g) b v) w) +
      (fderiv ℝ (fderiv ℝ F) (g b) (fderiv ℝ g b v)) (fderiv ℝ g b w) = 0 := by
  have hg1 := (hg.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
  have hF1 := hg.continuousAt.eventually
    ((hF.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp))
  have hq : (fun y => fderiv ℝ F (g y) (fderiv ℝ g y w)) =ᶠ[𝓝 b] fun _ => (0 : ℝ) := by
    filter_upwards [hg1,hF1,he.fderiv (𝕜 := ℝ)] with y hgy hFy hy
    have hch := fderiv_comp y (hFy.differentiableAt (by simp))
      (hgy.differentiableAt (by simp))
    have hyw := DFunLike.congr_fun hy w
    rw [show (fun y => F (g y)) = F ∘ g from rfl, hch] at hyw
    simpa using hyw
  have hFD := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hgD := (hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hA := hFD.hasFDerivAt.comp b (hg.differentiableAt (by simp)).hasFDerivAt
  have hB := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp b hgD.hasFDerivAt
  have hd := (hA.clm_apply hB).fderiv
  have hz := hq.fderiv_eq (𝕜 := ℝ)
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply] at hd
  rw [hd] at hz
  have hh := DFunLike.congr_fun hz v
  simpa using hh

lemma height_hessian {F : E → ℝ} {a n : E}
    (hF : ContDiffAt ℝ ∞ F a) (hn : fderiv ℝ F a n = -1)
    {h : (fderiv ℝ F a).ker → ℝ} (hh : ContDiffAt ℝ ∞ h 0)
    (hh0 : h 0 = 0) (hd0 : fderiv ℝ h 0 = 0)
    (he : ∀ᶠ (v : (fderiv ℝ F a).ker) in 𝓝 0,
      F (a + (v : E) + h v • n) = F a)
    (v : (fderiv ℝ F a).ker) :
    (fderiv ℝ (fderiv ℝ h) 0 v) v =
      (fderiv ℝ (fderiv ℝ F) a (v : E)) (v : E) := by
  let K := (fderiv ℝ F a).ker
  let g : K → E := fun y => a + (y : E) + h y • n
  have hg : ContDiffAt ℝ ∞ g 0 := by
    exact (contDiffAt_const.add K.subtypeL.contDiff.contDiffAt).add
      (hh.smul contDiffAt_const)
  have hg0 : g 0 = a := by simp [g,hh0]
  have hdg {y : K} (hy : DifferentiableAt ℝ h y) :
      HasFDerivAt g (K.subtypeL + (fderiv ℝ h y).smulRight n) y :=
    (K.subtypeL.hasFDerivAt.const_add a).add (hy.hasFDerivAt.smul_const n)
  have hdg0 : fderiv ℝ g 0 = K.subtypeL := by
    simpa [hd0] using (hdg (hh.differentiableAt (by simp))).fderiv
  let A : (K →L[ℝ] ℝ) →L[ℝ] K →L[ℝ] E :=
    (ContinuousLinearMap.smulRightL ℝ K E).flip n
  have hnear : fderiv ℝ g =ᶠ[𝓝 0] fun y => K.subtypeL + A (fderiv ℝ h y) := by
    filter_upwards [(hh.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)] with y hy
    change ContDiffAt ℝ 1 h y at hy
    exact (hdg (hy.differentiableAt (by simp))).fderiv
  have hD := ((hh.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt
  have hA := (A.hasFDerivAt.comp 0 hD).const_add K.subtypeL
  simp only [Function.comp_apply] at hA
  have hsecond := hnear.fderiv_eq (𝕜 := ℝ)
  rw [hA.fderiv] at hsecond
  have hsecondv : (fderiv ℝ (fderiv ℝ g) 0 v) v =
      ((fderiv ℝ (fderiv ℝ h) 0 v) v) • n := by
    have hh := DFunLike.congr_fun (DFunLike.congr_fun hsecond v) v
    simpa [A] using hh
  have hEq := second_level_equation (g := g) (b := 0)
    (by simpa only [hg0] using hF) hg he v v
  rw [hg0,hdg0,hsecondv] at hEq
  simp only [Submodule.subtypeL_apply, map_smul, hn, smul_eq_mul] at hEq
  linarith

end DiagonalExtension.SmoothLevel

open Filter
open scoped Topology ContDiff
namespace DiagonalExtension.SmoothLevel
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

lemma eventually_contDiffAt_implicit {f : V × ℝ → ℝ} {U : Set (V × ℝ)}
    {u : V × ℝ} (hU : IsOpen U) (hu : u ∈ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hv : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ V ℝ).IsInvertible)
    {h : V → ℝ} (hh : ContDiffAt ℝ ∞ h u.1) (hh0 : h u.1 = u.2)
    (he : ∀ᶠ x in 𝓝 u.1, f (x,h x) = f u) :
    ∀ᶠ x in 𝓝 u.1, ContDiffAt ℝ ∞ h x := by
  have hfu : ContDiffAt ℝ ∞ f u := hf.contDiffAt (hU.mem_nhds hu)
  have hc : ContinuousAt (fun x => (x,h x)) u.1 := continuousAt_id.prodMk hh.continuousAt
  have hcu : Tendsto (fun x => (x,h x)) (𝓝 u.1) (𝓝 u) := by
    change Tendsto (fun x => (x,h x)) (𝓝 u.1) (𝓝 (u.1,h u.1)) at hc
    simpa only [hh0, Prod.eta] using hc
  have hD : ContinuousAt (fun z => fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ V ℝ) u :=
    (hfu.fderiv_right (m := ∞) (by simp)).continuousAt.clm_comp continuousAt_const
  have hinv : ∀ᶠ z in 𝓝 u,
      (fderiv ℝ f z ∘L ContinuousLinearMap.inr ℝ V ℝ).IsInvertible := by
    rcases hv with ⟨e,he⟩
    have heN := e.nhds
    rw [he] at heN
    exact hD.eventually heN
  have hH := (hh.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).eventually (by simp)
  filter_upwards [hcu.eventually (hU.mem_nhds hu),hcu.eventually hinv,hH,
    he.eventually_nhds,he] with x hxU hxv hxh hxe hxe0
  have hfx : ContDiffAt ℝ ∞ f (x,h x) := hf.contDiffAt (hU.mem_nhds hxU)
  let k := hfx.implicitFunction (by simp) hxv
  have hk : ContDiffAt ℝ ∞ k x := hfx.contDiffAt_implicitFunction (by simp) hxv
  have hxc : ContinuousAt (fun y => (y,h y)) x := continuousAt_id.prodMk hxh.continuousAt
  have hiff := hxc.eventually (hfx.eventually_apply_eq_iff_implicitFunction (by simp) hxv)
  have heq : k =ᶠ[𝓝 x] h := by
    filter_upwards [hxe,hiff] with y hy hyiff
    exact hyiff.mp (hy.trans hxe0.symm)
  exact hk.congr_of_eventuallyEq heq.symm

end DiagonalExtension.SmoothLevel

open Filter
open scoped Topology ContDiff
namespace DiagonalExtension.SmoothLevel
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

lemma positive_quadratic_lower (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ v : V, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖^2 ≤ B v v := by
  obtain ⟨c,hc,hbound⟩ := (isCompact_sphere (0 : V) 1).exists_forall_le'
    (f := fun v => B v v) (by fun_prop)
    (a := (0 : ℝ)) (fun v hv => hB v (by
      have hv' : ‖v‖ = 1 := by simpa using hv
      intro he; simp [he] at hv'))
  refine ⟨c,hc,fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn.ne']
  have hb := hbound (‖v‖⁻¹ • v) (by simpa using hu)
  simp only [map_smul, smul_apply, smul_eq_mul] at hb
  have hh := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  field_simp at hh
  nlinarith

variable {P : Type*} [TopologicalSpace P] {p : P}

lemma eventually_quadratic_lower {B : P → V →L[ℝ] V →L[ℝ] ℝ}
    (hB : ContinuousAt B p) (hp : ∀ v : V, v ≠ 0 → 0 < B p v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 p, ∀ v : V, c * ‖v‖^2 ≤ B x v v := by
  obtain ⟨k,hk,hbound⟩ := positive_quadratic_lower (B p) hp
  refine ⟨k/2,half_pos hk,?_⟩
  have he : ∀ᶠ x in 𝓝 p, ‖B x - B p‖ < k/2 := by
    filter_upwards [hB.eventually (Metric.ball_mem_nhds (B p) (half_pos hk))] with x hx
    change dist (B x) (B p) < k/2 at hx
    rwa [dist_eq_norm (B x) (B p)] at hx
  filter_upwards [he] with x hx
  intro v
  have heval : |B x v v - B p v v| ≤ ‖B x - B p‖ * ‖v‖^2 := by
    calc
      _ = ‖(B x - B p) v v‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖(B x - B p) v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖B x - B p‖ * ‖v‖) * ‖v‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
      _ = _ := by ring
  have hmul := mul_le_mul_of_nonneg_right hx.le (sq_nonneg ‖v‖)
  have hab := (abs_le.mp (heval.trans hmul)).1
  have hh := hbound v
  linarith

end DiagonalExtension.SmoothLevel

namespace DiagonalExtension.SmoothLevel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem exists_convex_height {F : E → ℝ} {a : E} {U : Set E}
    (hU : IsOpen U) (ha : a ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hreg : fderiv ℝ F a ≠ 0)
    (hpos : ∀ v : E, v ≠ 0 → fderiv ℝ F a v = 0 →
      0 < (fderiv ℝ (fderiv ℝ F) a v) v) :
    ∃ (n : E) (h : (fderiv ℝ F a).ker → ℝ) (c r : ℝ),
      0 < c ∧ 0 < r ∧ fderiv ℝ F a n = -1 ∧ h 0 = 0 ∧ fderiv ℝ h 0 = 0 ∧
      ContDiffOn ℝ ∞ h (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, ∀ v : (fderiv ℝ F a).ker,
        c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ h) x v) v) ∧
      (∀ (v : (fderiv ℝ F a).ker), v ∈ Metric.ball 0 r → F (a + (v : E) + h v • n) = F a) ∧
      (∀ z ∈ Metric.ball (0 : (fderiv ℝ F a).ker × ℝ) r,
        a + (z.1 : E) + z.2 • n ∈ U ∧
        (F (a + (z.1 : E) + z.2 • n) = F a ↔ h z.1 = z.2)) := by
  have hFa := hF.contDiffAt (hU.mem_nhds ha)
  obtain ⟨n,h,hn,hh,hh0,hd0,he,hiff⟩ := exists_height hFa hreg
  let K := (fderiv ℝ F a).ker
  let L : K × ℝ →L[ℝ] E :=
    K.subtypeL.comp (ContinuousLinearMap.fst ℝ K ℝ) +
      (ContinuousLinearMap.snd ℝ K ℝ).smulRight n
  let g : K × ℝ → E := fun z => a + L z
  let f : K × ℝ → ℝ := F ∘ g
  have hg : ContDiff ℝ ∞ g := by dsimp [g]; fun_prop
  have hg0 : g 0 = a := by simp [g]
  have hfu : ContDiffOn ℝ ∞ f (g ⁻¹' U) :=
    hF.comp hg.contDiffOn (fun _ hx => hx)
  have hf : ContDiffAt ℝ ∞ f 0 :=
    hfu.contDiffAt ((hU.preimage hg.continuous).mem_nhds (by simpa [hg0]))
  have hdf : fderiv ℝ f 0 = (fderiv ℝ F a).comp L := by
    have hhF : HasFDerivAt F (fderiv ℝ F a) (a + L 0) := by
      simpa using (hFa.differentiableAt (by simp)).hasFDerivAt
    exact (hhF.comp 0 (L.hasFDerivAt.const_add a)).fderiv
  have hdvert : fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ K ℝ =
      -(ContinuousLinearMap.id ℝ ℝ) := by
    rw [hdf]; ext; simp [L,hn]
  have hv : (fderiv ℝ f 0 ∘L ContinuousLinearMap.inr ℝ K ℝ).IsInvertible := by
    rw [hdvert]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := -(ContinuousLinearMap.id ℝ ℝ)) <;>
      ext <;> simp
  have hsmooth : ∀ᶠ x in 𝓝 (0 : K), ContDiffAt ℝ ∞ h x :=
    eventually_contDiffAt_implicit (hU.preimage hg.continuous) (by simpa [hg0])
      hfu hv hh hh0 (by simpa [f,g,L,add_assoc] using he)
  have hD : ContinuousAt (fderiv ℝ (fderiv ℝ h)) (0 : K) :=
    ((hh.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).continuousAt
  have hposh : ∀ v : K, v ≠ 0 → 0 < (fderiv ℝ (fderiv ℝ h) 0 v) v := by
    intro v hv
    rw [height_hessian hFa hn hh hh0 hd0 he]
    exact hpos v (by intro h; apply hv; exact Subtype.ext h) v.property
  obtain ⟨c,hc,hlower⟩ := eventually_quadratic_lower hD hposh
  have hev : ∀ᶠ x in 𝓝 (0 : K), ContDiffAt ℝ ∞ h x ∧
      (∀ v : K, c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ h) x v) v) ∧
      F (a + (x : E) + h x • n) = F a := hsmooth.and (hlower.and he)
  obtain ⟨r₁,hr₁,hr₁bound⟩ := Metric.eventually_nhds_iff.mp hev
  have hez : ∀ᶠ z in 𝓝 (0 : K × ℝ),
      a + (z.1 : E) + z.2 • n ∈ U ∧
      (F (a + (z.1 : E) + z.2 • n) = F a ↔ h z.1 = z.2) := by
    have hnear : ∀ᶠ z in 𝓝 (0 : K × ℝ), g z ∈ U := by
      have hcont : Tendsto g (𝓝 (0 : K × ℝ)) (𝓝 a) := by
        have hx := hg.continuous.continuousAt (x := (0 : K × ℝ))
        change Tendsto g (𝓝 0) (𝓝 (g 0)) at hx
        simpa only [hg0] using hx
      exact hcont.eventually (hU.mem_nhds ha)
    simpa [g,L,add_assoc] using hnear.and hiff
  obtain ⟨r₂,hr₂,hr₂bound⟩ := Metric.eventually_nhds_iff.mp hez
  refine ⟨n,h,c,min r₁ r₂,hc,lt_min hr₁ hr₂,hn,hh0,hd0,?_,?_,?_,?_⟩
  · intro x hx
    exact (hr₁bound (lt_of_lt_of_le hx (min_le_left _ _))).1.contDiffWithinAt
  · intro x hx
    exact (hr₁bound (lt_of_lt_of_le hx (min_le_left _ _))).2.1
  · intro x hx
    exact (hr₁bound (lt_of_lt_of_le hx (min_le_left _ _))).2.2
  · intro z hz
    exact hr₂bound (lt_of_lt_of_le hz (min_le_right _ _))

end DiagonalExtension.SmoothLevel

open scoped Topology ContDiff
namespace DiagonalExtension.SmoothLevel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def kernelNormalEquiv (L : E →L[ℝ] ℝ) (n : E) (hn : L n = -1) :
    (L.ker × ℝ) ≃L[ℝ] E where
  toFun z := (z.1 : E) + z.2 • n
  invFun x := (⟨x + L x • n, by simp [hn]⟩, -L x)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      simp [hn]
    · simp [hn]
  right_inv x := by simp
  map_add' z w := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]; abel
  map_smul' c z := by simp [smul_add, smul_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma kernelNormalEquiv_apply (L : E →L[ℝ] ℝ) (n : E) (hn : L n = -1)
    (z : L.ker × ℝ) : kernelNormalEquiv L n hn z = (z.1 : E) + z.2 • n := rfl

@[simp] lemma kernelNormalEquiv_symm_snd (L : E →L[ℝ] ℝ) (n : E) (hn : L n = -1)
    (x : E) : ((kernelNormalEquiv L n hn).symm x).2 = -L x := rfl

lemma kernelNormalEquiv_symm_fst (L : E →L[ℝ] ℝ) (n : E) (hn : L n = -1)
    (x : E) : (((kernelNormalEquiv L n hn).symm x).1 : E) = x + L x • n := rfl

end DiagonalExtension.SmoothLevel

namespace DiagonalExtension
open SmoothLevel

theorem IsSurface.exists_convex_chart {S : Set E3} (hS : IsSurface S) {a : E3}
    (ha : a ∈ S) :
    ∃ (U : Set E3) (F G : E3 → ℝ) (n : E3)
      (h : (fderiv ℝ F a).ker → ℝ) (c r : ℝ),
      IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ContDiffOn ℝ ∞ G U ∧
      fderiv ℝ F a ≠ 0 ∧ F a = 0 ∧ 0 ≤ G a ∧
      fderiv ℝ F a n = -1 ∧ 0 < c ∧ 0 < r ∧
      h 0 = 0 ∧ fderiv ℝ h 0 = 0 ∧
      ContDiffOn ℝ ∞ h (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, ∀ v : (fderiv ℝ F a).ker,
        c * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ h) x v) v) ∧
      (∀ z ∈ Metric.ball (0 : (fderiv ℝ F a).ker × ℝ) r,
        a + (z.1 : E3) + z.2 • n ∈ U ∧
        (a + (z.1 : E3) + z.2 • n ∈ S ↔
          z.2 = h z.1 ∧ 0 ≤ G (a + (z.1 : E3) + z.2 • n))) ∧
      (G a = 0 → fderiv ℝ (fun v : (fderiv ℝ F a).ker =>
        G (a + (v : E3) + h v • n)) 0 ≠ 0) := by
  obtain ⟨U,F,G,hU,haU,hF,hG,hset,hreg,hbd,hpos⟩ := hS.2 a ha
  have haFG : F a = 0 ∧ 0 ≤ G a := by
    have hh : a ∈ S ∩ U := ⟨ha,haU⟩
    rw [hset] at hh
    exact hh.2
  obtain ⟨n,h,c,r,hc,hr,hn,hh0,hd0,hh,hlower,he,hiff⟩ :=
    exists_convex_height hU haU hF hreg hpos
  refine ⟨U,F,G,n,h,c,r,hU,haU,hF,hG,hreg,haFG.1,haFG.2,hn,hc,hr,
    hh0,hd0,hh,hlower,?_,?_⟩
  · intro z hz
    obtain ⟨hzU,hzif⟩ := hiff z hz
    refine ⟨hzU,?_⟩
    have hmem : a + (z.1 : E3) + z.2 • n ∈ S ↔
        F (a + (z.1 : E3) + z.2 • n) = 0 ∧
          0 ≤ G (a + (z.1 : E3) + z.2 • n) := by
      constructor
      · intro hx
        have hh : a + (z.1 : E3) + z.2 • n ∈ S ∩ U := ⟨hx,hzU⟩
        rw [hset] at hh
        exact hh.2
      · intro hx
        have hh : a + (z.1 : E3) + z.2 • n ∈ S ∩ U := by
          rw [hset]
          exact ⟨hzU,hx⟩
        exact hh.1
    rw [hmem, ← haFG.1, hzif, eq_comm]
  · intro hGa
    let K := (fderiv ℝ F a).ker
    let g : K → E3 := fun v => a + (v : E3) + h v • n
    have hg0 : g 0 = a := by simp [g,hh0]
    have hhAt : ContDiffAt ℝ ∞ h (0 : K) :=
      hh.contDiffAt (Metric.ball_mem_nhds 0 hr)
    have hdg : HasFDerivAt g K.subtypeL (0 : K) := by
      have hd := (K.subtypeL.hasFDerivAt.const_add a).add
        ((hhAt.differentiableAt (by simp)).hasFDerivAt.smul_const n)
      convert! hd using 1
      simp [hd0]
    have hdG : HasFDerivAt G (fderiv ℝ G a) (g 0) := by
      simpa [hg0] using ((hG.contDiffAt (hU.mem_nhds haU)).differentiableAt (by simp)).hasFDerivAt
    have hcomp := (hdG.comp 0 hdg).fderiv
    change fderiv ℝ (fun v : K => G (g v)) 0 = _ at hcomp
    rw [show (fun v : K => G (a + (v : E3) + h v • n)) = (fun v => G (g v)) from rfl,
      hcomp]
    obtain ⟨v,hv,hGv⟩ := hbd hGa
    intro hzero
    have hval := DFunLike.congr_fun hzero (⟨v,hv⟩ : K)
    exact hGv (by simpa using hval)

end DiagonalExtension

end

end OAI
