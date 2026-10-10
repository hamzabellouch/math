import Mathlib
import OAI.Analysis.SymmetricDomains.ContinuousFderivLocallyUniform
import OAI.Analysis.SymmetricDomains.HurwitzZeroFreeOr
import OAI.Analysis.SymmetricDomains.AnalyticNhdDifferentiableAffine

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem analytic_montel_expanding_domains {n m : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) (f : ℕ → Affine n → Affine m)
    (hlocal : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ball x r ⊆ S ∧ ∀ᶠ j in atTop,
        DifferentiableOn ℂ (f j) (ball x r) ∧ ∀ y ∈ ball x r, ‖f j y‖ ≤ M) :
    ∃ g : Affine n → Affine m, AnalyticOnNhd ℂ g S ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  obtain ⟨g,hg,φ,hφ,hconv⟩ := montel_expanding_domains hS f hlocal
  exact ⟨g,analyticOnNhd_of_differentiableOn_affine hS hg,φ,hφ,hconv⟩

theorem locallyUniform_postcomp
    {X Y Z ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {l : Filter ι} {S : Set X} {f : ι → X → Y} {g : X → Y} {H : Y → Z}
    (hfg : TendstoLocallyUniformlyOn f g l S) (hg : ContinuousOn g S)
    (hH : Continuous H) :
    TendstoLocallyUniformlyOn (fun j x => H (f j x)) (fun x => H (g x)) l S := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hfg ⊢
  intro ε hε x hx
  obtain ⟨δ,hδ,hδH⟩ := Metric.continuousAt_iff.mp (hH.continuousAt : ContinuousAt H (g x)) (ε/2) (half_pos hε)
  obtain ⟨W,hW,hunif⟩ := hfg (δ/2) (half_pos hδ) x hx
  have hnear : {y | dist (g y) (g x) < δ/2} ∈ 𝓝[S] x :=
    (Metric.tendsto_nhds.mp (hg x hx)) (δ/2) (half_pos hδ)
  refine ⟨W ∩ {y | dist (g y) (g x) < δ/2},inter_mem hW hnear,?_⟩
  filter_upwards [hunif] with j hj y hy
  have hy2 : dist (g y) (g x) < δ/2 := hy.2
  have hfy : dist (f j y) (g x) < δ := by
    calc
      dist (f j y) (g x) ≤ dist (f j y) (g y)+dist (g y) (g x) := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (f j y)]; linarith [hj y hy.1]
  calc
    dist (H (g y)) (H (f j y)) ≤ dist (H (g y)) (H (g x))+dist (H (g x)) (H (f j y)) := dist_triangle _ _ _
    _ < ε := by
      rw [dist_comm (H (g x))]
      linarith [hδH (lt_trans hy.2 (half_lt_self hδ)),hδH hfy]

theorem analyticAt_clm_det {n : ℕ}
    (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
    AnalyticAt ℂ (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T.det) L := by
  classical
  have he : ∀ i j : Fin n, AnalyticAt ℂ
      (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T (Pi.single j 1) i) L := by
    intro i j
    exact ((ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℂ (Fin n → ℂ) (Pi.single j 1))).analyticAt L
  have hd : (fun T : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => T.det) =
      fun T => ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ i, T (Pi.single i 1) (σ i) := by
    funext T
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix' T.toLinearMap, Matrix.det_apply']
    rfl
  rw [hd]
  have hs := Finset.analyticAt_sum Finset.univ (fun σ _ =>
    (show AnalyticAt ℂ (fun _ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) => (Equiv.Perm.sign σ : ℂ)) L from analyticAt_const).mul
      (Finset.analyticAt_prod Finset.univ (fun i _ => he (σ i) i)))
  simpa only [Finset.sum_fn,Finset.prod_fn,Pi.mul_apply] using hs

theorem analyticOnNhd_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → (Fin n → ℂ)} (hf : AnalyticOnNhd ℂ f S) :
    AnalyticOnNhd ℂ (fun x => (fderiv ℂ f x).det) S := by
  intro x hx
  exact (analyticAt_clm_det (fderiv ℂ f x)).comp (hf x hx).fderiv

theorem tendstoLocallyUniformlyOn_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    TendstoLocallyUniformlyOn (fun j x => (fderiv ℂ (f j) x).det)
      (fun x => (fderiv ℂ g x).det) atTop S := by
  have hg := analyticOnNhd_of_differentiableOn_affine hS
    (differentiableOn_of_locally_uniform_limit hS hfg hf)
  exact locallyUniform_postcomp (tendstoLocallyUniformlyOn_fderiv hS hfg hf)
    hg.fderiv.continuousOn ContinuousLinearMap.continuous_det

theorem hurwitz_zero_free_or_zero_locally
    {n : ℕ} {S : Set (Fin n → ℂ)} (hS : IsOpen S) (hconn : IsPreconnected S)
    {f : ℕ → (Fin n → ℂ) → ℂ} {g : (Fin n → ℂ) → ℂ}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (f j) W ∧ ∀ z ∈ W, f j z ≠ 0) :
    (∀ z ∈ S, g z ≠ 0) ∨ (∀ z ∈ S, g z = 0) := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => h.1⟩
  have hc := (differentiableOn_of_locally_uniform_limit hS hfg hdiff).continuousOn
  have hzero : ∀ p ∈ S, g p = 0 → ∀ᶠ z in 𝓝 p, g z = 0 := by
    intro p hp hgp
    obtain ⟨W,hW,he⟩ := hf p hp
    obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hp))
    exact hurwitz_zero_interior_finiteDim isOpen_ball
      (hfg.mono fun z hz => (hsub hz).2)
      (he.mono fun _ h => h.1.mono fun z hz => (hsub hz).1)
      (he.mono fun _ h z hz => h.2 z (hsub hz).1) (mem_ball_self hR) hgp
  by_cases hn : ∀ z ∈ S, g z ≠ 0
  · exact Or.inl hn
  right
  push Not at hn
  obtain ⟨p,hp,hgp⟩ := hn
  let Z := {z | z ∈ S ∧ g z = 0}
  let N := {z | z ∈ S ∧ g z ≠ 0}
  have hZ : IsOpen Z := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1) (hzero z hz.1 hz.2)
  have hN : IsOpen N := isOpen_iff_mem_nhds.mpr fun z hz =>
    inter_mem (hS.mem_nhds hz.1)
      (((hc z hz.1).continuousAt (hS.mem_nhds hz.1)).eventually_ne hz.2)
  have hdis : Disjoint Z N := Set.disjoint_left.mpr fun _ hz hn => hn.2 hz.2
  have hcover : S ⊆ Z ∪ N := by
    intro z hz
    by_cases hg : g z = 0
    · exact Or.inl ⟨hz,hg⟩
    · exact Or.inr ⟨hz,hg⟩
  have hsub := hconn.subset_left_of_subset_union hZ hN hdis hcover ⟨p,hp,hp,hgp⟩
  exact fun z hz => (hsub hz).2

theorem jacobian_nonzero_of_anchor {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (f j) W ∧ ∀ z ∈ W, (fderiv ℂ (f j) z).det ≠ 0)
    (hanchor : ∃ p ∈ S, (fderiv ℂ g p).det ≠ 0) :
    ∀ p ∈ S, (fderiv ℂ g p).det ≠ 0 := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => h.1.differentiableOn⟩
  have hconv := tendstoLocallyUniformlyOn_jacobian hS hfg hdiff
  have hlocal : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (fun z => (fderiv ℂ (f j) z).det) W ∧
        ∀ z ∈ W, (fderiv ℂ (f j) z).det ≠ 0 := by
    intro x hx
    obtain ⟨W,hW,he⟩ := hf x hx
    exact ⟨W,hW,he.mono fun _ h => ⟨(analyticOnNhd_jacobian h.1).differentiableOn,h.2⟩⟩
  rcases hurwitz_zero_free_or_zero_locally hS hconn hconv hlocal with h | h
  · exact h
  · obtain ⟨p,hp,hpne⟩ := hanchor
    exact (hpne (h p hp)).elim

theorem jacobian_ne_zero_of_right_inverse {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hS : IsOpen S) (hT : IsOpen T) {f g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hf : DifferentiableOn ℂ f S) (hg : DifferentiableOn ℂ g T)
    (hmap : MapsTo g T S) (hright : ∀ y ∈ T, f (g y) = y)
    {y : Fin n → ℂ} (hy : y ∈ T) : (fderiv ℂ f (g y)).det ≠ 0 := by
  have he : (f ∘ g) =ᶠ[𝓝 y] id := by
    filter_upwards [hT.mem_nhds hy] with z hz
    exact hright z hz
  have hdf := (hf.differentiableAt (hS.mem_nhds (hmap hy))).hasFDerivAt
  have hdg := (hg.differentiableAt (hT.mem_nhds hy)).hasFDerivAt
  have hid := (hdf.comp y hdg).unique ((hasFDerivAt_id y).congr_of_eventuallyEq he)
  have hdet := congrArg ContinuousLinearMap.det hid
  change LinearMap.det ((fderiv ℂ f (g y)).toLinearMap.comp (fderiv ℂ g y).toLinearMap) =
    LinearMap.det (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  intro hzero
  change LinearMap.det (fderiv ℂ f (g y)).toLinearMap = 0 at hzero
  rw [hzero,zero_mul] at hdet
  exact zero_ne_one hdet

theorem eventually_image_ball_of_nonzero_jacobian {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : ℕ → (Fin n → ℂ) → (Fin n → ℂ)} {g : (Fin n → ℂ) → (Fin n → ℂ)}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j) W)
    {x : Fin n → ℂ} (hx : x ∈ S) (hne : (fderiv ℂ g x).det ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ S ∧
      ∀ᶠ j in atTop, ball (g x) r ⊆ f j '' closedBall x R := by
  let L : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ g x).toLinearMap hne).toContinuousLinearEquiv
  have hL : fderiv ℂ g x = (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) := by
    ext v i
    rfl
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro z hz
    obtain ⟨W,hW,he⟩ := hf z hz
    exact ⟨W,hW,he.mono fun _ h => h.differentiableOn⟩
  exact eventually_image_ball hS hfg hdiff hx L hL
    (continuousAt_fderiv_of_locally_uniform_analytic hS hfg hf hx)

end Release061

end OAI
