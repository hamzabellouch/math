import Mathlib
import OAI.Analysis.AffineBernstein.GaussCoordinates
import OAI.Analysis.AffineBernstein.AngularCofactor

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem homogeneousSupport_cofactor_divergence {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {e : E}
    (hh : ContDiffAt ℝ ∞ (homogeneousSupport K) e)
    (frame : ι → E) (hf : ∀ i, inner ℝ e (frame i) = 0) (i : ι) :
    (∑ j, fderiv ℝ (fun y =>
      (radiusMatrix (homogeneousSupport K) frame y).adjugate j i) e (frame j)) = 0 :=
  radiusMatrix_cofactor_divergence hh (homogeneousSupport_hessian_radial hK hne hh) frame hf i

theorem gaussPoint_sublevel_equations {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0}) {e : E} (he : e ≠ 0)
    (hh : DifferentiableAt ℝ (homogeneousSupport {y | y ∈ W ∧ F y ≤ 0}) e) :
    let Y := gaussPoint {y | y ∈ W ∧ F y ≤ 0} e
    Y ∈ W ∧ F Y = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
      fderiv ℝ F Y = lam • InnerProductSpace.toDual ℝ E e := by
  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  obtain ⟨z, hz, hzF, lam, hlam, hder, -, hsup⟩ :=
    exists_support_multiplier hW hcv hF hx₀ hneg hK hℓ
  have heq := gaussPoint_eq_of_max hK ⟨hz, hzF.le⟩ hsup hh
  dsimp only
  rw [heq]
  exact ⟨hz, hzF, lam, hlam, hder⟩

/- Local differential form of strict curvature duality: the Hessian of a
one-homogeneous support is positive on every nonzero tangent vector. -/
theorem support_hessian_pos_of_equations {H F lam : E → ℝ} {e : E}
    (hh : ContDiffAt ℝ ∞ H e) (hF : ContDiffAt ℝ ∞ F (gradient H e))
    (hl : DifferentiableAt ℝ lam e) (hlpos : 0 < lam e)
    (heq : (fun q => fderiv ℝ F (gradient H q)) =ᶠ[𝓝 e]
      (fun q => lam q • InnerProductSpace.toDual ℝ E q))
    (hlevel : (fun q => F (gradient H q)) =ᶠ[𝓝 e] (fun _ => (0 : ℝ)))
    (hpos : ∀ z : E, z ≠ 0 → 0 <
      fderiv ℝ (fderiv ℝ F) (gradient H e) z z)
    {v : E} (hv : v ≠ 0) (ht : inner ℝ e v = 0) :
    0 < fderiv ℝ (fderiv ℝ H) e v v := by
  let Y := gradient H
  let V := fderiv ℝ Y e v
  have hY := (contDiffAt_gradient hh).differentiableAt (by simp)
  have hdF := hF.differentiableAt (by simp)
  have hdFd := (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hd1 := hdF.hasFDerivAt.comp e hY.hasFDerivAt
  have hd0 := (hd1.congr_of_eventuallyEq hlevel.symm).unique
    (hasFDerivAt_const (0 : ℝ) e)
  have hz : fderiv ℝ F (Y e) V = 0 := by
    have hz := congrArg (fun L : E →L[ℝ] ℝ => L v) hd0
    simpa [Y, V] using hz
  have horth : inner ℝ e V = 0 := by
    rw [heq.eq_of_nhds] at hz
    simpa [ne_of_gt hlpos] using hz
  have hd2 := hdFd.hasFDerivAt.comp e hY.hasFDerivAt
  have hd3 := hl.hasFDerivAt.smul
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.hasFDerivAt
  have hd23 := (hd2.congr_of_eventuallyEq heq.symm).unique hd3
  have hident (z : E) : fderiv ℝ (fderiv ℝ F) (Y e) V z =
      fderiv ℝ lam e v * inner ℝ e z + lam e * inner ℝ v z := by
    have hi := congrArg (fun L : E →L[ℝ] (E →L[ℝ] ℝ) => L v z) hd23
    simpa [Y, V, add_comm] using hi
  have hV : V ≠ 0 := by
    intro hVz
    have hi := hident v
    rw [hVz, map_zero, zero_apply, ht, mul_zero, zero_add] at hi
    have hvv : inner ℝ v v = 0 := (mul_eq_zero.mp hi.symm).resolve_left (ne_of_gt hlpos)
    exact hv (inner_self_eq_zero.mp hvv)
  have hi := hident V
  rw [horth, mul_zero, zero_add] at hi
  have hg : inner ℝ v V = fderiv ℝ (fderiv ℝ H) e v v := by
    rw [real_inner_comm]
    exact inner_fderiv_gradient hh v v
  rw [hg] at hi
  exact (mul_pos_iff_of_pos_left hlpos).mp (hi ▸ hpos V hV)

/- Strict positivity of the actual homogeneous support Hessian on tangent
vectors. The multiplier is constructed from the actual Gauss point, not given
as a differential identity hypothesis. -/
theorem homogeneousSupport_hessian_pos {W : Set E} (hW : IsOpen W) {F : E → ℝ}
    (hcv : ConvexOn ℝ W F) (hF : ContDiffOn ℝ ∞ F W)
    {x₀ : E} (hx₀ : x₀ ∈ W) (hneg : F x₀ < 0)
    (hK : IsCompact {y | y ∈ W ∧ F y ≤ 0}) {e : E} (he : e ≠ 0)
    (hh : ContDiffAt ℝ ∞ (homogeneousSupport {y | y ∈ W ∧ F y ≤ 0}) e)
    (hpos : ∀ y ∈ W, F y = 0 → ∀ z : E, z ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ F) y z z)
    {v : E} (hv : v ≠ 0) (ht : inner ℝ e v = 0) :
    0 < fderiv ℝ (fderiv ℝ (homogeneousSupport {y | y ∈ W ∧ F y ≤ 0})) e v v := by
  let K : Set E := {y | y ∈ W ∧ F y ≤ 0}
  let H := homogeneousSupport K
  let Y := gradient H
  have heq := gaussPoint_sublevel_equations hW hcv hF hx₀ hneg hK he
    (hh.differentiableAt (by simp))
  change Y e ∈ W ∧ F (Y e) = 0 ∧ ∃ lam : ℝ, 0 < lam ∧
    fderiv ℝ F (Y e) = lam • InnerProductSpace.toDual ℝ E e at heq
  have hFc := hF.contDiffAt (hW.mem_nhds heq.1)
  have hY := (contDiffAt_gradient hh).differentiableAt (by simp)
  let lam : E → ℝ := fun q => fderiv ℝ F (Y q) e / inner ℝ q e
  have hden : inner ℝ e e ≠ 0 := fun hz => he (inner_self_eq_zero.mp hz)
  have hld : DifferentiableAt ℝ lam e := by
    have hnum := (((hFc.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).comp e hY).clm_apply
      (differentiableAt_const e)
    have hdenf : DifferentiableAt ℝ (fun q : E => inner ℝ q e) e :=
      differentiableAt_id.inner ℝ (differentiableAt_const e)
    simpa only [lam, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply, Function.comp_def] using hnum.fun_mul (hdenf.fun_inv hden)
  have hlpos : 0 < lam e := by
    obtain ⟨a, ha, hea⟩ := heq.2.2
    have hla : lam e = a := by
      simp only [lam, hea, smul_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hden
    rwa [hla]
  have hevent : ∀ᶠ q in 𝓝 e, Y q ∈ W ∧ F (Y q) = 0 ∧
      fderiv ℝ F (Y q) = lam q • InnerProductSpace.toDual ℝ E q := by
    have hne : ∀ᶠ q in 𝓝 e, q ≠ 0 := eventually_ne_nhds he
    have hdne : ∀ᶠ q in 𝓝 e, inner ℝ q e ≠ 0 :=
      (continuousAt_id.inner continuousAt_const).eventually (eventually_ne_nhds hden)
    filter_upwards [hne, hdne,
      (hh.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq hqd hqc
    have hqe := gaussPoint_sublevel_equations hW hcv hF hx₀ hneg hK hq
      (hqc.differentiableAt (by norm_num))
    change Y q ∈ W ∧ F (Y q) = 0 ∧ ∃ a : ℝ, 0 < a ∧
      fderiv ℝ F (Y q) = a • InnerProductSpace.toDual ℝ E q at hqe
    obtain ⟨a, ha, hea⟩ := hqe.2.2
    have hla : lam q = a := by
      simp only [lam, hea, smul_apply, InnerProductSpace.toDual_apply_apply, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hqd
    exact ⟨hqe.1, hqe.2.1, hla.symm ▸ hea⟩
  apply support_hessian_pos_of_equations (H := H) (F := F) (lam := lam)
    hh hFc hld hlpos
  · filter_upwards [hevent] with q hq; exact hq.2.2
  · filter_upwards [hevent] with q hq; exact hq.2.1
  · exact hpos _ heq.1 heq.2.1
  · exact hv
  · exact ht

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/- Positive angular radius comes from the actual original graph Hessian,
after any invertible affine change of coordinates with compact centered fibers. -/
theorem affineEpigraph_radius_positive [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0)
    {v : E} (hv : v ≠ 0) (ht : inner ℝ e v = 0) :
    0 < sphereRadius (homogeneousSupport
      {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) e v v := by
  let W : Set (S × E) := {p | (a + L p).1 ∈ Ω}
  let F : S × E → ℝ := fun p => u (a + L p).1 - (a + L p).2
  have hbase : ContDiff ℝ ∞ (fun p : S × E => (a + L p).1) :=
    (contDiff_const.add L.contDiff).fst
  have hheight : ContDiff ℝ ∞ (fun p : S × E => (a + L p).2) :=
    (contDiff_const.add L.contDiff).snd
  have hW : IsOpen W := hΩ.preimage hbase.continuous
  have hF : ContDiffOn ℝ ∞ F W :=
    (hu.comp hbase.contDiffOn (fun _ h => h)).sub hheight.contDiffOn
  have hFu : ConvexOn ℝ Ω u :=
    convexOn_of_hessian_posSemidef hΩ hcv hu (fun x hx => (hp x hx).posSemidef)
  have hFeq (r : S) : (fun q => F (r, q)) = (fun q =>
      u ((a + L (r, 0)).1 + affineFiberHorizontal L q) -
        ((a + L (r, 0)).2 + affineFiberHeight L q)) := by
    funext q
    change u (a + L (r, q)).1 - (a + L (r, q)).2 = _
    rw [affine_coordinates_split a L r q]
  have hWeq (r : S) : {y | (r, y) ∈ W} =
      {y | (a + L (r, 0)).1 + affineFiberHorizontal L y ∈ Ω} := by
    ext y
    change (a + L (r, y)).1 ∈ Ω ↔ _
    rw [affine_coordinates_split a L r y]
    rfl
  have hcvF (r : S) : ConvexOn ℝ {y | (r, y) ∈ W} (fun y => F (r, y)) := by
    rw [hFeq, hWeq]
    exact convexOn_affineSlice hFu (a + L (r, 0)).1 (a + L (r, 0)).2
      (affineFiberHorizontal L) (affineFiberHeight L)
  have hKeq (r : S) : {y | (r, y) ∈ W ∧ F (r, y) ≤ 0} =
      {y | (r, y) ∈ affineEpigraphPullback Ω u a L} := by
    ext y
    simp only [W, F, affineEpigraphPullback, mem_ofPred_eq, sub_nonpos]
  have hK' : IsCompact {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by rw [hKeq]; exact hK s hs
  have hzero' : (0 : E) ∈ interior {y | (s, y) ∈ W ∧ F (s, y) ≤ 0} := by
    rw [hKeq]; exact hzero s hs
  have hA : Function.Injective (affineFiberHorizontal L) :=
    affineFiberHorizontal_injective (hK s hs) ⟨0, interior_subset (hzero s hs)⟩
  have hH (y : E) (hy : (s, y) ∈ W) (v : E) (hv : v ≠ 0) :
      0 < fderiv ℝ (fderiv ℝ (fun q => F (s, q))) y v v := by
    have huc := hu.contDiffAt (hΩ.mem_nhds hy)
    have hx : (a + L (s, y)).1 = (a + L (s, 0)).1 + affineFiberHorizontal L y :=
      congrArg Prod.fst (affine_coordinates_split a L s y)
    rw [hFeq, affineSlice_second (by rw [← hx]; exact huc)]
    exact second_fderiv_pos (by rw [← hx]; exact huc)
      (by rw [← hx]; exact hp _ hy)
      (fun hh => hv (hA (by simpa using hh)))
  have hzW : (s, (0 : E)) ∈ W := (interior_subset hzero').1
  have hzF : F (s, 0) < 0 := sublevel_interior_strict (hcvF s) hzero'
    (((hF.contDiffAt (hW.mem_nhds hzW)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)) (hH 0 hzW)

  have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
    intro hz; apply he
    exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
  have hsupp := contDiffAt_homogeneousSupport_fibers
    (K := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L})
    (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hs hℓ).1
  have hh : ContDiffAt ℝ ∞ (homogeneousSupport
      {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) e :=
    hsupp.comp e (contDiffAt_const.prodMk contDiffAt_id)
  rw [sphereRadius_eq_hessian hh _ _ ht]
  have hh' : ContDiffAt ℝ ∞ (homogeneousSupport {y | (s,y) ∈ W ∧ F (s,y) ≤ 0}) e := by
    rw [hKeq]; exact hh
  have hresult := homogeneousSupport_hessian_pos
    (W := {y | (s,y) ∈ W}) (F := fun y => F (s,y))
    (hW.preimage (by fun_prop)) (hcvF s)
    (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h))
    hzW hzF hK' he hh' (fun y hy _ => hH y hy) hv ht
  change 0 < fderiv ℝ (fderiv ℝ
    (homogeneousSupport {y | (s,y) ∈ W ∧ F (s,y) ≤ 0})) e v v at hresult
  rw [hKeq] at hresult
  exact hresult

end AffineBernstein

end

end OAI
