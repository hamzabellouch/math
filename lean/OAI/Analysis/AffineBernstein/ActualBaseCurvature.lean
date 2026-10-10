import Mathlib
import OAI.Analysis.AffineBernstein.ActualAngularSupport
import OAI.Analysis.AffineBernstein.BaseConcavity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/- The genuine defining function for any affine coordinates of the graph. -/
def affineDefining {n : ℕ} (u : Space n → ℝ) (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) (p : V) : ℝ := u (a + L p).1 - (a + L p).2

theorem affineDefining_deriv {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (v : V) :
    fderiv ℝ (affineDefining u a L) p v =
      fderiv ℝ u (a + L p).1 (L v).1 - (L v).2 := by
  let A := (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  let b := (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  have hd := ((hu.differentiableAt (by simp)).hasFDerivAt.comp p
    (A.hasFDerivAt.const_add a.1)).sub (b.hasFDerivAt.const_add a.2)
  change HasFDerivAt (affineDefining u a L) _ p at hd
  rw [hd.fderiv]
  rfl

theorem affineDefining_second {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (v w : V) :
    fderiv ℝ (fderiv ℝ (affineDefining u a L)) p v w =
      fderiv ℝ (fderiv ℝ u) (a + L p).1 (L v).1 (L w).1 := by
  let A := (ContinuousLinearMap.fst ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  let b := (ContinuousLinearMap.snd ℝ (Space n) ℝ).comp L.toContinuousLinearMap
  exact affineSlice_second (A := A) (b := b) (z := a.2) hu v w

/- Positive curvature on the tangent hyperplane, including affine maps that
mix the original vertical direction with the new base and fiber coordinates. -/
theorem affineDefining_tangent_curvature {n : ℕ} {u : Space n → ℝ} (a : Space n × ℝ)
    (L : V ≃L[ℝ] (Space n × ℝ)) {p : V}
    (hu : ContDiffAt ℝ ∞ u (a + L p).1) (hp : (hessian u (a + L p).1).PosDef)
    {v : V} (hv : v ≠ 0) (ht : fderiv ℝ (affineDefining u a L) p v = 0) :
    0 < fderiv ℝ (fderiv ℝ (affineDefining u a L)) p v v := by
  rw [affineDefining_deriv a L hu] at ht
  have hhor : (L v).1 ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_sub, neg_eq_zero] at ht
    apply hv
    apply L.injective
    exact (Prod.ext hz ht).trans (map_zero L).symm
  rw [affineDefining_second a L hu]
  exact second_fderiv_pos hu hp hhor

variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The actual support point is on the original graph and its fiber conormal is
positive. No Gauss inverse or support-equation hypotheses are assumed. -/
theorem affineEpigraph_gauss_equations [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) :
    let Y := gaussPoint {y | (s,y) ∈ affineEpigraphPullback Ω u a L} e
    (a + L (s,Y)).1 ∈ Ω ∧ affineDefining u a L (s,Y) = 0 ∧
      ∃ lam : ℝ, 0 < lam ∧ fderiv ℝ (fun y => affineDefining u a L (s,y)) Y =
        lam • InnerProductSpace.toDual ℝ E e := by
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
  have hh' : ContDiffAt ℝ ∞ (homogeneousSupport {y | (s,y) ∈ W ∧ F (s,y) ≤ 0}) e := by
    rw [hKeq]; exact hh
  have hresult := gaussPoint_sublevel_equations
    (W := {y | (s,y) ∈ W}) (F := fun y => F (s,y))
    (hW.preimage (by fun_prop)) (hcvF s)
    (hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ h => h))
    hzW hzF hK' he (hh'.differentiableAt (by simp))
  simp only [mem_ofPred_eq] at hresult
  rw [hKeq] at hresult
  exact hresult

/- Strict negativity of the base Hessian of the literal support function. This
is the other positive block of the genuine tube second fundamental form. -/
theorem affineEpigraph_base_hessian_negative [FiniteDimensional ℝ E] [Nontrivial E]
    {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s, y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {e : E} (he : e ≠ 0) {v : S} (hv : v ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun r => homogeneousSupport
      {y | (r,y) ∈ affineEpigraphPullback Ω u a L} e)) s v v < 0 := by
  let K : S → Set E := fun r => {y | (r,y) ∈ affineEpigraphPullback Ω u a L}
  let Y : S → E := fun r => gaussPoint (K r) e
  let F := affineDefining u a L
  have hY : ContDiffAt ℝ ∞ Y s :=
    (affineEpigraph_gauss_smooth hΩ hcv hu hp a L hB hK hzero hs he).comp
      (f := fun r : S => (r,e)) s (contDiffAt_id.prodMk contDiffAt_const)
  obtain ⟨hbase, hlevel0, lam, hlam, hnorm⟩ :=
    affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hs he
  change (a + L (s,Y s)).1 ∈ Ω at hbase
  have huc := hu.contDiffAt (hΩ.mem_nhds hbase)
  have hF : ContDiffAt ℝ ∞ F (s,Y s) :=
    (huc.comp (s,Y s) ((contDiffAt_const.add L.contDiff.contDiffAt).fst)).sub
      ((contDiffAt_const.add L.contDiff.contDiffAt).snd)
  have hlevel : (fun r => F (r,Y r)) =ᶠ[𝓝 s] (fun _ => 0) := by
    filter_upwards [hB.mem_nhds hs] with r hr
    exact (affineEpigraph_gauss_equations hΩ hcv hu hp a L hB hK hzero hr he).2.1
  have hnormal (z : E) : fderiv ℝ F (s,Y s) (0,z) = lam * inner ℝ e z := by
    have hd := (hF.differentiableAt (by simp)).hasFDerivAt.comp (Y s)
      ((hasFDerivAt_const s (Y s)).prodMk (hasFDerivAt_id (Y s)))
    have hh := congrArg (fun A : E →L[ℝ] ℝ => A z) hnorm
    change fderiv ℝ (F ∘ Prod.mk s) (Y s) z = _ at hh
    rw [hd.fderiv] at hh
    exact hh
  have hneg := support_base_hessian_neg hF hY hlevel hlam hnormal
    (fun z hz ht => affineDefining_tangent_curvature a L huc (hp _ hbase) hz ht) hv
  have heq : (fun r => homogeneousSupport (K r) e) =ᶠ[𝓝 s]
      (fun r => inner ℝ e (Y r)) := by
    filter_upwards [hB.mem_nhds hs] with r hr
    have hℓ : InnerProductSpace.toDual ℝ E e ≠ 0 := by
      intro hz; apply he
      exact (InnerProductSpace.toDual ℝ E).injective (hz.trans (map_zero _).symm)
    have hsup := contDiffAt_homogeneousSupport_fibers
      (K := K) (affineEpigraph_support_smooth hΩ hcv hu hp a L hB hK hzero hr hℓ).1
    have hd : DifferentiableAt ℝ (homogeneousSupport (K r)) e :=
      (hsup.comp e (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    exact (gaussPoint_mem_support (hK r hr) ⟨0, interior_subset (hzero r hr)⟩ hd).2
  rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
  exact hneg

end AffineBernstein
end

end OAI
