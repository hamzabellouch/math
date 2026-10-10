import Mathlib
import OAI.Analysis.AffineBernstein.ActualTubeArea
import OAI.Analysis.AffineBernstein.GaussSurjectivity

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section AffineGaussSurjectivity
open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The full boundary above the regular base domain is covered by actual
support gradients, including the direction obtained from the original graph. -/
theorem affineEpigraph_gauss_surjective {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ B) {y : E} (hy : (a+L (s,y)).1 ∈ Ω)
    (hyF : affineDefining u a L (s,y) = 0) :
    let e := gradient (fun q => affineDefining u a L (s,q)) y
    e ≠ 0 ∧ ∀ c : ℝ, 0 < c →
      gaussPoint {q | (s,q) ∈ affineEpigraphPullback Ω u a L} (c • e) = y := by
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

  have hdy : DifferentiableAt ℝ (fun q => F (s,q)) y :=
    (((hF.contDiffAt (hW.mem_nhds hy)).comp y
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
  have hgy := convex_sublevel_gradient_support (hcvF s) hy hzW hyF hzF hdy
  dsimp only
  refine ⟨hgy.1, ?_⟩
  intro c hc
  let e := gradient (fun q => F (s,q)) y
  have hce : c • e ≠ 0 := smul_ne_zero hc.ne' hgy.1
  have hm : IsMaxOn (fun q => inner ℝ (c • e) q)
      {q | (s,q) ∈ affineEpigraphPullback Ω u a L} y := by
    intro q hq
    change inner ℝ (c • e) q ≤ inner ℝ (c • e) y
    simp only [inner_smul_left,conj_trivial]
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply hgy.2
    change q ∈ {q | (s,q) ∈ W ∧ F (s,q) ≤ 0}
    rwa [hKeq]
  have hyv : y ∈ {q | (s,q) ∈ affineEpigraphPullback Ω u a L} := by
    rw [← hKeq]
    exact ⟨hy,hyF.le⟩
  have hj := (affineEpigraph_support_jets hΩ hcv hu hp a L hB hK hzero hs hce).1
  exact gaussPoint_eq_of_max (hK s hs) hyv (homogeneousSupport_eq_of_max hyv hm)
    ((hj.comp (c • e) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))

end AffineGaussSurjectivity

-- WholeSphereArea

end
end AffineBernstein
end

end OAI
