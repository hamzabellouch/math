import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.TransverseZeroKernel

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
namespace YauCounterexamples
open scoped Manifold BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2 * (2 * (k : ℝ))}
variable (A : CompactMetricAtlas g k hs)

def transferAcross {g' : SmoothMetric E M} {l : ℕ}
    {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))} (B : CompactMetricAtlas g' l ht) (n : ℕ) :
    A.H (2 * (n : ℝ)) →L[ℝ] B.H (2 * (n : ℝ)) :=
  ∑ i, B.lift (A.p i) (A.χ i) (A.chart_χ i) (A.smooth_χ i) n ∘L
    A.localize (2 * (n : ℝ)) i

omit [T2Space M] in
lemma transferAcross_representative {g' : SmoothMetric E M} {l : ℕ}
    {ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ))} (B : CompactMetricAtlas g' l ht) (n : ℕ)
    (hn : Module.finrank ℝ E < 2 * (2 * (n : ℝ))) (u : A.H (2 * (n : ℝ))) :
    B.representative (2 * (n : ℝ)) (A.transferAcross B n u) =
      A.representative (2 * (n : ℝ)) u := by
  ext x
  simp only [transferAcross, sum_apply, map_sum, BoundedContinuousFunction.sum_apply,
    ContinuousLinearMap.comp_apply, B.lift_representative _ _ _ _ n hn]
  exact (manifoldSobolevRepresentative_eq_sum A.p A.η
    (fun i => HasCompactSupport.of_compactSpace (A.η i)) A.chart_η A.smooth_η
    A.χ A.chart_χ A.sum_η (fun i y hy => (A.one_χ i).self_of_nhdsSet hy) hn u x).symm

def power (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u : A.H (2 * (l : ℝ))) : ℕ → A.H (2 * (l : ℝ))
  := Nat.rec (A.ofSmooth (2 * (l : ℝ)) ⟨fun _ => 1, contMDiff_const⟩)
    (fun _ v => A.product l ht u v)

omit [T2Space M] in
lemma power_representative (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (u : A.H (2 * (l : ℝ))) (n : ℕ) (x : M) :
    A.representative (2 * (l : ℝ)) (A.power l ht u n) x =
      (A.representative (2 * (l : ℝ)) u x) ^ n := by
  induction n with
  | zero =>
    change A.representative (2 * (l : ℝ))
      (A.ofSmooth (2 * (l : ℝ)) ⟨fun _ => 1, contMDiff_const⟩) x = _
    erw [A.ofSmooth_representative _ ht]
    rfl
  | succ n ih =>
    change A.representative (2 * (l : ℝ)) (A.product l ht u (A.power l ht u n)) x = _
    rw [A.product_representative l ht, ih, pow_succ']

def polynomial {N : ℕ} (l : ℕ) (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (a : Fin N → ManifoldSmoothFunctions E M) (u : A.H (2 * (l : ℝ))) : A.H (2 * (l : ℝ)) :=
  ∑ i, A.product l ht (A.ofSmooth (2 * (l : ℝ)) (a i)) (A.power l ht u i.val)

omit [T2Space M] in
lemma polynomial_representative {N : ℕ} (l : ℕ)
    (ht : Module.finrank ℝ E < 2 * (2 * (l : ℝ)))
    (a : Fin N → ManifoldSmoothFunctions E M) (u : A.H (2 * (l : ℝ))) (x : M) :
    A.representative (2 * (l : ℝ)) (A.polynomial l ht a u) x =
      ∑ i, a i x * (A.representative (2 * (l : ℝ)) u x) ^ i.val := by
  simp only [polynomial, map_sum, BoundedContinuousFunction.sum_apply,
    A.product_representative l ht, A.power_representative l ht, A.ofSmooth_representative _ ht]

theorem semilinear_regularity_step {N : ℕ} (a : Fin N → ManifoldSmoothFunctions E M) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, complexLaplaceBeltrami g u x = ∑ i, a i x * u x ^ i.val)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u)
    (ht : Module.finrank ℝ E < 2 * (2 * ((k + 1 : ℕ) : ℝ))) :
    ∃ (B : CompactMetricAtlas g (k + 1) ht)
      (w : B.H (2 * ((k + 1 + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + 1 + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
  let B := (nonempty_compactMetricAtlas g (k + 1) ht).some
  let C : ∀ i, B.PatchCoefficients i := fun i => (B.nonempty_patchCoefficients i).some
  obtain ⟨β, hβ, ha⟩ := B.exists_parametrix_threshold C
  obtain ⟨hb, hc⟩ := ha β le_rfl
  let v' := A.transfer B (k + 1) v
  let F := β • v' - B.polynomial (k + 1) ht a v'
  let w := B.resolvent C β hb hc F
  refine ⟨B, w, ?_⟩
  apply complex_positive_shift_solution_unique g (by linarith : 0 < β) (B.representative_C2 w) hu
  intro x
  rw [B.resolvent_equation]
  have hv' : (B.representative (2 * ((k + 1 : ℕ) : ℝ)) v' : M → ℂ) = u := by
    change (B.representative (2 * ((k + 1 : ℕ) : ℝ)) (A.transfer B (k + 1) v) : M → ℂ) = u
    rw [A.transfer_representative B (k + 1) ht]
    exact hv
  simp only [F, map_sub, map_smul, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.smul_apply, Complex.real_smul,
    B.polynomial_representative (k + 1) ht, congrFun hv' x, he]

theorem represented_semilinear_solution_smooth {N : ℕ}
    (a : Fin N → ManifoldSmoothFunctions E M) {u : M → ℂ}
    (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 2 u)
    (he : ∀ x, complexLaplaceBeltrami g u x = ∑ i, a i x * u x ^ i.val)
    (v : A.H (2 * ((k + 1 : ℕ) : ℝ)))
    (hv : (A.representative (2 * ((k + 1 : ℕ) : ℝ)) v : M → ℂ) = u) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ u := by
  have hkn (n : ℕ) : Module.finrank ℝ E < 2 * (2 * ((k + n : ℕ) : ℝ)) := by
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hrep (n : ℕ) : ∃ (B : CompactMetricAtlas g (k + n) (hkn n))
      (w : B.H (2 * ((k + n + 1 : ℕ) : ℝ))),
      (B.representative (2 * ((k + n + 1 : ℕ) : ℝ)) w : M → ℂ) = u := by
    induction n with
    | zero =>
      simp only [Nat.add_zero]
      exact ⟨A, v, hv⟩
    | succ n ih =>
      obtain ⟨B, w, hw⟩ := ih
      have ht : Module.finrank ℝ E < 2 * (2 * ((k + n + 1 : ℕ) : ℝ)) := by
        simpa only [Nat.add_assoc] using hkn (n + 1)
      convert B.semilinear_regularity_step a hu he w hw ht using 1
  apply contMDiff_infty.mpr
  intro L
  obtain ⟨B, w, hw⟩ := hrep (L + 1)
  rw [← hw]
  apply contMDiff_manifoldSobolevRepresentative B.p B.η
    (fun i => HasCompactSupport.of_compactSpace (B.η i)) B.chart_η B.smooth_η
    B.χ B.chart_χ B.smooth_χ B.sum_η
    (fun i x hx => (B.one_χ i).self_of_nhdsSet hx) L _ w
  push_cast
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  linarith

end CompactMetricAtlas
end YauCounterexamples

end

end OAI
