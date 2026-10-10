import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology NNReal

namespace WeakMTWTransport
section RestrictedTransform
variable {M : Type*} [MetricSpace M] [CompactSpace M]

def restrictedTransform (v : M → ℝ) (S : Set M) (x : M) : ℝ :=
  sSup ((fun y => -cost x y-v y) '' S)

omit [CompactSpace M] in
lemma exists_restrictedTransform_contact {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) (x : M) :
    ∃ y∈S, restrictedTransform v S x = -cost x y-v y ∧
      ∀ z∈S, -cost x z-v z ≤ restrictedTransform v S x := by
  obtain ⟨y,hy,H⟩ := hS.exists_isMaxOn hSn
    (((continuous_cost_right x).neg.sub hv).continuousOn)
  have hg : IsGreatest ((fun y => -cost x y-v y) '' S) (-cost x y-v y) := by
    refine ⟨mem_image_of_mem _ hy,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact H hz
  refine ⟨y,hy,hg.csSup_eq,?_⟩
  intro z hz
  rw [restrictedTransform,hg.csSup_eq]
  exact H hz

omit [CompactSpace M] in
lemma restrictedTransform_lipschitz {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) {D : ℝ≥0}
    (hD : ∀ x y : M,dist x y≤D) : LipschitzWith D (restrictedTransform v S) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x x'
  obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  obtain ⟨y',hy',he',H'⟩ := exists_restrictedTransform_contact hv hS hSn x'
  have A := H y' hy'
  have B := H' y hy
  have C := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y)).1
  have C' := (abs_le.mp (cost_lipschitz_of_distance_bound hD x x' y')).2
  rw [Real.dist_eq,abs_le]
  constructor <;> linarith only [he,he',A,B,C,C']

lemma continuous_restrictedTransform {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) :
    Continuous (restrictedTransform v S) := by
  let D : ℝ≥0 := ⟨Metric.diam (univ:Set M),Metric.diam_nonneg⟩
  exact (restrictedTransform_lipschitz hv hS hSn (D := D)
    (fun x y => Metric.dist_le_diam_of_mem isCompact_univ.isBounded
      (mem_univ x) (mem_univ y))).continuous

variable [Nonempty M]

lemma restrictedTransform_le {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) (x : M) :
    restrictedTransform v S x ≤ cTransform v x := by
  obtain ⟨y,hy,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  rw [he]
  have Hc := cTransform_gap_nonneg hv x y
  dsimp only [contactGap] at Hc
  linarith only [Hc]

lemma restrictedTransform_eq_of_contact {v : M → ℝ} (hv : Continuous v)
    {S : Set M} (hS : IsCompact S) (hSn : S.Nonempty) {x y : M}
    (hy : y∈S) (hc : contactGap (cTransform v) v x y=0) :
    restrictedTransform v S x=cTransform v x := by
  obtain ⟨z,hz,he,H⟩ := exists_restrictedTransform_contact hv hS hSn x
  have H' := H y hy
  have Hc := restrictedTransform_le hv hS hSn x
  dsimp only [contactGap] at hc
  linarith only [H',Hc,hc]

lemma cTransform_eq_max_restricted {v : M → ℝ} (hv : Continuous v)
    {S R : Set M} (hS : IsCompact S) (hSn : S.Nonempty)
    (hR : IsCompact R) (hRn : R.Nonempty) {x : M}
    (hcover : ∀ y, contactGap (cTransform v) v x y=0 → y∈S ∪ R) :
    cTransform v x=max (restrictedTransform v S x) (restrictedTransform v R x) := by
  have hle := max_le (restrictedTransform_le hv hS hSn x)
    (restrictedTransform_le hv hR hRn x)
  obtain ⟨y,hy,_⟩ := exists_cTransform_contact hv x
  have hc : contactGap (cTransform v) v x y=0 := by
    dsimp [contactGap]; linarith only [hy]
  rcases hcover y hc with h|h
  · rw [restrictedTransform_eq_of_contact hv hS hSn h hc]
    exact (max_eq_left (restrictedTransform_le hv hR hRn x)).symm
  · rw [restrictedTransform_eq_of_contact hv hR hRn h hc]
    exact (max_eq_right (restrictedTransform_le hv hS hSn x)).symm

end RestrictedTransform
end WeakMTWTransport

end

end

end

end OAI
