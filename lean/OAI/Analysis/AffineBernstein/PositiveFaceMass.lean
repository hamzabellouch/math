import Mathlib
import OAI.Analysis.AffineBernstein.AffineStripArea
import OAI.Analysis.AffineBernstein.OrthantGeometry

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

lemma integral_le_good_add_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {K G : Set X} {S : ι → Set X} {f : X → ℝ}
    (hK : MeasurableSet K) (hG : MeasurableSet G) (hS : ∀ i, MeasurableSet (S i))
    (hGK : G ⊆ K) (hsub : ∀ i, S i ⊆ K) (hcover : K ⊆ G ∪ ⋃ i, S i)
    (hn : ∀ x ∈ K, 0 ≤ f x) :
    (∫ x in K, f x ∂μ) ≤ (∫ x in G, f x ∂μ) + ∑ i, ∫ x in S i, f x ∂μ := by
  let T : Option ι → Set X := fun i => Option.casesOn i G S
  have hh : (∫ x in K, f x ∂μ) ≤ ∑ i, ∫ x in T i, f x ∂μ := by
    apply integral_le_sum_cover hK (fun i => by cases i; exact hG; exact hS _)
      (fun i => by cases i; exact hGK; exact hsub _)
    · intro x hx
      rcases hcover hx with h | h
      · exact mem_iUnion.mpr ⟨none,h⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp h
        exact mem_iUnion.mpr ⟨some i,hi⟩
    · exact hn
  simpa [T,Fintype.sum_option] using hh

/- Quantitative positive area away from finitely many supporting faces. -/
theorem affine_image_good_area_lower {n k : ℕ} {Ω K : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (L : (Space n × ℝ) ≃L[ℝ] (Space n × ℝ)) (v : Space n × ℝ)
    (s : Fin k → Fin n ⊕ Unit) {R ε c : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hxR : ∀ x ∈ K, ∀ i, |(L (x,u x)+v).1 i| ≤ R)
    (htR : ∀ x ∈ K, |(L (x,u x)+v).2| ≤ R)
    (hlow : ∀ x ∈ K, ∀ i, -ε ≤ ambientCoordinates n (L (x,u x)+v) (s i))
    (harea : c ≤ Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      (∫ x in K, affineAreaDensity u x))
    (heps : (k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal*ε^((n:ℝ)/((n:ℝ)+2)) ≤ c/2) :
    c/2 ≤ Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2)) *
      ∫ x in K ∩ {x | ∀ i, ε < ambientCoordinates n (L (x,u x)+v) (s i)}, affineAreaDensity u x := by
  classical
  let F := fun x => L (x,u x)+v
  let G := K ∩ {x | ∀ i, ε < ambientCoordinates n (F x) (s i)}
  let S (i : Fin k) := K ∩ {x | ambientCoordinates n (F x) (s i) ≤ ε}
  let a := Real.rpow |L.toContinuousLinearMap.det| ((n:ℝ)/((n:ℝ)+2))
  have hF : ContinuousOn F K :=
    ((L.continuous.comp_continuousOn (continuousOn_id.prodMk (hu.continuousOn.mono hKΩ))).add continuousOn_const)
  have hmS (i : Fin k) : MeasurableSet (S i) :=
    measurableSet_inter_preimage_continuousOn hK
      ((continuous_ambientCoordinate (s i)).comp_continuousOn hF) measurableSet_Iic
  have hmG : MeasurableSet G := by
    change MeasurableSet (K ∩ F ⁻¹' {z : Space n × ℝ | ∀ i, ε < ambientCoordinates n z (s i)})
    apply measurableSet_inter_preimage_continuousOn hK hF
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (continuous_ambientCoordinate (s i)).measurable
  have hcov : K ⊆ G ∪ ⋃ i, S i := by
    intro x hx
    by_cases hh : ∀ i, ε < ambientCoordinates n (F x) (s i)
    · exact Or.inl ⟨hx,hh⟩
    · push Not at hh
      obtain ⟨i,hi⟩ := hh
      exact Or.inr (mem_iUnion.mpr ⟨i,hx,hi⟩)
  have hsum := integral_le_good_add_cover (μ := volume) (f := affineAreaDensity u)
    hK hmG hmS inter_subset_left (fun i => inter_subset_left) hcov
    (fun x hx => Real.rpow_nonneg (hp x (hKΩ hx)).det_pos.le _)
  have hbound : a * ∑ i, ∫ x in S i, affineAreaDensity u x ≤ c/2 := by
    calc
      _ = ∑ i, a * ∫ x in S i, affineAreaDensity u x := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin k, (graphAreaBoxBound n (2*max R 1)).toReal * ε^((n:ℝ)/((n:ℝ)+2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact affine_image_strip_area hΩ hcv (hmS i) (fun x hx => hKΩ hx.1) hu hp L v (s i) hR hε
          (fun x hx => hxR x hx.1) (fun x hx => htR x hx.1)
          (fun x hx => abs_le.mpr ⟨hlow x hx.1 i,hx.2⟩)
      _ = (k:ℝ)*(graphAreaBoxBound n (2*max R 1)).toReal*ε^((n:ℝ)/((n:ℝ)+2)) := by simp; ring
      _ ≤ c/2 := heps
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (abs_nonneg L.toContinuousLinearMap.det) ((n:ℝ)/((n:ℝ)+2)))
  change a * _ ≤ a * _ at hh
  rw [mul_add] at hh
  change c ≤ a * _ at harea
  change c/2 ≤ a * _
  linarith

end AffineBernstein

end

end OAI
