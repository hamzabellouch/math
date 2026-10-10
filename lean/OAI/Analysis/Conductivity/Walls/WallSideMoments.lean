import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactPhysicalCorrections
import OAI.Analysis.Conductivity.Walls.ParametricWallTensors

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix MeasureTheory Filter Topology

lemma boxCoordinates_positive_integral (f : Coord3 → ℝ) :
    (∫ x in {x : Coord3 | 0<x 2},f x)=
      ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),f (boxCoordinates.symm p) := by
  let U : Set Box3 := (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ)
  let S : Set Coord3 := {x | 0<x 2}
  have he : (fun x => U.indicator (fun p => f (boxCoordinates.symm p)) (boxCoordinates x))=S.indicator f := by
    funext x
    by_cases hx : 0<x 2
    · have hU : boxCoordinates x∈U := ⟨mem_univ _,hx⟩
      rw [indicator_of_mem hU,indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx),boxCoordinates.symm_apply_apply]
    · have hU : boxCoordinates x∉U := fun hh => hx hh.2
      rw [indicator_of_notMem hU,indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx)]
  have hh := boxCoordinates_integral (U.indicator (fun p => f (boxCoordinates.symm p)))
  rw [he,integral_indicator (isOpen_lt continuous_const (continuous_apply 2)).measurableSet,
    integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi)] at hh
  exact hh

lemma wallPositivePair_moment {v : Box3 → ℝ} {r : PhysicalSourcePair} {δ : ℝ}
    (hδ : 0<δ) (hs : ∀ j x,x∈tsupport (r j) → δ≤|x 2|) :
    physicalSourceMoment (wallCoordinatePair v) (fun j => wallPositiveCut δ (r j))=
      ![∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),r 0 (boxCoordinates.symm p),
        ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),r 1 (boxCoordinates.symm p),
        ∫ p in (univ : Set (ℝ×ℝ))×ˢIoi (0:ℝ),
          v p*r 0 (boxCoordinates.symm p)-p.1.1*r 1 (boxCoordinates.symm p)] := by
  have hcut (j) := wallPositiveCut_indicator hδ (hs j)
  have hS : MeasurableSet {x : Coord3 | 0<x 2} :=
    (isOpen_lt continuous_const (continuous_apply 2)).measurableSet
  have he : (fun x => wallCoordinatePair v x 1*wallPositiveCut δ (r 0) x-
      wallCoordinatePair v x 0*wallPositiveCut δ (r 1) x)=
      {x : Coord3 | 0<x 2}.indicator (fun x => wallCoordinatePair v x 1*r 0 x-
        wallCoordinatePair v x 0*r 1 x) := by
    funext x
    rw [hcut 0,hcut 1]
    by_cases hx : 0<x 2
    · simp only [indicator_of_mem (show x∈{x : Coord3 | 0<x 2} from hx)]
    · simp only [indicator_of_notMem (show x∉{x : Coord3 | 0<x 2} from hx),mul_zero,sub_zero]
  ext i
  fin_cases i
  · change (∫ x,wallPositiveCut δ (r 0) x)=_
    rw [hcut 0,integral_indicator hS,boxCoordinates_positive_integral]
    rfl
  · change (∫ x,wallPositiveCut δ (r 1) x)=_
    rw [hcut 1,integral_indicator hS,boxCoordinates_positive_integral]
    rfl
  · change (∫ x,wallCoordinatePair v x 1*wallPositiveCut δ (r 0) x-
      wallCoordinatePair v x 0*wallPositiveCut δ (r 1) x)=_
    rw [he,integral_indicator hS,boxCoordinates_positive_integral]
    simp only [wallCoordinatePair,Matrix.cons_val_zero,Matrix.cons_val_one,boxCoordinates.apply_symm_apply]
    rfl

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix Filter Topology
open scoped Matrix.Norms.Elementwise

lemma symmetricSource_compactSmoothPair {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) : CompactSmoothPair (symmetricSource H u) :=
  fun j => ⟨coordinateDivergence_smooth (symmetricFlux_smooth hH hu j),
    coordinateDivergence_compact (symmetricFlux_compact hc u j)⟩

lemma physicalSourceMoment_symmetricSource {H : Coord3 → Mat3} {u : Coord3 → Fin 2 → ℝ}
    (hH : ContDiff ℝ (↑(⊤:ℕ∞)) H) (hc : HasCompactSupport H)
    (hsy : ∀ x,(H x).IsSymm) (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) :
    physicalSourceMoment u (symmetricSource H u)=0 := by
  have hh := (symmetric_cutoff_sources H hH hc hsy u hu).2.2.2
  ext i
  fin_cases i
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

lemma wallPositiveCut_sub (δ : ℝ) (f g : Coord3 → ℝ) :
    wallPositiveCut δ (f-g)=wallPositiveCut δ f-wallPositiveCut δ g := by
  funext x
  simp only [wallPositiveCut,Pi.sub_apply,mul_sub]

lemma wallPositiveCut_zero (δ : ℝ) : wallPositiveCut δ 0=0 := by
  funext x; simp [wallPositiveCut]

lemma CompactSmoothPair.wallPositiveCut {r : PhysicalSourcePair} (hr : CompactSmoothPair r) (δ : ℝ) :
    CompactSmoothPair (fun j => wallPositiveCut δ (r j)) := fun j =>
  ⟨wallPositiveCut_smooth (hr j).1,(hr j).2.mul_left⟩

lemma PairSupported.wallPositiveCut {r : PhysicalSourcePair} {K : Set Coord3}
    (hr : PairSupported r K) (δ : ℝ) :
    PairSupported (fun j => wallPositiveCut δ (r j)) K := fun j =>
  tsupport_mul_subset_right.trans (hr j)

lemma wallPositiveSource_moment {χ v : Box3 → ℝ} {a : (ℝ×ℝ) → ℝ} {δ : ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hχc : HasCompactSupport χ)
    (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤:ℕ∞)) a)
    (hz : ∀ q,wallDerivative v (q,0)=0)
    (hne : ∀ p∈tsupport χ,wallQuotient (wallDerivative v) p≠0)
    (hcut : ∀ q,χ (q,0)*a q=a q) (hδ : 0<δ)
    (hgap : ∀ j x,x∈tsupport (symmetricSource (wallHomogeneousTensor χ v a)
      (wallCoordinatePair v) j) → δ≤|x 2|) :
    physicalSourceMoment (wallCoordinatePair v)
      (fun j => wallPositiveCut δ (symmetricSource (wallHomogeneousTensor χ v a)
        (wallCoordinatePair v) j))=
      fun i => -(∫ q,a q*wallActualMoment v q i) := by
  rw [wallPositivePair_moment hδ hgap]
  have hh := wallHomogeneousTensor_transfers hχ hχc hv ha hz hne hcut
  ext i
  fin_cases i
  · simpa [wallActualMoment] using hh.1
  · exact hh.2.1
  · exact hh.2.2

lemma compact_parametric_norm_small_global {P F : Type*} [TopologicalSpace P]
    [NormedAddCommGroup F] {f : P×Coord3 → F} {p : P} {K : Set Coord3}
    (hK : IsCompact K) (hf : ∀ x∈K,ContinuousAt f (p,x))
    (hz : ∀ x,f (p,x)=0)
    (hs : ∀ᶠ q in 𝓝 p,tsupport (fun x => f (q,x))⊆K)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ q in 𝓝 p,∀ x,‖f (q,x)‖≤ε := by
  filter_upwards [compact_parametric_norm_small hK hf (fun x _ => hz x) hε,hs] with q small supp
  intro x
  by_cases hx : x∈K
  · exact small x hx
  · rw [image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun hh => hx (supp hh)),norm_zero]
    exact hε.le

end ScalarConductivity

end
end

end OAI
