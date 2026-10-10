import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralOInfinityCopies
import OAI.Analysis.WeakInfiniteness.HalfFlipCriterion
import OAI.Analysis.WeakInfiniteness.TensorFlipEquivalence

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

universe u v

section WordEstimates

variable {D : Type u} {B : Type v} [CStarAlgebra D] [NonUnitalCStarAlgebra B]

lemma norm_starHom_cuntzWord_sub_le (φ ψ : D →⋆ₙₐ[ℂ] B)
    (s : ℕ → D) (hs : ∀ i,‖s i‖≤1) (w : List (ℕ × Bool))
    (δ : ℝ) (hδ : 0≤δ) (h1 : ‖φ 1-ψ 1‖≤δ)
    (hgen : ∀ ib∈w,‖φ (s ib.1)-ψ (s ib.1)‖≤δ) :
    ‖φ (cuntzWord s w)-ψ (cuntzWord s w)‖≤((w.length:ℝ)+1)*δ := by
  induction w with
  | nil => simpa [cuntzWord] using h1
  | cons ib w ih =>
    rcases ib with ⟨i,b⟩
    let x : D := if b then s i else star (s i)
    have hx : ‖x‖≤1 := by dsimp only [x]; cases b <;> simpa only [Bool.false_eq_true,↓reduceIte,norm_star] using hs i
    have hxφ : ‖φ x‖≤1 := (NonUnitalStarAlgHom.norm_apply_le _ _).trans hx
    have hwψ : ‖ψ (cuntzWord s w)‖≤1 :=
      (NonUnitalStarAlgHom.norm_apply_le _ _).trans (norm_cuntzWord_le_one s hs w)
    have hxd : ‖φ x-ψ x‖≤δ := by
      have hh := hgen (i,b) (by simp)
      dsimp only [x]
      cases b
      · simpa only [Bool.false_eq_true,↓reduceIte,map_star,← star_sub,norm_star] using hh
      · simpa using hh
    have hi := ih (fun p hp => hgen p (List.mem_cons_of_mem _ hp))
    change ‖φ (x*cuntzWord s w)-ψ (x*cuntzWord s w)‖≤_
    have he : φ (x*cuntzWord s w)-ψ (x*cuntzWord s w)=
        φ x*(φ (cuntzWord s w)-ψ (cuntzWord s w))+(φ x-ψ x)*ψ (cuntzWord s w) := by
      rw [map_mul,map_mul]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖φ x*(φ (cuntzWord s w)-ψ (cuntzWord s w))‖+
          ‖(φ x-ψ x)*ψ (cuntzWord s w)‖ := norm_add_le _ _
      _ ≤ ‖φ x‖*‖φ (cuntzWord s w)-ψ (cuntzWord s w)‖+
          ‖φ x-ψ x‖*‖ψ (cuntzWord s w)‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 1*(((w.length:ℝ)+1)*δ)+δ*1 := add_le_add
        (mul_le_mul hxφ hi (norm_nonneg _) zero_le_one)
        (mul_le_mul hxd hwψ (norm_nonneg _) hδ)
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

def cuntzPolynomialHomWeight (c : List (ℕ × Bool) →₀ ℂ) : ℝ :=
  ∑ w∈c.support,‖c w‖*((w.length:ℝ)+1)

lemma cuntzPolynomialHomWeight_nonneg (c : List (ℕ × Bool) →₀ ℂ) :
    0≤cuntzPolynomialHomWeight c := by
  unfold cuntzPolynomialHomWeight
  positivity

lemma norm_starHom_cuntzPolynomial_sub_le (φ ψ : D →⋆ₙₐ[ℂ] B)
    (s : ℕ → D) (hs : ∀ i,‖s i‖≤1) (c : List (ℕ × Bool) →₀ ℂ)
    (δ : ℝ) (hδ : 0≤δ) (h1 : ‖φ 1-ψ 1‖≤δ)
    (hgen : ∀ w∈c.support,∀ ib∈w,‖φ (s ib.1)-ψ (s ib.1)‖≤δ) :
    ‖φ (cuntzPolynomial s c)-ψ (cuntzPolynomial s c)‖≤cuntzPolynomialHomWeight c*δ := by
  have he : φ (cuntzPolynomial s c)-ψ (cuntzPolynomial s c)=
      ∑ w∈c.support,c w • (φ (cuntzWord s w)-ψ (cuntzWord s w)) := by
    simp only [cuntzPolynomial,Finsupp.sum,map_sum,map_smul,← Finset.sum_sub_distrib,smul_sub]
  rw [he]
  calc
    _ ≤ ∑ w∈c.support,‖c w • (φ (cuntzWord s w)-ψ (cuntzWord s w))‖ := norm_sum_le _ _
    _ ≤ ∑ w∈c.support,‖c w‖*(((w.length:ℝ)+1)*δ) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_starHom_cuntzWord_sub_le φ ψ s hs w δ hδ h1 (hgen w hw))
        (norm_nonneg _)
    _ = _ := by simp only [cuntzPolynomialHomWeight,Finset.sum_mul]; congr 1; ext w; ring

end WordEstimates

variable (D : Type u) [CStarAlgebra D]

def GeneratorHalfFlip (s : ℕ → D) : Prop :=
  ∀ (N : ℕ) (ε : ℝ),0<ε →
    ∃ u : unitary (Unitization ℂ (MinimalTensor D D)),
      ‖unitizationInnerFun u (minimalElementary (1:D) (1:D))-
        minimalElementary (1:D) (1:D)‖<ε ∧
      ∀ i<N,‖unitizationInnerFun u (minimalElementary (s i) (1:D))-
        minimalElementary (1:D) (s i)‖<ε

variable {D}

lemma ApproximateHalfFlip.generatorTests (h : ApproximateHalfFlip D) (s : ℕ → D) :
    GeneratorHalfFlip D s := by
  classical
  intro N ε hε
  obtain ⟨u,hu⟩ := h (insert 1 ((Finset.range N).image s)) ε hε
  refine ⟨u,hu 1 (Finset.mem_insert_self _ _),?_⟩
  intro i hi
  exact hu _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩))

lemma GeneratorHalfFlip.halfFlip (s : ℕ → D) (hs : ∀ i,‖s i‖≤1)
    (hdense : DenseRange (cuntzPolynomial s)) (h : GeneratorHalfFlip D s) :
    ApproximateHalfFlip D := by
  classical
  intro K ε hε
  have happ (d : D) : ∃ c : List (ℕ × Bool) →₀ ℂ,
      ‖d-cuntzPolynomial s c‖<ε/8 := by
    obtain ⟨c,hc⟩ := Metric.denseRange_iff.mp hdense d (ε/8) (by positivity)
    exact ⟨c,by simpa only [dist_eq_norm] using hc⟩
  choose c hc using happ
  let C : ℝ := 1+∑ d∈K,cuntzPolynomialHomWeight (c d)
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun d (_ : d∈K) => cuntzPolynomialHomWeight_nonneg (c d))
    dsimp only [C]
    linarith
  have hdC (d : D) (hd : d∈K) : cuntzPolynomialHomWeight (c d)≤C := by
    have hb := Finset.single_le_sum (f := fun d => cuntzPolynomialHomWeight (c d))
      (fun _ _ => cuntzPolynomialHomWeight_nonneg _) hd
    dsimp only [C]
    linarith
  let L := K.biUnion (fun d => (c d).support.biUnion (fun w => w.toFinset.image Prod.fst))
  let N := L.sup id+1
  have hN (d : D) (hd : d∈K) (w : List (ℕ × Bool)) (hw : w∈(c d).support)
      (ib : ℕ × Bool) (hib : ib∈w) : ib.1<N := by
    have hi : ib.1∈L := Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_biUnion.mpr
      ⟨w,hw,Finset.mem_image.mpr ⟨ib,by simpa using hib,rfl⟩⟩⟩
    have hh : ib.1≤L.sup id := Finset.le_sup (f := id) hi
    exact lt_of_le_of_lt hh (Nat.lt_succ_self _)
  let δ := ε/(4*C)
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨u,hu1,hu⟩ := h N δ hδ
  let φ := (unitizationInnerHom u).comp (minimalLeftEmbedding D D)
  let ψ := (minimalFlipHom D D).comp (minimalLeftEmbedding D D)
  have hφ (d : D) : φ d=unitizationInnerFun u (minimalElementary d (1:D)) := rfl
  have hψ (d : D) : ψ d=minimalElementary (1:D) d := by
    exact minimalFlipHom_elementary d 1
  have h1 : ‖φ 1-ψ 1‖≤δ := by rw [hφ,hψ]; exact hu1.le
  refine ⟨u,?_⟩
  intro d hd
  have hpoly : ‖φ (cuntzPolynomial s (c d))-
      ψ (cuntzPolynomial s (c d))‖≤cuntzPolynomialHomWeight (c d)*δ := by
    apply norm_starHom_cuntzPolynomial_sub_le φ ψ s hs (c d) δ hδ.le h1
    intro w hw ib hib
    rw [hφ,hψ]
    exact (hu ib.1 (hN d hd w hw ib hib)).le
  have hm : cuntzPolynomialHomWeight (c d)*δ≤ε/4 := by
    calc
      _ ≤ C*δ := mul_le_mul_of_nonneg_right (hdC d hd) hδ.le
      _ = _ := by dsimp only [δ]; field_simp
  have hf : ‖φ d-φ (cuntzPolynomial s (c d))‖<ε/8 := by
    rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt (hc d)
  have hg : ‖ψ (cuntzPolynomial s (c d))-ψ d‖<ε/8 := by
    rw [norm_sub_rev,← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le _ _).trans_lt (hc d)
  rw [← hφ,← hψ]
  have he : φ d-ψ d=(φ d-φ (cuntzPolynomial s (c d)))+
      (φ (cuntzPolynomial s (c d))-ψ (cuntzPolynomial s (c d)))+
      (ψ (cuntzPolynomial s (c d))-ψ d) := by abel
  rw [he]
  have hb := norm_add₃_le (a := φ d-φ (cuntzPolynomial s (c d)))
    (b := φ (cuntzPolynomial s (c d))-ψ (cuntzPolynomial s (c d)))
    (c := ψ (cuntzPolynomial s (c d))-ψ d)
  linarith

def OInfinityGeneratorHalfFlip : Prop := GeneratorHalfFlip OInfinity oInfinityIsometry

lemma oInfinity_halfFlip_iff_generatorHalfFlip :
    ApproximateHalfFlip OInfinity ↔ OInfinityGeneratorHalfFlip := by
  constructor
  · intro h
    exact h.generatorTests oInfinityIsometry
  · intro h
    exact GeneratorHalfFlip.halfFlip oInfinityIsometry
      (fun i => norm_isometry_le_one
        (by rw [oInfinityIsometry_relations,ite_eq_left rfl]))
      oInfinityPolynomial_denseRange h

end

end WeakPureInfiniteness
end

end OAI
