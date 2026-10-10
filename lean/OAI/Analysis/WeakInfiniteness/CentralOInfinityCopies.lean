import Mathlib
import OAI.Analysis.WeakInfiniteness.CentralCopiesTensor
import OAI.Analysis.WeakInfiniteness.CentralCuntzWords
import OAI.Analysis.WeakInfiniteness.CentralExactPair
import OAI.Analysis.WeakInfiniteness.UnitalCuntzEmbedding

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

universe u

variable {A : Type u} [CStarAlgebra A]

lemma cstar_norm_pow_le_one (s : A) (hs : ‖s‖≤1) (n : ℕ) : ‖s^n‖≤1 := by
  induction n with
  | zero => simpa using (cstar_norm_one_le_one (A := A))
  | succ n ih =>
    rw [pow_succ]
    exact (norm_mul_le _ _).trans ((mul_le_mul ih hs (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

lemma norm_commutator_pow_le (a s : A) (hs : ‖s‖≤1) (δ : ℝ) (hδ : 0≤δ)
    (hcomm : ‖a*s-s*a‖≤δ) (n : ℕ) : ‖a*s^n-s^n*a‖≤(n:ℝ)*δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hn : ‖s^n‖≤1 := cstar_norm_pow_le_one s hs n
    calc
      _ ≤ ‖a*s^n-s^n*a‖*‖s‖+‖s^n‖*‖a*s-s*a‖ := norm_commutator_mul_le _ _ _
      _ ≤ ((n:ℝ)*δ)*1+1*δ := by
        exact add_le_add (mul_le_mul ih hs (norm_nonneg _) (by positivity))
          (mul_le_mul hn hcomm (norm_nonneg _) zero_le_one)
      _ = _ := by simp only [Nat.cast_add,Nat.cast_one]; ring

lemma LocalCentralExactCuntzPair.central_generators (h : LocalCentralExactCuntzPair A)
    (E : Finset A) (L : Finset ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ θ : OInfinity →⋆ₐ[ℂ] A,∀ a ∈ E,∀ i ∈ L,
      ‖a*θ (oInfinityIsometry i)-θ (oInfinityIsometry i)*a‖<ε := by
  classical
  let N : ℝ := 1+∑ i ∈ L,((i:ℝ)+1)
  have hN : 0<N := by dsimp only [N]; positivity
  have hiN (i : ℕ) (hi : i∈L) : (i:ℝ)+1≤N := by
    have hb := Finset.single_le_sum (f := fun j : ℕ => (j:ℝ)+1)
      (fun _ _ => by positivity) hi
    dsimp only [N]
    linarith
  let δ := ε/(2*N)
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨r,s,hr,hs,hrs,hcomm⟩ := h E δ hδ
  refine ⟨oInfinityMap (fun n => s^n*r) (binaryCuntzFamily_relations hr hs hrs),?_⟩
  intro a ha i hi
  rw [oInfinityMap_isometry]
  have hrn : ‖r‖≤1 := norm_isometry_le_one hr
  have hsn : ‖s‖≤1 := norm_isometry_le_one hs
  have hn : ‖s^i‖≤1 := cstar_norm_pow_le_one s hsn i
  have hp := norm_commutator_pow_le a s hsn δ hδ.le (hcomm a ha).2.le i
  calc
    _ ≤ ‖a*s^i-s^i*a‖*‖r‖+‖s^i‖*‖a*r-r*a‖ := norm_commutator_mul_le _ _ _
    _ ≤ ((i:ℝ)*δ)*1+1*δ := add_le_add
      (mul_le_mul hp hrn (norm_nonneg _) (by positivity))
      (mul_le_mul hn (hcomm a ha).1.le (norm_nonneg _) zero_le_one)
    _ = ((i:ℝ)+1)*δ := by ring
    _ ≤ N*δ := mul_le_mul_of_nonneg_right (hiN i hi) hδ.le
    _ = ε/2 := by dsimp only [δ]; field_simp
    _ < ε := by linarith

lemma oInfinityPolynomial_denseRange : DenseRange (cuntzPolynomial oInfinityIsometry) := by
  have hsub : (StarAlgebra.adjoin ℂ (Set.range oInfinityIsometry) : Set OInfinity) ⊆
      Set.range (cuntzPolynomial oInfinityIsometry) := by
    intro y hy
    exact exists_cuntzPolynomial_of_mem_adjoin _ _ hy
  have ht : closure (StarAlgebra.adjoin ℂ (Set.range oInfinityIsometry) : Set OInfinity)=Set.univ := by
    change (closedStarSpan (Set.range oInfinityIsometry) : Set OInfinity)=Set.univ
    rw [oInfinity_generators_dense]
    rfl
  apply dense_iff_closure_eq.mpr
  apply Set.eq_univ_of_univ_subset
  rw [← ht]
  exact closure_mono hsub

lemma LocalCentralExactCuntzPair.approximatelyCentralCopies
    (h : LocalCentralExactCuntzPair A) : ApproximatelyCentralCopies A OInfinity := by
  classical
  intro E K ε hε
  let M : ℝ := 1+∑ a ∈ E,‖a‖
  have hM : 0<M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a∈E) : ‖a‖≤M := by
    have hb := Finset.single_le_sum (f := fun a : A => ‖a‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]
    linarith
  have happ (d : OInfinity) : ∃ c : List (ℕ × Bool) →₀ ℂ,
      ‖d-cuntzPolynomial oInfinityIsometry c‖<ε/(8*M) := by
    obtain ⟨c,hc⟩ := Metric.denseRange_iff.mp oInfinityPolynomial_denseRange d (ε/(8*M)) (by positivity)
    exact ⟨c,by simpa only [dist_eq_norm] using hc⟩
  choose c hc using happ
  let C : ℝ := 1+∑ d ∈ K,cuntzPolynomialCentralWeight (c d)
  have hC : 0<C := by
    have hh := Finset.sum_nonneg (fun d (_ : d∈K) => cuntzPolynomialCentralWeight_nonneg (c d))
    dsimp only [C]
    linarith
  have hdC (d : OInfinity) (hd : d∈K) : cuntzPolynomialCentralWeight (c d)≤C := by
    have hb := Finset.single_le_sum (f := fun d => cuntzPolynomialCentralWeight (c d))
      (fun _ _ => cuntzPolynomialCentralWeight_nonneg _) hd
    dsimp only [C]
    linarith
  let L : Finset ℕ := K.biUnion (fun d => (c d).support.biUnion (fun w => w.toFinset.image Prod.fst))
  have hL (d : OInfinity) (hd : d∈K) (w : List (ℕ × Bool)) (hw : w∈(c d).support)
      (ib : ℕ × Bool) (hib : ib∈w) : ib.1∈L := by
    apply Finset.mem_biUnion.mpr
    refine ⟨d,hd,Finset.mem_biUnion.mpr ⟨w,hw,?_⟩⟩
    exact Finset.mem_image.mpr ⟨ib,by simpa using hib,rfl⟩
  let δ := ε/(4*C)
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨θ,hθ⟩ := h.central_generators (E ∪ E.image star) L δ hδ
  refine ⟨θ,?_⟩
  intro a ha d hd
  let s : ℕ → A := fun i => θ (oInfinityIsometry i)
  have hs (i : ℕ) : ‖s i‖≤1 := by
    apply norm_isometry_le_one
    dsimp only [s]
    rw [← map_star,← map_mul,oInfinityIsometry_relations,ite_eq_left rfl,map_one]
  have hpoly : ‖a*θ (cuntzPolynomial oInfinityIsometry (c d))-
      θ (cuntzPolynomial oInfinityIsometry (c d))*a‖≤cuntzPolynomialCentralWeight (c d)*δ := by
    rw [map_cuntzPolynomial]
    apply norm_cuntzPolynomial_commutator_le s hs a (c d) δ hδ.le
    intro w hw ib hib
    exact ⟨(hθ a (Finset.mem_union_left _ ha) ib.1 (hL d hd w hw ib hib)).le,
      (hθ (star a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
        ib.1 (hL d hd w hw ib hib)).le⟩
  have hn : ‖θ d-θ (cuntzPolynomial oInfinityIsometry (c d))‖≤
      ‖d-cuntzPolynomial oInfinityIsometry (c d)‖ := by
    rw [← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le _ _
  have herr : 2*‖a‖*‖θ d-θ (cuntzPolynomial oInfinityIsometry (c d))‖≤ε/4 := by
    calc
      _ ≤ 2*M*(ε/(8*M)) := by
        gcongr
        · exact haM a ha
        · exact hn.trans (hc d).le
      _ = _ := by field_simp; ring
  have hmain : cuntzPolynomialCentralWeight (c d)*δ≤ε/4 := by
    calc
      _ ≤ C*δ := mul_le_mul_of_nonneg_right (hdC d hd) hδ.le
      _ = _ := by dsimp only [δ]; field_simp
  rw [norm_sub_rev]
  have hb := norm_commutator_perturbation_le a (θ d) (θ (cuntzPolynomial oInfinityIsometry (c d)))
  linarith

end

end WeakPureInfiniteness
end

end OAI
