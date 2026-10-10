import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.Admissible01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
noncomputable section
open scoped Topology BigOperators commutatorElement
noncomputable section
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
open scoped BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
noncomputable section
open scoped Topology BigOperators
namespace SourceBlocks
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open ConstructedWordPlan.RationalPivotPlan SourcePivotPaths
attribute [local instance] Classical.propDecidable
variable {a : ℕ}

def targetBlock (i : Fin a) (t : Fin (pivot i).targets) : Block a := ⟨i,tailEnum i t⟩

@[simp] lemma targetBlock_target (i : Fin a) (t : Fin (pivot i).targets) :
    (targetBlock i t).target = t := (tailEnum i).symm_apply_apply t

@[simp] lemma targetBlock_set (i : Fin a) (t : Fin (pivot i).targets) :
    (targetBlock i t).set = block (pivot i).index (pivot i).tail t := rfl

@[simp] lemma targetBlock_block (B : Block a) : targetBlock B.1 B.target = B := by
  rcases B with ⟨i,T⟩
  change (⟨i,tailEnum i ((tailEnum i).symm T)⟩ : Block a) = ⟨i,T⟩
  rw [Equiv.apply_symm_apply]

lemma pair_injective (i : Fin a) : Function.Injective
    (fun e : Fin (pivot i).pairs => ((pivot i).owner e,(pivot i).added e)) := by
  intro e f h
  apply (pairEnum i).injective
  exact Subtype.ext h

 
def subsetPairs (B : Block a) (U : Finset (Finset (Fin a))) : OwnSubset (pivot B.1) B.target :=
  ⟨Finset.univ.filter (fun e => (pivot B.1).owner e = B.target ∧ (pivot B.1).added e ∈ U),
    fun pairIndex membership => show (pivot B.1).owner pairIndex = B.target from
      (Finset.mem_filter.mp membership).2.1⟩

lemma mem_subsetPairs (B : Block a) (U : Finset (Finset (Fin a)))
    (e : Fin (pivot B.1).pairs) :
    e ∈ (subsetPairs B U).val ↔ (pivot B.1).owner e = B.target ∧ (pivot B.1).added e ∈ U := by
  simp [subsetPairs]

lemma subsetPairs_sum (B : Block a) (U : Finset (Finset (Fin a)))
    (hU : ∀ A ∈ U, Added B.1 B.2.val A) (f : Finset (Fin a) → ℚ) :
    (∑ e ∈ (subsetPairs B U).val, f ((pivot B.1).added e)) = ∑ A ∈ U, f A := by
  apply Finset.sum_bij (fun e _ => (pivot B.1).added e)
  · intro e he
    exact ((mem_subsetPairs B U e).mp he).2
  · intro e he f hf h
    apply pair_injective B.1
    exact Prod.ext (((mem_subsetPairs B U e).mp he).1.trans
      ((mem_subsetPairs B U f).mp hf).1.symm) h
  · intro A hA
    obtain ⟨e,he,hAe⟩ := (added_exists_iff B A).mpr (hU A hA)
    exact ⟨e,(mem_subsetPairs B U e).mpr ⟨he,hAe ▸ hA⟩,hAe⟩
  · intro e he
    rfl

abbrev Models (a r : ℕ) := Block a → ℚ → Fin r → ℤ → ℝ

 

def scalar {r : ℕ} (S : Models a r) (D : Pivot a) : ScalarModels D r :=
  fun t v c k => if h : (D.tail t).Nonempty then
    S ⟨D.index,⟨D.tail t,h,D.tail_lt t⟩⟩ v c k else 0

lemma scalar_canonical {r : ℕ} (S : Models a r) (i : Fin a)
    (t : Fin (pivot i).targets) (v : ℚ) (c : Fin r) (k : ℤ) :
    scalar S (pivot i) t v c k = S (targetBlock i t) v c k := by
  have ht := (tailEnum i t).property.1
  simp only [scalar, show (pivot i).tail t = (tailEnum i t).val from rfl, dite_eq_left ht]
  rfl

 
def offset (ht : Fin a → ℤ) (b : Scale a) (u : Fin a → ℕ)
    (B : Block a) (U : Finset (Finset (Fin a))) : ℚ :=
  ∑ A ∈ U, ((height ht A : ℚ)*blockProduct b A /
    ((height ht B.set : ℚ)*blockProduct b B.set)) *
      (height (fun j => (u j : ℤ)) A : ℚ)

 

def aligned {r : ℕ} (S : Models a r) (ht : Fin a → ℤ) (b : Scale a)
    (u : Fin a → ℕ) (τ : ℝ) : Prop :=
  ∀ (B : Block a) (U : Finset (Finset (Fin a))),
    (∀ A ∈ U, Added B.1 B.2.val A) → ∀ c : Fin r,
      ∃ Δ : ℤ, (Δ : ℚ) = offset ht b u B U ∧
        (2*τ < S B (blockProduct b B.set) c (height (fun j => (u j : ℤ)) B.set) →
          τ < S B (blockProduct b B.set) c (height (fun j => (u j : ℤ)) B.set+Δ))

 

theorem aligned_of_canonical {r : ℕ} (S : Models a r) (ht : Fin a → ℤ)
    (b : Scale a) (u : Fin a → ℕ) (τ : ℝ)
    (h : ∀ D ∈ pivots a, comparison D r (scalar S D) ht b u (u D.index) τ) :
    aligned S ht b u τ := by
  intro B U hU c
  have hc := h (pivot B.1) (mem_pivots B.1) B.target (subsetPairs B U) c
  obtain ⟨Δ,hΔ,himp⟩ := hc
  refine ⟨Δ,?_,?_⟩
  · rw [hΔ]
    calc
      _ = ∑ e ∈ (subsetPairs B U).val,
          ((height ht ((pivot B.1).added e) : ℚ)*blockProduct b ((pivot B.1).added e)/
            ((height ht B.set : ℚ)*blockProduct b B.set))*
          (height (fun j => (u j : ℤ)) ((pivot B.1).added e) : ℚ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [((mem_subsetPairs B U e).mp he).1, block_target_set]
      _ = _ := subsetPairs_sum B U hU (fun A =>
        ((height ht A : ℚ)*blockProduct b A/((height ht B.set : ℚ)*blockProduct b B.set))*
          (height (fun j => (u j : ℤ)) A : ℚ))
  · have hnot : B.1 ∉ B.2.val := by
      intro hi
      exact lt_irrefl _ (B.2.property.2 B.1 hi)
    have hy : height (fun j => (u j : ℤ)) ((pivot B.1).tail B.target)*(u (pivot B.1).index : ℤ) =
        height (fun j => (u j : ℤ)) B.set := by
      simp only [block_target_tail, pivot_index, Block.set, height, Finset.prod_insert hnot, mul_comm]
    simpa only [scalar_canonical, targetBlock_block, block_target_set, hy] using himp

end SourceBlocks

 

 

 

noncomputable section
open scoped Topology BoundedContinuousFunction NNReal BigOperators
namespace SourceFiniteMenuModels
open SourceAdmissible SourceBlocks SourceChartedAlignment SourceChartedMenu
open SourcePivotPaths ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
attribute [local instance] Classical.propDecidable
variable {a s r : ℕ}

 

structure System (A : Parameters a) (values : Finset ℚ) (r : ℕ) (F : Menu s) where
  model : ℕ → Models a r
  K : ℝ≥0
  piece : ℕ → Block a → ∀ (v : ℚ), v ∈ values →
    Fin r → ℤ → ℤ → Piece F K
  represents : ∀ N B v hv c k,
    model N B v c k =
      (piece N B v hv c (k/(A.H N B.1 : ℤ)) (k%(A.M N : ℤ))).eval
        ((k-k%(A.M N : ℤ))/(A.M N : ℤ))

variable {A : Parameters a} {values : Finset ℚ} {F : Menu s} (S : System A values r F)

def extended (N : ℕ) : Models a r := fun B v c k =>
  if v ∈ values then S.model N B v c k else 0

lemma extended_eq (N : ℕ) (B : Block a) (v : ℚ) (hv : v ∈ values) (c : Fin r) (k : ℤ) :
    extended S N B v c k = S.model N B v c k := ite_eq_left hv

 

def charted (i : Fin a) : ChartedModels s r (pivot i) where
  G _ _ _ := F.productG
  group _ _ _ := inferInstance
  topology _ _ _ := inferInstance
  topGroup _ _ _ := inferInstance
  Γ _ _ _ := F.productΓ
  dim _ _ _ := F.productChart.dim
  coords _ _ _ := F.productChart.coords
  second _ _ _ := F.productChart.second
  filtration _ _ _ := F.productChart.filtration
  weight _ _ _ := F.productChart.weight
  level_iff _ _ _ := F.productChart.level_iff
  weight_pos _ _ _ := F.productChart.weight_pos
  lattice_iff _ _ _ := F.productChart.lattice_iff
  weight_mono _ _ _ := F.productChart.weight_mono
  level0 _ _ _ := F.productChart.level0
  level1 _ _ _ := F.productChart.level1
  step _ _ _ := F.productChart.step
  g t N v c b r' := if hv : v ∈ values then (S.piece N (targetBlock i t) v hv c b r').padG else 1
  x t N v c b r' := if hv : v ∈ values then (S.piece N (targetBlock i t) v hv c b r').padX else 1
  obs t N v c b r' := if hv : v ∈ values then (S.piece N (targetBlock i t) v hv c b r').padObs else 0
  metric _ _ _ := F.productMetric
  compatible _ _ _ := F.productCompatible
  K := S.K
  B := 1
  lip := by
    let : MetricSpace (F.productG ⧸ F.productΓ) :=
      F.productMetric.replaceTopology F.productCompatible
    intro t N v c b r'
    by_cases hv : v ∈ values
    · simp only [dite_eq_left hv]
      exact (S.piece N (targetBlock i t) v hv c b r').pad_lip
    · simp only [dite_eq_right hv, BoundedContinuousFunction.coe_zero]
      exact LipschitzWith.const' 0
  bound := by
    intro t N v c b r' z
    by_cases hv : v ∈ values
    · simp only [dite_eq_left hv]
      exact (S.piece N (targetBlock i t) v hv c b r').pad_bound z
    · simp only [dite_eq_right hv, BoundedContinuousFunction.coe_zero, Pi.zero_apply, abs_zero, zero_le_one]

 

lemma charted_models (i : Fin a) (N : ℕ) :
    A.models (charted S i) N = scalar (extended S N) (pivot i) := by
  funext t v c k
  rw [scalar_canonical]
  by_cases hv : v ∈ values
  · rw [extended_eq S N (targetBlock i t) v hv c k, S.represents]
    change (if h : v ∈ values then (S.piece N (targetBlock i t) v h c
        (k/(A.H N i : ℤ)) (k%(A.M N : ℤ))).padObs else 0)
      (QuotientGroup.mk
        ((if h : v ∈ values then (S.piece N (targetBlock i t) v h c
          (k/(A.H N i : ℤ)) (k%(A.M N : ℤ))).padG else 1)^((k-k%(A.M N : ℤ))/(A.M N : ℤ))*
         (if h : v ∈ values then (S.piece N (targetBlock i t) v h c
          (k/(A.H N i : ℤ)) (k%(A.M N : ℤ))).padX else 1))) = _
    simp only [dite_eq_left hv]
    exact (S.piece N (targetBlock i t) v hv c
      (k/(A.H N i : ℤ)) (k%(A.M N : ℤ))).pad_orbit _
  · simp only [extended, ite_eq_right hv]
    simp only [Parameters.models, scalarModels, SourceIntegerArrays.pieceModel,
      charted, dite_eq_right hv]
    rfl

 

theorem represents_all : ∀ D ∈ pivots a, ∃ C : ChartedModels s r D,
    ∀ N, scalar (extended S N) D = A.models C N := by
  intro D hD
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hD
  exact ⟨charted S i,fun N => (charted_models S i N).symm⟩

end SourceFiniteMenuModels

 

 

 

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace SourceMenuAlignment
open SourceAdmissible SourceBlocks SourceChartedAlignment SourceChartedMenu
open SourceFiniteMenuModels SourcePivotPaths
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
attribute [local instance] Classical.propDecidable
variable {a : ℕ}

instance law_probability (A : Parameters a) (N : ℕ)
    (hX : ∀ i, 4*primorial (N+1) ≤ A.X N i) : IsProbabilityMeasure (A.law N hX) := by
  unfold Parameters.law
  infer_instance

def tuples (s r : ℕ) (hs : 1 ≤ s) : Finset (Scale a) :=
  multipliers (sourcePlan s r hs (pivots a))

def values (s r : ℕ) (hs : 1 ≤ s) : Finset ℚ :=
  (tuples (a:=a) s r hs).biUnion (fun b => Finset.univ.image (fun B : Block a => blockProduct b B.set))

lemma closure (s r : ℕ) (hs : 1 ≤ s) (b : Scale a) (hb : b ∈ tuples s r hs) (B : Block a) :
    blockProduct b B.set ∈ values (a:=a) s r hs :=
  Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨B,Finset.mem_univ _,rfl⟩⟩

lemma tuples_pos (s r : ℕ) (hs : 1 ≤ s) :
    ∀ b ∈ tuples (a:=a) s r hs, ∀ j, 0 < b j :=
  source_multipliers_pos s r hs _

lemma values_pos (s r : ℕ) (hs : 1 ≤ s) :
    ∀ v ∈ values (a:=a) s r hs, 0 < v := by
  intro v hv
  obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.prod_pos (fun j _ => tuples_pos s r hs b hb j)

 

def event {r : ℕ} (bs : Finset (Scale a)) (S : Models a r)
    (ht : Fin a → ℤ) (τ : ℝ) : Set (Fin a → ℕ) :=
  {u | ∃ b ∈ bs, aligned S ht b u τ}

 

theorem menu_alignment_eventually (s r : ℕ) (hs : 1 ≤ s)
    (A : Parameters a) (F : Menu s) (S : System A (values (a:=a) s r hs) r F)
    (τ : ℝ) (hτ : 0 < τ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∃ hX : ∀ i, 4*primorial (N+1) ≤ A.X N i,
      delta s r hs (pivots a) ≤
        (A.law N hX).real (event (tuples s r hs) (S.model N) (A.ht N) τ) + ε := by
  have h := (admissible_charted_alignment (a:=a) s r hs).2.2 A
    (fun N => scalar (extended S N)) (represents_all S) τ hτ ε hε
  filter_upwards [h] with N hN
  obtain ⟨hX,hN⟩ := hN
  refine ⟨hX,hN.trans (_root_.add_le_add_left (measureReal_mono (μ:=A.law N hX) ?_ (measure_ne_top _ _)) _)⟩
  intro u hu
  obtain ⟨b,hb,hb'⟩ := hu
  refine ⟨b,hb,?_⟩
  have ha := aligned_of_canonical (extended S N) (A.ht N) b u τ hb'
  intro B U hU c
  obtain ⟨Δ,hΔ,himp⟩ := ha B U hU c
  refine ⟨Δ,hΔ,?_⟩
  simpa only [extended_eq S N B _ (closure s r hs b hb B)] using himp

 

theorem menu_alignment_liminf (s r : ℕ) (hs : 1 ≤ s)
    (A : Parameters a) (F : Menu s) (S : System A (values (a:=a) s r hs) r F)
    (μ : ℕ → Measure (Fin a → ℕ))
    (hμ : ∀ N (hX : ∀ i, 4*primorial (N+1) ≤ A.X N i), μ N = A.law N hX)
    (τ : ℝ) (hτ : 0 < τ) :
    delta s r hs (pivots a) ≤
      Filter.liminf (fun N => (μ N).real (event (tuples s r hs) (S.model N) (A.ht N) τ)) atTop := by
  let p : ℕ → ℝ := fun N => (μ N).real (event (tuples s r hs) (S.model N) (A.ht N) τ)
  have hb : IsBoundedUnder (· ≥ ·) atTop p :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall (fun N => measureReal_nonneg))
  have hu : IsBoundedUnder (· ≤ ·) atTop p := by
    apply isBoundedUnder_of_eventually_le (a:=1)
    filter_upwards [menu_alignment_eventually s r hs A F S τ hτ 1 zero_lt_one] with N hN
    obtain ⟨hX,_⟩ := hN
    dsimp [p]
    rw [hμ N hX]
    exact measureReal_le_one
  apply (Filter.le_liminf_iff hu.isCoboundedUnder_ge hb).mpr
  intro y hy
  have he : 0 < (delta s r hs (pivots a)-y)/2 := by linarith
  filter_upwards [menu_alignment_eventually s r hs A F S τ hτ _ he] with N hN
  obtain ⟨hX,hN⟩ := hN
  change y < (μ N).real _
  rw [hμ N hX]
  linarith

end SourceMenuAlignment

 

 

 

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
