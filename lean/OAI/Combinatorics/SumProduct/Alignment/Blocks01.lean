import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FiniteMenu01
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
namespace SourceChartedMenu
open SourceProductChart SourceFiniteMenu

 

structure Menu (s : ℕ) where
  size : ℕ
  G : Fin size → Type
  [group : ∀ i, Group (G i)]
  [topology : ∀ i, TopologicalSpace (G i)]
  [topGroup : ∀ i, IsTopologicalGroup (G i)]
  Γ : ∀ i, Subgroup (G i)
  chart : ∀ i, Chart s (G i) (Γ i)
  metric : ∀ i, MetricSpace (G i ⧸ Γ i)
  compatible : ∀ i, QuotientGroup.instTopologicalSpace (Γ i) =
    (metric i).toUniformSpace.toTopologicalSpace

attribute [instance] Menu.group Menu.topology Menu.topGroup
variable {s : ℕ} (M : Menu s)

abbrev Menu.productG := ∀ i, M.G i
abbrev Menu.productΓ : Subgroup M.productG := productLattice M.G M.Γ

def Menu.productChart : Chart s M.productG M.productΓ := product M.G M.Γ M.chart

@[instance_reducible]
def Menu.productMetric : MetricSpace (M.productG ⧸ M.productΓ) :=
  SourceFiniteMenu.productMetric M.G M.Γ M.metric M.compatible

lemma Menu.productCompatible : QuotientGroup.instTopologicalSpace M.productΓ =
    M.productMetric.toUniformSpace.toTopologicalSpace := rfl

 

structure Piece (K : ℝ≥0) where
  index : Fin M.size
  g : M.G index
  x : M.G index
  obs : (M.G index ⧸ M.Γ index) →ᵇ ℝ
  lip : letI : MetricSpace (M.G index ⧸ M.Γ index) :=
    (M.metric index).replaceTopology (M.compatible index)
    LipschitzWith K obs
  range : ∀ z, obs z ∈ Set.Icc (0:ℝ) 1

variable {M} {K : ℝ≥0} (P : Piece M K)

def Piece.eval (k : ℤ) : ℝ := P.obs (QuotientGroup.mk (P.g^k*P.x))

def Piece.padG : M.productG := Pi.mulSingle P.index P.g
def Piece.padX : M.productG := Pi.mulSingle P.index P.x
def Piece.padObs : (M.productG ⧸ M.productΓ) →ᵇ ℝ :=
  paddedObservable M.G M.Γ P.index P.obs

lemma Piece.pad_orbit (k : ℤ) :
    P.padObs (QuotientGroup.mk (P.padG^k*P.padX)) = P.eval k :=
  padded_orbit M.G M.Γ P.index P.obs P.g P.x k

lemma Piece.pad_lip :
    letI : MetricSpace (M.productG ⧸ M.productΓ) :=
      M.productMetric.replaceTopology M.productCompatible
    LipschitzWith K P.padObs := by
  let : ∀ i, MetricSpace (M.G i ⧸ M.Γ i) :=
    fun i => (M.metric i).replaceTopology (M.compatible i)
  exact padded_lipschitz M.G M.Γ M.metric M.compatible P.index P.obs K P.lip

lemma Piece.pad_range (z : M.productG ⧸ M.productΓ) :
    P.padObs z ∈ Set.Icc (0:ℝ) 1 := P.range _

lemma Piece.pad_bound (z : M.productG ⧸ M.productΓ) : |P.padObs z| ≤ 1 :=
  abs_le.mpr ⟨(by linarith [(P.pad_range z).1]),(P.pad_range z).2⟩

end SourceChartedMenu

 

 

 

noncomputable section
open scoped BigOperators
namespace SourceBlocks
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.RationalPivotPlan
open SourcePivotPaths
attribute [local instance] Classical.propDecidable
variable {a : ℕ}

 
def Tail (i : Fin a) := {T : Finset (Fin a) // T.Nonempty ∧ ∀ j ∈ T, j < i}
instance blocks01TailFintype (i : Fin a) : Fintype (Tail i) := by unfold Tail; infer_instance

 
def Added (i : Fin a) (T A : Finset (Fin a)) : Prop :=
  ∃ (P : Finset (Fin a)) (j : Fin a), P.Nonempty ∧
    (∀ p ∈ P, ∀ t ∈ T, p < t) ∧ (∀ t ∈ T, t < j) ∧ j < i ∧ A = insert j P

lemma Added.lt {i : Fin a} {T A : Finset (Fin a)}
    (hT : T.Nonempty) (h : Added i T A) : ∀ x ∈ A, x < i := by
  obtain ⟨P,j,hP,hPT,hTj,hji,rfl⟩ := h
  obtain ⟨t,ht⟩ := hT
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hji
  · exact (hPT x hx t ht).trans ((hTj t ht).trans hji)

lemma Added.before {i : Fin a} {T A : Finset (Fin a)} (h : Added i T A) :
    ∃ x ∈ A, ∀ t ∈ T, x < t := by
  obtain ⟨P,j,hP,hPT,hTj,hji,rfl⟩ := h
  obtain ⟨x,hx⟩ := hP
  exact ⟨x,Finset.mem_insert_of_mem hx,hPT x hx⟩

lemma Added.disjoint {i : Fin a} {T A : Finset (Fin a)} (h : Added i T A) :
    Disjoint A T := by
  obtain ⟨P,j,hP,hPT,hTj,hji,rfl⟩ := h
  apply Finset.disjoint_left.mpr
  intro x hx ht
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact lt_irrefl _ (hTj _ ht)
  · exact lt_irrefl x (hPT x hx x ht)

def tailEnum (i : Fin a) : Fin (Fintype.card (Tail i)) ≃ Tail i := (Fintype.equivFin _).symm

def PairIndex (i : Fin a) :=
  {z : Fin (Fintype.card (Tail i)) × Finset (Fin a) // Added i (tailEnum i z.1).val z.2}
instance blocks01PairIndexFintype (i : Fin a) : Fintype (PairIndex i) := by unfold PairIndex; infer_instance

def pairEnum (i : Fin a) : Fin (Fintype.card (PairIndex i)) ≃ PairIndex i := (Fintype.equivFin _).symm

 
def pivot (i : Fin a) : Pivot a where
  index := i
  targets := Fintype.card (Tail i)
  tail t := (tailEnum i t).val
  pairs := Fintype.card (PairIndex i)
  owner e := (pairEnum i e).val.1
  added e := (pairEnum i e).val.2
  tail_lt t := (tailEnum i t).property.2
  added_lt e := (pairEnum i e).property.lt (tailEnum i (pairEnum i e).val.1).property.1
  before e := (pairEnum i e).property.before

@[simp] lemma pivot_index (i : Fin a) : (pivot i).index = i := rfl

lemma pivot_disjoint (i : Fin a) (e : Fin (pivot i).pairs) :
    Disjoint ((pivot i).added e) ((pivot i).tail ((pivot i).owner e)) :=
  (pairEnum i e).property.disjoint

 
def pivots (a : ℕ) : List (Pivot a) := List.ofFn pivot

lemma pivots_ordered : (pivots a).Pairwise (fun D E => D.index < E.index) :=
  List.pairwise_ofFn.mpr fun _ _ h => h

lemma mem_pivots (i : Fin a) : pivot i ∈ pivots a := List.mem_ofFn.mpr ⟨i,rfl⟩

 

abbrev Block (a : ℕ) := Σ i : Fin a, Tail i

def Block.set (B : Block a) : Finset (Fin a) := insert B.1 B.2.val

def Block.target (B : Block a) : Fin (pivot B.1).targets := (tailEnum B.1).symm B.2

@[simp] lemma block_target_tail (B : Block a) : (pivot B.1).tail B.target = B.2.val := by
  exact congrArg Subtype.val ((tailEnum B.1).apply_symm_apply B.2)

lemma block_target_set (B : Block a) :
    block (pivot B.1).index (pivot B.1).tail B.target = B.set := by
  simp only [block, pivot_index, block_target_tail, Block.set]

 

lemma added_exists_iff (B : Block a) (A : Finset (Fin a)) :
    (∃ e : Fin (pivot B.1).pairs, (pivot B.1).owner e = B.target ∧ (pivot B.1).added e = A) ↔
      Added B.1 B.2.val A := by
  constructor
  · rintro ⟨e,he,ha⟩
    have hp := (pairEnum B.1 e).property
    change Added B.1 ((pivot B.1).tail ((pivot B.1).owner e)) ((pivot B.1).added e) at hp
    simpa only [he,ha,block_target_tail] using hp
  · intro h
    let z : PairIndex B.1 := ⟨(B.target,A),by
      change Added B.1 ((pivot B.1).tail B.target) A
      rwa [block_target_tail]⟩
    refine ⟨(pairEnum B.1).symm z,?_,?_⟩
    · exact congrArg (fun v : PairIndex B.1 => v.val.1) ((pairEnum B.1).apply_symm_apply z)
    · exact congrArg (fun v : PairIndex B.1 => v.val.2) ((pairEnum B.1).apply_symm_apply z)

end SourceBlocks

 

 

 

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction NNReal
namespace SourceChartedAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily SourcePivotPaths SourceRawPrefix
variable {a : ℕ}

 
structure Realizes (s r : ℕ) (C : CommonScales a) (D : Pivot a)
    (S : ℕ → ScalarModels D r) where
  scales : PivotScales C D
  model : ChartedModels s r D
  eq_model : ∀ N, S N = model.scalar C scales N

variable (s r : ℕ) (hs : 1 ≤ s) (C : CommonScales a)

 

theorem charted_step (D : Pivot a) (Ss : ℕ → ScalarModels D r)
    (R : Realizes s r C D Ss) (Fs B : Finset (Scale a))
    (hFs : ∀ b ∈ Fs, ∀ j, 0 < b j) (b : Scale a) (hb : b ∈ B)
    (hpos : ∀ j, 0 < b j) (q₀ : ℕ) (hq₀ : 0 < q₀)
    (hterm : terminalDenom D s r hs Fs b ∣ q₀)
    (hplan : pivotModulus s r hs D Fs B ∣ q₀) (τ : ℝ) (hτ : 0 < τ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ E : Set (Fin a → ℕ), Earlier D.index E →
      gain s r hs D Fs * (C.law N).real E ≤
        (C.law N).real {u | u ∈ E ∧ success D r s hs Fs (Ss N) (C.ht N) b u (u D.index) τ} + ε := by
  let F := R.model
  let P := R.scales
  have he := source_uniform_prefix_extension D s r hs Fs q₀ b F.G F.Γ F.dim F.coords
    F.second F.filtration F.weight F.level_iff F.weight_pos F.lattice_iff F.weight_mono
    F.level0 F.level1 F.step C.M P.J P.R P.H C.L C.ht F.g F.x F.obs C.w C.X
    C.hw C.hX C.hXt C.hWM C.hM C.hMs P.hJ P.hRJ C.hL C.hLs C.hWL C.hML C.hLexact
    (fun t j => C.hXL _) P.hH P.hRrad P.hdom P.hxdom C.hpowWM hq₀ C.hht P.hheight
    P.hdisj hterm hpos hFs P.hratio F.metric F.compatible F.K F.B F.lip F.bound
    B hb hplan τ hτ ε hε
  filter_upwards [he] with N hN
  rw [R.eq_model N]
  exact hN

 

theorem local_of_charts (Ss : ℕ → (D : Pivot a) → ScalarModels D r)
    (Ds : List (Pivot a)) (R : ∀ D ∈ Ds, Realizes s r C D (fun N => Ss N D))
    (B : Finset (Scale a)) (hB : ∀ b ∈ B, ∀ j, 0 < b j)
    (q₀ : ℕ) (hq₀ : 0 < q₀) (hq : planModulus s r hs Ds B ∣ q₀)
    (b : Scale a) (hb : b ∈ B) (τ : ℝ) (hτ : 0 < τ) :
    localEstimates s r hs τ C.law Ss C.ht Ds b := by
  induction Ds generalizing B b with
  | nil => trivial
  | cons D Ds ih =>
    refine ⟨?_, ?_⟩
    · exact charted_step s r hs C D (fun N => Ss N D) (R D (by simp))
        (multipliers (sourcePlan s r hs Ds)) B (source_multipliers_pos s r hs Ds)
        b hb (hB b hb) q₀ hq₀ ((planModulus_terminal s r hs D Ds B b hb).trans hq)
        ((planModulus_head s r hs D Ds B).trans hq) τ hτ
    · intro p hp
      exact ih (fun D hD => R D (List.mem_cons_of_mem _ hD))
        (nextScales s r hs D Ds B) (nextScales_pos s r hs D Ds B hB)
        ((planModulus_tail s r hs D Ds B).trans hq) (scaleRun D 0 p b)
        (mem_nextScales s r hs D Ds B b hb p hp)

 

theorem charted_alignment
    (Ds : List (Pivot a)) (horder : Ds.Pairwise (fun D E => D.index < E.index)) :
    0 < delta s r hs Ds ∧
    (∀ b ∈ multipliers (sourcePlan s r hs Ds), ∀ j, 0 < b j) ∧
    ∀ (C : CommonScales a) (Ss : ℕ → (D : Pivot a) → ScalarModels D r),
      (∀ D ∈ Ds, Realizes s r C D (fun N => Ss N D)) →
      ∀ τ : ℝ, 0 < τ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N in atTop, delta s r hs Ds ≤
        (C.law N).real {u | ∃ b ∈ multipliers (sourcePlan s r hs Ds),
          ∀ D ∈ Ds, comparison D r (Ss N D) (C.ht N) b u (u D.index) τ} + ε := by
  refine ⟨delta_pos s r hs Ds, source_multipliers_pos s r hs Ds, ?_⟩
  intro C Ss R τ hτ ε hε
  apply eventual_final_alignment s r hs τ C.law Ss C.ht Ds horder _ ε hε
  exact local_of_charts s r hs C Ss Ds R {1} (by simp) (planModulus s r hs Ds {1})
    (planModulus_pos s r hs Ds {1}) dvd_rfl 1 (by simp) τ hτ

end SourceChartedAlignment

 

 

 

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
