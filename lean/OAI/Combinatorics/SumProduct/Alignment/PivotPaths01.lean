import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.IntegerArrays14
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open scoped BigOperators BoundedContinuousFunction Topology NNReal ENNReal
end

 

 

 

noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace SourceRawPrefix
variable {n : ℕ}

 
def Earlier (i : Fin n) (E : Set (Fin n → ℕ)) : Prop :=
  ∀ u v, (∀ j, j < i → u j = v j) → (u ∈ E ↔ v ∈ E)

def Through (i : Fin n) (E : Set (Fin n → ℕ)) : Prop :=
  ∀ u v, (∀ j, j ≤ i → u j = v j) → (u ∈ E ↔ v ∈ E)

lemma Earlier.update_iff {i : Fin n} {E : Set (Fin n → ℕ)} (hE : Earlier i E)
    (u : Fin n → ℕ) (x : ℕ) : Function.update u i x ∈ E ↔ u ∈ E := by
  apply hE
  intro j hj
  exact Function.update_of_ne (ne_of_lt hj) _ _

lemma Through.earlier {i j : Fin n} {E : Set (Fin n → ℕ)} (hE : Through i E)
    (hij : i < j) : Earlier j E := by
  intro u v huv
  apply hE
  intro k hk
  exact huv k (hk.trans_lt hij)

lemma earlier_univ (i : Fin n) : Earlier i Set.univ := by
  intro u v h
  simp

lemma through_inter {i : Fin n} {E F : Set (Fin n → ℕ)}
    (hE : Through i E) (hF : Through i F) : Through i (E ∩ F) := by
  intro u v h
  exact and_congr (hE u v h) (hF u v h)

 

theorem resample_preserves (ν : Fin n → Measure ℕ) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) :
    MeasurePreserving (fun z : (Fin n → ℕ) × ℕ => Function.update z.1 i z.2)
      ((Measure.pi ν).prod (ν i)) (Measure.pi ν) := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro u
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have he : (fun z : (Fin n → ℕ) × ℕ => Function.update z.1 i z.2) ⁻¹' {u} =
      (Set.univ.pi (Function.update (fun j => {u j}) i Set.univ)) ×ˢ {u i} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
      Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hz
      constructor
      · intro j
        by_cases hji : j = i
        · subst j; simp
        · simpa [Function.update_of_ne hji] using congrFun hz j
      · simpa using congrFun hz i
    · rintro ⟨hy,hx⟩
      ext j
      by_cases hji : j = i
      · subst j; simpa using hx
      · simpa [Function.update_of_ne hji] using hy j
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_singleton]
  have hf : (fun j => ν j (Function.update (fun k : Fin n => ({u k} : Set ℕ)) i (Set.univ : Set ℕ) j)) =
      Function.update (fun j => ν j {u j}) i 1 := by
    funext j
    by_cases hji : j = i
    · subst j; simp
    · simp [hji]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [one_mul]
  simpa only [Finset.sdiff_singleton_eq_erase] using Finset.prod_erase_mul Finset.univ (fun j => ν j {u j}) (Finset.mem_univ i)

open RawHarmonicProbability ProductExposureLaw

lemma raw_resample (X : Fin n → ℕ) (W : ℕ) (hW : 0 < W)
    (hX : ∀ j, 4*W ≤ X j) (i : Fin n) :
    MeasurePreserving (fun z : (Fin n → ℕ) × ℕ => Function.update z.1 i z.2)
      (jointLaw X (X i) W hW hX (hX i)) (outsideLaw X W hW hX) :=
  resample_preserves (fun j => (law (X j) W hW (hX j) : Measure ℕ)) i

 
lemma raw_resample_real (X : Fin n → ℕ) (W : ℕ) (hW : 0 < W)
    (hX : ∀ j, 4*W ≤ X j) (i : Fin n) (E : Set (Fin n → ℕ)) :
    (jointLaw X (X i) W hW hX (hX i)).real
      {z | Function.update z.1 i z.2 ∈ E} = (outsideLaw X W hW hX).real E := by
  apply congrArg ENNReal.toReal
  exact (raw_resample X W hW hX i).measure_preimage (Set.to_countable E).measurableSet.nullMeasurableSet

end SourceRawPrefix

 

 

 

noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
namespace SourcePivotPaths
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open SourceRawPrefix
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a) (r : ℕ)

 

abbrev ScalarModels := Fin D.targets → ℚ → Fin r → ℤ → ℝ

 
def comparison (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a)
    (u : Fin a → ℕ) (x : ℕ) (τ : ℝ) : Prop :=
  ∀ (t : Fin D.targets) (U : OwnSubset D t) (c : Fin r),
    let av := blockProduct b (block D.index D.tail t)
    ∃ Δ : ℤ,
      (Δ : ℚ) = ∑ e ∈ U.val,
        ((height ht (D.added e) : ℚ)*blockProduct b (D.added e)/
          ((height ht (block D.index D.tail (D.owner e)) : ℚ)*
            blockProduct b (block D.index D.tail (D.owner e))))*
          (height (fun j => (u j : ℤ)) (D.added e) : ℚ) ∧
      (2*τ < S t av c (height (fun j => (u j : ℤ)) (D.tail t)*(x : ℤ)) →
        τ < S t av c (height (fun j => (u j : ℤ)) (D.tail t)*(x : ℤ)+Δ))

 
def outcome (Fs : Finset (Scale a)) (S : ScalarModels D r) (ht : Fin a → ℤ)
    (b : Scale a) (p : Path D) (u : Fin a → ℕ) (x : ℕ) (τ : ℝ) : Prop :=
  ∀ d ∈ Fs, comparison D r S ht (scaleRun D 0 p b*d) u x τ

def success (s : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a))
    (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a)
    (u : Fin a → ℕ) (x : ℕ) (τ : ℝ) : Prop :=
  ∃ p ∈ pivotOptions s r hs D Fs, outcome D r Fs S ht b p u x τ

lemma comparison_congr (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a)
    (u v : Fin a → ℕ) (huv : ∀ j, j < D.index → u j = v j) (x : ℕ) (τ : ℝ) :
    comparison D r S ht b u x τ ↔ comparison D r S ht b v x τ := by
  have ha (e) : height (fun j => (u j : ℤ)) (D.added e) =
      height (fun j => (v j : ℤ)) (D.added e) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (fun m : ℕ => (m : ℤ)) (huv j (D.added_lt e j hj))
  have ht' (t) : height (fun j => (u j : ℤ)) (D.tail t) =
      height (fun j => (v j : ℤ)) (D.tail t) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact congrArg (fun m : ℕ => (m : ℤ)) (huv j (D.tail_lt t j hj))
  simp only [comparison, ha, ht']

lemma comparison_through (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a) (τ : ℝ) :
    Through D.index {u | comparison D r S ht b u (u D.index) τ} := by
  intro u v huv
  change comparison D r S ht b u (u D.index) τ ↔ comparison D r S ht b v (v D.index) τ
  rw [huv D.index le_rfl]
  exact comparison_congr D r S ht b u v (fun j hj => huv j hj.le) _ τ

lemma outcome_through (Fs : Finset (Scale a)) (S : ScalarModels D r)
    (ht : Fin a → ℤ) (b : Scale a) (p : Path D) (τ : ℝ) :
    Through D.index {u | outcome D r Fs S ht b p u (u D.index) τ} := by
  intro u v huv
  simp only [Set.mem_ofPred_eq, outcome]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro hd
  exact comparison_through D r S ht _ τ u v huv

lemma success_through (s : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a))
    (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a) (τ : ℝ) :
    Through D.index {u | success D r s hs Fs S ht b u (u D.index) τ} := by
  intro u v huv
  simp only [Set.mem_ofPred_eq, success]
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  exact outcome_through D r Fs S ht b p τ u v huv

lemma success_update_iff (s : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a))
    (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a)
    (u : Fin a → ℕ) (x : ℕ) (τ : ℝ) :
    success D r s hs Fs S ht b (Function.update u D.index x) x τ ↔
      success D r s hs Fs S ht b u x τ := by
  simp only [success, outcome]
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  apply forall_congr'
  intro d
  apply forall_congr'
  intro hd
  apply comparison_congr
  intro j hj
  exact Function.update_of_ne (ne_of_lt hj) _ _

section OriginalModels
variable (s : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (b : Scale a)
variable (G : Fin D.targets → ℚ → Fin r → Type)
  [∀ t v c, Group (G t v c)] [∀ t v c, TopologicalSpace (G t v c)]
  (Γ : ∀ t v c, Subgroup (G t v c))
  (M H : ℕ → ℕ) (ht : ℕ → Fin a → ℤ)
  (g x : ∀ t, ℕ → ∀ v c, ℤ → ℤ → G t v c)
  (F : ∀ t, ℕ → ∀ v c, ℤ → ℤ → ((G t v c) ⧸ Γ t v c) →ᵇ ℝ)

def scalarModels (N : ℕ) : ScalarModels D r :=
  fun t v c k => SourceIntegerArrays.pieceModel (Γ t v c) (M N) (H N)
    (g t N v c) (x t N v c) (fun b r => F t N v c b r) k

 
lemma original_success (N : ℕ) (u : Fin a → ℕ) (xp : ℕ) (τ : ℝ) :
    pivotProperty D s r hs Fs b G Γ M H
      (fun t N _ => g t N) (fun t N _ => x t N) (fun t N _ => F t N) ht N u xp τ ↔
    success D r s hs Fs (scalarModels D r G Γ M H g x F N) (ht N) b u xp τ := by
  simp only [pivotProperty, success]
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  constructor
  · intro h d hd t U c
    exact h (⟨d,hd⟩,⟨t,U⟩,c)
  · intro h i
    exact h i.1.val i.1.property i.2.1.1 i.2.1.2 i.2.2
end OriginalModels

open MeasureTheory ProductExposureLaw RawHarmonicProbability

 

theorem success_mass_resample (s : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a))
    (S : ScalarModels D r) (ht : Fin a → ℤ) (b : Scale a) (τ : ℝ)
    (X : Fin a → ℕ) (W : ℕ) (hW : 0 < W) (hX : ∀ j, 4*W ≤ X j)
    (E : Set (Fin a → ℕ)) (hE : Earlier D.index E) :
    (jointLaw X (X D.index) W hW hX (hX D.index)).real
      {z | z.1 ∈ E ∧ success D r s hs Fs S ht b z.1 z.2 τ} =
    (outsideLaw X W hW hX).real
      {u | u ∈ E ∧ success D r s hs Fs S ht b u (u D.index) τ} := by
  rw [← raw_resample_real X W hW hX D.index]
  congr 1
  ext z
  simp only [Set.mem_ofPred_eq, Function.update_self, hE.update_iff,
    success_update_iff]

end SourcePivotPaths

 

 

end
end
end

end OAI
