import OAI.Analysis.RotationWeights.ConditionalBounds

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
namespace CircleCoupling

section

section

section
lemma digit_below_threshold {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (ht : t ≤ l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : u ≤ 1-w) (hz : (d:ℝ)/(l:ℝ) ≤ z) (hzu : z<u) : d < l-t := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  by_contra h
  have hdl : ((l-t:ℕ):ℝ) ≤ d := by exact_mod_cast (Nat.le_of_not_gt h)
  rw [Nat.cast_sub ht] at hdl
  have hdz := (div_le_iff₀ hl').mp hz
  have hzu' := mul_lt_mul_of_pos_right hzu hl'
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  nlinarith [mul_pos hl' _hw]
lemma digit_above_threshold {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : w ≤ u) (hz : z ≤ ((d:ℝ)+1)/(l:ℝ)) (hzu : u≤z) : t ≤ d := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  by_contra h
  have hdt : (d:ℝ)+1 ≤ t := by exact_mod_cast (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge h))
  have hdz := (le_div_iff₀ hl').mp hz
  have hzu' := mul_le_mul_of_nonneg_right hzu hl'.le
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  nlinarith [mul_pos hl' _hw]
lemma top_forces_above {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (ht : t ≤ l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : u ≤ 1-w) (hz : (d:ℝ)/(l:ℝ) ≤ z) (hdt : l-t ≤ d) : u < z := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  have hdl : ((l-t:ℕ):ℝ) ≤ d := by exact_mod_cast hdt
  rw [Nat.cast_sub ht] at hdl
  have hdz := (div_le_iff₀ hl').mp hz
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  by_contra h
  have huz := mul_le_mul_of_nonneg_right (le_of_not_gt h) hl'.le
  nlinarith [mul_pos hl' _hw]
lemma bottom_forces_below {l t d : ℕ} {w u z : ℝ}
    (hl : 0<l) (_hw : 0<w) (htu : (t:ℝ) ≤ (l:ℝ)*w/2)
    (hu : w ≤ u) (hz : z ≤ ((d:ℝ)+1)/(l:ℝ)) (hdt : d<t) : z < u := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  have hdl : (d:ℝ)+1 ≤ t := by exact_mod_cast (Nat.add_one_le_iff.mpr hdt)
  have hdz := (le_div_iff₀ hl').mp hz
  have hun := mul_le_mul_of_nonneg_right hu hl'.le
  by_contra h
  have huz := mul_le_mul_of_nonneg_right (le_of_not_gt h) hl'.le
  nlinarith [mul_pos hl' _hw]
open CircleDigits
abbrev LabelledDigits (b : ℕ → ℕ) := ∀ n, Option (Fin 5) × (Fin (b n) × Fin (b n))
def selectedBelow (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) (d : Digits b) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => scaledTail b d i < u i)
def selectedAbove (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) (d : Digits b) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => u i ≤ scaledTail b d i)

lemma crossing_top_domination {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (top : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (ht : ∀ i ∈ I, t i ≤ b i) (hw : ∀ i ∈ I, 0<w i)
    (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, u i ≤ 1-w i)
    (hlocal : ∀ i ∈ I, ∀ d : Fin (b i), d.val < b i-t i →
      μ i ({z | z.2.1=d} ∩ {z | z.1=some top}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.1=d})
    (H : Set (LabelledDigits b)) (hH : MeasurableSet H)
    (hcard : ∀ ω ∈ H, m/40 ≤ ((selectedBelow b I u (fun i => (ω i).2.1)).card:ℝ))
    (hsupport : ∀ ω ∈ H, ∀ i ∈ I, (ω i).1=some top → b i-t i ≤ (ω i).2.2.val)
    (hnocross : ∀ ω ∈ H, ∀ i ∈ I, ¬(scaledTail b (fun i => (ω i).2.1) i < u i ∧
      u i ≤ scaledTail b (fun i => (ω i).2.2) i)) :
    Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) ((Measure.infinitePi μ).restrict H) ≤
      ENNReal.ofReal (Real.exp (-m*ρ/400)) •
        Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) (Measure.infinitePi μ) := by
  classical
  apply infinite_selected_failures μ I (fun _ z => z.2.1) (fun _ => by fun_prop)
    (endpoint b) (measurable_endpoint b) H hH
    (fun _ => {z | z.1=some top}ᶜ) (selectedBelow b I u)
    (fun _ => ENNReal.ofReal (1-ρ/10))
  · intro d i hi
    have hi' : scaledTail b d i < u i := (Finset.mem_filter.mp hi).2
    have hh := hlocal i i.property (d i) (digit_below_threshold
      (by have := hb i; omega) (ht i i.property) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb d i).1 hi')
    simpa only [Set.preimage,Set.mem_singleton_iff] using hh
  · intro ω hω
    rw [Finset.prod_const]
    exact failure_power_exponential ρ m _ hρ hρ1 (hcard ω hω)
  · intro ω hω i hi hlabel
    have hx : scaledTail b (fun i => (ω i).2.1) i < u i := (Finset.mem_filter.mp hi).2
    apply hnocross ω hω i i.property
    refine ⟨hx,le_of_lt ?_⟩
    exact top_forces_above (by have := hb i; omega) (ht i i.property) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb (fun i => (ω i).2.2) i).1
      (hsupport ω hω i i.property hlabel)

lemma crossing_bottom_domination {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (bottom : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hw : ∀ i ∈ I, 0<w i) (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, w i ≤ u i)
    (hlocal : ∀ i ∈ I, ∀ d : Fin (b i), t i ≤ d.val →
      μ i ({z | z.2.2=d} ∩ {z | z.1=some bottom}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.2=d})
    (H : Set (LabelledDigits b)) (hH : MeasurableSet H)
    (hcard : ∀ ω ∈ H, m/40 ≤ ((selectedAbove b I u (fun i => (ω i).2.2)).card:ℝ))
    (hsupport : ∀ ω ∈ H, ∀ i ∈ I, (ω i).1=some bottom → (ω i).2.1.val<t i)
    (hnocross : ∀ ω ∈ H, ∀ i ∈ I, ¬(scaledTail b (fun i => (ω i).2.1) i < u i ∧
      u i ≤ scaledTail b (fun i => (ω i).2.2) i)) :
    Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) ((Measure.infinitePi μ).restrict H) ≤
      ENNReal.ofReal (Real.exp (-m*ρ/400)) •
        Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) (Measure.infinitePi μ) := by
  classical
  apply infinite_selected_failures μ I (fun _ z => z.2.2) (fun _ => by fun_prop)
    (endpoint b) (measurable_endpoint b) H hH
    (fun _ => {z | z.1=some bottom}ᶜ) (selectedAbove b I u)
    (fun _ => ENNReal.ofReal (1-ρ/10))
  · intro d i hi
    have hi' : u i ≤ scaledTail b d i := (Finset.mem_filter.mp hi).2
    have hh := hlocal i i.property (d i) (digit_above_threshold
      (by have := hb i; omega) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb d i).2 hi')
    simpa only [Set.preimage,Set.mem_singleton_iff] using hh
  · intro ω hω
    rw [Finset.prod_const]
    exact failure_power_exponential ρ m _ hρ hρ1 (hcard ω hω)
  · intro ω hω i hi hlabel
    have hy : u i ≤ scaledTail b (fun i => (ω i).2.2) i := (Finset.mem_filter.mp hi).2
    apply hnocross ω hω i i.property
    refine ⟨?_,hy⟩
    exact bottom_forces_below (by have := hb i; omega) (hw i i.property)
      (hround i i.property) (hu i i.property) (digit_interval_weak hb (fun i => (ω i).2.1) i).2
      (hsupport ω hω i i.property hlabel)
end
open CircleDigits
lemma measurable_selectedBelow_card (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) :
    Measurable (fun d : Digits b => (selectedBelow b I u d).card) := by
  classical
  have he : (fun d : Digits b => (selectedBelow b I u d).card) =
      fun d => ∑ i : I, if scaledTail b d i < u i then 1 else 0 := by
    funext d
    simp only [selectedBelow,Finset.card_filter]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (measurable_scaledTail b i) measurable_const)
    measurable_const measurable_const

def noCross (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) : Set (LabelledDigits b) :=
  {ω | ∀ i ∈ I, ¬(scaledTail b (fun k => (ω k).2.1) i < u i ∧
    u i ≤ scaledTail b (fun k => (ω k).2.2) i)}
lemma measurableSet_noCross (b : ℕ → ℕ) (I : Finset ℕ) (u : ℕ → ℝ) :
    MeasurableSet (noCross b I u) := by
  simp only [noCross,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  exact ((measurableSet_lt ((measurable_scaledTail b i).comp (by fun_prop)) measurable_const).inter
    (measurableSet_le measurable_const ((measurable_scaledTail b i).comp (by fun_prop)))).compl

lemma selected_card_sum {b : ℕ → ℕ} (I : Finset ℕ) (u : ℕ → ℝ) (ω : LabelledDigits b)
    (horder : ∀ i ∈ I, scaledTail b (fun k => (ω k).2.1) i ≤ scaledTail b (fun k => (ω k).2.2) i)
    (hno : ω ∈ noCross b I u) :
    (selectedBelow b I u (fun k => (ω k).2.1)).card +
      (selectedAbove b I u (fun k => (ω k).2.2)).card = I.card := by
  classical
  have he : selectedAbove b I u (fun k => (ω k).2.2) =
      Finset.univ.filter (fun i : I => ¬scaledTail b (fun k => (ω k).2.1) i < u i) := by
    ext i
    simp only [selectedAbove,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]
    constructor
    · intro hi
      by_contra hh
      exact hno i i.property ⟨lt_of_not_ge hh,hi⟩
    · intro hi
      exact hi.trans (horder i i.property)
  rw [he]
  simpa only [selectedBelow,Finset.card_univ,Fintype.card_coe] using
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
      (p := fun i => scaledTail b (fun k => (ω k).2.1) i < u i)

lemma crossing_split {b : ℕ → ℕ} (I : Finset ℕ) (u : ℕ → ℝ) (m : ℝ)
    (hI : m/20 ≤ (I.card:ℝ)) (G : Set (LabelledDigits b)) (hG : MeasurableSet G)
    (horder : ∀ ω ∈ G, ∀ i ∈ I,
      scaledTail b (fun k => (ω k).2.1) i ≤ scaledTail b (fun k => (ω k).2.2) i) :
    ∃ H₁ H₂ : Set (LabelledDigits b), MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Disjoint H₁ H₂ ∧ H₁ ∪ H₂ = noCross b I u ∩ G ∧
      (∀ ω ∈ H₁, m/40 ≤ ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ)) ∧
      (∀ ω ∈ H₂, m/40 ≤ ((selectedAbove b I u (fun k => (ω k).2.2)).card:ℝ)) := by
  classical
  let A : Set (LabelledDigits b) := {ω | (I.card:ℝ)/2 ≤
    ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_selectedBelow_card b I u).comp (show Measurable (fun ω : LabelledDigits b => fun k => (ω k).2.1) from by fun_prop)))
  let N := noCross b I u ∩ G
  refine ⟨N ∩ A,N \ A,((measurableSet_noCross b I u).inter hG).inter hA,
    ((measurableSet_noCross b I u).inter hG).diff hA,disjoint_left.mpr (by
      intro ω h₁ h₂; exact h₂.2 h₁.2),?_,?_,?_⟩
  · exact Set.inter_union_sdiff N A
  · intro ω hω
    have ha : (I.card:ℝ)/2 ≤ ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) := hω.2
    linarith
  · intro ω hω
    have ha : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) < (I.card:ℝ)/2 :=
      lt_of_not_ge hω.2
    have hs := selected_card_sum I u ω (horder ω hω.1.2) hω.1.1
    have hs' : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) +
      ((selectedAbove b I u (fun k => (ω k).2.2)).card:ℝ) = I.card := by exact_mod_cast hs
    linarith
end
open CircleDigits

lemma conditional_crossing_estimates {b : ℕ → ℕ} (hb : ∀ i, 2 ≤ b i)
    (μ : ∀ i, Measure (Option (Fin 5) × (Fin (b i) × Fin (b i))))
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ℕ) (t : ℕ → ℕ) (u w : ℕ → ℝ)
    (top bottom : Fin 5) (ρ m : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hI : m/20 ≤ (I.card:ℝ)) (ht : ∀ i ∈ I, t i ≤ b i) (hw : ∀ i ∈ I, 0<w i)
    (hround : ∀ i ∈ I, (t i:ℝ) ≤ (b i:ℝ)*w i/2)
    (hu : ∀ i ∈ I, w i ≤ u i ∧ u i ≤ 1-w i)
    (htop : ∀ i ∈ I, ∀ d : Fin (b i), d.val < b i-t i →
      μ i ({z | z.2.1=d} ∩ {z | z.1=some top}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.1=d})
    (hbottom : ∀ i ∈ I, ∀ d : Fin (b i), t i ≤ d.val →
      μ i ({z | z.2.2=d} ∩ {z | z.1=some bottom}ᶜ) ≤ ENNReal.ofReal (1-ρ/10)*μ i {z | z.2.2=d})
    (G : Set (LabelledDigits b)) (hG : MeasurableSet G) (hae : ∀ᵐ ω ∂Measure.infinitePi μ, ω ∈ G)
    (horder : ∀ ω ∈ G, ∀ i ∈ I,
      scaledTail b (fun k => (ω k).2.1) i ≤ scaledTail b (fun k => (ω k).2.2) i)
    (hst : ∀ ω ∈ G, ∀ i ∈ I, (ω i).1=some top → b i-t i ≤ (ω i).2.2.val)
    (hsb : ∀ ω ∈ G, ∀ i ∈ I, (ω i).1=some bottom → (ω i).2.1.val<t i) :
    ∃ H₁ H₂ : Set (LabelledDigits b), MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Disjoint H₁ H₂ ∧ H₁ ∪ H₂ = noCross b I u ∧
      H₁ = noCross b I u ∩ {ω | (I.card:ℝ)/2 ≤ ((selectedBelow b I u (fun i => (ω i).2.1)).card:ℝ)} ∧
      Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) ((Measure.infinitePi μ).restrict H₁) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (fun ω => endpoint b (fun i => (ω i).2.1)) (Measure.infinitePi μ) ∧
      Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) ((Measure.infinitePi μ).restrict H₂) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (fun ω => endpoint b (fun i => (ω i).2.2)) (Measure.infinitePi μ) := by
  classical
  let A : Set (LabelledDigits b) := {ω | (I.card:ℝ)/2 ≤
    ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ)}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      ((measurable_selectedBelow_card b I u).comp (show Measurable (fun ω : LabelledDigits b => fun k => (ω k).2.1) from by fun_prop)))
  let N := noCross b I u
  have hN := measurableSet_noCross b I u
  let H₁ := N ∩ A
  let H₂ := N \ A
  have h₁ : MeasurableSet H₁ := hN.inter hA
  have h₂ : MeasurableSet H₂ := hN.diff hA
  have he (H : Set (LabelledDigits b)) :
      (Measure.infinitePi μ).restrict H = (Measure.infinitePi μ).restrict (H ∩ G) := by
    apply Measure.restrict_congr_set
    filter_upwards [hae] with ω hω
    change (ω ∈ H) = (ω ∈ H ∩ G)
    apply propext
    exact ⟨fun h => ⟨h,hω⟩,fun h => h.1⟩
  refine ⟨H₁,H₂,h₁,h₂,disjoint_left.mpr (by intro ω h₁ h₂; exact h₂.2 h₁.2),
    Set.inter_union_sdiff N A,rfl,?_,?_⟩
  · rw [he]
    apply crossing_top_domination hb μ I t u w top ρ m hρ hρ1 ht hw hround
      (fun i hi => (hu i hi).2) htop (H₁ ∩ G) (h₁.inter hG)
    · intro ω hω
      have ha : (I.card:ℝ)/2 ≤ ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) := hω.1.2
      linarith
    · intro ω hω i hi
      exact hst ω hω.2 i hi
    · intro ω hω
      exact hω.1.1
  · rw [he]
    apply crossing_bottom_domination hb μ I t u w bottom ρ m hρ hρ1 hw hround
      (fun i hi => (hu i hi).1) hbottom (H₂ ∩ G) (h₂.inter hG)
    · intro ω hω
      have ha : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) < (I.card:ℝ)/2 :=
        lt_of_not_ge hω.1.2
      have hs := selected_card_sum I u ω (horder ω hω.2) hω.1.1
      have hs' : ((selectedBelow b I u (fun k => (ω k).2.1)).card:ℝ) +
        ((selectedAbove b I u (fun k => (ω k).2.2)).card:ℝ) = I.card := by exact_mod_cast hs
      linarith
    · intro ω hω i hi
      exact hsb ω hω.2 i hi
    · intro ω hω
      exact hω.1.1
end
namespace CoordinateParameters
variable (P : CoordinateParameters)
def width (e : Bool) : ℝ := if e then P.b else P.a
def prob (e : Bool) : ℝ := if e then P.σ else P.ρ
def topLabel (e : Bool) : Fin 5 := if e then 2 else 0
def bottomLabel (e : Bool) : Fin 5 := if e then 3 else 1
lemma width_pos (e : Bool) : 0<P.width e := by cases e <;> first | exact P.a_pos | exact P.b_pos
lemma width_round (e : Bool) : 0 < roundedWidth P.l (P.width e) ∧ roundedWidth P.l (P.width e) < P.l ∧
    (P.l:ℝ)*P.width e/3 ≤ roundedWidth P.l (P.width e) ∧
    (roundedWidth P.l (P.width e):ℝ) ≤ (P.l:ℝ)*P.width e/2 := by
  cases e <;> first | exact P.width_a | exact P.width_b
lemma prob_nonneg (e : Bool) : 0≤P.prob e := by cases e <;> first | exact P.ρ_nonneg | exact P.σ_nonneg
lemma prob_le_one (e : Bool) : P.prob e≤1 := by cases e <;> first | exact P.ρ_le_one | exact P.σ_le_one
lemma top_failure (tagged e : Bool) (d : Fin P.l)
    (hd : d.val < P.l-roundedWidth P.l (P.width e)) :
    P.law tagged ({z | z.2.1=d} ∩ {z | z.1=some (topLabel e)}ᶜ) ≤
      ENNReal.ofReal (1-P.prob e/10)*P.law tagged {z | z.2.1=d} := by
  cases e
  · exact P.top_a_failure tagged d hd
  · exact P.top_b_failure tagged d hd
lemma bottom_failure (tagged e : Bool) (d : Fin P.l)
    (hd : roundedWidth P.l (P.width e) ≤ d.val) :
    P.law tagged ({z | z.2.2=d} ∩ {z | z.1=some (bottomLabel e)}ᶜ) ≤
      ENNReal.ofReal (1-P.prob e/10)*P.law tagged {z | z.2.2=d} := by
  cases e
  · exact P.bottom_a_failure tagged d hd
  · exact P.bottom_b_failure tagged d hd
lemma top_support (e : Bool) (z : P.Sample)
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (hlabel : z.1=some (topLabel e)) : P.l-roundedWidth P.l (P.width e) ≤ z.2.2.val := by
  cases e <;> simp only [topLabel,Bool.false_eq_true,↓reduceIte] at hlabel
  · have h := hz
    simp [supportCondition,hlabel] at h
    change P.l - roundedWidth P.l P.a ≤ _
    omega
  · have h := hz
    simp [supportCondition,hlabel] at h
    change P.l - roundedWidth P.l P.b ≤ _
    omega
lemma bottom_support (e : Bool) (z : P.Sample)
    (hz : supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) z)
    (hlabel : z.1=some (bottomLabel e)) : z.2.1.val < roundedWidth P.l (P.width e) := by
  cases e <;> simp only [bottomLabel,Bool.false_eq_true,↓reduceIte] at hlabel
  · have h := hz
    simp [supportCondition,hlabel] at h
    exact h.1
  · have h := hz
    simp [supportCondition,hlabel] at h
    exact h.1
end CoordinateParameters
namespace DigitSystem
open CircleDigits CoordinateParameters
variable (S : DigitSystem)
def crossingWidth (e : Bool) : ℕ → ℝ | 0 => 1 | n+1 => (S.coord n).width e
def crossingDigit (e : Bool) : ℕ → ℕ | 0 => 0 | n+1 => roundedWidth (S.coord n).l ((S.coord n).width e)
def supported : Set S.Samples := {ω | (∀ i, (ω i).2.1 ≤ (ω i).2.2) ∧ ∀ n,
  supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a)
    (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) (ω (n+1))}
lemma measurableSet_supported : MeasurableSet S.supported := by
  simp only [supported,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter (fun n => ((Set.to_countable {z : S.Sample n | z.2.1 ≤ z.2.2}).measurableSet).preimage (measurable_pi_apply n))
  · exact MeasurableSet.iInter (fun n => ((Set.to_countable {z : S.Sample (n+1) | supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a) (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) z}).measurableSet).preimage (measurable_pi_apply (n+1)))
lemma ae_supported (tagged : ℕ → Bool) : ∀ᵐ ω ∂S.probability tagged, ω ∈ S.supported := by
  have hs : ∀ᵐ ω ∂S.probability tagged, ∀ n,
      supportCondition (S.coord n).l (roundedWidth (S.coord n).l (S.coord n).a)
        (roundedWidth (S.coord n).l (S.coord n).b) (roundedTag (S.coord n).l (S.coord n).m) (ω (n+1)) := by
    rw [ae_all_iff]
    intro n
    exact (measurePreserving_eval_infinitePi (S.law tagged) (n+1)).quasiMeasurePreserving.ae
      ((S.coord n).law_support (tagged n))
  filter_upwards [S.ae_digit_order tagged,hs] with ω hω hs
  exact ⟨hω,hs⟩
end DigitSystem
end CircleCoupling
namespace CircleCoupling.DigitSystem
open CircleDigits CoordinateParameters
variable (S : DigitSystem)

lemma actual_crossing_estimates (tagged : ℕ → Bool) (e : Bool) (I : Finset ℕ)
    (h0 : 0 ∉ I) (u : ℕ → ℝ) (m ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hI : m/20 ≤ (I.card:ℝ))
    (hcommon : ∀ n, n+1 ∈ I → (S.coord n).prob e=ρ)
    (hu : ∀ i ∈ I, S.crossingWidth e i ≤ u i ∧ u i ≤ 1-S.crossingWidth e i) :
    ∃ H₁ H₂ : Set S.Samples, MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Disjoint H₁ H₂ ∧ H₁ ∪ H₂ = noCross S.radix I u ∧
      H₁ = noCross S.radix I u ∩ {ω | (I.card:ℝ)/2 ≤
        ((selectedBelow S.radix I u (fun i => (ω i).2.1)).card:ℝ)} ∧
      Measure.map (S.endpoint (fun _ => false)) ((S.probability tagged).restrict H₁) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (S.endpoint (fun _ => false)) (S.probability tagged) ∧
      Measure.map (S.endpoint (fun _ => true)) ((S.probability tagged).restrict H₂) ≤
        ENNReal.ofReal (Real.exp (-m*ρ/400)) •
          Measure.map (S.endpoint (fun _ => true)) (S.probability tagged) := by
  apply conditional_crossing_estimates S.radix_ge_two (S.law tagged) I
    (S.crossingDigit e) u (S.crossingWidth e) (topLabel e) (bottomLabel e) ρ m hρ hρ1 hI
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_round e |>.2.1.le
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_pos e
  · intro i hi
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).width_round e |>.2.2.2
  · exact hu
  · intro i hi d hd
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n =>
      have hh := (S.coord n).top_failure (tagged n) e d hd
      rw [hcommon n hi] at hh
      exact hh
  · intro i hi d hd
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n =>
      have hh := (S.coord n).bottom_failure (tagged n) e d hd
      rw [hcommon n hi] at hh
      exact hh
  · exact S.measurableSet_supported
  · exact S.ae_supported tagged
  · intro ω hω i _
    exact scaledTail_mono S.radix_ge_two hω.1 i
  · intro ω hω i hi hlabel
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).top_support e _ (hω.2 n) hlabel
  · intro ω hω i hi hlabel
    cases i with
    | zero => exact False.elim (h0 hi)
    | succ n => exact (S.coord n).bottom_support e _ (hω.2 n) hlabel
end CircleCoupling.DigitSystem

end

end OAI
