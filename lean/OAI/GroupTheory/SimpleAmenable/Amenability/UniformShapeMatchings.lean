import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.FinitePartitionArrows

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformShapeMatchings
open Classical Set

noncomputable def partitionShapeSetoid (a m : ℕ) : Setoid (TrackPolygonPartition a m) where
  r P Q := ∃g : polygonFullGroup a m,PartitionArrow P Q g
  iseqv := ⟨fun P => ⟨1,PartitionArrow.one P⟩,
    fun ⟨g,hg⟩ => ⟨g⁻¹,hg.inv⟩,
    fun ⟨g,hg⟩ ⟨h,hh⟩ => ⟨h*g,hh.mul hg⟩⟩

noncomputable def partitionBaseline {a m : ℕ} (P : TrackPolygonPartition a m) : TrackPolygonPartition a m :=
  (Quotient.mk (partitionShapeSetoid a m) P).out

theorem partitionBaseline_related {a m : ℕ} (P : TrackPolygonPartition a m) :
    ∃g : polygonFullGroup a m,PartitionArrow (partitionBaseline P) P g :=
  Quotient.exact (Quotient.out_eq (Quotient.mk (partitionShapeSetoid a m) P))

theorem partitionBaseline_eq {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) : partitionBaseline P=partitionBaseline Q :=
  congrArg Quotient.out (Quotient.sound (s:=partitionShapeSetoid a m) ⟨g,hg⟩)

noncomputable def matchingSupport {a m : ℕ} (P : TrackPolygonPartition a m) : Finset (polygonFullGroup a m) :=
  (show Set.Finite {g : polygonFullGroup a m | PartitionArrow (partitionBaseline P) P g} from
    @Set.toFinite _ _ (PartitionArrow.arrows_finite (partitionBaseline P) P)).toFinset

@[simp] theorem mem_matchingSupport {a m : ℕ} (P : TrackPolygonPartition a m) (g : polygonFullGroup a m) :
    g∈matchingSupport P ↔ PartitionArrow (partitionBaseline P) P g := Set.Finite.mem_toFinset _

theorem matchingSupport_nonempty {a m : ℕ} (P : TrackPolygonPartition a m) : (matchingSupport P).Nonempty := by
  obtain ⟨g,hg⟩ := partitionBaseline_related P
  exact ⟨g,(mem_matchingSupport P g).mpr hg⟩

theorem matchingSupport_transport {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) : matchingSupport Q=(matchingSupport P).image (fun x => g*x) := by
  have hb := partitionBaseline_eq hg
  ext h
  simp only [Finset.mem_image,mem_matchingSupport]
  constructor
  · intro hh
    refine ⟨g⁻¹*h,?_,by group⟩
    have h := hg.inv.mul hh
    rwa [←hb] at h
  · rintro ⟨x,hx,rfl⟩
    have h := hg.mul hx
    rwa [hb] at h

noncomputable def matchingAverage {a m : ℕ} (P : TrackPolygonPartition a m)
    (f : polygonFullGroup a m → ℝ) : ℝ :=
  (∑x∈matchingSupport P,f x)/(matchingSupport P).card

theorem matchingAverage_range {a m : ℕ} (P : TrackPolygonPartition a m)
    {f : polygonFullGroup a m → ℝ} (hf : ∀x,f x∈Icc (0:ℝ) 1) : matchingAverage P f∈Icc (0:ℝ) 1 := by
  have hc : (0:ℝ)<(matchingSupport P).card := by exact_mod_cast (matchingSupport_nonempty P).card_pos
  refine ⟨div_nonneg (Finset.sum_nonneg (fun x _ => (hf x).1)) hc.le,?_⟩
  apply (div_le_one hc).mpr
  calc
    (∑x∈matchingSupport P,f x) ≤ ∑_x∈matchingSupport P,(1:ℝ) := Finset.sum_le_sum (fun x _ => (hf x).2)
    _ = _ := by simp

theorem matchingAverage_transport {a m : ℕ} {P Q : TrackPolygonPartition a m} {g : polygonFullGroup a m}
    (hg : PartitionArrow P Q g) (f : polygonFullGroup a m → ℝ) :
    matchingAverage Q f=matchingAverage P (fun x => f (g*x)) := by
  unfold matchingAverage
  rw [matchingSupport_transport hg,Finset.card_image_of_injective _ (fun _ _ h => mul_left_cancel h),Finset.sum_image]
  intro _ _ _ _ equality
  exact mul_left_cancel equality

end UniformShapeMatchings

section FiniteSupportedLaws
open Classical MeasureTheory Set

theorem finset_indicator_measurable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (T : Finset X) (f : X → ℝ) : Measurable ((T : Set X).indicator f) := by
  apply measurable_zero.measurable_of_countable_ne
  apply T.finite_toSet.countable.mono
  intro x hx
  by_contra hn
  exact hx (by simp [hn])

theorem integrable_of_finite_support {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (f : X → ℝ) :
    Integrable f μ := by
  have hi : Integrable ((T : Set X).indicator f) μ := by
    have he : (T : Set X).indicator f=fun x => ∑z∈T,({z} : Set X).indicator (fun _ => f z) x := by
      funext x
      by_cases hx : x∈T
      · simp only [Set.indicator_of_mem hx]
        symm
        rw [Finset.sum_eq_single x]
        · simp
        · intro _ _ distinct
          simp [Set.indicator_of_notMem,Ne.symm distinct]
        · exact fun hn => (hn hx).elim
      · simp only [Set.indicator_of_notMem hx]
        symm
        apply Finset.sum_eq_zero
        intro z hz
        have hz' : x≠z := fun h => hx (h.symm ▸ hz)
        simp [hz']
    rw [he]
    apply integrable_finsetSum
    intro point _
    exact (integrable_const (f point)).indicator (measurableSet_singleton point)
  apply hi.congr
  filter_upwards [hT] with x hx
  simp [hx]

theorem integral_of_finite_support {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (f : X → ℝ) :
    (∫x,f x ∂μ)=∑x∈T,μ.real {x}*f x := by
  have he : f=ᵐ[μ] fun x => ∑z∈T,({z} : Set X).indicator (fun _ => f z) x := by
    filter_upwards [hT] with x hx
    symm
    rw [Finset.sum_eq_single x]
    · simp
    · intro _ _ distinct
      simp [Set.indicator_of_notMem,Ne.symm distinct]
    · exact fun hn => (hn hx).elim
  rw [integral_congr_ae he,integral_finsetSum T (fun z _ =>
    (integrable_const (f z)).indicator (measurableSet_singleton z))]
  apply Finset.sum_congr rfl
  intro point _
  rw [integral_indicator_const (f point) (measurableSet_singleton point)]
  rfl

theorem ObservableClose.finiteSupport {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {μ ν : Measure X} (T U : Finset X) (hT : ∀ᵐx ∂μ,x∈T) (hU : ∀ᵐx ∂ν,x∈U)
    {ε : ℝ} (h : ObservableClose μ ν ε) (f : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) :
    |(∫x,f x ∂μ)-(∫x,f x ∂ν)| ≤ ε := by
  let V := T∪U
  let f' := (V : Set X).indicator f
  have heμ : f'=ᵐ[μ] f := by
    filter_upwards [hT] with x hx
    exact Set.indicator_of_mem (Finset.mem_union_left U hx) f
  have heν : f'=ᵐ[ν] f := by
    filter_upwards [hU] with x hx
    exact Set.indicator_of_mem (Finset.mem_union_right T hx) f
  have hh := h f' (finset_indicator_measurable V f) (by
    intro x
    by_cases hx : x∈V
    · simpa only [f',Set.indicator_of_mem hx] using hf x
    · simp [f',hx])
  rwa [integral_congr_ae heμ,integral_congr_ae heν] at hh

theorem integral_difference_le_failure {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsFiniteMeasure μ] (T : Finset X) (hT : ∀ᵐx ∂μ,x∈T)
    (f g : X → ℝ) (hf : ∀x,f x∈Icc (0:ℝ) 1) (hg : ∀x,g x∈Icc (0:ℝ) 1)
    (E : Set X) (hE : MeasurableSet E) (he : ∀x,x∉E → f x=g x) :
    |(∫x,f x ∂μ)-(∫x,g x ∂μ)| ≤ μ.real E := by
  have hif := integrable_of_finite_support μ T hT f
  have hig := integrable_of_finite_support μ T hT g
  rw [←integral_sub hif hig]
  calc
    _ ≤ ∫x,|f x-g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫x,E.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono (hif.sub hig).abs ((integrable_const 1).indicator hE)
      intro x
      by_cases hx : x∈E
      · rw [Set.indicator_of_mem hx]
        change |f x-g x| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hf x).1,(hg x).2],by linarith [(hg x).1,(hf x).2]⟩
      · simp [Set.indicator_of_notMem hx,he x hx]
    _ = μ.real E := by simp [integral_indicator hE,Measure.real]

end FiniteSupportedLaws

end SimpleAmenable
end
end

end OAI
