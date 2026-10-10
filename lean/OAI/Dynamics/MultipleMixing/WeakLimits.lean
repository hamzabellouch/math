import OAI.Dynamics.MultipleMixing.OrbitCancellation
import OAI.Dynamics.MultipleMixing.Saturation

namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology

section InitialCorrelations
universe u
variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    (base : InitialLaws I X T) (hk : 3 ≤ Fintype.card I)
    {μ : Measure X} [IsProbabilityMeasure μ] (hμ : (base.law 0).map (zeroEquiv I X) = μ)
    (hT : MeasurePreserving T μ μ)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => μ (A ∩ (T^[n]) ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := μ) (fun m z => α ((T^[m]) z)) n / n)
      atTop (𝓝 0))
include hk hμ hT hmix hα hcenter hH in
lemma initial_correlation_zero (i : I) (f : I → X → ℂ)
    (hf : ∀ j, Measurable (f j)) (hb : ∀ j y, ‖f j y‖ ≤ 1)
    (hi : ∀ y, f i y = v (α y)) :
    (∫ y, ∏ j, f j (zeroEquiv I X (plane 0 0 j y)) ∂base.law 1) = 0 := by
  obtain ⟨M,he,hM⟩ := Object.Saturating.exists_saturated_extension (initialObject base)
  have hμM : M.localLaw.map M.x = μ := by
    rw [Object.localLaw,Measure.map_map M.measurable_x (zeroEquiv I M.Y).measurable]
    have he : M.x ∘ zeroEquiv I M.Y = zeroEquiv I X ∘ amap M.x 0 := rfl
    rw [he,←Measure.map_map (zeroEquiv I X).measurable (measurable_amap M.measurable_x 0),M.over_base,hμ]
  have h := Object.Rolled.saturated_correlation_zero M hM hk hμM hT hmix α hα v hcenter hH i
    (fun j => f j ∘ M.x ∘ zeroEquiv I M.Y)
    (fun j => (hf j).comp (M.measurable_x.comp (zeroEquiv I M.Y).measurable))
    (fun j y => hb j _) (fun y => hi _)
  rw [←M.over_base 1,integral_map (measurable_amap M.measurable_x 1).aemeasurable
    (show AEStronglyMeasurable (fun y : Arr I X 1 => ∏ j, f j (zeroEquiv I X (plane 0 0 j y)))
      ((M.law 1).map (amap M.x 1)) from
      (Finset.measurable_prod _ (fun j _ => (hf j).comp ((zeroEquiv I X).measurable.comp
        (measurable_plane _ _ _)))).aestronglyMeasurable)]
  exact h
end InitialCorrelations


universe u
variable {I : Type u} {X : Type u} [TopologicalSpace X]

def firstDuplicate (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) : Arr I X n → Arr I X (n+1) :=
  fun y v => (T^[d (v 0)]) (y (fun j => v j.succ))

lemma continuous_firstDuplicate (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) :
    Continuous (firstDuplicate T d n) :=
  continuous_pi fun _v => (T.continuous.iterate _).comp (continuous_apply _)

lemma continuous_array_amap {Y : Type u} [TopologicalSpace Y] {f : X → Y}
    (hf : Continuous f) (n : ℕ) : Continuous (amap (I := I) f n) :=
  continuous_pi fun _ => hf.comp (continuous_apply _)

lemma continuous_array_plane (n : ℕ) (a : Fin (n+1)) (i : I) :
    Continuous (plane (Y := X) n a i) := continuous_pi fun _ => continuous_apply _

lemma continuous_array_planes (n : ℕ) (J : Finset I) :
    Continuous (planes (Y := X) n J) := continuous_pi fun _ => continuous_array_plane _ _ _

omit [TopologicalSpace X] in
lemma amap_iterate (f : X → X) (m n : ℕ) :
    amap (I := I) (f^[m]) n = (amap f n)^[m] := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ,amap_comp,ih,Function.iterate_succ]

lemma plane_firstDuplicate_zero (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) (i : I) :
    plane n 0 i ∘ firstDuplicate T d n = amap (T^[d i]) n := by
  funext y v
  simp [plane,firstDuplicate,amap,Fin.insertNth_zero']

lemma plane_firstDuplicate_succ (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ)
    (a : Fin (n+1)) (i : I) :
    plane (n+1) a.succ i ∘ firstDuplicate T d (n+1) =
      firstDuplicate T d n ∘ plane n a i := by
  funext y v
  have hv : v = Fin.cons (v 0) (fun j => v j.succ) := by
    ext j
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  conv_lhs => simp only [Function.comp_apply,plane,firstDuplicate]
  rw [hv,Fin.insertNth_succ_cons]
  simp only [Fin.cons_zero,Fin.cons_succ]
  rfl

lemma planes_firstDuplicate_succ (T : X ≃ₜ X) (d : I → ℕ) (n : ℕ) (J : Finset I) :
    planes (n+1) J ∘ firstDuplicate T d (n+1) =
      (fun z j => firstDuplicate T d n (z j)) ∘ planes n J := by
  funext y j
  exact congrFun (plane_firstDuplicate_succ T d n (Fin.last n) j) y

section ContinuousPush
variable {A B C : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]

def continuousPush (f : A → B) (hf : Continuous f) (μ : ProbabilityMeasure A) : ProbabilityMeasure B :=
  let _ : AEMeasurable f (μ : Measure A) := hf.measurable.aemeasurable
  μ.map f
lemma continuous_continuousPush (f : A → B) (hf : Continuous f) :
    Continuous (continuousPush f hf) := ProbabilityMeasure.continuous_map hf
lemma continuousPush_comp (f : A → B) (hf : Continuous f) (g : B → C) (hg : Continuous g)
    (μ : ProbabilityMeasure A) :
    continuousPush g hg (continuousPush f hf μ) = continuousPush (g ∘ f) (hg.comp hf) μ := by
  apply Subtype.ext
  exact Measure.map_map hg.measurable hf.measurable
lemma continuousPush_id (μ : ProbabilityMeasure A) : continuousPush id continuous_id μ = μ := by
  apply Subtype.ext
  exact Measure.map_id

lemma continuousPush_pi {J : Type*} [Fintype J] [SecondCountableTopology A] [SecondCountableTopology B] (f : J → A → B)
    (hf : ∀ j, Continuous (f j)) (ν : J → ProbabilityMeasure A) :
    continuousPush (fun z : J → A => fun j => f j (z j))
      (continuous_pi fun j => (hf j).comp (continuous_apply j)) (ProbabilityMeasure.pi ν) =
      ProbabilityMeasure.pi (fun j => continuousPush (f j) (hf j) (ν j)) := by
  apply Subtype.ext
  exact Measure.pi_map_pi (fun j => (hf j).measurable.aemeasurable)
end ContinuousPush

variable [Fintype I] [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable (T : X ≃ₜ X) (d : ℕ → I → ℕ) (U : Ultrafilter ℕ) (μ : ProbabilityMeasure X)

def weakArrayLaw : (n : ℕ) → ProbabilityMeasure (Arr I X n)
  | 0 => continuousPush (fun x _ => x) (continuous_pi fun _ => continuous_id) μ
  | n+1 => (U.map (fun b => continuousPush (firstDuplicate T (d b) n)
      (continuous_firstDuplicate T (d b) n) (weakArrayLaw n))).lim

omit [MetrizableSpace X] in
lemma weakArrayLaw_tendsto (n : ℕ) :
    Tendsto (fun b => continuousPush (firstDuplicate T (d b) n)
      (continuous_firstDuplicate T (d b) n) (weakArrayLaw T d U μ n)) U
      (𝓝 (weakArrayLaw T d U μ (n+1))) :=
  (U.map _).le_nhds_lim

omit [Fintype I] [CompactSpace X] [T2Space X] [SecondCountableTopology X] [MetrizableSpace X]
  [MeasurableSpace X] [BorelSpace X] in
lemma firstDuplicate_amap (b : ℕ) (n : ℕ) :
    amap T (n+1) ∘ firstDuplicate T (d b) n = firstDuplicate T (d b) n ∘ amap T n := by
  funext y v
  exact Function.Commute.iterate_right (Function.Commute.refl (T : X → X)) _ _

lemma weakArrayLaw_invariant (hμ : MeasurePreserving T μ μ) (n : ℕ) :
    continuousPush (amap T n) (continuous_array_amap T.continuous n) (weakArrayLaw T d U μ n) =
      weakArrayLaw T d U μ n := by
  induction n with
  | zero =>
    apply Subtype.ext
    change (Measure.map (fun x _ => x) μ).map (amap T 0) = Measure.map (fun x _ => x) μ
    rw [Measure.map_map (measurable_amap T.measurable 0) (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)]
    change μ.toMeasure.map ((fun x _ => x) ∘ T) = _
    rw [←Measure.map_map (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id) T.measurable,hμ.map_eq]
  | succ n ih =>
    have h := (continuous_continuousPush (amap T (n+1)) (continuous_array_amap T.continuous _)).tendsto
      (weakArrayLaw T d U μ (n+1)) |>.comp (weakArrayLaw_tendsto T d U μ n)
    have he (b : ℕ) : continuousPush (amap T (n+1)) (continuous_array_amap T.continuous _)
        (continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
          (weakArrayLaw T d U μ n)) =
        continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
          (weakArrayLaw T d U μ n) := by
      simp only [continuousPush_comp, firstDuplicate_amap]
      rw [←continuousPush_comp (amap T n) (continuous_array_amap T.continuous n)
        (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n),ih]
    exact tendsto_nhds_unique h ((weakArrayLaw_tendsto T d U μ n).congr fun b => (he b).symm)

lemma weakArrayLaw_iterate_invariant (hμ : MeasurePreserving T μ μ) (n m : ℕ) :
    continuousPush (amap (T^[m]) n) (continuous_array_amap (T.continuous.iterate m) n)
      (weakArrayLaw T d U μ n) = weakArrayLaw T d U μ n := by
  apply Subtype.ext
  have h : MeasurePreserving (amap (I := I) T n) (weakArrayLaw T d U μ n : Measure (Arr I X n)) (weakArrayLaw T d U μ n : Measure (Arr I X n)) :=
    ⟨(continuous_array_amap T.continuous n).measurable,
      congrArg Subtype.val (weakArrayLaw_invariant T d U μ hμ n)⟩
  change (weakArrayLaw T d U μ n : Measure (Arr I X n)).map (amap (T^[m]) n) = _
  rw [amap_iterate]
  exact (h.iterate m).map_eq

lemma weakArrayLaw_consistent (hμ : MeasurePreserving T μ μ) (n : ℕ)
    (a : Fin (n+1)) (i : I) :
    continuousPush (plane n a i) (continuous_array_plane n a i) (weakArrayLaw T d U μ (n+1)) =
      weakArrayLaw T d U μ n := by
  induction n with
  | zero =>
    have h := (continuous_continuousPush (plane 0 a i) (continuous_array_plane 0 a i)).tendsto
      (weakArrayLaw T d U μ 1) |>.comp (weakArrayLaw_tendsto T d U μ 0)
    have he (b : ℕ) : continuousPush (plane 0 a i) (continuous_array_plane 0 a i)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d U μ 0)) = weakArrayLaw T d U μ 0 := by
      have ha : a = 0 := by apply Fin.ext; omega
      subst a
      simpa only [continuousPush_comp,plane_firstDuplicate_zero] using
        weakArrayLaw_iterate_invariant T d U μ hμ 0 (d b i)
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun b => (he b).symm)
  | succ n ih =>
    induction a using Fin.cases with
    | zero =>
      have h := (continuous_continuousPush (plane (n+1) 0 i) (continuous_array_plane _ _ _)).tendsto
        (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
      have he (b : ℕ) : continuousPush (plane (n+1) 0 i) (continuous_array_plane _ _ _)
          (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
            (weakArrayLaw T d U μ (n+1))) = weakArrayLaw T d U μ (n+1) := by
        simpa only [continuousPush_comp,plane_firstDuplicate_zero] using
          weakArrayLaw_iterate_invariant T d U μ hμ (n+1) (d b i)
      exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun b => (he b).symm)
    | succ a =>
      have h := (continuous_continuousPush (plane (n+1) a.succ i) (continuous_array_plane _ _ _)).tendsto
        (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
      have he (b : ℕ) : continuousPush (plane (n+1) a.succ i) (continuous_array_plane _ _ _)
          (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
            (weakArrayLaw T d U μ (n+1))) =
          continuousPush (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n)
            (weakArrayLaw T d U μ n) := by
        simp only [continuousPush_comp,plane_firstDuplicate_succ]
        rw [←continuousPush_comp (plane n a i) (continuous_array_plane n a i)
          (firstDuplicate T (d b) n) (continuous_firstDuplicate T (d b) n),ih a]
      exact tendsto_nhds_unique h ((weakArrayLaw_tendsto T d U μ n).congr fun b => (he b).symm)

lemma weakArrayLaw_proper
    (hproper : ∀ J : Finset I, J ≠ Finset.univ →
      Tendsto (fun b => continuousPush (planes 0 J) (continuous_array_planes 0 J)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d U μ 0))) U
        (𝓝 (ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d U μ 0))))
    (n : ℕ) (J : Finset I) (hJ : J ≠ Finset.univ) :
    continuousPush (planes n J) (continuous_array_planes n J) (weakArrayLaw T d U μ (n+1)) =
      ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d U μ n) := by
  induction n with
  | zero =>
    exact tendsto_nhds_unique
      ((continuous_continuousPush (planes 0 J) (continuous_array_planes 0 J)).tendsto
        _ |>.comp (weakArrayLaw_tendsto T d U μ 0)) (hproper J hJ)
  | succ n ih =>
    have h := (continuous_continuousPush (planes (n+1) J) (continuous_array_planes _ _)).tendsto
      (weakArrayLaw T d U μ (n+2)) |>.comp (weakArrayLaw_tendsto T d U μ (n+1))
    have he (b : ℕ) : continuousPush (planes (n+1) J) (continuous_array_planes _ _)
        (continuousPush (firstDuplicate T (d b) (n+1)) (continuous_firstDuplicate T (d b) (n+1))
          (weakArrayLaw T d U μ (n+1))) =
        ProbabilityMeasure.pi (fun _ : J => continuousPush (firstDuplicate T (d b) n)
          (continuous_firstDuplicate T (d b) n) (weakArrayLaw T d U μ n)) := by
      simp only [continuousPush_comp,planes_firstDuplicate_succ]
      rw [←continuousPush_comp (planes n J) (continuous_array_planes n J)
        (fun z j => firstDuplicate T (d b) n (z j))
        (continuous_pi fun j => (continuous_firstDuplicate T (d b) n).comp (continuous_apply j)),ih]
      exact continuousPush_pi _ (fun _ => continuous_firstDuplicate T (d b) n) _
    have hp := (ProbabilityMeasure.continuous_pi (α := fun _ : J => Arr I X (n+1))).tendsto
      (fun _ : J => weakArrayLaw T d U μ (n+1)) |>.comp
        (tendsto_pi_nhds.mpr (fun _ : J => weakArrayLaw_tendsto T d U μ n))
    exact tendsto_nhds_unique h (hp.congr fun b => (he b).symm)

end ArrayObjects

section
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {I X : Type*} [Fintype I] [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]

lemma probability_pi_tendsto_of_rectangles (ρ : ℕ → ProbabilityMeasure (I → X))
    (μ : I → ProbabilityMeasure X)
    (h : ∀ s : I → Set X, (∀ i, MeasurableSet (s i)) →
      Tendsto (fun n => (ρ n : Measure (I → X)) (Set.pi Set.univ s)) atTop
        (𝓝 (∏ i, (μ i : Measure X) (s i)))) :
    Tendsto ρ atTop (𝓝 (ProbabilityMeasure.pi μ)) := by
  apply isPiSystem_pi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨s,hs,rfl⟩
    exact MeasurableSet.univ_pi fun i => hs i (mem_univ i)
  · intro u hu x hx
    obtain ⟨s,hs,hsub⟩ := isOpen_pi_iff'.mp hu x hx
    refine ⟨Set.pi Set.univ s,⟨s,fun i _ => (hs i).1.measurableSet,rfl⟩,?_,hsub⟩
    exact set_pi_mem_nhds Set.finite_univ fun i _ => (hs i).1.mem_nhds (hs i).2
  · rintro _ ⟨s,hs,rfl⟩
    have hh := h s (fun i => hs i (mem_univ i))
    have he : (∏ i, (μ i : Measure X) (s i)) =
        (ProbabilityMeasure.pi μ : Measure (I → X)) (Set.pi Set.univ s) := by
      exact (Measure.pi_pi _ _).symm
    rw [he] at hh
    exact (ENNReal.tendsto_toNNReal (measure_ne_top _ _)).comp hh
end

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace ArrayObjects
universe u
variable {I : Type u} [Fintype I] [retained15 : DecidableEq I]
    {X : StandardSpace.{u}} [TopologicalSpace X] [retained16 : CompactSpace X] [retained17 : T2Space X]
    [SecondCountableTopology X] [retained18 : MetrizableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (d : ℕ → I → ℕ) (μ : ProbabilityMeasure X)

include retained15 retained16 retained17 retained18 in
lemma weakArrayLaw_proper_input
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))
    (J : Finset I) (hJ : J ≠ Finset.univ) :
    Tendsto (fun b => continuousPush (planes 0 J) (continuous_array_planes 0 J)
      (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
        (weakArrayLaw T d (Ultrafilter.of atTop) μ 0))) (↑(Ultrafilter.of (atTop : Filter ℕ)))
      (𝓝 (ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d (Ultrafilter.of atTop) μ 0))) := by
  let _ := retained15
  let _ := retained16
  let _ := retained17
  let _ := retained18
  let ρ : ℕ → ProbabilityMeasure (J → X) := fun b =>
    continuousPush (fun x j => (T^[d b j]) x)
      (continuous_pi fun j => T.continuous.iterate (d b j)) μ
  have hρ : Tendsto ρ atTop (𝓝 (ProbabilityMeasure.pi (fun _ : J => μ))) := by
    apply Rokhlin.probability_pi_tendsto_of_rectangles
    intro s hs
    convert hrect J hJ s hs using 1
    ext b
    change ((μ : Measure X).map (fun x => fun j : J => (T^[d b j]) x)) (Set.pi Set.univ s) = _
    rw [Measure.map_apply (show Measurable (fun x : X => fun j : J => (T^[d b j]) x) from
      (continuous_pi fun j : J => T.continuous.iterate (d b j)).measurable)
      (MeasurableSet.univ_pi hs)]
    congr 1
    ext x
    simp
  have hpush := (continuous_continuousPush
    (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
    (continuous_pi fun j => continuous_pi fun _ => continuous_apply j)).tendsto
      (ProbabilityMeasure.pi (fun _ : J => μ)) |>.comp hρ
  have he : continuousPush (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
      (continuous_pi fun j => continuous_pi fun _ => continuous_apply j)
      (ProbabilityMeasure.pi (fun _ : J => μ)) =
      ProbabilityMeasure.pi (fun _ : J => weakArrayLaw T d (Ultrafilter.of atTop) μ 0) := by
    exact continuousPush_pi (fun _ : J => fun x : X => fun _ : Index I 0 => x)
      (fun _ => continuous_pi fun _ => continuous_id) (fun _ => μ)
  rw [he] at hpush
  have he' (b : ℕ) : continuousPush
      (fun z : J → X => fun j : J => fun _ : Index I 0 => z j)
      (continuous_pi fun j => continuous_pi fun _ => continuous_apply j) (ρ b) =
      continuousPush (planes 0 J) (continuous_array_planes 0 J)
        (continuousPush (firstDuplicate T (d b) 0) (continuous_firstDuplicate T (d b) 0)
          (weakArrayLaw T d (Ultrafilter.of atTop) μ 0)) := by
    simp only [ρ,weakArrayLaw,continuousPush_comp]
    rfl
  exact (hpush.congr he').mono_left (Ultrafilter.of_le atTop)

variable (hμ : MeasurePreserving T μ μ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))

def weakInitialLaws : InitialLaws I X T.toMeasurableEquiv where
  law n := weakArrayLaw T d (Ultrafilter.of atTop) μ n
  probability _ := inferInstance
  invariant n := ⟨(continuous_array_amap T.continuous n).measurable,
    congrArg Subtype.val (weakArrayLaw_invariant T d (Ultrafilter.of atTop) μ hμ n)⟩
  consistent n a i := congrArg Subtype.val (weakArrayLaw_consistent T d (Ultrafilter.of atTop) μ hμ n a i)
  proper n J hJ := congrArg Subtype.val (weakArrayLaw_proper T d (Ultrafilter.of atTop) μ
    (weakArrayLaw_proper_input T d μ hrect) n J hJ)

lemma weakInitialLaws_zero : ((weakInitialLaws T d μ hμ hrect).law 0).map (zeroEquiv I X) = μ := by
  change ((μ : Measure X).map (fun x _ => x)).map (zeroEquiv I X) = μ
  rw [Measure.map_map (zeroEquiv I X).measurable (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)]
  exact Measure.map_id

lemma weakInitialLaws_correlation (f : I → C(X,ℝ)) (δ : ℝ)
    (hc : ∀ b, δ ≤ ∫ x, ∏ i, f i ((T^[d b i]) x) ∂(μ : Measure X)) :
    δ ≤ ∫ y, ∏ i, f i (zeroEquiv I X (plane 0 0 i y))
      ∂(weakInitialLaws T d μ hμ hrect).law 1 := by
  let F : C(Arr I X 1,ℝ) := ⟨fun y => ∏ i, f i (zeroEquiv I X (plane 0 0 i y)),
    continuous_finsetProd _ (fun i _ => (f i).continuous.comp (continuous_apply _))⟩
  have h := (ProbabilityMeasure.continuous_integral_continuousMap F).tendsto
    (weakArrayLaw T d (Ultrafilter.of atTop) μ 1) |>.comp
      (weakArrayLaw_tendsto T d (Ultrafilter.of atTop) μ 0)
  apply ge_of_tendsto h
  apply Eventually.of_forall
  intro b
  change δ ≤ ∫ y, F y ∂(((μ : Measure X).map (fun x _ => x)).map (firstDuplicate T (d b) 0))
  rw [Measure.map_map (continuous_firstDuplicate T (d b) 0).measurable
    (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id),
    integral_map ((continuous_firstDuplicate T (d b) 0).measurable.comp
      (show Measurable (fun x : X => fun _ : Index I 0 => x) from Measurable.of_eval fun _ => measurable_id)).aemeasurable F.continuous.measurable.aestronglyMeasurable]
  exact hc b

include hμ hrect in

lemma compact_zero_entropy_no_witness (hk : 3 ≤ Fintype.card I)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => (μ : Measure X) (A ∩ (T^[n]) ⁻¹' B)) atTop
        (𝓝 ((μ : Measure X) A * (μ : Measure X) B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℝ)
    (hcenter : ∫ x, v (α x) ∂(μ : Measure X) = 0)
    (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := (μ : Measure X))
      (fun m x => α ((T^[m]) x)) n / n) atTop (𝓝 0))
    (i : I) (f : I → C(X,ℝ)) (hb : ∀ j x, |f j x| ≤ 1)
    (hi : ∀ x, f i x = v (α x)) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ b, δ ≤ ∫ x, ∏ j, f j ((T^[d b j]) x) ∂(μ : Measure X)) : False := by
  let base := weakInitialLaws T d μ hμ hrect
  have hz := initial_correlation_zero base hk (weakInitialLaws_zero T d μ hμ hrect) hμ hmix
    α hα (fun a => (v a : ℂ)) (by rw [integral_complex_ofReal,hcenter,Complex.ofReal_zero]) hH i
    (fun j x => (f j x : ℂ))
    (fun j => Complex.continuous_ofReal.measurable.comp (f j).continuous.measurable)
    (fun j x => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hb j x)
    (fun x => congrArg Complex.ofReal (hi x))
  have hzR : (∫ y, ∏ j, f j (zeroEquiv I X (plane 0 0 j y)) ∂base.law 1) = 0 := by
    have hh := congrArg Complex.re hz
    simpa only [←Complex.ofReal_prod,integral_complex_ofReal,Complex.ofReal_re,Complex.zero_re] using hh
  have hpos := weakInitialLaws_correlation T d μ hμ hrect f δ hc
  rw [show (weakInitialLaws T d μ hμ hrect) = base from rfl,hzR] at hpos
  exact (not_le_of_gt hδ) hpos
end ArrayObjects

end Rokhlin

end

end OAI
