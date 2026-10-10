import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.ActionLimits
import OAI.Geometry.CAT0Fillings.Slices.Approximation

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

def TupleKernel (hT : IsMetricCurrent T) (π : Fin k → X → ℝ) : Prop :=
  ∀ (f : X → ℝ), Integrable f μ → borelAction μ hT f π = 0

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma tuple_lipschitz_update {π : Fin k → X → ℝ}
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k)
    {v : X → ℝ} (hv : ∃ K : ℝ≥0, LipschitzWith K v) :
    ∀ j, ∃ K : ℝ≥0, LipschitzWith K (Function.update π i v j) := by
  classical
  intro j
  by_cases he : j = i
  · simpa [he] using hv
  · simpa only [Function.update_of_ne he] using hπ j

lemma TupleKernel.of_boundedLip {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (hz : ∀ b, BoundedLip b → T b π = 0) : TupleKernel μ hT π := by
  intro f hf
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have ht := borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg π hπ
  have he (n : ℕ) : borelAction μ hT (g n).val π = 0 := by
    rw [borelAction_eq μ hT hμ ⟨(g n).property,hπ⟩]
    exact hz (g n).val (g n).property
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma TupleKernel.coord_const {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) (c : ℝ) : TupleKernel μ hT (Function.update π i (fun _ => c)) := by
  classical
  intro f hf
  exact borelAction_const_coord μ hT hμ hf _
    (tuple_lipschitz_update hπ i ⟨0,LipschitzWith.const c⟩) i c (fun _ => by simp)

lemma TupleKernel.coord_linear {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) (a c : ℝ) :
    TupleKernel μ hT (Function.update π i (fun x => a*u x+c*v x)) := by
  classical
  intro f hf
  have hh := borelAction_linearCoord μ hT hμ hf (Function.update π i u)
    (tuple_lipschitz_update hπ i hu) i v hv a c
  simp only [Function.update_self,Function.update_idem,hku f hf,hkv f hf,mul_zero,add_zero] at hh
  exact hh

lemma TupleKernel.coord_min {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) :
    TupleKernel μ hT (Function.update π i (fun x => min (u x) (v x))) := by
  classical
  obtain ⟨K,hK⟩ := hu
  obtain ⟨L,hL⟩ := hv
  intro f hf
  let E := {x | u x ≤ v x}
  have hE : MeasurableSet E := measurableSet_le hK.continuous.measurable hL.continuous.measurable
  let τ := Function.update π i (fun x => min (u x) (v x))
  have hτ := tuple_lipschitz_update hπ i ⟨max K L,hK.min hL⟩
  have h1 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE)
    τ hτ i u ⟨K,hK⟩ (by
      intro x hx
      have hxE : x ∈ E := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      simpa only [τ,Function.update_self] using min_eq_left hxE)
  have h2 := borelAction_congr_coord_on_support μ hT hμ (hf.indicator hE.compl)
    τ hτ i v ⟨L,hL⟩ (by
      intro x hx
      have hxE : x ∈ Eᶜ := by
        by_contra hh
        exact hx (indicator_of_notMem hh _)
      simpa only [τ,Function.update_self] using min_eq_right (le_of_not_ge (show ¬u x ≤ v x from hxE)))
  simp only [τ,Function.update_idem,hku _ (hf.indicator hE)] at h1
  simp only [τ,Function.update_idem,hkv _ (hf.indicator hE.compl)] at h2
  have heq : f = fun x => E.indicator f x+Eᶜ.indicator f x := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [heq]
  change borelAction μ hT (E.indicator f + Eᶜ.indicator f) τ = 0
  rw [borelAction_add μ hT (hf.indicator hE) (hf.indicator hE.compl) _ hτ,h1,h2]
  simp

lemma TupleKernel.coord_neg {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u : X → ℝ} (hu : ∃ K, LipschitzWith K u)
    (hku : TupleKernel μ hT (Function.update π i u)) :
    TupleKernel μ hT (Function.update π i (fun x => -u x)) := by
  simpa using TupleKernel.coord_linear μ hμ hπ i hu hu hku hku (-1) 0

lemma TupleKernel.coord_max {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {u v : X → ℝ} (hu : ∃ K, LipschitzWith K u) (hv : ∃ K, LipschitzWith K v)
    (hku : TupleKernel μ hT (Function.update π i u))
    (hkv : TupleKernel μ hT (Function.update π i v)) :
    TupleKernel μ hT (Function.update π i (fun x => max (u x) (v x))) := by
  have hnu : ∃ K, LipschitzWith K (fun x => -u x) := ⟨hu.choose,hu.choose_spec.neg⟩
  have hnv : ∃ K, LipschitzWith K (fun x => -v x) := ⟨hv.choose,hv.choose_spec.neg⟩
  have hm := TupleKernel.coord_min μ hμ hπ i hnu hnv
    (TupleKernel.coord_neg μ hμ hπ i hu hku) (TupleKernel.coord_neg μ hμ hπ i hv hkv)
  have hLm : ∃ K, LipschitzWith K (fun x => min (-u x) (-v x)) :=
    ⟨max hnu.choose hnv.choose,hnu.choose_spec.min hnv.choose_spec⟩
  have he : (fun x => -(min (-u x) (-v x))) = (fun x => max (u x) (v x)) := by
    funext x
    by_cases hx : u x ≤ v x
    · simp only [max_eq_right hx,min_eq_right (neg_le_neg hx),neg_neg]
    · have hx' := le_of_not_ge hx
      simp only [max_eq_left hx',min_eq_left (neg_le_neg hx'),neg_neg]
  simpa only [he] using TupleKernel.coord_neg μ hμ hπ i hLm hm

lemma TupleKernel.coord_limit {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    (i : Fin k) {us : ℕ → X → ℝ} {u : X → ℝ} {K : ℝ≥0}
    (hs : ∀ n, TupleKernel μ hT (Function.update π i (us n)))
    (hK : ∀ n, LipschitzWith K (us n))
    (hlim : ∀ x, Tendsto (fun n => us n x) atTop (𝓝 (u x))) :
    TupleKernel μ hT (Function.update π i u) := by
  classical
  intro f hf
  have hunif : ∀ j, ∃ L, ∀ n, LipschitzWith L (Function.update π i (us n) j) := by
    intro j
    by_cases he : j = i
    · subst j
      exact ⟨K,by simpa using hK⟩
    · exact ⟨(hπ j).choose,fun n => by simpa only [Function.update_of_ne he] using (hπ j).choose_spec⟩
  have hpoint : ∀ j x, Tendsto (fun n => Function.update π i (us n) j x) atTop
      (𝓝 (Function.update π i u j x)) := by
    intro j x
    by_cases he : j = i
    · subst j
      simpa using hlim x
    · simpa only [Function.update_of_ne he] using tendsto_const_nhds (x := π j x)
  have ht := borelAction_sequentialContinuity μ hT hμ hf (Function.update π i u)
    (fun n => Function.update π i (us n)) hunif hpoint
  simp only [hs _ f hf] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma tupleKernel_lipLattice {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) :
    LipLattice (fun u => TupleKernel μ hT (Function.update π i u)) where
  const := TupleKernel.coord_const μ hμ hπ i
  linear := fun hu hv hku hkv => TupleKernel.coord_linear μ hμ hπ i hu hv hku hkv
  min := fun hu hv hku hkv => TupleKernel.coord_min μ hμ hπ i hu hv hku hkv
  max := fun hu hv hku hkv => TupleKernel.coord_max μ hμ hπ i hu hv hku hkv
  limit := fun hs hK hlim => TupleKernel.coord_limit μ hμ hπ i hs hK hlim

end CAT0Fillings.SliceReconstruction
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]

lemma tupleKernel_comp_pi {hT : IsMetricCurrent T} (hμ : Controls T μ)
    {m : ℕ} {u : X → (Fin m → ℝ)} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hgen : ∀ ρ : Fin k → Fin m, TupleKernel μ hT (fun i x => u x (ρ i)))
    (φ : Fin k → (Fin m → ℝ) → ℝ) (hφ : ∀ i, ∃ K, LipschitzWith K (φ i)) :
    TupleKernel μ hT (fun i x => φ i (u x)) := by
  classical
  let Fits (s : Finset (Fin k)) (π : Fin k → X → ℝ) : Prop :=
    ∀ i, (i ∈ s → ∃ (K : ℝ≥0) (ψ : (Fin m → ℝ) → ℝ), LipschitzWith K ψ ∧ π i = fun x => ψ (u x)) ∧
      (i ∉ s → ∃ j : Fin m, π i = fun x => u x j)
  have hul (j : Fin m) : LipschitzWith L (fun x => u x j) := by
    simpa only [one_mul,Function.comp_def,Function.eval] using (LipschitzWith.eval j).comp hu
  have hfitlip {s : Finset (Fin k)} {π : Fin k → X → ℝ} (hf : Fits s π) :
      ∀ i, ∃ K, LipschitzWith K (π i) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨K,ψ,hψ,he⟩ := (hf i).1 hi
      exact ⟨K*L,by simpa only [he,Function.comp_def] using hψ.comp hu⟩
    · obtain ⟨j,he⟩ := (hf i).2 hi
      exact ⟨L,he ▸ hul j⟩
  have hstep (s : Finset (Fin k)) : ∀ π, Fits s π → TupleKernel μ hT π := by
    induction s using Finset.induction_on with
    | empty =>
      intro π hf
      choose ρ hρ using fun i => (hf i).2 (Finset.notMem_empty i)
      have he : π = fun i x => u x (ρ i) := by funext i;exact hρ i
      rw [he]
      exact hgen ρ
    | @insert i s hi ih =>
      intro π hf
      obtain ⟨K,ψ,hψ,heψ⟩ := (hf i).1 (Finset.mem_insert_self i s)
      have hsgen (j : Fin m) : TupleKernel μ hT (Function.update π i (fun x => u x j)) := by
        apply ih
        intro l
        constructor
        · intro hl
          have hli : l ≠ i := by rintro rfl;exact hi hl
          obtain ⟨K',ψ',hψ',heψ'⟩ := (hf l).1 (Finset.mem_insert_of_mem hl)
          exact ⟨K',ψ',hψ',by simpa only [Function.update_of_ne hli] using heψ'⟩
        · intro hl
          by_cases hli : l = i
          · subst l
            exact ⟨j,by simp⟩
          · have hl' : l ∉ insert i s := by simp only [Finset.mem_insert];exact not_or.mpr ⟨hli,hl⟩
            obtain ⟨j',hj'⟩ := (hf l).2 hl'
            exact ⟨j',by simpa only [Function.update_of_ne hli] using hj'⟩
      have hc := (tupleKernel_lipLattice μ hμ (hfitlip hf) i).comp_pi hu hsgen hψ
      have hup : Function.update π i (fun x => ψ (u x)) = π := by rw [←heψ];exact Function.update_eq_self i π
      simpa only [hup] using hc
  apply hstep Finset.univ
  intro i
  constructor
  · intro _
    exact ⟨(hφ i).choose,φ i,(hφ i).choose_spec,rfl⟩
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end CAT0Fillings.SliceReconstruction
end

end OAI
