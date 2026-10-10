import Mathlib
import OAI.Probability.Perceptron.Cascade.WeightedTotalBiasedLaw

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise
namespace SphericalPerceptronFreeEnergy

lemma cascadeBiasedLaw_zero (n : ℕ) (z : Fin n → ℝ) :
    cascadeBiasedLaw n z 0 = (cascadeLaw n z : Measure (StableCascade n)) := by
  simp [cascadeBiasedLaw,normalizedMeasure]

lemma stableBlockProbability_eppf_value {a b : ℝ} (hb : 0 < b) (hb1 : b < 1) (ha : a < b)
    (ns : List ℕ) (hne : ns ≠ []) (hn : ∀ n ∈ ns, 1 ≤ n) :
    (∫⁻ η, stableBlockProbability ns η (Fin.elim0 : Fin 0 → ℝ) ∂stableTotalBiasedLaw a b) =
      ENNReal.ofReal (stableEppfValue a b (ns.map (fun n : ℕ => (n:ℝ)))) := by
  simpa only [stableEppfValue,List.length_map,List.map_map,Function.comp_def] using
    stableBlockProbability_eppf hb hb1 ha ns hne hn (Fin.elim0 : Fin 0 → ℝ)

lemma cascadeShapeProbability_law (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    (∫⁻ η, cascadeShapeProbability n z s η ∂(cascadeLaw n z : Measure (StableCascade n))) =
      cascadeShapeLikelihood n z 0 s := by
  rw [← cascadeBiasedLaw_zero n z]
  exact cascadeShapeProbability_integral n z hz hz0 hz1 0 hz0 s hs

def focusedShapeProbability : (n : ℕ) → (Fin n → ℝ) → ℕ → CascadeVisitShape n → StableCascade n → ℝ≥0∞
  | n, z, 0, s, η => cascadeShapeProbability n z s η
  | 0, _, _+1, _, _ => 0
  | _+1, _, _+1, [], _ => 0
  | n+1, z, d+1, s::ss, η => markedBlockProbability
      ((cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
        ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)))
      (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
        (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)

def focusedShapeNumerator : (n : ℕ) → (Fin n → ℝ) → ℝ → ℕ → CascadeVisitShape n → ℝ
  | n, _, a, 0, s => (cascadeVisitCount n s : ℝ)-a
  | 0, _, _, _+1, _ => 0
  | _+1, _, _, _+1, [] => 0
  | n+1, z, _, d+1, s::_ => focusedShapeNumerator n (fun i => z i.succ) (z 0) d s

lemma focusedShapeProbability_cons {n d : ℕ} (z : Fin (n+1) → ℝ)
    (s : CascadeVisitShape n) (ss : List (CascadeVisitShape n)) :
    focusedShapeProbability (n+1) z (d+1) (s::ss) =
      (fun η : Measure (ℝ×StableCascade n) => markedBlockProbability
        ((cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
          ss.map (fun t => (cascadeVisitCount n t,cascadeShapeProbability n (fun i => z i.succ) t)))
        (η.map (logMarkShift (centeredLogMark (cascadeLaw n (fun i => z i.succ)) (z 0)
          (fun C => Real.log (cascadeTotal n C))))) (Fin.elim0 : Fin 0 → ℝ)) := by
  funext η
  rfl

lemma markedBlockProbability_map_measurable {S : Type*} [MeasurableSpace S]
    [Nonempty S] (ns : List (ℕ × (S → ℝ≥0∞)))
    (hm : ∀ nf ∈ ns, Measurable nf.2) (F : ℝ×S → ℝ×S) (hF : Measurable F) :
    Measurable (fun η : Measure (ℝ×S) =>
      markedBlockProbability ns (η.map F) (Fin.elim0 : Fin 0 → ℝ)) := by
  exact (markedBlockProbability_measurable ns hm 0).comp
    ((Measure.measurable_map _ hF).prodMk measurable_const)

lemma focusedShapeProbability_measurable (n : ℕ) (z : Fin n → ℝ) (d : ℕ) (s : CascadeVisitShape n) :
    Measurable (focusedShapeProbability n z d s) := by
  induction n generalizing d with
  | zero => cases d <;> exact measurable_const
  | succ n ih =>
    cases d with
    | zero => exact cascadeShapeProbability_measurable (n+1) z s
    | succ d =>
      cases s with
      | nil => exact measurable_const
      | cons s ss =>
        have hm : ∀ nf ∈ (cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
            ss.map (fun s => (cascadeVisitCount n s,cascadeShapeProbability n (fun i => z i.succ) s)),
            Measurable nf.2 := by
          intro nf hnf
          rcases List.mem_cons.mp hnf with rfl | hh
          · exact ih (fun i => z i.succ) d s
          · obtain ⟨s',_,rfl⟩ := List.mem_map.mp hh
            exact cascadeShapeProbability_measurable n (fun i => z i.succ) s'
        have hF := logMarkShift_measurable (centeredLogMark_measurable
          (cascadeLaw n (fun i => z i.succ)) (z 0) (cascadeTotal_measurable n).log)
        let ns := (cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
          ss.map (fun t => (cascadeVisitCount n t,cascadeShapeProbability n (fun i => z i.succ) t))
        rw [focusedShapeProbability_cons]
        exact markedBlockProbability_map_measurable ns hm _ hF

lemma focusedShapeNumerator_pos (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha : a < 1)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    0 < focusedShapeNumerator n z a d s := by
  induction n generalizing d a with
  | zero =>
    have hd0 : d = 0 := Nat.eq_zero_of_le_zero hd
    subst d
    change 0 < (cascadeVisitCount 0 s : ℝ)-a
    have hr : (1:ℝ) ≤ cascadeVisitCount 0 s := by exact_mod_cast cascadeVisitCount_pos 0 s hs
    linarith
  | succ n ih =>
    cases d with
    | zero =>
      change 0 < (cascadeVisitCount (n+1) s : ℝ)-a
      have hr : (1:ℝ) ≤ cascadeVisitCount (n+1) s := by exact_mod_cast cascadeVisitCount_pos (n+1) s hs
      linarith
    | succ d =>
      obtain ⟨hne,hs⟩ := hs
      cases s with
      | nil => exact (hne rfl).elim
      | cons s ss =>
        exact ih (fun i => z i.succ) (fun i j h => hz (Fin.succ_lt_succ_iff.mpr h))
          (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (hz1 0) d (by omega) s (hs s (by simp))

theorem focusedShapeProbability_integral (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) (a : ℝ) (ha1 : a < 1) (ha : ∀ i, a < z i)
    (d : ℕ) (hd : d ≤ n) (s : CascadeVisitShape n) (hs : CascadeVisitShape.Valid n s) :
    (∫⁻ η, focusedShapeProbability n z d s η ∂cascadeBiasedLaw n z a) =
      cascadeShapeLikelihood n z a s *
        ENNReal.ofReal (focusedShapeNumerator n z a d s/((cascadeVisitCount n s:ℝ)-a)) := by
  induction d generalizing n a with
  | zero =>
    have hc : 0 < (cascadeVisitCount n s:ℝ)-a := by
      have hh : (1:ℝ) ≤ cascadeVisitCount n s := by exact_mod_cast cascadeVisitCount_pos n s hs
      linarith
    simp only [focusedShapeProbability,focusedShapeNumerator,div_self hc.ne',ENNReal.ofReal_one,mul_one]
    exact cascadeShapeProbability_integral n z hz hz0 hz1 a ha s hs
  | succ d ih =>
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨hne,hs⟩ := hs
      cases s with
      | nil => exact (hne rfl).elim
      | cons s ss =>
        have htail : StrictMono (fun i : Fin n => z i.succ) := fun i j h => hz (Fin.succ_lt_succ_iff.mpr h)
        have hsz := hs s (by simp)
        have hcount : (1:ℝ) ≤ cascadeVisitCount n s := by exact_mod_cast cascadeVisitCount_pos n s hsz
        have hrb : 0 < (cascadeVisitCount n s:ℝ)-z 0 := by linarith [hz1 0]
        have hwhole : 0 < (cascadeVisitCount (n+1) (s::ss):ℝ)-a := by
          have hh : (1:ℝ) ≤ cascadeVisitCount (n+1) (s::ss) := by
            exact_mod_cast cascadeVisitCount_pos (n+1) (s::ss) ⟨by simp,hs⟩
          linarith
        have hc : (cascadeVisitCount (n+1) (s::ss):ℝ)-a =
            (cascadeVisitCount n s:ℝ)+(ss.map (fun t => (cascadeVisitCount n t:ℝ))).sum-a := by
          simp only [cascadeVisitCount,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_list_sum,
            List.map_map,Function.comp_def]
        have hnp := focusedShapeNumerator_pos n (fun i => z i.succ) htail
          (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (hz1 0) d (by omega) s hsz
        have hchild := ih n (fun i => z i.succ) htail (fun i => hz0 i.succ) (fun i => hz1 i.succ)
          (z 0) (hz1 0) (fun i => hz (by simp)) (by omega) s hsz
        have hprod : (ss.map (fun t => ∫⁻ C, cascadeShapeProbability n (fun i => z i.succ) t C
            ∂cascadeBiasedLaw n (fun i => z i.succ) (z 0))).prod =
            (ss.map (cascadeShapeLikelihood n (fun i => z i.succ) (z 0))).prod := by
          congr 1
          apply List.map_congr_left
          intro t ht
          exact cascadeShapeProbability_integral n (fun i => z i.succ) htail
            (fun i => hz0 i.succ) (fun i => hz1 i.succ) (z 0) (fun i => hz (by simp)) t (hs t (by simp [ht]))
        let ns := (cascadeVisitCount n s+1,focusedShapeProbability n (fun i => z i.succ) d s)::
          ss.map (fun t => (cascadeVisitCount n t,cascadeShapeProbability n (fun i => z i.succ) t))
        have hn : ∀ nf ∈ ns, 1 ≤ nf.1 := by
          intro nf hnf
          rcases List.mem_cons.mp hnf with rfl | hh
          · simp
          · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hh
            exact cascadeVisitCount_pos n t (hs t (by simp [ht]))
        have hm : ∀ nf ∈ ns, Measurable nf.2 := by
          intro nf hnf
          rcases List.mem_cons.mp hnf with rfl | hh
          · exact focusedShapeProbability_measurable n (fun i => z i.succ) d s
          · obtain ⟨t,_,rfl⟩ := List.mem_map.mp hh
            exact cascadeShapeProbability_measurable n (fun i => z i.succ) t
        change (∫⁻ η, markedBlockProbability ns _ _ ∂cascadeBiasedLaw (n+1) z a) = _
        rw [cascadeRootBlock_factor z hz hz0 hz1 (ha 0) ns (by simp [ns]) hn hm,
          stableBlockProbability_eppf_value (hz0 0) (hz1 0) (ha 0) (ns.map Prod.fst)
            (by simp [ns]) (by intro r hr; obtain ⟨nf,hmem,rfl⟩ := List.mem_map.mp hr; exact hn nf hmem)]
        simp only [ns,List.map_cons,List.prod_cons,List.map_map,Function.comp_def,Nat.cast_add,Nat.cast_one]
        rw [hchild,hprod,stableEppfValue_join (by linarith [hz1 0]) _ (by rw [← hc]; exact hwhole),
          ENNReal.ofReal_mul (div_nonneg hrb.le (by rw [← hc]; exact hwhole.le))]
        simp only [cascadeShapeLikelihood,List.map_cons,List.prod_cons,focusedShapeNumerator]
        rw [hc]
        let D := (cascadeVisitCount n s:ℝ)+(ss.map (fun t => (cascadeVisitCount n t:ℝ))).sum-a
        let U := focusedShapeNumerator n (fun i => z i.succ) (z 0) d s
        have hcancel : (U/((cascadeVisitCount n s:ℝ)-z 0))*(((cascadeVisitCount n s:ℝ)-z 0)/D) = U/D := by
          field_simp
        have hmul : ENNReal.ofReal (U/((cascadeVisitCount n s:ℝ)-z 0))*
            ENNReal.ofReal (((cascadeVisitCount n s:ℝ)-z 0)/D) = ENNReal.ofReal (U/D) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hnp.le hrb.le),hcancel]
        calc
          _ = (cascadeShapeLikelihood n (fun i => z i.succ) (z 0) s *
              (ss.map (cascadeShapeLikelihood n (fun i => z i.succ) (z 0))).prod *
              ENNReal.ofReal (stableEppfValue a (z 0)
                ((cascadeVisitCount n s:ℝ)::ss.map (fun t => (cascadeVisitCount n t:ℝ))))) *
              (ENNReal.ofReal (U/((cascadeVisitCount n s:ℝ)-z 0))*
                ENNReal.ofReal (((cascadeVisitCount n s:ℝ)-z 0)/D)) := by dsimp [U,D]; ring
          _ = _ := by rw [hmul]

lemma descendant_transform_independent {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D) [SFinite ν] [SFinite ρ]
    (T : S × C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ) :
    (ν.prod ρ).map (fun p => (p.1,T p)) = ν.prod θ := by
  exact ((MeasurePreserving.id ν).skew_product (g := fun s c => T (s,c)) hT (ae_of_all _ hLaw)).map_eq

lemma stableIntensity_normalized_mark_projection {S : Type*} [MeasurableSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb : 0 ≤ b)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    ((stableLogIntensity b).prod ν).map (fun p : ℝ×S => p.1+F p.2) = stableLogIntensity b := by
  have : IsProbabilityMeasure (ν.withDensity (fun x => ENNReal.ofReal (Real.exp (b*F x)))) :=
    normalized_mark_density_probability ν hI hM
  change Measure.map (Prod.fst ∘ logMarkShift F) ((stableLogIntensity b).prod ν) = _
  rw [← Measure.map_map measurable_fst (logMarkShift_measurable hF),stableLogIntensity_mark_shift ν hb hF,
    Measure.map_fst_prod,measure_univ,one_smul]

lemma stableIntensity_descendant_transform {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    ((stableLogIntensity b).prod (ν.prod ρ)).map
      (fun p : ℝ×(S×C) => (p.1+F p.2.1,T p.2)) = (stableLogIntensity b).prod θ := by
  let I := stableLogIntensity b
  have hmark : MeasurePreserving (fun p : S×C => (p.1,T p)) (ν.prod ρ) (ν.prod θ) :=
    ⟨measurable_fst.prodMk hT, descendant_transform_independent ν ρ θ T hT hLaw⟩
  have hs : MeasurePreserving (fun p : ℝ×S => p.1+F p.2) (I.prod ν) I :=
    ⟨measurable_fst.add (hF.comp measurable_snd), stableIntensity_normalized_mark_projection ν hb hF hI hM⟩
  have hassoc : MeasurePreserving (MeasurableEquiv.prodAssoc : (ℝ×S)×D ≃ᵐ ℝ×(S×D))
      ((I.prod ν).prod θ) (I.prod (ν.prod θ)) :=
    ⟨MeasurableEquiv.prodAssoc.measurable,Measure.prodAssoc_prod⟩
  have hmain := (hs.prod (MeasurePreserving.id θ)).comp
    ((hassoc.symm).comp ((MeasurePreserving.id I).prod hmark))
  exact hmain.map_eq

lemma stablePoisson_descendant_transform {S C D : Type*}
    [MeasurableSpace S] [MeasurableSpace C] [MeasurableSpace D]
    [Nonempty S] [Nonempty C] [Nonempty D]
    (ν : Measure S) (ρ : Measure C) (θ : Measure D)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] [IsProbabilityMeasure θ]
    {b : ℝ} (hb : 0 ≤ b) (T : S×C → D) (hT : Measurable T)
    (hLaw : ∀ s, ρ.map (fun c => T (s,c)) = θ)
    {F : S → ℝ} (hF : Measurable F)
    (hI : Integrable (fun x => Real.exp (b*F x)) ν)
    (hM : (∫ x, Real.exp (b*F x) ∂ν) = 1) :
    (poissonRandomMeasureLaw ((stableLogIntensity b).prod (ν.prod ρ))).map
      (Measure.map (fun p : ℝ×(S×C) => (p.1+F p.2.1,T p.2))) =
        poissonRandomMeasureLaw ((stableLogIntensity b).prod θ) := by
  rw [poissonRandomMeasureLaw_map _ (by fun_prop)]
  congr 1
  exact stableIntensity_descendant_transform ν ρ θ hb T hT hLaw hF hI hM

lemma countKernel_parameter_map_measurable {X S D : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace D]
    (F : X×(ℝ×S) → D) (hF : Measurable F) :
    Measurable (fun p : X×Measure (ℝ×S) =>
      (markedStableCountKernel p.2).map (fun q => F (p.1,q))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  let κ : Kernel (X×Measure (ℝ×S)) (ℝ×S) := markedStableCountKernel.comap Prod.snd measurable_snd
  have hh : Measurable (fun p : (X×Measure (ℝ×S))×(ℝ×S) =>
      (s.indicator (fun _ => (1:ℝ≥0∞))) (F (p.1.1,p.2))) :=
    (measurable_const.indicator hs).comp (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  have hi := hh.lintegral_kernel_prod_right' (κ := κ)
  convert hi using 1
  funext p
  calc
    _ = ∫⁻ d, s.indicator (fun _ => (1:ℝ≥0∞)) d ∂(markedStableCountKernel p.2).map (fun q => F (p.1,q)) :=
      (lintegral_indicator_one hs).symm
    _ = _ := lintegral_map (measurable_const.indicator hs)
      (hF.comp (measurable_const.prodMk measurable_id))

lemma markedStableCountKernel_ae_eq {S : Type*} [MeasurableSpace S] [Nonempty S]
    (ν : Measure S) [IsProbabilityMeasure ν] {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ᵐ η ∂poissonRandomMeasureLaw ((stableLogIntensity b).prod ν), markedStableCountKernel η = η := by
  exact (markedStable_regular ν hb0 hb1).mono (fun η hη => markedStableCountKernel_eq η hη.1 hη.2)

@[reducible] def DecoratedCascade (S : Type) [MeasurableSpace S] : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (Measure (ℝ×(S×DecoratedCascade S n)))

instance decoratedCascadeNonempty (S : Type) [MeasurableSpace S] (n : ℕ) :
    Nonempty (DecoratedCascade S n) := by
  cases n with
  | zero => exact ⟨()⟩
  | succ n => exact ⟨(0 : Measure (ℝ×(S×DecoratedCascade S n)))⟩

def decoratedCascadeLaw {S : Type} [MeasurableSpace S] [Nonempty S]
    (ν : ProbabilityMeasure S) : (n : ℕ) → (Fin n → ℝ) → ProbabilityMeasure (DecoratedCascade S n)
  | 0, _ => ⟨Measure.dirac (),by exact Measure.dirac.isProbabilityMeasure⟩
  | n+1, z => ⟨poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod
      ((ν : Measure S).prod (decoratedCascadeLaw ν n (fun i => z i.succ)))),
        by exact poissonRandomMeasureLaw_probability _⟩

def decoratedCascadeTransform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → StableCascade n
  | 0, _, _ => ()
  | n+1, F, p => (markedStableCountKernel p.2).map (fun q : ℝ×(S×DecoratedCascade S n) =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2)))

lemma decoratedCascadeTransform_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) : Measurable (decoratedCascadeTransform step n F) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let H : X×(ℝ×(S×DecoratedCascade S n)) → ℝ×StableCascade n := fun p =>
      (p.2.1+F 0 (p.1,p.2.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,p.2.2.1),p.2.2.2))
    have hH : Measurable H :=
      (measurable_snd.fst.add ((hF 0).comp (measurable_fst.prodMk measurable_snd.snd.fst))).prodMk
        ((ih (fun i => F i.succ) (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd))
    exact countKernel_parameter_map_measurable H hH

theorem decoratedCascadeTransform_law {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) (x : X) :
    (decoratedCascadeLaw ν n z : Measure (DecoratedCascade S n)).map
      (fun η => decoratedCascadeTransform step n F (x,η)) = cascadeLaw n z := by
  induction n generalizing x with
  | zero =>
    change Measure.map (fun _ : Unit => ()) (Measure.dirac ()) = Measure.dirac ()
    exact Measure.map_dirac ()
  | succ n ih =>
    let ρ : Measure (DecoratedCascade S n) := decoratedCascadeLaw ν n (fun i => z i.succ)
    let θ : Measure (StableCascade n) := cascadeLaw n (fun i => z i.succ)
    let T : S×DecoratedCascade S n → StableCascade n := fun p =>
      decoratedCascadeTransform step n (fun i => F i.succ) (step (x,p.1),p.2)
    have hT : Measurable T :=
      (decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
        ((hstep.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
    have ht : ∀ s, ρ.map (fun c => T (s,c)) = θ := fun s =>
      ih (fun i => z i.succ) (fun i => hz0 i.succ) (fun i => hz1 i.succ)
        (fun i => F i.succ) (fun i => hF i.succ) (fun i => hI i.succ) (fun i => hM i.succ) (step (x,s))
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n :=
      fun p => (p.1+F 0 (x,p.2.1),T p.2)
    change (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
      (fun η => (markedStableCountKernel η).map G) = poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod θ)
    calc
      _ = (poissonRandomMeasureLaw ((stableLogIntensity (z 0)).prod ((ν : Measure S).prod ρ))).map
            (Measure.map G) := by
        apply Measure.map_congr
        filter_upwards [markedStable_regular ((ν : Measure S).prod ρ) (hz0 0) (hz1 0)] with η hη
        rw [markedStableCountKernel_eq η hη.1 hη.2]
      _ = _ := stablePoisson_descendant_transform (ν : Measure S) ρ θ (hz0 0).le T hT ht
        ((hF 0).comp (measurable_const.prodMk measurable_id)) (hI 0 x) (hM 0 x)

lemma decoratedCascadeTransform_root_independent {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    [Nonempty S] (ν : ProbabilityMeasure S) (μ : Measure X) [SFinite μ]
    (step : X×S → X) (hstep : Measurable step)
    (n : ℕ) (z : Fin n → ℝ) (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1)
    (F : Fin n → X×S → ℝ) (hF : ∀ i, Measurable (F i))
    (hI : ∀ i x, Integrable (fun s => Real.exp (z i*F i (x,s))) ν)
    (hM : ∀ i x, (∫ s, Real.exp (z i*F i (x,s)) ∂ν) = 1) :
    (μ.prod (decoratedCascadeLaw ν n z)).map (fun p => (p.1,decoratedCascadeTransform step n F p)) =
      μ.prod (cascadeLaw n z) := by
  apply descendant_transform_independent _ _ _ _ (decoratedCascadeTransform_measurable step hstep n F hF)
  exact decoratedCascadeTransform_law ν step hstep n z hz0 hz1 F hF hI hM

lemma cascadeTotal_log_memLp_two (n : ℕ) (z : Fin n → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    MemLp (fun η => Real.log (cascadeTotal n η)) 2 (cascadeLaw n z : Measure (StableCascade n)) := by
  cases n with
  | zero => simp [cascadeTotal,cascadeTotalE]
  | succ n =>
    obtain ⟨hp,hI⟩ := cascadeTotal_regular (n+1) z hz hz0 hz1
    let ε : ℝ := z 0/4
    have hε : 0 < ε := div_pos (hz0 0) (by norm_num)
    have hmin : ∀ i, z 0 ≤ z i := fun i => hz.monotone (Fin.zero_le i)
    have hplus : ∀ i, 2*ε < z i := by intro i; dsimp [ε]; linarith [hmin i,hz0 0]
    have hminus : ∀ i, -(2*ε) < z i := by intro i; linarith [hz0 i]
    apply (memLp_two_iff_integrable_sq (cascadeTotal_measurable (n+1)).log.aestronglyMeasurable).mpr
    apply (((hI (2*ε) hplus).add (hI (-(2*ε)) hminus)).div_const (ε^2)).mono'
      ((cascadeTotal_measurable (n+1)).log.pow_const (2:ℕ)).aestronglyMeasurable
    filter_upwards [hp] with η hη
    change |(Real.log (cascadeTotal (n+1) η))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact log_sq_le_two_rpow hη hε

def decoratedWeightedTotalE {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) : (n : ℕ) → (Fin n → X×S → ℝ) → X×DecoratedCascade S n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, F, p => ∫⁻ q : ℝ×(S×DecoratedCascade S n),
      ENNReal.ofReal (Real.exp (q.1+F 0 (p.1,q.2.1))) *
        decoratedWeightedTotalE step n (fun i => F i.succ) (step (p.1,q.2.1),q.2.2)
          ∂markedStableCountKernel p.2

lemma decoratedWeightedTotalE_transform {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X×S → X) (hstep : Measurable step) (n : ℕ) (F : Fin n → X×S → ℝ)
    (hF : ∀ i, Measurable (F i)) (p : X×DecoratedCascade S n) :
    cascadeTotalE n (decoratedCascadeTransform step n F p) = decoratedWeightedTotalE step n F p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let G : ℝ×(S×DecoratedCascade S n) → ℝ×StableCascade n := fun q =>
      (q.1+F 0 (p.1,q.2.1),decoratedCascadeTransform step n (fun i => F i.succ)
        (step (p.1,q.2.1),q.2.2))
    have hG : Measurable G :=
      (measurable_fst.add ((hF 0).comp (measurable_const.prodMk measurable_snd.fst))).prodMk
        ((decoratedCascadeTransform_measurable step hstep n _ (fun i => hF i.succ)).comp
          ((hstep.comp (measurable_const.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))
    change (∫⁻ q : ℝ×StableCascade n, ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2
      ∂(markedStableCountKernel p.2).map G) = _
    have hw : Measurable (fun q : ℝ×StableCascade n => ENNReal.ofReal (Real.exp q.1)*cascadeTotalE n q.2) :=
      ((Real.measurable_exp.comp measurable_fst).ennreal_ofReal.mul ((cascadeTotalE_measurable n).comp measurable_snd))
    calc
      _ = ∫⁻ q, ENNReal.ofReal (Real.exp (G q).1)*cascadeTotalE n (G q).2 ∂markedStableCountKernel p.2 :=
        lintegral_map hw hG
      _ = _ := by
        apply lintegral_congr
        intro q
        dsimp only [G]
        rw [ih (fun i => F i.succ) (fun i => hF i.succ)]

end SphericalPerceptronFreeEnergy

end

end OAI
