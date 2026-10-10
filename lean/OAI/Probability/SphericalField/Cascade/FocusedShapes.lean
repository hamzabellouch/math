import Mathlib
import OAI.Probability.SphericalField.Cascade.Shapes

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
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

end SphericalPerceptron
end
end
end

end OAI
