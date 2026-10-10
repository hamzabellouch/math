import OAI.Analysis.SeparableQuotients.Positive.FiniteSuppression

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Sampling

structure FullTuple (I : Type*) (n : ℕ) where
  val : Fin n → I

instance {I : Type*} {n : ℕ} : CoeFun (FullTuple I n) (fun _ => Fin n → I) :=
  ⟨FullTuple.val⟩

instance {I : Type*} {n : ℕ} : MeasurableSpace (FullTuple I n) := ⊤

namespace FullTuple
variable {I : Type*} {n : ℕ}
def nil : FullTuple I 0 := ⟨Fin.elim0⟩
def cons (a : I) (t : FullTuple I n) : FullTuple I (n + 1) := ⟨Fin.cons a t.val⟩
def head (t : FullTuple I (n + 1)) : I := t 0
def tail (t : FullTuple I (n + 1)) : FullTuple I n := ⟨fun i => t i.succ⟩
@[simp] lemma cons_zero (a : I) (t : FullTuple I n) : cons a t 0 = a := rfl
@[simp] lemma cons_succ (a : I) (t : FullTuple I n) (i : Fin n) :
    cons a t i.succ = t i := rfl
@[simp] lemma head_cons (a : I) (t : FullTuple I n) : head (cons a t) = a := rfl
@[simp] lemma tail_cons (a : I) (t : FullTuple I n) : tail (cons a t) = t := by
  cases t
  rfl
@[simp] lemma cons_head_tail (t : FullTuple I (n + 1)) : cons t.head t.tail = t := by
  cases t with
  | mk t =>
    change FullTuple.mk (Fin.cons (t 0) (fun i => t i.succ)) = FullTuple.mk t
    apply congrArg FullTuple.mk
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
lemma eq_nil (t : FullTuple I 0) : t = nil := by
  cases t with
  | mk t => congr; funext i; exact Fin.elim0 i
end FullTuple

variable {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]

def orderedMeasure (μ : Measure I) : (n : ℕ) → Measure (FullTuple I n)
  | 0 => Measure.dirac FullTuple.nil
  | n + 1 => μ.bind (fun a => (orderedMeasure μ n).map (FullTuple.cons a))

instance orderedMeasure_probability (μ : Measure I) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (orderedMeasure μ n) := by
  induction n with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    have := ih
    apply isProbabilityMeasure_bind (Measurable.of_discrete.aemeasurable)
    apply Eventually.of_forall
    intro a
    infer_instance

lemma ae_bind_iff_of_full {T : Type*} [MeasurableSpace T] [DiscreteMeasurableSpace T]
    (μ : Measure I) (ν : I → Measure T) (P : T → Prop) :
    (∀ᵐ t ∂μ.bind ν, P t) ↔ ∀ᵐ a ∂μ, ∀ᵐ t ∂ν a, P t := by
  simp only [ae_iff]
  rw [Measure.bind_apply (MeasurableSet.of_discrete) (Measurable.of_discrete.aemeasurable)]
  exact lintegral_eq_zero_iff Measurable.of_discrete

omit [DiscreteMeasurableSpace I] in
lemma ae_orderedMeasure_zero (μ : Measure I) (P : FullTuple I 0 → Prop) :
    (∀ᵐ t ∂orderedMeasure μ 0, P t) ↔ P FullTuple.nil := by
  exact ae_dirac_iff MeasurableSet.of_discrete

lemma ae_orderedMeasure_succ (μ : Measure I) {n : ℕ}
    (P : FullTuple I (n + 1) → Prop) :
    (∀ᵐ t ∂orderedMeasure μ (n + 1), P t) ↔
      ∀ᵐ a ∂μ, ∀ᵐ t ∂orderedMeasure μ n, P (FullTuple.cons a t) := by
  rw [orderedMeasure, ae_bind_iff_of_full]
  apply eventually_congr
  exact Eventually.of_forall (fun _ => ae_map_iff Measurable.of_discrete.aemeasurable
    MeasurableSet.of_discrete)



def orderedAE (μ : Measure I) : (n : ℕ) → (FullTuple I n → Prop) → Prop
  | 0, P => P FullTuple.nil
  | n + 1, P => ∀ᵐ a ∂μ, orderedAE μ n (fun t => P (FullTuple.cons a t))

lemma ae_orderedMeasure_iff (μ : Measure I) (n : ℕ) (P : FullTuple I n → Prop) :
    (∀ᵐ t ∂orderedMeasure μ n, P t) ↔ orderedAE μ n P := by
  induction n with
  | zero => exact ae_orderedMeasure_zero μ P
  | succ n ih =>
    rw [ae_orderedMeasure_succ]
    apply eventually_congr
    exact Eventually.of_forall (fun _ => ih _)

lemma coded_cross_vanishing
    {I T C K : Type*} [MeasurableSpace I] [MeasurableSpace T]
    [MeasurableSpace C] [MeasurableSpace K]
    {μ : Measure I} {ν : Measure T} [SFinite μ] [SFinite ν]
    {code : I → C} {Y : T → K} {Φ : C × K → ℝ} {D : Set K}
    (hc : Measurable code) (hY : Measurable Y) (hΦ : Measurable Φ)
    (hYD : ∀ t, Y t ∈ D)
    (hnull : ∀ y ∈ D, ∀ᵐ i ∂μ, Φ (code i, y) = 0) :
    ∀ᵐ i ∂μ, ∀ᵐ t ∂ν, Φ (code i, Y t) = 0 := by
  have hm : Measurable (fun z : I × T => Φ (code z.1, Y z.2)) :=
    hΦ.comp (hc.prodMap hY)
  apply (Measure.ae_ae_comm (μ := μ) (ν := ν) (p := fun i t => Φ (code i, Y t) = 0)
    (measurableSet_eq_fun hm measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun t => hnull (Y t) (hYD t))



lemma orderedMeasure_succ_apply (μ : Measure I) {n : ℕ}
    (A : Set (FullTuple I (n + 1))) :
    orderedMeasure μ (n + 1) A =
      ∫⁻ a, orderedMeasure μ n (FullTuple.cons a ⁻¹' A) ∂μ := by
  rw [orderedMeasure, Measure.bind_apply MeasurableSet.of_discrete
    Measurable.of_discrete.aemeasurable]
  apply lintegral_congr
  intro a
  exact Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete



lemma ordered_cross_vanishing
    {C K : Type*} [MeasurableSpace C] [MeasurableSpace K]
    {μ : Measure I} [IsProbabilityMeasure μ]
    {code : I → C} {Φ : C × K → ℝ} {D : Set K}
    (hΦ : Measurable Φ)
    (hnull : ∀ y ∈ D, ∀ᵐ a ∂μ, Φ (code a, y) = 0)
    {n : ℕ} (i : Fin n) (Y : FullTuple I n → K)
    (hYD : ∀ t, Y t ∈ D)
    (hindep : ∀ u v, (∀ j, j ≠ i → u j = v j) → Y u = Y v) :
    ∀ᵐ t ∂orderedMeasure μ n, Φ (code (t i), Y t) = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert hindep
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hindep
      obtain ⟨a₀⟩ := nonempty_of_isProbabilityMeasure μ
      have hsame (a : I) (t : FullTuple I n) :
          Y (FullTuple.cons a t) = Y (FullTuple.cons a₀ t) := by
        apply hindep
        intro j hj
        exact Fin.cases (fun h => False.elim (h rfl))
          (fun _ _ => rfl) j hj
      apply (ae_orderedMeasure_succ μ _).mpr
      have hh := coded_cross_vanishing
        (μ := μ) (ν := orderedMeasure μ n) (code := code)
        (Y := fun t => Y (FullTuple.cons a₀ t))
        Measurable.of_discrete Measurable.of_discrete hΦ
        (fun t => hYD _) hnull
      simpa only [FullTuple.cons_zero, hsame] using hh
    · intro hindep
      apply (ae_orderedMeasure_succ μ _).mpr
      apply Eventually.of_forall
      intro a
      apply ih i (fun t => Y (FullTuple.cons a t)) (fun t => hYD _)
      intro u v huv
      apply hindep
      intro j hj
      refine Fin.cases (fun _ => rfl) (fun k hk => ?_) j hj
      exact huv k (fun hki => hk (congrArg Fin.succ hki))

lemma ae_orderedMeasure_coord (μ : Measure I) [IsProbabilityMeasure μ]
    {n : ℕ} (i : Fin n) (P : I → Prop) :
    (∀ᵐ t ∂orderedMeasure μ n, P (t i)) ↔ ∀ᵐ a ∂μ, P a := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ae_orderedMeasure_succ, FullTuple.cons_zero, eventually_const]
    · simp only [ae_orderedMeasure_succ, FullTuple.cons_succ, ih, eventually_const]


namespace FullTuple
variable {J : Type*} {n : ℕ}
def toList (t : FullTuple J n) : List J := List.ofFn t.val
@[simp] lemma toList_nil : (nil : FullTuple J 0).toList = [] := rfl
@[simp] lemma toList_cons (a : J) (t : FullTuple J n) :
    (cons a t).toList = a :: t.toList := by
  simp only [toList, cons, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
end FullTuple


def GoodPrefix (μ : Measure I) (G : List I → Prop) (p : List I) : Prop :=
  ∀ n, ∀ᵐ t ∂orderedMeasure μ n, G (p ++ t.toList)

lemma goodPrefix_extend (μ : Measure I) [IsProbabilityMeasure μ]
    (G : List I → Prop) (p : List I) (hp : GoodPrefix μ G p) :
    ∃ a, GoodPrefix μ G (p ++ [a]) := by
  have hh : ∀ᵐ a ∂μ, ∀ n, ∀ᵐ t ∂orderedMeasure μ n,
      G ((p ++ [a]) ++ t.toList) := by
    apply ae_all_iff.mpr
    intro n
    have hn := (ae_orderedMeasure_succ μ _).mp (hp (n + 1))
    simpa only [FullTuple.toList_cons, List.append_assoc, List.singleton_append] using hn
  exact hh.exists



lemma exists_good_prefix_sequence (μ : Measure I) [IsProbabilityMeasure μ]
    (G : List I → Prop)
    (hG : ∀ n, ∀ᵐ t ∂orderedMeasure μ n, G t.toList) :
    ∃ α : ℕ → I, ∀ n, G (List.ofFn (fun i : Fin n => α i.val)) := by
  have hstart : GoodPrefix μ G [] := by
    simpa only [GoodPrefix, List.nil_append] using hG
  let S := { p : List I // GoodPrefix μ G p }
  let next : S → I := fun p => Classical.choose (goodPrefix_extend μ G p.1 p.2)
  let step : S → S := fun p => ⟨p.1 ++ [next p],
    Classical.choose_spec (goodPrefix_extend μ G p.1 p.2)⟩
  let chain : ℕ → S := Nat.rec ⟨[], hstart⟩ (fun _ p => step p)
  let α : ℕ → I := fun n => next (chain n)
  have hval : ∀ n, (chain n).1 = List.ofFn (fun i : Fin n => α i.val) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change (chain n).1 ++ [α n] = _
      rw [ih, List.ofFn_succ']
      simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append]
  refine ⟨α, fun n => ?_⟩
  have hh := (ae_orderedMeasure_zero μ _).mp ((chain n).2 0)
  simpa only [FullTuple.toList_nil, List.append_nil, hval] using hh


lemma exists_good_tuple_sequence (μ : Measure I) [IsProbabilityMeasure μ]
    (G : (n : ℕ) → FullTuple I n → Prop)
    (hG : ∀ n, ∀ᵐ t ∂orderedMeasure μ n, G n t) :
    ∃ α : ℕ → I, ∀ n, G n ⟨fun i : Fin n => α i.val⟩ := by
  let goodList : List I → Prop := fun l => G l.length ⟨l.get⟩
  have he (n : ℕ) (t : FullTuple I n) : goodList t.toList ↔ G n t := by
    cases t with
    | mk t =>
      exact Eq.to_iff (congrArg (fun p : Σ n : ℕ, Fin n → I => G p.1 ⟨p.2⟩)
        (List.equivSigmaTuple.apply_symm_apply ⟨n, t⟩))
  have hh : ∀ n, ∀ᵐ t ∂orderedMeasure μ n, goodList t.toList := by
    intro n
    exact (hG n).mono (fun t ht => (he n t).mpr ht)
  obtain ⟨α, hα⟩ := exists_good_prefix_sequence μ goodList hh
  exact ⟨α, fun n => (he n ⟨fun i : Fin n => α i.val⟩).mp (hα n)⟩

end SeparableQuotient.Positive.Sampling

end

end

end OAI
