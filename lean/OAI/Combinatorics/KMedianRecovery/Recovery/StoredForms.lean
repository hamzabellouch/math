import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CountedTrace
import OAI.Combinatorics.KMedianRecovery.Encoding.Matrix

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility
open scoped BigOperators
variable {V R : Type*} [Fintype V] {n : ℕ}

def storedForms (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ) :
    Option (V → ℚ) :=
  (Ellipsoid.Stored.exactSolve (rows.map (fun r => (f r).enumeratedRow e)) B).map
    (fun y v => y (e.symm v))

lemma storedForms_sound (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℚ) (hx : storedForms e rows f B=some x) :
    (∀ r∈rows,(f r).eval x≤0) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp hx
  have hs := Ellipsoid.Stored.exactSolve_some _ B y hy
  exact ⟨fun r hr => ((f r).enumeratedRow_holds e y).mp
    (hs.1 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)),fun j => hs.2 (e.symm j)⟩

lemma storedForms_complete (e : Fin n ≃ V) (rows : List R) (f : R → Form V) (B : ℕ)
    (x : V → ℝ) (hx : ∀ r∈rows,(f r).realEval x≤0) (hb : ∀ j,|x j|≤(B:ℝ)) :
    ∃ y,storedForms e rows f B=some y := by
  have hh : ∀ q∈rows.map (fun r => (f r).enumeratedRow e),q.RealHolds (fun i => x (e i)) := by
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact ((f r).enumeratedRow_realHolds e x).mpr (hx r hr)
  obtain ⟨y,hy⟩ := Ellipsoid.Stored.exactSolve_complete _ B ⟨fun i => x (e i),hh,fun i => hb (e i)⟩
  exact ⟨fun v => y (e.symm v),by simp only [storedForms,hy,Option.map_some]⟩

end MetricKMedianRecovery.RationalLinearFeasibility

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalLinearFeasibility RationalOpenability OpenabilityLinearization

def storedOpening {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam eta : ℚ) (i : Fin m) : Option (Variables (Fin d) F → ℚ) :=
  storedForms (variableEnum d F)
    (kindRows (List.ofFn (fun j : Fin d => j)) (subtypeList W) (subtypeList F))
    (forms distance F W v z lam eta i) ⌈(1+v^2)*z⌉₊

lemma storedOpening_witness {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (x : Variables (Fin d) F → ℚ) (hx : storedOpening distance F W v z lam eta i=some x) :
    Feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i
      (fun j => (x (.inl j):ℝ)) (fun f a j => (x (.inr (f,a,j)):ℝ)) := by
  have hs := (storedForms_sound _ _ _ _ x hx).1
  apply (system_iff loc distance hd F W v z lam eta i (fun j => (x j:ℝ))).mp
  intro k
  rw [←forms_eq loc distance hd,Form.realEval_cast]
  exact_mod_cast hs k (mem_kindRows _ _ _ (by simp) (mem_subtypeList W) (mem_subtypeList F) k)

lemma storedOpening_sound {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (x : Variables (Fin d) F → ℚ) (hx : storedOpening distance F W v z lam eta i=some x) :
    etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  apply (openable_iff_linear_feasible loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mpr
  exact ⟨_,_,storedOpening_witness loc distance hd F W v z lam eta i x hx⟩

lemma storedOpening_complete {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ))
    (h : etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i) :
    ∃ x,storedOpening distance F W v z lam eta i=some x := by
  obtain ⟨tau,y,hf,ht,hy⟩ := (openable_iff_bounded loc F W (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i hv hv1 hz).mp h
  let x : Variables (Fin d) F → ℝ := Sum.elim tau (fun p => y p.1 p.2.1 p.2.2)
  have hx : ∀ k,(forms distance F W v z lam eta i k).realEval x≤0 := by
    rw [forms_eq loc distance hd]
    exact (system_iff loc distance hd F W v z lam eta i x).mpr hf
  have hb : ∀ j,|x j|≤(⌈(1+v^2)*z⌉₊:ℝ) := by
    intro j
    have hh : 0≤x j ∧ x j≤(1+(v:ℝ)^2)*(z:ℝ) := by
      cases j with
      | inl j => exact ht j
      | inr p => exact hy p.1 p.2.1 p.2.2
    rw [abs_of_nonneg hh.1]
    apply hh.2.trans
    have hb := Nat.le_ceil ((1+v^2)*z)
    exact_mod_cast hb
  exact storedForms_complete _ _ _ _ x (fun k _ => hx k) hb

lemma storedOpening_none_iff {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F W : Finset (Fin m)) (v z lam eta : ℚ) (i : Fin m)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(z:ℝ)) :
    storedOpening distance F W v z lam eta i=none ↔
      ¬etaOpenable loc F W (1-3*(v:ℝ)) (1+(v:ℝ)^2) (v:ℝ) (z:ℝ) (lam:ℝ) (eta:ℝ) i := by
  constructor
  · intro hn ho
    obtain ⟨x,hx⟩ := storedOpening_complete loc distance hd F W v z lam eta i hv hv1 hz ho
    simp [hn] at hx
  · intro hn
    cases he : storedOpening distance F W v z lam eta i with
    | none => rfl
    | some x => exact (hn (storedOpening_sound loc distance hd F W v z lam eta i hv hv1 hz x he)).elim

end MetricKMedianRecovery.EffectiveOpenability

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer OpenabilityLinearization

structure State (m d : ℕ) where
  opened : Finset (Fin m)
  phase : ℚ
  budget : Vector ℚ d

structure Event (m d : ℕ) where
  facility : Fin m
  bid : Vector ℚ d

noncomputable def State.real {m d : ℕ} (s : State m d) : ExecutionState (Fin d) (Fin m) :=
  ⟨s.opened,(s.phase:ℝ),fun j => (s.budget[j]:ℝ)⟩

def update {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) : State m d :=
  ⟨insert e.facility s.opened,s.phase,
    Vector.ofFn (fun j => if active distance v s.phase s.opened j then e.bid[j] else s.budget[j])⟩

lemma update_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (e : Event m d) (j : Fin d) :
    (update distance v s e).budget[j] =
      if active distance v s.phase s.opened j then e.bid[j] else s.budget[j] := by
  simp only [update,Fin.getElem_fin,Vector.getElem_ofFn]

lemma update_real {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (v : ℚ) (s : State m d) (e : Event m d) :
    (update distance v s e).real=regularUpdate loc (1-3*(v:ℝ)) s.real e.facility s.opened
      (fun j => (e.bid[j]:ℝ)) := by
  classical
  change ExecutionState.mk (insert e.facility s.opened) (s.phase:ℝ)
      (fun j => (((update distance v s e).budget[j]:ℚ):ℝ)) =
    ExecutionState.mk (insert e.facility s.opened) (s.phase:ℝ)
      (fun j => if activeAt loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened j then
        if activeAt loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened j then (e.bid[j]:ℝ) else (s.phase:ℝ)
        else (s.budget[j]:ℝ))
  congr 1
  funext j
  rw [update_get]
  by_cases hj : active distance v s.phase s.opened j
  · simp only [ite_eq_left hj, ite_eq_left ((active_iff loc distance hd v s.phase s.opened j).mp hj)]
  · simp only [ite_eq_right hj, ite_eq_right (fun h => hj ((active_iff loc distance hd v s.phase s.opened j).mpr h))]

def first {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) : List (Fin m) → Option (Event m d)
  | [] => none
  | i::todo =>
    if i∈F ∧ i∉W then
      match storedOpening distance F W v z lam 0 i with
      | none => first distance F W v z lam todo
      | some x => some ⟨i,Vector.ofFn (fun j => x (.inl j))⟩
    else first distance F W v z lam todo

lemma first_some {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (todo : List (Fin m)) (e : Event m d)
    (he : first distance F W v z lam todo=some e) :
    e.facility∈F ∧ e.facility∉W ∧ ∃ x,
      storedOpening distance F W v z lam 0 e.facility=some x ∧
      ∀ j : Fin d,e.bid[j]=x (.inl j) := by
  induction todo with
  | nil => cases he
  | cons i todo ih =>
    simp only [first] at he
    split at he
    next hi =>
      cases hx : storedOpening distance F W v z lam 0 i with
      | none => rw [hx] at he; exact ih he
      | some x =>
        rw [hx] at he
        have he' : (⟨i,Vector.ofFn (fun j => x (.inl j))⟩ : Event m d)=e := Option.some.inj he
        subst e
        exact ⟨hi.1,hi.2,x,hx,by intro j; simp⟩
    next hi => exact ih he

lemma first_none_iff {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (todo : List (Fin m)) :
    first distance F W v z lam todo=none ↔
      ∀ i∈todo,i∈F → i∉W → storedOpening distance F W v z lam 0 i=none := by
  induction todo with
  | nil => simp [first]
  | cons i todo ih =>
    by_cases hi : i∈F ∧ i∉W
    · simp only [first,ite_eq_left hi]
      cases hx : storedOpening distance F W v z lam 0 i with
      | none =>
        rw [ih]
        constructor
        · intro h j hj hjF hjW
          rcases List.mem_cons.mp hj with rfl|hj
          · exact hx
          · exact h j hj hjF hjW
        · intro h j hj
          exact h j (List.mem_cons_of_mem i hj)
      | some x =>
        constructor
        · intro h; cases h
        · intro h
          have hh := h i List.mem_cons_self hi.1 hi.2
          rw [hx] at hh
          cases hh
    · simp only [first,ite_eq_right hi,ih]
      constructor
      · intro h j hj hjF hjW
        rcases List.mem_cons.mp hj with rfl|hj
        · exact (hi ⟨hjF,hjW⟩).elim
        · exact h j hj hjF hjW
      · intro h j hj
        exact h j (List.mem_cons_of_mem i hj)

lemma first_plain {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ) (s : State m d) (todo : List (Fin m)) (e : Event m d)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(s.phase:ℝ))
    (he : first distance F s.opened v s.phase lam todo=some e) :
    PlainOpening loc F (v:ℝ) (lam:ℝ) s.real (update distance v s e).real := by
  obtain ⟨hi,hin,x,hx,he⟩ := first_some distance F s.opened v s.phase lam todo e he
  have hw := storedOpening_witness loc distance hd F s.opened v s.phase lam 0 e.facility x hx
  have htau : (fun j : Fin d => (e.bid[j]:ℝ))=(fun j => (x (.inl j):ℝ)) := by
    funext j
    rw [he j]
  refine ⟨e.facility,hi,hin,(fun j => (e.bid[j]:ℝ)),?_,?_,?_,update_real loc distance hd v s e⟩
  · rw [htau]
    exact hw.1
  · change (lam:ℝ) ≤ openingPayment loc (1-3*(v:ℝ)) (s.phase:ℝ) s.opened e.facility _
    rw [htau,payment_eq_linear loc s.opened (v:ℝ) (s.phase:ℝ) e.facility _ hv hv1 hz hw.1]
    simpa only [Rat.cast_zero,mul_zero,sub_zero] using hw.2.1
  · intro f hf a ha
    rw [htau,dual_eq]
    have hy := hw.2.2 ⟨f,hf⟩ a ha
    exact (Finset.sum_le_sum (fun j _ => max_le (hy.1 j).2 (hy.1 j).1)).trans hy.2

lemma first_none_maximal {m d : ℕ} [PseudoMetricSpace (Fin m)]
    (loc : Fin d → Fin m) (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,(distance f j:ℝ)=dist f (loc j))
    (F : Finset (Fin m)) (v lam : ℚ) (s : State m d)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hz : (0:ℝ)≤(s.phase:ℝ))
    (he : first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i))=none) :
    PhaseMaximal loc F (v:ℝ) (lam:ℝ) s.real := by
  intro i hi hin
  have hn := (first_none_iff distance F s.opened v s.phase lam _).mp he i (by simp) hi hin
  simpa only [Rat.cast_zero,State.real] using
    (storedOpening_none_iff loc distance hd F s.opened v s.phase lam 0 i hv hv1 hz).mp hn

def finish {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) : ℕ → State m d → State m d × List (Event m d)
  | 0,s => (s,[])
  | fuel+1,s =>
    match first distance F s.opened v s.phase lam (List.ofFn (fun i : Fin m => i)) with
    | none => (s,[])
    | some e =>
      let r := finish distance F v lam fuel (update distance v s e)
      (r.1,e::r.2)

end MetricKMedianRecovery.RationalPhase

end OAI
