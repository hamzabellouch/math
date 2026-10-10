import OAI.Computability.WitnessedChoice.GuardedProgram

namespace OAI


namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

namespace FiniteIteration

variable {X : Type}

def run (f : Finset X → Finset X) : ℕ → Finset X
  | 0 => ∅
  | k+1 => f (run f k)

lemma run_subset (f : Finset X → Finset X) (C : Finset X)
    (hC : ∀ s, s ⊆ C → f s ⊆ C) (k : ℕ) : run f k ⊆ C := by
  induction k with
  | zero => exact Finset.empty_subset C
  | succ k ih => exact hC _ ih

lemma run_step (f : Finset X → Finset X) (hi : ∀ s, s ⊆ f s) (k : ℕ) :
    run f k ⊆ run f (k+1) := hi _

lemma run_comparison (f : Finset X → Finset X) (hi : ∀ s, s ⊆ f s)
    {k : ℕ} (h : ∀ i < k, run f i ≠ run f (i+1)) : k ≤ (run f k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk := h k (by omega)
    have hc := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨run_step f hi k,hk⟩)
    have hh := ih (fun i hi => h i (by omega))
    omega

lemma exists_stationary (f : Finset X → Finset X) (C : Finset X)
    (hi : ∀ s, s ⊆ f s) (hC : ∀ s, s ⊆ C → f s ⊆ C) :
    ∃ t ≤ C.card, run f t = run f (t+1) := by
  by_contra hn
  push Not at hn
  have hs : ∀ i < C.card+1, run f i ≠ run f (i+1) := fun i h => hn i (by omega)
  have hc := run_comparison f hi hs
  have hb := Finset.card_le_card (run_subset f C hC (C.card+1))
  omega

lemma run_stationary_after (f : Finset X → Finset X) {t : ℕ}
    (ht : run f t = run f (t+1)) (k : ℕ) (hk : t ≤ k) : run f k = run f t := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => simp
  | succ l ih =>
    change f (run f (t+l)) = run f t
    rw [ih (by omega)]
    exact ht.symm

lemma run_fixed (f : Finset X → Finset X) (C : Finset X)
    (hi : ∀ s, s ⊆ f s) (hC : ∀ s, s ⊆ C → f s ⊆ C) :
    f (run f C.card) = run f C.card := by
  obtain ⟨t,ht,he⟩ := exists_stationary f C hi hC
  exact (run_stationary_after f he (C.card+1) (by omega)).trans
    (run_stationary_after f he C.card ht).symm

lemma run_least (f : Finset X → Finset X) (hm : Monotone f)
    (s : Finset X) (hs : f s ⊆ s) (k : ℕ) : run f k ⊆ s := by
  induction k with
  | zero => exact Finset.empty_subset s
  | succ k ih => exact (hm ih).trans hs

end FiniteIteration

lemma TC_ofFinset_mono {s t : Finset (HF A)} (h : s ⊆ t) :
    TC (ofFinset s) ⊆ TC (ofFinset t) := by
  simp only [TC,elements_ofFinset]
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem ordinaryIteration_finite (p : ℕ) (f : Finset (HF A) → Finset (HF A))
    (step : HF A → Result (HF A)) (C : Finset (HF A))
    (heval : ∀ s, step (ofFinset s) = some (ofFinset (f s)))
    (hi : ∀ s, s ⊆ f s) (hC : ∀ s, s ⊆ C → f s ⊆ C)
    (htime : C.card ≤ p) (hspace : (TC (ofFinset C)).card ≤ p) :
    ordinaryIteration p step = some (ofFinset (FiniteIteration.run f C.card)) := by
  let F : HF A → HF A := fun x => ofFinset (f (elements x))
  have he (k : ℕ) : (F^[k]) emptyHF = ofFinset (FiniteIteration.run f k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih]
      simp only [F,elements_ofFinset,FiniteIteration.run]
  have hb (k : ℕ) : (TC ((F^[k]) emptyHF)).card ≤ p := by
    rw [he]
    exact (Finset.card_le_card (TC_ofFinset_mono (FiniteIteration.run_subset f C hC k))).trans hspace
  have hf : F ((F^[C.card]) emptyHF) = (F^[C.card]) emptyHF := by
    rw [he]
    simp only [F,elements_ofFinset,FiniteIteration.run_fixed f C hi hC]
  have loop : ∀ t fuel, t < fuel → ∀ s,
      (∀ k ≤ t, (TC ((F^[k]) (ofFinset s))).card ≤ p) →
      F ((F^[t]) (ofFinset s)) = (F^[t]) (ofFinset s) →
      iterationLoop p step fuel (ofFinset s) = some ((F^[t]) (ofFinset s)) := by
    intro t
    induction t with
    | zero =>
      intro fuel hu s hs hstop
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hp := hs 0 (Nat.zero_le 0)
        simp only [Function.iterate_zero,id_eq] at hp hstop ⊢
        rw [iterationLoop,ite_eq_left hp,heval,Option.bind_some]
        have hh : ofFinset s = ofFinset (f s) := by simpa [F] using hstop.symm
        rw [ite_eq_left hh]
    | succ t ih =>
      intro fuel hu s hs hstop
      cases fuel with
      | zero => omega
      | succ fuel =>
        have hp := hs 0 (Nat.zero_le (t+1))
        simp only [Function.iterate_zero,id_eq] at hp
        rw [iterationLoop,ite_eq_left hp,heval,Option.bind_some]
        by_cases hh : ofFinset s = ofFinset (f s)
        · rw [ite_eq_left hh]
          apply congrArg some
          exact ((show Function.IsFixedPt F (ofFinset s) from (by simpa only [Function.IsFixedPt,F,elements_ofFinset] using hh.symm)).iterate (t+1)).symm
        · rw [ite_eq_right hh,Function.iterate_succ_apply]
          have hFs : F (ofFinset s) = ofFinset (f s) := by simp only [F,elements_ofFinset]
          rw [hFs]
          apply ih fuel (by omega) (f s)
          · intro k hk
            have h := hs (k+1) (by omega)
            simpa only [Function.iterate_succ_apply,F,elements_ofFinset] using h
          · simpa only [Function.iterate_succ_apply,F,elements_ofFinset] using hstop
  have hh := loop C.card (p+1) (by omega) ∅ (fun k _ => hb k) hf
  change iterationLoop p step (p+1) emptyHF = _
  change iterationLoop p step (p+1) emptyHF = some ((F^[C.card]) emptyHF) at hh
  rw [he] at hh
  exact hh

end

end WitnessedChoice.BGS



namespace WitnessedChoice.BGS.BFS

noncomputable section

open Classical SimpleGraph

variable {V : Type} [Fintype V]

abbrev Item (V : Type) (k : ℕ) := V × V × Fin (k+1)

def update (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) : Finset (Item V k) :=
  R ∪ Finset.univ.filter (fun x => x.1 = x.2.1 ∧ x.2.2.val = 0) ∪
    Finset.univ.filter (fun x => ∃ u : V, ∃ j : Fin (k+1),
      (x.1,u,j) ∈ R ∧ x.2.2.val = j.val+1 ∧ (u = x.2.1 ∨ G.Adj u x.2.1))

@[simp] lemma mem_update (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) (x : Item V k) :
    x ∈ update G k R ↔ (x ∈ R ∨ (x.1 = x.2.1 ∧ x.2.2.val = 0)) ∨
      ∃ u : V, ∃ j : Fin (k+1), (x.1,u,j) ∈ R ∧ x.2.2.val = j.val+1 ∧
        (u = x.2.1 ∨ G.Adj u x.2.1) := by simp [update,or_assoc]

lemma update_inflationary (G : SimpleGraph V) (k : ℕ) (R : Finset (Item V k)) : R ⊆ update G k R := by
  intro x hx
  exact (mem_update G k R x).mpr (Or.inl (Or.inl hx))

lemma update_mono (G : SimpleGraph V) (k : ℕ) : Monotone (update G k) := by
  intro R S h x hx
  rcases (mem_update G k R x).mp hx with (hx|hx)|⟨u,j,hm,he,ha⟩
  · exact (mem_update G k S x).mpr (Or.inl (Or.inl (h hx)))
  · exact (mem_update G k S x).mpr (Or.inl (Or.inr hx))
  · exact (mem_update G k S x).mpr (Or.inr ⟨u,j,h hm,he,ha⟩)

def closure (G : SimpleGraph V) (k : ℕ) : Finset (Item V k) :=
  FiniteIteration.run (update G k) (Fintype.card (Item V k))

lemma closure_fixed (G : SimpleGraph V) (k : ℕ) : update G k (closure G k) = closure G k := by
  exact FiniteIteration.run_fixed (update G k) Finset.univ (update_inflationary G k)
    (fun _ _ => Finset.subset_univ _)

lemma closure_nil (G : SimpleGraph V) (k : ℕ) (v : V) : (v,v,0) ∈ closure G k := by
  rw [← closure_fixed]
  exact (mem_update _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl,rfl⟩))

lemma closure_step (G : SimpleGraph V) {k : ℕ} {v u w : V} {i j : Fin (k+1)}
    (hm : (v,u,j) ∈ closure G k) (he : i.val = j.val+1) (ha : u=w ∨ G.Adj u w) :
    (v,w,i) ∈ closure G k := by
  rw [← closure_fixed]
  exact (mem_update _ _ _ _).mpr (Or.inr ⟨u,j,hm,he,ha⟩)

def good (G : SimpleGraph V) (k : ℕ) : Finset (Item V k) :=
  Finset.univ.filter (fun x => ∃ w : G.Walk x.1 x.2.1, w.length ≤ x.2.2.val)

lemma update_good (G : SimpleGraph V) (k : ℕ) : update G k (good G k) ⊆ good G k := by
  intro x hx
  rcases x with ⟨v,w,i⟩
  simp only [good,Finset.mem_filter,Finset.mem_univ,true_and]
  rcases (mem_update _ _ _ _).mp hx with (hx|⟨hvw,hi⟩)|⟨u,j,hj,he,(hu|ha)⟩
  · simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  · dsimp at hvw hi
    subst w
    exact ⟨.nil,by simp⟩
  · dsimp at hu he
    subst w
    obtain ⟨p,hp⟩ := (show ∃ p : G.Walk v u, p.length ≤ j.val by simpa [good] using hj)
    exact ⟨p,by omega⟩
  · dsimp at he
    obtain ⟨p,hp⟩ := (show ∃ p : G.Walk v u, p.length ≤ j.val by simpa [good] using hj)
    exact ⟨p.concat ha,by simp only [Walk.length_concat]; omega⟩

lemma closure_sound (G : SimpleGraph V) (k : ℕ) : closure G k ⊆ good G k :=
  FiniteIteration.run_least _ (update_mono G k) _ (update_good G k) _

lemma closure_walk (G : SimpleGraph V) {k : ℕ} {v w : V} (p : G.Walk v w)
    (hp : p.length ≤ k) : (v,w,(⟨p.length,by omega⟩ : Fin (k+1))) ∈ closure G k := by
  induction p using Walk.concatRec with
  | Hnil => exact closure_nil G k _
  | @Hconcat u v w p ha ih =>
    apply closure_step G (ih (by simp only [Walk.length_concat] at hp; omega))
    · simp only [Walk.length_concat]
    · exact Or.inr ha

lemma closure_pad (G : SimpleGraph V) {k : ℕ} {v w : V} {j : Fin (k+1)}
    (hj : (v,w,j) ∈ closure G k) (t : ℕ) (ht : j.val+t ≤ k) :
    (v,w,(⟨j.val+t,by omega⟩ : Fin (k+1))) ∈ closure G k := by
  induction t with
  | zero => simpa using hj
  | succ t ih =>
    apply closure_step G (ih (by omega))
    · dsimp; omega
    · exact Or.inl rfl

lemma mem_closure_iff (G : SimpleGraph V) (k : ℕ) (v w : V) (i : Fin (k+1)) :
    (v,w,i) ∈ closure G k ↔ ∃ p : G.Walk v w, p.length ≤ i.val := by
  constructor
  · intro h
    simpa only [good,Finset.mem_filter,Finset.mem_univ,true_and] using closure_sound G k h
  · rintro ⟨p,hp⟩
    have hp' : p.length ≤ k := by omega
    have h := closure_pad G (closure_walk G p hp') (i.val-p.length) (by dsimp; omega)
    have he : (⟨p.length+(i.val-p.length),by omega⟩ : Fin (k+1)) = i := Fin.ext (by dsimp; omega)
    simpa only [he] using h

lemma closure_reachable (G : SimpleGraph V) (k : ℕ) (hk : Fintype.card V ≤ k)
    (v w : V) : (v,w,Fin.last k) ∈ closure G k ↔ G.Reachable v w := by
  rw [mem_closure_iff]
  constructor
  · rintro ⟨p,_⟩
    exact ⟨p⟩
  · intro h
    obtain ⟨p,hp⟩ := h.exists_isPath
    exact ⟨p,Nat.le_trans (Nat.le_of_lt hp.length_lt) hk⟩

end

end WitnessedChoice.BGS.BFS



namespace WitnessedChoice.BGS

noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A : Type}

theorem iterationLoop_stationary (p : ℕ) (f : HF A → HF A)
    (step : HF A → Result (HF A)) (heval : ∀ x, step x = some (f x))
    (t fuel : ℕ) (hfu : t < fuel) (x : HF A)
    (hsize : ∀ k ≤ t, (TC ((f^[k]) x)).card ≤ p)
    (hstop : f ((f^[t]) x) = (f^[t]) x) :
    iterationLoop p step fuel x = some ((f^[t]) x) := by
  have hx : (TC x).card ≤ p := by simpa using hsize 0 (Nat.zero_le t)
  induction t generalizing fuel x with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [Function.iterate_zero, id_eq] at hstop ⊢
      rw [iterationLoop,ite_eq_left hx,heval,Option.bind_some,ite_eq_left hstop.symm]
  | succ t ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      rw [iterationLoop,ite_eq_left hx,heval,Option.bind_some]
      by_cases h : x = f x
      · rw [ite_eq_left h]
        congr 1
        exact ((show Function.IsFixedPt f x from h.symm).iterate (t+1)).symm
      · rw [ite_eq_right h]
        rw [Function.iterate_succ_apply]
        apply ih fuel (by omega) (f x)
        · intro k hk
          rw [← Function.iterate_succ_apply]
          exact hsize (k+1) (by omega)
        · simpa only [Function.iterate_succ_apply] using hstop
        · simpa using hsize 1 (by omega)

theorem ordinaryIteration_stationary (p : ℕ) (f : HF A → HF A)
    (step : HF A → Result (HF A)) (heval : ∀ x, step x = some (f x))
    (t : ℕ) (ht : t ≤ p)
    (hsize : ∀ k ≤ t, (TC ((f^[k]) emptyHF)).card ≤ p)
    (hstop : f ((f^[t]) emptyHF) = (f^[t]) emptyHF) :
    ordinaryIteration p step = some ((f^[t]) emptyHF) :=
  iterationLoop_stationary p f step heval t (p+1) (by omega) emptyHF hsize hstop

end



noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

variable {A X : Type} [Fintype X]

theorem ordinaryIteration_encoded (p : ℕ) (code : X → HF A)
    (f : Finset X → Finset X) (F : HF A → HF A) (step : HF A → Result (HF A))
    (hstep : ∀ x, step x = some (F x))
    (hcode : ∀ s, F (ofFinset (s.image code)) = ofFinset ((f s).image code))
    (hi : ∀ s, s ⊆ f s) (htime : Fintype.card X ≤ p)
    (hspace : (TC (ofFinset (Finset.univ.image code))).card ≤ p) :
    ordinaryIteration p step = some (ofFinset
      ((FiniteIteration.run f (Fintype.card X)).image code)) := by
  have he (k : ℕ) : (F^[k]) emptyHF = ofFinset ((FiniteIteration.run f k).image code) := by
    induction k with
    | zero => simp only [Function.iterate_zero,id_eq,FiniteIteration.run,Finset.image_empty,emptyHF]
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,hcode]
      rfl
  have hf : F ((F^[Fintype.card X]) emptyHF) = (F^[Fintype.card X]) emptyHF := by
    rw [he,hcode]
    have hh := FiniteIteration.run_fixed f (Finset.univ : Finset X) hi
      (fun _ _ => Finset.subset_univ _)
    simpa only [Finset.card_univ] using
      congrArg (fun s => ofFinset (s.image code)) hh
  have hs (k : ℕ) : (TC ((F^[k]) emptyHF)).card ≤ p := by
    rw [he]
    exact (Finset.card_le_card (TC_ofFinset_mono (Finset.image_subset_image
      (Finset.subset_univ _)))).trans hspace
  have h := ordinaryIteration_stationary p F step hstep (Fintype.card X) htime (fun k _ => hs k) hf
  rwa [he] at h

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {n : ℕ} {A : Type} [Fintype A] (S : Input A) (env : Fin n → HF A)

def HFTriple (u v i : HF A) : HF A := Hereditary.pair u (Hereditary.pair v i)

omit [Fintype A] in
lemma HFTriple_injective {u v i u' v' i' : HF A} :
    HFTriple u v i = HFTriple u' v' i' ↔ u=u' ∧ v=v' ∧ i=i' := by
  simp only [HFTriple,pair_eq_pair]

@[simp] lemma mem_distanceBase (V : QuotedTerm n) (z : HF A) :
    z ∈ elements ((distanceBase V).meaning S env) ↔
      ∃ v ∈ elements (V.meaning S env), HFTriple v v emptyHF = z := by
  simp [distanceBase,HFTriple]

@[simp] lemma mem_distanceFresh (V J R : QuotedTerm n) (z : HF A) :
    z ∈ elements ((distanceFresh V J R).meaning S env) ↔
    ∃ v ∈ elements (V.meaning S env), ∃ w ∈ elements (V.meaning S env),
      ∃ i ∈ elements (ordinal (A := A) (Fintype.card A+1)),
        ofFinset (insert i (elements i)) ∈ elements (ordinal (A := A) (Fintype.card A+1)) ∧
        (∃ u ∈ elements (V.meaning S env),
          HFTriple v u i ∈ elements (R.meaning S env) ∧
          (u=w ∨ (QuotedFormula.adjacent J.up.up (.var 0) (.var 1)).meaning S
            (Fin.cons u (Fin.cons w env)))) ∧
        HFTriple v w (ofFinset (insert i (elements i))) = z := by
  simp [distanceFresh,HFTriple,QuotedFormula.adjacent,and_assoc]

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

open QuotedTerm

variable {A V : Type} [Fintype A] [Fintype V]

def blockIncident (S : Input A) (v e : HF A) : Prop :=
  ∃ t ∈ elements v, ∃ s ∈ elements e, inputHF S .I t s = true

def blockAdjacent (S : Input A) (J u v : HF A) : Prop :=
  u ≠ v ∧ ∃ e ∈ elements J, blockIncident S u e ∧ blockIncident S v e

def distanceCode (code : V → HF A) (x : BFS.Item V (Fintype.card A)) : HF A :=
  HFTriple (code x.1) (code x.2.1) (ordinal x.2.2.val)

omit [Fintype V] in
lemma distanceCode_injective (code : V → HF A) (hc : Function.Injective code) :
    Function.Injective (distanceCode code) := by
  rintro ⟨u,v,i⟩ ⟨u',v',i'⟩ h
  obtain ⟨hu,hv,hi⟩ := HFTriple_injective.mp h
  have := hc hu
  have := hc hv
  have := Fin.ext (ordinal_injective hi)
  congr

omit [Fintype A] [Fintype V] in
lemma ordinal_mem_elements (i j : ℕ) : ordinal (A := A) i ∈ elements (ordinal j) ↔ i<j := by
  change ordinal i ∈ ordinal (A := A) j ↔ _
  rw [mem_ordinal]
  simp only [ordinal_injective.eq_iff]
  aesop

lemma distanceStep_encoded {n : ℕ} (S : Input A) (env : Fin n → HF A)
    (VT J R : QuotedTerm n) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V)
    (hV : VT.meaning S env = ofFinset (Finset.univ.image code))
    (hJ : ∀ u v, blockAdjacent S (J.meaning S env) (code u) (code v) ↔ G.Adj u v)
    (r : Finset (BFS.Item V (Fintype.card A)))
    (hR : R.meaning S env = ofFinset (r.image (distanceCode code))) :
    (distanceStep VT J R).meaning S env =
      ofFinset ((BFS.update G (Fintype.card A) r).image (distanceCode code)) := by
  simp only [distanceStep,meaning_cup,hR,elements_ofFinset]
  apply ofFinset_inj.mpr
  ext z
  simp only [Finset.mem_union,Finset.mem_image,mem_distanceBase,mem_distanceFresh,
    hV,hR,elements_ofFinset,Finset.mem_univ,true_and]
  constructor
  · rintro ((⟨x,hx,hz⟩ | ⟨_,⟨v,rfl⟩,hz⟩) | ⟨_,⟨v,rfl⟩,_,⟨w,rfl⟩,i,hi,hs,hm,hz⟩)
    · exact ⟨x,(BFS.mem_update _ _ _ _).mpr (Or.inl (Or.inl hx)),hz⟩
    · exact ⟨(v,v,0),(BFS.mem_update _ _ _ _).mpr (Or.inl (Or.inr ⟨rfl,rfl⟩)),hz⟩
    · obtain ⟨j,hj,rfl⟩ := (mem_ordinal i (Fintype.card A+1)).mp hi
      change ordinal (j+1) ∈ elements (ordinal (A := A) (Fintype.card A+1)) at hs
      have hs' := (ordinal_mem_elements (A := A) _ _).mp hs
      obtain ⟨_,⟨u,rfl⟩,hm,ha⟩ := hm
      obtain ⟨y,hy,he⟩ := hm
      rcases y with ⟨v',u',i'⟩
      obtain ⟨hev,heu,hei⟩ := HFTriple_injective.mp he
      have ev := hc hev
      have eu := hc heu
      have ei := ordinal_injective hei
      dsimp at ev eu ei
      subst v'
      subst u'
      have hadj : u=w ∨ G.Adj u w := by
        rcases ha with ha | ha
        · exact Or.inl (hc ha)
        · exact Or.inr ((hJ u w).mp (by
            simpa only [QuotedFormula.meaning_adjacent,meaning_up,meaning_var,
              Fin.cons_zero,Fin.cons_one,blockAdjacent,blockIncident] using ha))
      refine ⟨(v,w,⟨j+1,hs'⟩),(BFS.mem_update _ _ _ _).mpr
        (Or.inr ⟨u,i',hy,?_,hadj⟩),hz⟩
      dsimp
      omega
  · rintro ⟨x,hx,rfl⟩
    rcases x with ⟨v,w,i⟩
    rcases (BFS.mem_update _ _ _ _).mp hx with (hx | ⟨he,hi⟩) | ⟨u,j,hj,he,ha⟩
    · exact Or.inl (Or.inl ⟨(v,w,i),hx,rfl⟩)
    · dsimp at he hi
      subst w
      have hi' : i = 0 := Fin.ext hi
      subst i
      exact Or.inl (Or.inr ⟨code v,⟨v,rfl⟩,rfl⟩)
    · apply Or.inr
      refine ⟨code v,⟨v,rfl⟩,code w,⟨w,rfl⟩,ordinal j.val,
        (ordinal_mem_elements (A := A) _ _).mpr j.isLt,?_,?_,?_⟩
      · change ordinal (j.val+1) ∈ elements (ordinal (A := A) (Fintype.card A+1))
        apply (ordinal_mem_elements (A := A) _ _).mpr
        dsimp at he
        omega
      · refine ⟨code u,⟨u,rfl⟩,⟨(v,u,j),hj,rfl⟩,?_⟩
        rcases ha with rfl | ha
        · exact Or.inl rfl
        · apply Or.inr
          simpa only [QuotedFormula.meaning_adjacent,meaning_up,meaning_var,Fin.cons_zero,
            Fin.cons_one,blockAdjacent,blockIncident] using (hJ u w).mpr ha
      · change HFTriple (code v) (code w) (ordinal (j.val+1)) =
          HFTriple (code v) (code w) (ordinal i.val)
        congr 2
        exact he.symm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace CPTTerm

variable {n : ℕ} {A V : Type} [Fintype A] [Fintype V]

theorem distance_value (VT J : CPTTerm n) (S : Input A) (p : Polynomial ℝ)
    (env : Fin n → HF A) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V)
    (hV : VT.value S p env = ofFinset (Finset.univ.image code))
    (hJ : ∀ u v, blockAdjacent S (J.value S p env) (code u) (code v) ↔ G.Adj u v)
    (htime : Fintype.card (BFS.Item V (Fintype.card A)) ≤ resource p (Fintype.card A))
    (hspace : (TC (ofFinset (Finset.univ.image (distanceCode code)))).card ≤
      resource p (Fintype.card A)) :
    (distance VT J).value S p env =
      ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)) := by
  simp only [distance,value_letIn,value_up]
  apply value_eq
  rw [eval_iterate]
  apply ordinaryIteration_encoded _ (distanceCode code) (BFS.update G (Fintype.card A)) _ _
    (fun _ => rfl) _ (BFS.update_inflationary G _) htime hspace
  intro r
  simp only [value_quoted]
  apply distanceStep_encoded S _ (.var 2) (.var 1) (.var 0) code hc G
  · exact hV
  · exact hJ
  · rfl

end CPTTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary QuotedTerm

namespace QuotedFormula

variable {n : ℕ} {A : Type} [Fintype A]

@[simp] lemma meaning_allFin (S : Input A) (env : Fin n → HF A) (k : ℕ)
    (f : Fin k → QuotedFormula n) : (allFin k f).meaning S env ↔ ∀ i, (f i).meaning S env := by
  simp [allFin]

@[simp] lemma meaning_anyList (S : Input A) (env : Fin n → HF A) (l : List (QuotedFormula n)) :
    (anyList l).meaning S env ↔ ∃ q ∈ l, q.meaning S env := by
  induction l with
  | nil => simp [anyList,falsehood,truth]
  | cons q l ih => simp [anyList,ih]

@[simp] lemma meaning_anyFin (S : Input A) (env : Fin n → HF A) (k : ℕ)
    (f : Fin k → QuotedFormula n) : (anyFin k f).meaning S env ↔ ∃ i, (f i).meaning S env := by
  simp [anyFin]

end QuotedFormula

variable {A V : Type} [Fintype A] [Fintype V]

lemma coded_closure_mem (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (u v : V) (i : ℕ) (hi : i ≤ Fintype.card A) :
    HFTriple (code u) (code v) (ordinal i) ∈
      elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔
    ∃ w : G.Walk u v, w.length ≤ i := by
  change distanceCode code (u,v,(⟨i,by omega⟩ : Fin (Fintype.card A+1))) ∈ _ ↔ _
  rw [elements_ofFinset,Finset.mem_image]
  constructor
  · rintro ⟨x,hx,he⟩
    have := distanceCode_injective code hc he
    subst x
    exact (BFS.mem_closure_iff G _ u v _).mp hx
  · intro h
    exact ⟨_,(BFS.mem_closure_iff G _ u v _).mpr h,rfl⟩

lemma coded_closure_mem_dist (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (u v : V) (i : ℕ) (hi : i ≤ Fintype.card A) :
    HFTriple (code u) (code v) (ordinal i) ∈
      elements (ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ↔
    G.dist u v ≤ i := by
  rw [coded_closure_mem code hc G u v i hi]
  constructor
  · rintro ⟨w,hw⟩
    exact (G.dist_le w).trans hw
  · intro hi
    obtain ⟨w,hw⟩ := hG.exists_walk_length_eq_dist u v
    exact ⟨w,hw ▸ hi⟩

namespace QuotedTerm

variable {n : ℕ}

theorem meaning_distanceAt (S : Input A) (env : Fin n → HF A)
    (R ut vt : QuotedTerm n) (code : V → HF A) (hc : Function.Injective code)
    (G : SimpleGraph V) (hG : G.Connected) (u v : V)
    (hR : R.meaning S env = ofFinset ((BFS.closure G (Fintype.card A)).image (distanceCode code)))
    (hu : ut.meaning S env = code u) (hv : vt.meaning S env = code v)
    (hcard : Fintype.card V ≤ Fintype.card A) :
    (distanceAt R ut vt).meaning S env = ordinal (G.dist u v) := by
  obtain ⟨w,hw,hwd⟩ := (hG u v).exists_path_of_dist
  have hd : G.dist u v ≤ Fintype.card A := by
    rw [← hwd]
    exact (Nat.le_of_lt hw.length_lt).trans hcard
  simp only [distanceAt,meaning_unique,meaning_filter,meaning_indices,
    QuotedFormula.meaning_and,QuotedFormula.meaning_mem,meaning_triple,
    meaning_up,hu,hv,hR,meaning_var,Fin.cons_zero,QuotedFormula.meaning_allIn,
    QuotedFormula.meaning_imp,QuotedFormula.meaning_neg,Fin.cons_one]
  have hf : ((elements (ordinal (A := A) (Fintype.card A+1))).filter fun z =>
      HFTriple (code u) (code v) z ∈ elements (ofFinset
        ((BFS.closure G (Fintype.card A)).image (distanceCode code))) ∧
      ∀ y ∈ elements (ordinal (Fintype.card A+1)), y ∈ elements z →
        HFTriple (code u) (code v) y ∉ elements (ofFinset
          ((BFS.closure G (Fintype.card A)).image (distanceCode code)))) =
      {ordinal (G.dist u v)} := by
    ext z
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,hmem,hmin⟩
      obtain ⟨i,hi,rfl⟩ := (mem_ordinal z _).mp hz
      have him := (coded_closure_mem_dist code hc G hG u v i (by omega)).mp hmem
      have hie : i = G.dist u v := by
        by_contra h
        have hlt : G.dist u v < i := by omega
        exact hmin _ ((ordinal_mem_elements _ _).mpr (by omega))
          ((ordinal_mem_elements _ _).mpr hlt)
          ((coded_closure_mem_dist code hc G hG u v _ hd).mpr le_rfl)
      rw [hie]
    · intro hz
      subst z
      refine ⟨(ordinal_mem_elements _ _).mpr (by omega),
        (coded_closure_mem_dist code hc G hG u v _ hd).mpr le_rfl,?_⟩
      intro y hy hlt hm
      obtain ⟨i,hi,rfl⟩ := (mem_ordinal y _).mp hy
      have hil := (ordinal_mem_elements _ _).mp hlt
      have him := (coded_closure_mem_dist code hc G hG u v i (by omega)).mp hm
      omega
  change uniqueHF (ofFinset _) = _
  simp only [HFTriple] at hf
  trans uniqueHF (ofFinset {ordinal (G.dist u v)})
  · congr 2
    ext z
    simpa [HFTriple] using (Finset.ext_iff.mp hf z)
  · exact uniqueHF_singleton _

end QuotedTerm

end





noncomputable section

open Classical WitnessedSeparation WitnessedSeparation.Hereditary

namespace QuotedTerm

variable {A : Type} [Fintype A] {n : ℕ}

def firstHF (x : HF A) : HF A := uniqueHF (unionHF (ofFinset
  ((elements x).filter (fun z => cardHF z = ordinal 1))))

def secondHF (x : HF A) : HF A :=
  if cardHF (unionHF x) = ordinal 1 then firstHF x else
    uniqueHF (ofFinset ((elements (unionHF x)).filter
      (fun z => z ∉ elements (Hereditary.singleton (firstHF x)))))

@[simp] lemma meaning_fst (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n) :
    a.fst.meaning S env = firstHF (a.meaning S env) := by
  simp [fst,firstHF]

@[simp] lemma meaning_snd (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n) :
    a.snd.meaning S env = secondHF (a.meaning S env) := by
  simp [snd,secondHF,meaning_cond]

lemma firstHF_pair (S : Input A) (x y : HF A) :
    firstHF (Hereditary.pair x y) = x := by
  have h := meaning_fst_pair S (Fin.cons x (Fin.cons y Fin.elim0)) (var 0) (var 1)
  simpa only [meaning_fst,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one] using h

lemma secondHF_pair (S : Input A) (x y : HF A) :
    secondHF (Hereditary.pair x y) = y := by
  have h := meaning_snd_pair S (Fin.cons x (Fin.cons y Fin.elim0)) (var 0) (var 1)
  simpa only [meaning_snd,meaning_pair,meaning_var,Fin.cons_zero,Fin.cons_one] using h

lemma meaning_fst_of_eq (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (x y : HF A) (h : a.meaning S env = Hereditary.pair x y) :
    a.fst.meaning S env = x := by rw [meaning_fst,h,firstHF_pair S]

lemma meaning_snd_of_eq (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (x y : HF A) (h : a.meaning S env = Hereditary.pair x y) :
    a.snd.meaning S env = y := by rw [meaning_snd,h,secondHF_pair S]

lemma meaning_component_tuple (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    (l : List (HF A)) (h : a.meaning S env = tupleCode l) (i : ℕ) (hi : i < l.length) :
    (a.component i).meaning S env = l[i] := by
  induction l generalizing a i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => exact meaning_fst_of_eq S env a x (tupleCode l) h
    | succ i =>
      have he := meaning_snd_of_eq S env a x (tupleCode l) h
      exact ih a.snd he i (by simpa using hi)

lemma meaning_component_ofFn (S : Input A) (env : Fin n → HF A) (a : QuotedTerm n)
    {k : ℕ} (f : Fin k → HF A) (h : a.meaning S env = tupleCode (List.ofFn f)) (i : Fin k) :
    (a.component i.val).meaning S env = f i := by
  simpa [List.getElem_ofFn] using meaning_component_tuple S env a (List.ofFn f) h i.val
    (by simp)

end QuotedTerm

end

end WitnessedChoice.BGS



namespace WitnessedChoice.TreeTest

noncomputable section

open Classical

structure RootedTree (V : Type) where
  root : V
  parent : V → V
  level : V → ℕ
  parent_lower : ∀ v, v ≠ root → level (parent v) < level v

namespace RootedTree

variable {V A : Type} (T : RootedTree V)

def Adj (v w : V) : Prop :=
  (v ≠ T.root ∧ T.parent v = w) ∨ (w ≠ T.root ∧ T.parent w = v)

theorem adj_symm {v w : V} (h : T.Adj v w) : T.Adj w v := h.symm

theorem parent_adj (v : V) (h : v ≠ T.root) : T.Adj v (T.parent v) := Or.inl ⟨h,rfl⟩

variable (B : V → Finset A) (rel : V → V → A → A → Prop)
  (hroot : (B T.root).Nonempty)
  (hext : ∀ v, v ≠ T.root → ∀ a ∈ B (T.parent v), ∃ b ∈ B v, rel (T.parent v) v a b)

def label (v : V) : {a : A // a ∈ B v} :=
  if hv : v = T.root then
    ⟨hroot.choose, hv ▸ hroot.choose_spec⟩
  else
    let u := label (T.parent v)
    let h := hext v hv u.val u.property
    ⟨h.choose, h.choose_spec.1⟩
termination_by T.level v
decreasing_by exact T.parent_lower v hv

lemma label_parent (v : V) (hv : v ≠ T.root) :
    rel (T.parent v) v (T.label B rel hroot hext (T.parent v)).val
      (T.label B rel hroot hext v).val := by
  conv_rhs => rw [label]
  simp only [dite_eq_right hv]
  exact (hext v hv _ (T.label B rel hroot hext (T.parent v)).property).choose_spec.2

theorem exists_labels
    (nonempty : ∀ v, (B v).Nonempty)
    (support : ∀ v w, T.Adj v w → ∀ a ∈ B v, ∃ b ∈ B w, rel v w a b)
    (symm : ∀ v w a b, rel v w a b → rel w v b a) :
    ∃ t : V → A, (∀ v, t v ∈ B v) ∧ ∀ v w, T.Adj v w → rel v w (t v) (t w) := by
  let he := fun v hv a ha => support (T.parent v) v (T.adj_symm (T.parent_adj v hv)) a ha
  let t := fun v => (T.label B rel (nonempty T.root) he v).val
  refine ⟨t, fun v => (T.label B rel (nonempty T.root) he v).property, ?_⟩
  intro v w h
  rcases h with ⟨hv, rfl⟩ | ⟨hw, rfl⟩
  · exact symm _ _ _ _ (T.label_parent B rel (nonempty T.root) he v hv)
  · exact T.label_parent B rel (nonempty T.root) he w hw

end RootedTree

structure Problem (V A : Type) where
  tree : RootedTree V
  configs : Finset A
  block : V → Finset A
  block_subset : ∀ v, block v ⊆ configs
  block_unique : ∀ v w a, a ∈ block v → a ∈ block w → v = w
  allowed : A → Prop
  compatible : V → V → A → A → Prop
  compatible_symm : ∀ v w a b, compatible v w a b → compatible w v b a

namespace Problem

variable {V A : Type} (P : Problem V A)

def update (S : Finset A) : Finset A := S ∪ P.configs.filter (fun a =>
  ¬ P.allowed a ∨ ∃ v, a ∈ P.block v ∧ ∃ w, P.tree.Adj v w ∧
    ¬ ∃ b ∈ P.block w, b ∉ S ∧ P.compatible v w a b)

def run : ℕ → Finset A
  | 0 => ∅
  | k+1 => P.update (run k)

lemma le_update (S : Finset A) : S ⊆ P.update S := Finset.subset_union_left

lemma update_subset {S : Finset A} (h : S ⊆ P.configs) : P.update S ⊆ P.configs :=
  Finset.union_subset h (Finset.filter_subset _ _)

lemma run_subset (k : ℕ) : P.run k ⊆ P.configs := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih => exact P.update_subset ih

lemma run_step (k : ℕ) : P.run k ⊆ P.run (k+1) := P.le_update _

lemma run_comparison {k : ℕ} (h : ∀ i < k, P.run i ≠ P.run (i+1)) : k ≤ (P.run k).card := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    have hk := h k (by omega)
    have hc : (P.run k).card < (P.run (k+1)).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨P.run_step k, hk⟩)
    have hi := ih (fun i hi => h i (by omega))
    omega

lemma exists_stationary : ∃ t ≤ P.configs.card, P.run t = P.run (t+1) := by
  by_contra hn
  push Not at hn
  have hstrict : ∀ i < P.configs.card + 1, P.run i ≠ P.run (i+1) := fun i hi => hn i (by omega)
  have hc := P.run_comparison hstrict
  have hb := Finset.card_le_card (P.run_subset (P.configs.card+1))
  omega

lemma run_stationary_after {t : ℕ} (ht : P.run t = P.run (t+1)) :
    ∀ k, t ≤ k → P.run k = P.run t := by
  intro k hk
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction l with
  | zero => simp
  | succ l ih =>
    change P.update (P.run (t+l)) = P.run t
    rw [ih (by omega)]
    exact ht.symm

def deleted : Finset A := P.run P.configs.card

lemma deleted_fixed : P.update P.deleted = P.deleted := by
  obtain ⟨t, ht, he⟩ := P.exists_stationary
  have h0 := P.run_stationary_after he P.configs.card ht
  have h1 := P.run_stationary_after he (P.configs.card+1) (by omega)
  exact h1.trans h0.symm

def survivors (v : V) : Finset A := (P.block v).filter (· ∉ P.deleted)

lemma mem_survivors {a : A} {v : V} : a ∈ P.survivors v ↔ a ∈ P.block v ∧ a ∉ P.deleted := by
  simp only [survivors, Finset.mem_filter]

lemma survival_allowed {v : V} {a : A} (ha : a ∈ P.survivors v) : P.allowed a := by
  obtain ⟨ha, hn⟩ := P.mem_survivors.mp ha
  by_contra he
  apply hn
  rw [← P.deleted_fixed]
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨P.block_subset v ha, Or.inl he⟩

lemma survival_support {v w : V} (hw : P.tree.Adj v w) {a : A} (ha : a ∈ P.survivors v) :
    ∃ b ∈ P.survivors w, P.compatible v w a b := by
  obtain ⟨ha, hn⟩ := P.mem_survivors.mp ha
  by_contra he
  have he' : ¬ ∃ b ∈ P.block w, b ∉ P.deleted ∧ P.compatible v w a b := by
    rintro ⟨b, hb, hnd, hc⟩
    exact he ⟨b, P.mem_survivors.mpr ⟨hb, hnd⟩, hc⟩
  apply hn
  rw [← P.deleted_fixed]
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨P.block_subset v ha, Or.inr ⟨v, ha, w, hw, he'⟩⟩

def Solution (t : V → A) : Prop :=
  (∀ v, t v ∈ P.block v ∧ P.allowed (t v)) ∧
    ∀ v w, P.tree.Adj v w → P.compatible v w (t v) (t w)

lemma solution_survives {t : V → A} (ht : P.Solution t) : ∀ k v, t v ∉ P.run k := by
  intro k
  induction k with
  | zero => simp [run]
  | succ k ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ih v hv
    · obtain ⟨_, hdel⟩ := Finset.mem_filter.mp hv
      rcases hdel with hna | ⟨v', hv', w, hw, hns⟩
      · exact hna (ht.1 v).2
      · have hh : v' = v := P.block_unique v' v (t v) hv' (ht.1 v).1
        subst v'
        exact hns ⟨t w, (ht.1 w).1, ih w, ht.2 v w hw⟩

theorem all_survive_iff_solution :
    (∀ v, (P.survivors v).Nonempty) ↔ ∃ t, P.Solution t := by
  constructor
  · intro h
    obtain ⟨t, ht, hcomp⟩ := P.tree.exists_labels P.survivors P.compatible h
      (fun _ _ hw _ ha => P.survival_support hw ha) P.compatible_symm
    exact ⟨t, ⟨fun v => ⟨(P.mem_survivors.mp (ht v)).1, P.survival_allowed (ht v)⟩, hcomp⟩⟩
  · rintro ⟨t, ht⟩ v
    exact ⟨t v, P.mem_survivors.mpr ⟨(ht.1 v).1, P.solution_survives ht _ v⟩⟩

end Problem

end

end WitnessedChoice.TreeTest

end OAI
