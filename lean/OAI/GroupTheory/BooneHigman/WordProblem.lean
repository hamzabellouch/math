import OAI.GroupTheory.BooneHigman.Basic

namespace OAI

/-!
Effective finite presentations, decidable word problem in simple groups, and the reverse implication.
-/

namespace FiniteAlgebraicEnvelopes

universe u

namespace WordProblem

open Primrec

def reduceStep {n : ℕ} (p : (Fin n × Bool) × Word n) : Word n :=
  List.casesOn p.2 [p.1] fun hd tl =>
    if p.1.1 = hd.1 ∧ p.1.2 = !hd.2 then tl else p.1 :: hd :: tl

theorem reduceStep_primrec (n : ℕ) : Primrec (@reduceStep n) := by
  unfold reduceStep
  refine Primrec.list_casesOn (h := fun (p q : (Fin n × Bool) × Word n) =>
    if p.1.1 = q.1.1 ∧ p.1.2 = !q.1.2 then q.2 else p.1 :: q.1 :: q.2)
    Primrec.snd (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) ?_
  unfold Primrec₂
  apply Primrec.ite
  · apply PrimrecPred.and
    · exact Primrec.eq.comp (Primrec.fst.comp <| Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp <| Primrec.fst.comp Primrec.snd)
    · exact Primrec.eq.comp (Primrec.snd.comp <| Primrec.fst.comp Primrec.fst)
        (Primrec.not.comp <| Primrec.snd.comp <| Primrec.fst.comp Primrec.snd)
  · exact Primrec.snd.comp Primrec.snd
  · exact Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

theorem reduce_primrec (n : ℕ) : Primrec (@FreeGroup.reduce (Fin n) _) := by
  have h := Primrec.list_rec (h := fun (_ : Word n) p => reduceStep (p.1, p.2.2))
    Primrec.id (Primrec.const [])
    ((reduceStep_primrec n).comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)))
  exact h

/-- A finite product of signed conjugates is a certificate for normal closure. -/
abbrev Factor (n m : ℕ) := Word n × Fin m × Bool
abbrev Certificate (n m : ℕ) := List (Factor n m)

def factorWord {n m : ℕ} (r : Fin m → Word n) (c : Factor n m) : Word n :=
  c.1 ++ (if c.2.2 then r c.2.1 else FreeGroup.invRev (r c.2.1)) ++
    FreeGroup.invRev c.1

def certificateWord {n m : ℕ} (r : Fin m → Word n) (cs : Certificate n m) : Word n :=
  (cs.map (factorWord r)).flatten

def factorValue {n m : ℕ} (r : Fin m → Word n) (c : Factor n m) : FreeGroup (Fin n) :=
  FreeGroup.mk c.1 * (if c.2.2 then FreeGroup.mk (r c.2.1) else
    (FreeGroup.mk (r c.2.1))⁻¹) * (FreeGroup.mk c.1)⁻¹

def certificateValue {n m : ℕ} (r : Fin m → Word n) (cs : Certificate n m) :
    FreeGroup (Fin n) := (cs.map (factorValue r)).prod

theorem mk_factorWord {n m} (r : Fin m → Word n) (c : Factor n m) :
    FreeGroup.mk (factorWord r c) = factorValue r c := by
  simp only [factorWord, factorValue, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  cases c.2.2 <;> rfl

theorem mk_certificateWord {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    FreeGroup.mk (certificateWord r cs) = certificateValue r cs := by
  induction cs with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons c cs ih =>
    simpa only [certificateWord, certificateValue, List.map_cons, List.flatten_cons,
      List.prod_cons, ← FreeGroup.mul_mk, mk_factorWord] using
      congrArg (factorValue r c * ·) ih

def flipFactor {n m} (c : Factor n m) : Factor n m := (c.1, c.2.1, !c.2.2)

theorem factorValue_flip {n m} (r : Fin m → Word n) (c : Factor n m) :
    factorValue r (flipFactor c) = (factorValue r c)⁻¹ := by
  rcases c with ⟨w, i, b⟩
  cases b <;> simp [factorValue, flipFactor]

theorem certificateValue_inv {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    certificateValue r (cs.reverse.map flipFactor) = (certificateValue r cs)⁻¹ := by
  simp only [certificateValue, List.map_map, List.prod_inv_reverse, List.map_reverse,
    Function.comp_def, factorValue_flip]

theorem certificateValue_mem {n m} (r : Fin m → Word n) (cs : Certificate n m) :
    certificateValue r cs ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
  apply (inferInstance : (Subgroup.normalClosure
    (Set.range fun i => FreeGroup.mk (r i))).Normal).conj_mem
  split <;> rename_i hb
  · exact Subgroup.subset_normalClosure ⟨c.2.1, rfl⟩
  · exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure ⟨c.2.1, rfl⟩)

theorem mem_normalClosure_iff_certificate {n m} (r : Fin m → Word n)
    (g : FreeGroup (Fin n)) :
    g ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) ↔
      ∃ cs : Certificate n m, certificateValue r cs = g := by
  refine ⟨fun hg => ?_, fun ⟨cs, heq⟩ => heq ▸ certificateValue_mem r cs⟩
  apply Subgroup.closure_induction (k := Group.conjugatesOfSet _)
    (p := fun x _ => ∃ cs : Certificate n m, certificateValue r cs = x) ?_ ?_ ?_ ?_ hg
  · intro x hx
    obtain ⟨y, ⟨i, rfl⟩, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hxy
    refine ⟨[(FreeGroup.toWord c, i, true)], ?_⟩
    simp [certificateValue, factorValue, FreeGroup.mk_toWord]
  · exact ⟨[], rfl⟩
  · rintro x y _ _ ⟨cx, rfl⟩ ⟨cy, rfl⟩
    exact ⟨cx ++ cy, by simp [certificateValue]⟩
  · rintro x _ ⟨cx, rfl⟩
    exact ⟨cx.reverse.map flipFactor, certificateValue_inv r cx⟩

theorem invRev_primrec (n : ℕ) : Primrec (@FreeGroup.invRev (Fin n)) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.not.comp <| Primrec.snd.comp Primrec.snd)

theorem factorWord_primrec (n m : ℕ) : Primrec₂ (@factorWord n m) := by
  unfold factorWord Primrec₂
  apply Primrec.list_append.comp
  · apply Primrec.list_append.comp
    · exact Primrec.fst.comp Primrec.snd
    · apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd)
        (Primrec.const true))
      · exact Primrec.fin_app.comp Primrec.fst (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
      · exact (invRev_primrec n).comp (Primrec.fin_app.comp Primrec.fst
          (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd))
  · exact (invRev_primrec n).comp (Primrec.fst.comp Primrec.snd)

theorem certificateWord_primrec (n m : ℕ) : Primrec₂ (@certificateWord n m) := by
  unfold certificateWord Primrec₂
  apply Primrec.list_flatten.comp
  exact Primrec.list_map Primrec.snd ((factorWord_primrec n m).comp (Primrec.fst.comp Primrec.fst)
    Primrec.snd)

/-- The certificate verifier is primitive recursive, including free reduction. -/
theorem verifies_primrec (n m : ℕ) : PrimrecPred
    (fun p : (Fin m → Word n) × Word n × Certificate n m =>
      certificateValue p.1 p.2.2 = FreeGroup.mk p.2.1) := by
  refine (Primrec.eq.comp
    ((reduce_primrec n).comp ((certificateWord_primrec n m).comp Primrec.fst
      (Primrec.snd.comp Primrec.snd)))
    ((reduce_primrec n).comp (Primrec.fst.comp Primrec.snd))).of_eq ?_
  intro p
  exact ⟨fun h => (mk_certificateWord p.1 p.2.2).symm.trans (FreeGroup.reduce.exact h),
    fun h => FreeGroup.reduce.sound ((mk_certificateWord p.1 p.2.2).trans h)⟩

/-- Unbounded search over encoded certificates gives a genuine semidecision. -/
theorem re_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α × β → Prop} (hp : ComputablePred p) : REPred (fun a => ∃ b, p (a,b)) := by
  obtain ⟨d, hc⟩ := hp
  let _ := d
  let test (a : α) (k : ℕ) : Bool :=
    ((Encodable.decode (α := β) k).map (fun b => decide (p (a,b)))).getD false
  have ht : Computable₂ test :=
    Computable.option_getD
      (Computable.option_map (Computable.decode.comp Computable.snd)
        (hc.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).to₂)
      (Computable.const false)
  refine (Partrec.dom_re (Partrec.rfind ht.partrec₂)).of_eq ?_
  intro a
  simp only [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := β) k with
    | none => simp [test, hd] at hk
    | some b => exact ⟨b, by simpa [test, hd] using hk⟩
  · rintro ⟨b, hb⟩
    exact ⟨Encodable.encode b, by simp [test, Encodable.encodek, hb]⟩

/-- Normal closure of any finite tuple of formal relators is uniformly r.e. -/
theorem normalClosure_re (n m : ℕ) : REPred
    (fun p : (Fin m → Word n) × Word n =>
      FreeGroup.mk p.2 ∈ Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (p.1 i))) := by
  have hp : ComputablePred (fun p : ((Fin m → Word n) × Word n) × Certificate n m =>
      certificateValue p.1.1 p.2 = FreeGroup.mk p.1.2) :=
    ((verifies_primrec n m).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).computablePred
  exact (re_exists hp).of_eq fun p => (mem_normalClosure_iff_certificate p.1 (FreeGroup.mk p.2)).symm

/-- Add one relator, uniformly effectively in that relator. -/
theorem consRelators_primrec {n m} (r : Fin m → Word n) :
    Primrec (fun w : Word n => Fin.cons (α := fun _ : Fin (m+1) => Word n) w r) := by
  apply Primrec.fin_curry.mpr
  apply Primrec₂.swap
  apply Primrec.fin_curry₁.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Primrec.id
  · exact Primrec.const (r j)

/-- In a simple quotient, adjoining a nontrivial word to the defining relators
kills every element, while adjoining a trivial word changes nothing. -/
theorem nontrivial_iff_normalClosure {H : Type*} [Group H] [IsSimpleGroup H]
    {n m} (φ : FreeGroup (Fin n) →* H) (hφ : Function.Surjective φ)
    (r : Fin m → Word n)
    (hr : Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) = φ.ker)
    (v : Word n) (hv : φ (FreeGroup.mk v) ≠ 1) (w : Word n) :
    φ (FreeGroup.mk w) ≠ 1 ↔
      FreeGroup.mk v ∈ Subgroup.normalClosure
        (Set.range fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) := by
  let S := Set.range fun i => FreeGroup.mk (r i)
  have hset : (Set.range fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) =
      insert (FreeGroup.mk w) S := by
    rw [show (fun i => FreeGroup.mk (Fin.cons (α := fun _ : Fin (m+1) => Word n) w r i)) =
      Fin.cons (α := fun _ : Fin (m+1) => FreeGroup (Fin n)) (FreeGroup.mk w) (fun i => FreeGroup.mk (r i)) by
        funext i; refine Fin.cases rfl (fun _ => rfl) i, Fin.range_cons]
  rw [hset]
  let N := Subgroup.normalClosure (insert (FreeGroup.mk w) S)
  have hker : φ.ker ≤ N := by
    rw [← hr]
    exact Subgroup.normalClosure_mono (Set.subset_insert _ _)
  have hwn : FreeGroup.mk w ∈ N := Subgroup.subset_normalClosure (Set.mem_insert _ _)
  constructor
  · intro hw
    have hn := (inferInstance : N.Normal).map φ hφ
    have htop : N.map φ = ⊤ := by
      rcases hn.eq_bot_or_eq_top with hb | ht
      · have he := (N.map_eq_bot_iff.mp hb) hwn
        exact False.elim (hw he)
      · exact ht
    have : N = ⊤ := by
      rw [← Subgroup.comap_map_eq_self hker, htop, Subgroup.comap_top]
    change FreeGroup.mk v ∈ N
    rw [this]; trivial
  · intro hvn hw
    have hle : N ≤ φ.ker := Subgroup.normalClosure_le_normal (by
      intro x hx
      rcases hx with rfl | hx
      · exact hw
      · rw [← hr]
        exact Subgroup.subset_normalClosure hx)
    exact hv (hle hvn)

/-- Parallel enumeration of the two normal-closure certificates decides equality. -/
theorem simple_presentation_computable {H : Type*} [Group H] [IsSimpleGroup H]
    {n m} (φ : FreeGroup (Fin n) →* H) (hφ : Function.Surjective φ)
    (r : Fin m → Word n)
    (hr : Subgroup.normalClosure (Set.range fun i => FreeGroup.mk (r i)) = φ.ker) :
    ComputablePred (fun w : Word n => φ (FreeGroup.mk w) = 1) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : H)
  obtain ⟨g, rfl⟩ := hφ a
  let v := FreeGroup.toWord g
  have hv : φ (FreeGroup.mk v) ≠ 1 := by simpa only [v, FreeGroup.mk_toWord] using ha
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  constructor
  · have hh := (normalClosure_re n m).comp
      (Computable.pair (Computable.const r) Computable.id)
    exact REPred.of_eq hh fun w => by
      dsimp only [Function.comp_def, id]
      rw [hr]; rfl
  · have hh := (normalClosure_re n (m+1)).comp
      (Computable.pair (consRelators_primrec r).to_comp (Computable.const v))
    exact REPred.of_eq hh fun w =>
      (nontrivial_iff_normalClosure φ hφ r hr v hv w).symm

theorem evalWord_eq_lift {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s w = FreeGroup.lift s (FreeGroup.mk w) := by
  simp only [evalWord, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a.2 <;> rfl

theorem hom_mk_eval {H : Type*} [Group H] {n} (φ : FreeGroup (Fin n) →* H)
    (w : Word n) : φ (FreeGroup.mk w) = evalWord (fun i => φ (FreeGroup.of i)) w := by
  rw [evalWord_eq_lift]
  exact FreeGroup.lift_unique φ (fun _ => rfl)

/-- The classical converse in Theorem 1.1, for the ambient simple group. -/
theorem finitelyPresentedSimple_wordProblem (H : Type*) [Group H]
    [Group.IsFinitelyPresented H] [IsSimpleGroup H] : HasDecidableWordProblem H := by
  classical
  obtain ⟨n, φ, hφ, S, hS, hker⟩ := Group.IsFinitelyPresented.out (G := H)
  let := hS.fintype
  let m := Fintype.card S
  let e : S ≃ Fin m := Fintype.equivFin S
  let r : Fin m → Word n := fun i => FreeGroup.toWord (e.symm i).val
  have hrel : (Set.range fun i => FreeGroup.mk (r i)) = S := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      simpa only [r, FreeGroup.mk_toWord] using (e.symm i).property
    · intro hg
      refine ⟨e ⟨g, hg⟩, ?_⟩
      simp only [r, Equiv.symm_apply_apply, FreeGroup.mk_toWord]
  refine ⟨n, (fun i => φ (FreeGroup.of i)), ?_, ?_⟩
  · rw [← FreeGroup.range_lift_eq_closure]
    have he : FreeGroup.lift (fun i => φ (FreeGroup.of i)) = φ := by ext i; simp
    rw [he]
    exact MonoidHom.range_eq_top.mpr hφ
  · exact (simple_presentation_computable φ hφ r (hrel.symm ▸ hker)).of_eq
      fun w => by rw [hom_mk_eval]

/-- Effective replacement of each generator by a fixed finite word. -/
def substitute {n m} (r : Fin n → Word m) (w : Word n) : Word m :=
  (w.map fun a => if a.2 then r a.1 else FreeGroup.invRev (r a.1)).flatten

theorem substitute_primrec {n m} (r : Fin n → Word m) : Primrec (substitute r) := by
  unfold substitute
  apply Primrec.list_flatten.comp
  apply Primrec.list_map Primrec.id
  apply Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true))
  · exact Primrec.fin_app.comp (Primrec.const r) (Primrec.fst.comp Primrec.snd)
  · exact (invRev_primrec m).comp (Primrec.fin_app.comp (Primrec.const r)
      (Primrec.fst.comp Primrec.snd))

theorem evalWord_append {H : Type*} [Group H] {n} (s : Fin n → H) (v w : Word n) :
    evalWord s (v ++ w) = evalWord s v * evalWord s w := by
  simp only [evalWord, List.map_append, List.prod_append]

theorem evalWord_invRev {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s (FreeGroup.invRev w) = (evalWord s w)⁻¹ := by
  simp only [evalWord_eq_lift, ← FreeGroup.inv_mk, map_inv]

theorem evalWord_substitute {H : Type*} [Group H] {n m}
    (s : Fin m → H) (r : Fin n → Word m) (w : Word n) :
    evalWord s (substitute r w) = evalWord (fun i => evalWord s (r i)) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change evalWord s ((if a.2 then r a.1 else FreeGroup.invRev (r a.1)) ++ substitute r w) =
      (if a.2 then evalWord s (r a.1) else (evalWord s (r a.1))⁻¹) *
        evalWord (fun i => evalWord s (r i)) w
    rw [evalWord_append, ih]
    congr 1
    cases a with
    | mk i b => cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, evalWord_invRev]

theorem evalWord_map {G H : Type*} [Group G] [Group H] {n} (f : G →* H)
    (s : Fin n → G) (w : Word n) : f (evalWord s w) = evalWord (fun i => f (s i)) w := by
  simp only [evalWord, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro a _
  split <;> simp_all only [map_inv]

/-- Word problem descends along embeddings of finitely generated groups. -/
theorem wordProblem_of_injective {G H : Type*} [Group G] [Group H] [Group.FG G]
    (f : G →* H) (hf : Function.Injective f) (hH : HasDecidableWordProblem H) :
    HasDecidableWordProblem G := by
  classical
  obtain ⟨m, t, ht, hc⟩ := hH
  obtain ⟨S, hSgen, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let := hSfin.fintype
  let n := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let s : Fin n → G := fun i => (e.symm i).val
  have hs : Set.range s = S := by
    ext g
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (e.symm i).property,
      fun hg => ⟨e ⟨g, hg⟩, by simp [s]⟩⟩
  have hsurj := FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr ht
  choose v hv using fun i : Fin n => hsurj (f (s i))
  let r : Fin n → Word m := fun i => FreeGroup.toWord (v i)
  have hr (i) : evalWord t (r i) = f (s i) := by
    rw [evalWord_eq_lift]
    change FreeGroup.lift t (FreeGroup.mk (FreeGroup.toWord (v i))) = _
    rw [FreeGroup.mk_toWord, hv]
  refine ⟨n, s, hs ▸ hSgen, ?_⟩
  have hh : ComputablePred (fun w : Word n => evalWord t (substitute r w) = 1) :=
    ⟨inferInstance, hc.decide.comp (substitute_primrec r).to_comp⟩
  exact hh.of_eq fun w => by
    rw [evalWord_substitute, show (fun i => evalWord t (r i)) = (fun i => f (s i)) from funext hr,
      ← evalWord_map, ← map_one f]
    exact hf.eq_iff

end WordProblem

/-- The complete reverse implication of the main theorem. -/
theorem main_reverse (G : Type u) [Group G] [Group.FG G]
    (hG : EmbedsInFinitelyPresentedSimpleGroup G) : HasDecidableWordProblem G := by
  obtain ⟨H, hH, hfp, hsimple, f, hf⟩ := hG
  let _ := hH
  let _ := hfp
  let _ := hsimple
  exact WordProblem.wordProblem_of_injective f hf (WordProblem.finitelyPresentedSimple_wordProblem H)

end FiniteAlgebraicEnvelopes

end OAI
