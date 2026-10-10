import OAI.ModelTheory.Categoricity.DirectedLimits

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace RelModel

variable {L : ℕ → Type} {M N P : RelModel.{u} L}

def Iso.refl (M : RelModel.{u} L) : M.Iso M := ⟨Equiv.refl _, fun _ _ _ => Iff.rfl⟩

def Iso.symm (e : M.Iso N) : N.Iso M where
  toEquiv := e.toEquiv.symm
  map_rel n s a := by
    have h := e.map_rel n s (e.toEquiv.symm ∘ a)
    simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

def Iso.trans (e : M.Iso N) (f : N.Iso P) : M.Iso P where
  toEquiv := e.toEquiv.trans f.toEquiv
  map_rel n s a := (e.map_rel n s a).trans (f.map_rel n s (e.toEquiv ∘ a))

theorem IsSubstructure.antisymm (h : M.IsSubstructure N) (k : N.IsSubstructure M) : M = N := by
  obtain ⟨A, r⟩ := M
  obtain ⟨B, s⟩ := N
  have he : A = B := ZFSet.ext (fun x => ⟨fun hx => h.subset hx, fun hx => k.subset hx⟩)
  subst B
  congr 1
  funext n c a
  exact propext (h.restrict n c a)

end RelModel

namespace Arrays

open Tuples

variable {M N : Data.{u}}

theorem Data.rawRel_length (s : Symbol) (xs : List M.Carrier) (h : M.rawRel s xs) :
    xs.length = s.arity := by
  unfold Data.rawRel at h
  split at h <;> simp_all [Symbol.arity]

def rawIsoOfTyped (e : M.Carrier ≃ N.Carrier)
    (he : ∀ n (s : Language n) a, N.rel n s (e ∘ a) ↔ M.rel n s a) : RawIso M N where
  toEquiv := e
  relates s xs := by
    by_cases hl : xs.length = s.arity
    · have h := he xs.length ⟨s, hl.symm⟩ xs.get
      simpa only [Data.rel, List.ofFn_get, ← List.map_ofFn] using h
    · constructor
      · intro h
        exact (hl ((List.length_map (f := e) (as := xs)).symm.trans (N.rawRel_length s _ h))).elim
      · intro h
        exact (hl (M.rawRel_length s xs h)).elim

structure Presentation (R : RelModel.{u} Language) where
  data : Data.{u}
  equiv : data.Carrier ≃ R.carrier
  relates : ∀ n (s : Language n) a, R.rel n s (equiv ∘ a) ↔ data.rel n s a

namespace Presentation

variable {R T V : RelModel.{u} Language} (P : Presentation R)

def transport (e : R.Iso T) : Presentation T where
  data := P.data
  equiv := P.equiv.trans e.toEquiv
  relates n s a := (e.map_rel n s (P.equiv ∘ a)).symm.trans (P.relates n s a)

theorem relates_symm (n : ℕ) (s : Language n) (a : Fin n → R.carrier) :
    R.rel n s a ↔ P.data.rel n s (P.equiv.symm ∘ a) := by
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using P.relates n s (P.equiv.symm ∘ a)

def comparison (Q : Presentation R) : RawIso P.data Q.data :=
  rawIsoOfTyped (P.equiv.trans Q.equiv.symm) (fun n s a => by
    have h := Q.relates_symm n s (P.equiv ∘ a)
    exact h.symm.trans (P.relates n s a))

@[simp] theorem comparison_onPoint (Q : Presentation R) (x : P.data.Carrier) :
    (P.comparison Q).toMap.onPoint x = Q.equiv.symm (P.equiv x) :=
  (P.comparison Q).toMap_onPoint x

theorem comparison_strong (Q : Presentation R) (hCH : CH.{u}) :
    (P.comparison Q).toMap.Strong hCH :=
  (P.comparison Q).toMap.strong_of_surjective hCH (P.comparison Q).base_surjective

theorem object_iff (Q : Presentation R) (hCH : CH.{u}) :
    P.data.IsObject hCH ↔ Q.data.IsObject hCH := by
  constructor
  · intro h
    exact (P.comparison Q).toMap.object_of_surjective hCH
      (P.comparison Q).index_surjective (P.comparison Q).base_surjective h
  · intro h
    exact (Q.comparison P).toMap.object_of_surjective hCH
      (Q.comparison P).index_surjective (Q.comparison P).base_surjective h

def isoOfMap (Q : Presentation T) (f : Map P.data Q.data)
    (hf : Function.Surjective f.onPoint) : R.Iso T where
  toEquiv := P.equiv.symm.trans ((Equiv.ofBijective f.onPoint ⟨f.injective, hf⟩).trans Q.equiv)
  map_rel n s a := by
    have h := (P.relates_symm n s a).trans (f.rel n s (P.equiv.symm ∘ a)).symm
    exact h.trans (Q.relates n s (f.onPoint ∘ P.equiv.symm ∘ a)).symm

def Inclusion (Q : Presentation T) (f : Map P.data Q.data) : Prop :=
  ∀ x, (Q.equiv (f.onPoint x)).val = (P.equiv x).val

theorem inclusion_unique {Q : Presentation T} {f g : Map P.data Q.data}
    (hf : P.Inclusion Q f) (hg : P.Inclusion Q g) : f = g := by
  apply Map.ext_onPoint
  intro x
  apply Q.equiv.injective
  apply Subtype.ext
  exact (hf x).trans (hg x).symm

theorem inclusion_refl : P.Inclusion P (Map.id P.data) := by
  intro x
  rw [Map.id_onPoint]

theorem Inclusion.comp {P : Presentation R} {Q : Presentation T} {O : Presentation V}
    {f : Map P.data Q.data} {g : Map Q.data O.data}
    (hg : Q.Inclusion O g) (hf : P.Inclusion Q f) : P.Inclusion O (g.comp f) := by
  intro x
  rw [Map.comp_onPoint]
  exact (hg (f.onPoint x)).trans (hf x)

theorem inclusion_comparison (Q : Presentation R) : P.Inclusion Q (P.comparison Q).toMap := by
  intro x
  rw [comparison_onPoint, Equiv.apply_symm_apply]

theorem Inclusion.substructure {Q : Presentation T} {f : Map P.data Q.data}
    (hf : P.Inclusion Q f) : R.IsSubstructure T := by
  have hsub : R.carrier ⊆ T.carrier := by
    intro x hx
    have he := hf (P.equiv.symm ⟨x, hx⟩)
    simp only [Equiv.apply_symm_apply] at he
    exact he ▸ (Q.equiv (f.onPoint (P.equiv.symm ⟨x, hx⟩))).property
  refine ⟨hsub, fun n s a => ?_⟩
  have he : (fun i => (⟨(a i).val, hsub (a i).property⟩ : T.carrier)) =
      Q.equiv ∘ f.onPoint ∘ P.equiv.symm ∘ a := by
    funext i
    apply Subtype.ext
    change (a i).val = (Q.equiv (f.onPoint (P.equiv.symm (a i)))).val
    simpa only [Equiv.apply_symm_apply] using (hf (P.equiv.symm (a i))).symm
  rw [he, Q.relates, f.rel, ← P.relates_symm]

end Presentation

variable (hCH : CH.{u})

def classData : ClassData.{u} Language where
  objects R := ∃ P : Presentation R, P.data.IsObject hCH
  strong R T := ∃ (P : Presentation R) (Q : Presentation T),
    P.data.IsObject hCH ∧ Q.data.IsObject hCH ∧
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f

namespace AEC

variable {hCH : CH.{u}} {R T V : RelModel.{u} Language}

abbrev Object (R : RelModel.{u} Language) := (classData hCH).objects R
abbrev Strong (R T : RelModel.{u} Language) := (classData hCH).strong R T

theorem strong_objects (h : Strong (hCH := hCH) R T) : Object (hCH := hCH) R ∧ Object (hCH := hCH) T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact ⟨⟨P, hp⟩, ⟨Q, hq⟩⟩

theorem object_presentation (h : Object (hCH := hCH) R) (P : Presentation R) : P.data.IsObject hCH := by
  obtain ⟨Q, hq⟩ := h
  exact (Q.object_iff P hCH).1 hq

theorem strong_rebase (h : Strong (hCH := hCH) R T) (P : Presentation R) (Q : Presentation T) :
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f := by
  obtain ⟨P', Q', hp, hq, f, hf, he⟩ := h
  refine ⟨(Q'.comparison Q).toMap.comp (f.comp (P.comparison P').toMap),
    (Q'.comparison_strong Q hCH).comp hCH (hf.comp hCH (P.comparison_strong P' hCH)), ?_⟩
  exact (Q'.inclusion_comparison Q).comp (he.comp (P.inclusion_comparison P'))

theorem strong_of {P : Presentation R} {Q : Presentation T}
    (hp : P.data.IsObject hCH) (hq : Q.data.IsObject hCH)
    (f : Map P.data Q.data) (hf : f.Strong hCH) (he : P.Inclusion Q f) : Strong (hCH := hCH) R T :=
  ⟨P, Q, hp, hq, f, hf, he⟩

theorem refl (h : Object (hCH := hCH) R) : Strong (hCH := hCH) R R := by
  obtain ⟨P, hp⟩ := h
  exact strong_of hp hp (Map.id P.data) (Map.id_strong hCH _) P.inclusion_refl

theorem substructure (h : Strong (hCH := hCH) R T) : R.IsSubstructure T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact he.substructure P

theorem antisymm (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T R) : R = T :=
  (substructure h).antisymm (substructure k)

theorem trans (h : Strong (hCH := hCH) R T) (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R V := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  obtain ⟨O, ho⟩ := (strong_objects k).2
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  exact strong_of hp ho (g.comp f) (hg.comp hCH hf) (he'.comp he)

theorem iso_objects (h : Object (hCH := hCH) R) (e : R.Iso T) : Object (hCH := hCH) T := by
  obtain ⟨P, hp⟩ := h
  exact ⟨P.transport e, hp⟩

theorem iso_strong {R' T' : RelModel.{u} Language} (h : Strong (hCH := hCH) R T)
    (e : R.Iso R') (f : T.Iso T')
    (he : ∀ x : R.carrier, (e.toEquiv x).val =
      (f.toEquiv ⟨x.val, (substructure h).subset x.property⟩).val) :
    Strong (hCH := hCH) R' T' := by
  obtain ⟨P, Q, hp, hq, g, hg, hinc⟩ := h
  refine strong_of (P := P.transport e) (Q := Q.transport f) hp hq g hg ?_
  intro x
  change (f.toEquiv (Q.equiv (g.onPoint x))).val = (e.toEquiv (P.equiv x)).val
  rw [he]
  congr 2
  exact Subtype.ext (hinc x)

theorem coherence (hsub : R.IsSubstructure T) (h : Strong (hCH := hCH) R V)
    (k : Strong (hCH := hCH) T V) : Strong (hCH := hCH) R T := by
  obtain ⟨P, O, hp, ho, f, hf, he⟩ := h
  obtain ⟨Q, hq⟩ := (strong_objects k).1
  obtain ⟨g, hg, he'⟩ := strong_rebase k Q O
  have hr : ∀ x : P.data.Carrier, ∃ y, g.onPoint y = f.onPoint x := by
    intro x
    let y : T.carrier := ⟨(P.equiv x).val, hsub.subset (P.equiv x).property⟩
    refine ⟨Q.equiv.symm y, O.equiv.injective (Subtype.ext ?_)⟩
    rw [he', he, Equiv.apply_symm_apply]
  obtain ⟨l, hl⟩ := f.factor g hr
  refine strong_of hp hq l (hf.factor hCH hl) ?_
  intro x
  have hv := congrArg (fun m : Map P.data O.data => (O.equiv (m.onPoint x)).val) hl
  rw [Map.comp_onPoint] at hv
  rw [he', he] at hv
  exact hv

end AEC

namespace Coding

variable {X : Type u} {A : ZFSet.{u}}

theorem cardinal (e : X ≃ A) : #X = A.card := by
  apply Cardinal.lift_injective.{u+1}
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift] using (Cardinal.lift_mk_eq'.2 ⟨e⟩)

def universeEquiv (X : Type u) : X ≃ Ordinal.toZFSet (#X).ord := Classical.choice (by
  apply Cardinal.lift_mk_eq'.1
  simp only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Ordinal.card_toZFSet, Cardinal.card_ord])

def rangeEquiv (f : X → ZFSet.{u}) (hf : Function.Injective f) : X ≃ ZFSet.range f :=
  Equiv.ofBijective (fun x => ⟨f x, ZFSet.mem_range.2 ⟨x, rfl⟩⟩) ⟨
    fun _ _ h => hf (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha⟩ := ZFSet.mem_range.1 hx
      exact ⟨a, Subtype.ext ha⟩⟩

def model (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : RelModel.{u} Language where
  carrier := A
  rel n s a := M.rel n s (e.symm ∘ a)

def presentation (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : Presentation (model M A e) where
  data := M
  equiv := e
  relates n s a := by
    change M.rel n s (fun i => e.symm (e (a i))) ↔ _
    simp only [Equiv.symm_apply_apply]

def coded (M : Data.{u}) : RelModel.{u} Language := model M _ (universeEquiv M.Carrier)

def codedPresentation (M : Data.{u}) : Presentation (coded M) :=
  presentation M _ (universeEquiv M.Carrier)

theorem coded_cardinal (M : Data.{u}) : (coded M).carrier.card = #M.Carrier :=
  (cardinal (universeEquiv M.Carrier)).symm

end Coding

namespace AEC

section

variable {hCH : CH.{u}} {R : RelModel.{u} Language}

theorem small (h : Object (hCH := hCH) R) (A : ZFSet.{u}) (hA : A ⊆ R.carrier) :
    ∃ T, Object (hCH := hCH) T ∧ Strong (hCH := hCH) T R ∧
      A ⊆ T.carrier ∧ T.carrier.card ≤ A.card + ℵ₀ := by
  obtain ⟨P, hp⟩ := h
  let S : Set P.data.Carrier := {x | (P.equiv x).val ∈ A}
  let e : S ≃ A := Equiv.ofBijective (fun x => ⟨(P.equiv x.val).val, x.property⟩) ⟨by
    intro a b hab
    apply Subtype.ext
    apply P.equiv.injective
    have hh : (P.equiv a.val).val = (P.equiv b.val).val := congrArg (fun z : A => z.val) hab
    exact Subtype.ext hh, by
    rintro ⟨a, ha⟩
    let x := P.equiv.symm ⟨a, hA ha⟩
    have hx : x ∈ S := by change (P.equiv x).val ∈ A; simpa only [x, Equiv.apply_symm_apply] using ha
    exact ⟨⟨x, hx⟩, Subtype.ext (by simp only [x, Equiv.apply_symm_apply])⟩⟩
  obtain ⟨M, f, hm, hf, hs, hc⟩ := P.data.small_subarray hCH hp S
  let z : M.Carrier → ZFSet.{u} := fun x => (P.equiv (f.onPoint x)).val
  have hz : Function.Injective z := Subtype.val_injective.comp (P.equiv.injective.comp f.injective)
  let eqv := Coding.rangeEquiv z hz
  let T := Coding.model M (ZFSet.range z) eqv
  let Q := Coding.presentation M (ZFSet.range z) eqv
  refine ⟨T, ⟨Q, hm⟩, strong_of (P := Q) (Q := P) hm hp f hf (fun x => rfl), ?_, ?_⟩
  · intro a ha
    have hx : P.equiv.symm ⟨a, hA ha⟩ ∈ S := by
      change (P.equiv (P.equiv.symm _)).val ∈ A
      simpa only [Equiv.apply_symm_apply] using ha
    obtain ⟨x, hx⟩ := hs hx
    exact ZFSet.mem_range.2 ⟨x, by change (P.equiv (f.onPoint x)).val = a; rw [hx]; simp⟩
  · change (ZFSet.range z).card ≤ A.card + ℵ₀
    rw [← Coding.cardinal eqv, ← Coding.cardinal e]
    exact hc

end

variable {hCH : CH.{u}}

theorem directed_union {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J → RelModel.{u} Language) (ho : ∀ i, Object (hCH := hCH) (F i))
    (hs : ∀ i j, i ≤ j → Strong (hCH := hCH) (F i) (F j)) :
    ∃ U, Object (hCH := hCH) U ∧ RelModel.IsUnion F U ∧
      (∀ i, Strong (hCH := hCH) (F i) U) ∧
      (∀ N, Object (hCH := hCH) N → (∀ i, Strong (hCH := hCH) (F i) N) → Strong (hCH := hCH) U N) := by
  classical
  let P (i : J) : Presentation (F i) := (ho i).choose
  have hp (i : J) : (P i).data.IsObject hCH := (ho i).choose_spec
  let maps (i j : J) (h : i ≤ j) : Map (P i).data (P j).data :=
    (strong_rebase (hs i j h) (P i) (P j)).choose
  have hm (i j : J) (h : i ≤ j) : (maps i j h).Strong hCH :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.1
  have hi (i j : J) (h : i ≤ j) : (P i).Inclusion (P j) (maps i j h) :=
    (strong_rebase (hs i j h) (P i) (P j)).choose_spec.2
  let S : System.Data (J := J) := {
    obj := fun i => (P i).data
    map := maps
    map_id := fun i => (P i).inclusion_unique (hi i i le_rfl) (P i).inclusion_refl
    map_comp := fun i j k h h' => (P i).inclusion_unique ((hi j k h').comp (hi i j h)) (hi i k (h.trans h')) }
  have hconv : ∀ i j h, (Set.range (S.map i j h).base).OrdConnected := fun i j h => (hm i j h).convex
  let A : ZFSet.{u} := ZFSet.iUnion (fun i => (F i).carrier)
  let stage (i : J) (x : (S.obj i).Carrier) : A :=
    ⟨((P i).equiv x).val, ZFSet.mem_iUnion.2 ⟨i, ((P i).equiv x).property⟩⟩
  let val : S.X → A := DirectLimit.lift S.pointMap stage (by
    intro i j h x
    apply Subtype.ext
    exact (hi i j h x).symm)
  have hv (i : J) (x : (S.obj i).Carrier) : val (S.point i x) = stage i x := rfl
  have hinj : Function.Injective val := by
    intro x y
    induction x, y using DirectLimit.induction₂ S.pointMap with
    | ih i x y =>
      intro h
      apply congrArg (S.point i)
      apply (P i).equiv.injective
      apply Subtype.ext
      exact congrArg (fun z : A => z.val) h
  have hsurj : Function.Surjective val := by
    intro a
    obtain ⟨i, hai⟩ := ZFSet.mem_iUnion.1 a.property
    refine ⟨S.point i ((P i).equiv.symm ⟨a.val, hai⟩), ?_⟩
    rw [hv]
    apply Subtype.ext
    change ((P i).equiv ((P i).equiv.symm ⟨a.val, hai⟩)).val = a.val
    simp only [Equiv.apply_symm_apply]
  let e : (S.limitData hconv).Carrier ≃ A :=
    (S.equivalence hconv).symm.trans (Equiv.ofBijective val ⟨hinj, hsurj⟩)
  have he (i : J) (x : (S.obj i).Carrier) :
      e ((S.toLimit hconv i).onPoint x) = stage i x := by
    change val ((S.equivalence hconv).symm ((S.toLimit hconv i).onPoint x)) = _
    rw [S.equivalence_symm_stage, hv]
  let U := Coding.model (S.limitData hconv) A e
  let Q := Coding.presentation (S.limitData hconv) A e
  have hu : Q.data.IsObject hCH := S.limit_object hconv hp hm
  have hstage (i : J) : Strong (hCH := hCH) (F i) U :=
    strong_of (P := P i) (Q := Q) (hp i) hu (S.toLimit hconv i)
      (S.toLimit_strong hconv hm i) (fun x => congrArg Subtype.val (he i x))
  refine ⟨U, ⟨Q, hu⟩, ⟨fun i => substructure (hstage i), ?_⟩, hstage, ?_⟩
  · intro x
    exact ZFSet.mem_iUnion.1 x.property
  · intro N hn hc
    obtain ⟨O, ho'⟩ := hn
    let q (i : J) : Map (S.obj i) O.data := (strong_rebase (hc i) (P i) O).choose
    have hq_strong (i : J) : (q i).Strong hCH := (strong_rebase (hc i) (P i) O).choose_spec.1
    have hq_inc (i : J) : (P i).Inclusion O (q i) := (strong_rebase (hc i) (P i) O).choose_spec.2
    have hq (i j : J) (h : i ≤ j) : (q j).comp (S.map i j h) = q i :=
      (P i).inclusion_unique ((hq_inc j).comp (hi i j h)) (hq_inc i)
    let f := S.liftMap hconv q hq
    refine strong_of hu ho' f (S.liftMap_strong hconv q hq hq_strong) ?_
    intro x
    obtain ⟨i, y, rfl⟩ := S.toLimit_covers hconv x
    change (O.equiv ((S.liftMap hconv q hq).onPoint ((S.toLimit hconv i).onPoint y))).val =
      (e ((S.toLimit hconv i).onPoint y)).val
    rw [S.liftMap_stage, he]
    exact hq_inc i y

theorem lsBound : (classData hCH).LSBound ℵ₀ := by
  refine ⟨le_rfl, ?_, ?_⟩
  · simpa only [Cardinal.lift_le_aleph0] using (Cardinal.mk_le_aleph0 (α := Σ n, Language n))
  · exact fun R h A ha => small h A ha

theorem isAEC : (classData hCH).IsAEC where
  strong_objects := strong_objects
  refl := refl
  antisymm := antisymm
  trans := trans
  substructure := substructure
  iso_objects h e := iso_objects h e.some
  iso_strong := iso_strong
  coherence := coherence
  chain_union γ hγ F ho hs := by
    let : Nonempty γ.ToType := Ordinal.nonempty_toType_iff.2 hγ
    exact directed_union F ho hs
  downward := ⟨ℵ₀, lsBound⟩

theorem hasLSNumber : (classData hCH).HasLSNumber ℵ₀ :=
  ⟨lsBound, fun _ h => h.1⟩

end AEC
end Arrays

end CHObstruction

end

end OAI
