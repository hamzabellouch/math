import OAI.CategoryTheory.Globular.Coglobular

namespace OAI

universe u v w

namespace Grothendieck
open CategoryTheory CategoryTheory.Limits Opposite
namespace Shape

def linearHeight (n k : ℕ) : ℕ := if k < n then k else n+1

theorem linearHeight_lt (n b k : ℕ) (hb : b < n) (hk : b < k) :
    b < linearHeight n k := by
  unfold linearHeight
  split_ifs <;> omega

theorem linear_adjacent_realization (n k : ℕ) (hk : k ≤ n) (ε : Bool) :
    (if ε then (linearGlobularDiagram n).target k (by omega)
       else (linearGlobularDiagram n).source k (by omega)) =
      realization.map (linearAdjacent n k hk ε) := by
  cases ε <;> rfl

theorem linear_face_low (n b k : ℕ) (h : b < k) (hk : k < n) (ε : Bool) :
    (linearGlobularDiagram n).face h (by omega) ε =
      realization.map (eqToHom (linearBlock_low n b (by omega)) ≫
        face h ε ≫ eqToHom (linearBlock_low n k hk).symm) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases eb : b = k
    · subst b
      rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
      congr 1
      simp only [linearAdjacent, dite_eq_left (by omega : k < n), dite_eq_left hk]
    · have hb : b < k := by omega
      rw [← (linearGlobularDiagram n).face_adjacent hb (by omega) ε false,
        ih hb (by omega), linear_adjacent_realization _ _ (by omega)]
      change realization.map _ ≫ realization.map _ = realization.map _
      rw [← Functor.map_comp]
      congr 1
      simp only [linearAdjacent, dite_eq_left (by omega : k < n), dite_eq_left hk]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp]

theorem linear_face_center (n b : ℕ) (h : b < n) (ε : Bool) :
    (linearGlobularDiagram n).face h (by omega) ε =
      realization.map (eqToHom (linearBlock_low n b h) ≫
        face (by omega : b < n+1) ε ≫ eqToHom (linearBlock_center n n rfl).symm) := by
  cases n with
  | zero => omega
  | succ n =>
    by_cases eb : b = n
    · subst b
      rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
      congr 1
      simp only [linearAdjacent, dite_eq_left (Nat.lt_succ_self n), dite_eq_right (lt_irrefl (n+1))]
    · have hb : b < n := by omega
      rw [← (linearGlobularDiagram (n+1)).face_adjacent hb (by omega) ε false,
        linear_face_low _ _ _ hb (by omega), linear_adjacent_realization _ _ (by omega)]
      change realization.map _ ≫ realization.map _ = realization.map _
      rw [← Functor.map_comp]
      congr 1
      simp only [linearAdjacent, dite_eq_left (Nat.lt_succ_self n), dite_eq_right (lt_irrefl (n+1))]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← Category.assoc (face _ ε), face_comp]

theorem linear_face_top (n : ℕ) (ε : Bool) :
    (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl ε =
      realization.map (eqToHom (linearBlock_center n n rfl) ≫
        (if ε then GlobularTheory.tripleLast n else GlobularTheory.tripleFirst n) ≫
        eqToHom (linearBlock_high n (n+1) (Nat.lt_succ_self n)).symm) := by
  rw [FiniteCoGlobularObject.face_succ, linear_adjacent_realization _ _ (by omega)]
  congr 1
  simp only [linearAdjacent, dite_eq_right (lt_irrefl n)]

theorem linear_face_top_low (n b : ℕ) (h : b < n) (ε : Bool) :
    (linearGlobularDiagram n).face (by omega : b < n+1) le_rfl ε =
      realization.map (eqToHom (linearBlock_low n b h) ≫
        face (by omega : b < n+1) ε ≫ GlobularTheory.tripleLast n ≫
        eqToHom (linearBlock_high n (n+1) (Nat.lt_succ_self n)).symm) := by
  rw [← (linearGlobularDiagram n).face_adjacent h le_rfl ε true,
    linear_face_center, linear_adjacent_realization _ _ (by omega)]
  change realization.map _ ≫ realization.map _ = realization.map _
  rw [← Functor.map_comp]
  congr 1
  simp only [linearAdjacent, dite_eq_right (lt_irrefl n), ↓reduceIte]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

theorem isPushout_attach (S : Shape) (b h : ℕ) (hl : b < S.1) (hr : b < h) :
    IsPushout (S.seam hl) (face hr false) (S.inl b h hl hr) (S.inr b h hl hr) := by
  have H := realization_pushout S b h hl hr
  apply IsPushout.mk'
  · exact H.w
  · intro T f g hi hj
    exact H.hom_ext hi hj
  · intro T f g hw
    exact ⟨H.desc f g hw, H.inl_desc _ _ _, H.inr_desc _ _ _⟩

end Shape
namespace GlobularTheory

theorem composition_isPushout (n : ℕ) :
    IsPushout (Shape.target n) (Shape.source n) (compositionLeft n) (compositionRight n) := by
  have h := Shape.isPushout_attach (Shape.globe (n+1)) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change IsPushout (Shape.target n ≫ 𝟙 _) (Shape.source n) (compositionLeft n) (compositionRight n) at h
  simpa only [Category.comp_id] using h

noncomputable def triplePrefix (n : ℕ) : compositionShape n ⟶ tripleShape n :=
  (compositionShape n).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

theorem triple_isPushout (n : ℕ) :
    IsPushout (Shape.target n ≫ compositionRight n) (Shape.source n)
      (triplePrefix n) (tripleLast n) := Shape.isPushout_attach _ _ _ _ _

noncomputable def tripleDesc {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S)
    (hab : Shape.target n ≫ a = Shape.source n ≫ b)
    (hbc : Shape.target n ≫ b = Shape.source n ≫ c) : tripleShape n ⟶ S :=
  (triple_isPushout n).desc ((composition_isPushout n).desc a b hab) c (by
    rw [Category.assoc, IsPushout.inr_desc]
    exact hbc)

@[reassoc (attr := simp)] theorem tripleDesc_first {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleFirst n ≫ tripleDesc n a b c hab hbc = a := by
  change (compositionLeft n ≫ triplePrefix n) ≫ tripleDesc n a b c hab hbc = a
  rw [tripleDesc, Category.assoc, IsPushout.inl_desc, IsPushout.inl_desc]

@[reassoc (attr := simp)] theorem tripleDesc_middle {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleMiddle n ≫ tripleDesc n a b c hab hbc = b := by
  change (compositionRight n ≫ triplePrefix n) ≫ tripleDesc n a b c hab hbc = b
  rw [tripleDesc, Category.assoc, IsPushout.inl_desc, IsPushout.inr_desc]

@[reassoc (attr := simp)] theorem tripleDesc_last {S : Shape} (n : ℕ)
    (a b c : Shape.globe (n+1) ⟶ S) (hab) (hbc) :
    tripleLast n ≫ tripleDesc n a b c hab hbc = c := by
  exact (triple_isPushout n).inr_desc _ _ _

theorem triple_hom_ext {S : Shape} (n : ℕ) {f g : tripleShape n ⟶ S}
    (h₀ : tripleFirst n ≫ f = tripleFirst n ≫ g)
    (h₁ : tripleMiddle n ≫ f = tripleMiddle n ≫ g)
    (h₂ : tripleLast n ≫ f = tripleLast n ≫ g) : f = g := by
  apply (triple_isPushout n).hom_ext
  · apply (composition_isPushout n).hom_ext
    · exact (Category.assoc _ _ _).symm.trans (h₀.trans (Category.assoc _ _ _))
    · exact (Category.assoc _ _ _).symm.trans (h₁.trans (Category.assoc _ _ _))
  · exact h₂

end GlobularTheory
namespace Shape

open GlobularTheory

noncomputable def lastArrow (S : Shape) : globe S.1 ⟶ S := S.last

abbrev appendTwo (n : ℕ) (T : Table (n+1)) : Shape :=
  (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).attach
    n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoOld (n : ℕ) (T : Table (n+1)) : ⟨n+1,T⟩ ⟶ appendTwo n T :=
  inl ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) ≫
    (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inl
      n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoMiddle (n : ℕ) (T : Table (n+1)) : globe (n+1) ⟶ appendTwo n T :=
  inr ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) ≫
    (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inl
      n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoLast (n : ℕ) (T : Table (n+1)) : globe (n+1) ⟶ appendTwo n T :=
  (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).inr
    n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)

noncomputable def appendTwoTail (n : ℕ) (T : Table (n+1)) : tripleShape n ⟶ appendTwo n T :=
  tripleDesc n (lastArrow ⟨n+1,T⟩ ≫ appendTwoOld n T) (appendTwoMiddle n T) (appendTwoLast n T)
    (by
      have h := (isPushout_attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).w
      change (target n ≫ lastArrow ⟨n+1,T⟩) ≫
        inl ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) =
        source n ≫ inr ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) at h
      simpa only [appendTwoOld, appendTwoMiddle, Category.assoc] using
        congrArg (fun f => f ≫ (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
          (Nat.lt_succ_self n)).inl n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) h)
    (by
      exact (Category.assoc _ _ _).symm.trans
        (isPushout_attach (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
          (Nat.lt_succ_self n)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)).w)

@[reassoc (attr := simp)] theorem appendTwoTail_first (n : ℕ) (T : Table (n+1)) :
    tripleFirst n ≫ appendTwoTail n T = lastArrow ⟨n+1,T⟩ ≫ appendTwoOld n T :=
  tripleDesc_first _ _ _ _ _ _

@[reassoc (attr := simp)] theorem appendTwoTail_middle (n : ℕ) (T : Table (n+1)) :
    tripleMiddle n ≫ appendTwoTail n T = appendTwoMiddle n T :=
  tripleDesc_middle _ _ _ _ _ _

@[reassoc (attr := simp)] theorem appendTwoTail_last (n : ℕ) (T : Table (n+1)) :
    tripleLast n ≫ appendTwoTail n T = appendTwoLast n T :=
  tripleDesc_last _ _ _ _ _ _

theorem appendTwo_isPushout (n : ℕ) (T : Table (n+1)) :
    IsPushout (lastArrow ⟨n+1,T⟩) (tripleFirst n) (appendTwoOld n T) (appendTwoTail n T) := by
  let S : Shape := ⟨n+1,T⟩
  let S' := S.attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let p := isPushout_attach S n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  let p' := isPushout_attach S' n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  apply IsPushout.mk'
  · exact (appendTwoTail_first n T).symm
  · intro R f g hf hg
    have hm := congrArg (tripleMiddle n ≫ ·) hg
    have hl := congrArg (tripleLast n ≫ ·) hg
    simp only [appendTwoTail_middle_assoc, appendTwoTail_last_assoc] at hm hl
    apply p'.hom_ext
    · apply p.hom_ext
      · exact (Category.assoc _ _ _).symm.trans (hf.trans (Category.assoc _ _ _))
      · exact (Category.assoc _ _ _).symm.trans (hm.trans (Category.assoc _ _ _))
    · exact hl
  · intro R f g hw
    have w₁ : S.seam (Nat.lt_succ_self n) ≫ f = source n ≫ (tripleMiddle n ≫ g) := by
      change (target n ≫ lastArrow S) ≫ f = _
      rw [Category.assoc, hw, ← Category.assoc]
      exact congrArg (· ≫ g) (triple_first_middle n)
    let d₁ : S' ⟶ R := p.desc f (tripleMiddle n ≫ g) w₁
    have w₂ : S'.seam (Nat.lt_succ_self n) ≫ d₁ = source n ≫ (tripleLast n ≫ g) := by
      change (target n ≫ S.inr n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) ≫ d₁ = _
      erw [Category.assoc, IsPushout.inr_desc, ← Category.assoc]
      exact congrArg (· ≫ g) (triple_middle_last n)
    let d₂ : appendTwo n T ⟶ R := p'.desc d₁ (tripleLast n ≫ g) w₂
    have ho : appendTwoOld n T ≫ d₂ = f := by
      change (p.cocone.inl ≫ p'.cocone.inl) ≫ d₂ = _
      erw [Category.assoc, IsPushout.inl_desc, IsPushout.inl_desc]
    have hm : appendTwoMiddle n T ≫ d₂ = tripleMiddle n ≫ g := by
      change (p.cocone.inr ≫ p'.cocone.inl) ≫ d₂ = _
      erw [Category.assoc, IsPushout.inl_desc, IsPushout.inr_desc]
    have hl : appendTwoLast n T ≫ d₂ = tripleLast n ≫ g := p'.inr_desc _ _ _
    refine ⟨d₂, ho, ?_⟩
    apply triple_hom_ext n
    · rw [appendTwoTail_first_assoc, ho]
      exact hw
    · rw [appendTwoTail_middle_assoc, hm]
    · rw [appendTwoTail_last_assoc, hl]

end Shape

theorem threeChain_pushout {K : Type u} [Category.{v} K]
    {A D B V T B₁ B₂ : K} {s t : A ⟶ D} {a : D ⟶ B}
    {c₀ c₁ : D ⟶ V} {c : V ⟶ T} {c₂ : D ⟶ T}
    {i : B ⟶ B₁} {j : D ⟶ B₁} {i' : B₁ ⟶ B₂} {j' : D ⟶ B₂}
    (p₀ : IsPushout t s c₀ c₁) (p₁ : IsPushout (t ≫ c₁) s c c₂)
    (p : IsPushout (t ≫ a) s i j) (p' : IsPushout (t ≫ j) s i' j')
    (m : T ⟶ B₂) (hm₀ : (c₀ ≫ c) ≫ m = a ≫ i ≫ i')
    (hm₁ : (c₁ ≫ c) ≫ m = j ≫ i') (hm₂ : c₂ ≫ m = j') :
    IsPushout a (c₀ ≫ c) (i ≫ i') m := by
  apply IsPushout.mk'
  · exact hm₀.symm
  · intro R f g hf hg
    apply p'.hom_ext
    · apply p.hom_ext
      · simpa only [Category.assoc] using hf
      · have h := congrArg ((c₁ ≫ c) ≫ ·) hg
        simpa only [← Category.assoc, hm₁] using h
    · have h := congrArg (c₂ ≫ ·) hg
      simpa only [← Category.assoc, hm₂] using h
  · intro R f g hw
    have w₁ : (t ≫ a) ≫ f = s ≫ ((c₁ ≫ c) ≫ g) := by
      rw [Category.assoc, hw]
      simpa only [Category.assoc] using congrArg (fun z => z ≫ c ≫ g) p₀.w
    let d₁ := p.desc f ((c₁ ≫ c) ≫ g) w₁
    have w₂ : (t ≫ j) ≫ d₁ = s ≫ (c₂ ≫ g) := by
      rw [Category.assoc, p.inr_desc]
      simpa only [Category.assoc] using congrArg (· ≫ g) p₁.w
    let d₂ := p'.desc d₁ (c₂ ≫ g) w₂
    have ho : (i ≫ i') ≫ d₂ = f := by
      rw [Category.assoc, p'.inl_desc, p.inl_desc]
    have hm : (j ≫ i') ≫ d₂ = (c₁ ≫ c) ≫ g := by
      rw [Category.assoc, p'.inl_desc, p.inr_desc]
    have hl : j' ≫ d₂ = c₂ ≫ g := p'.inr_desc _ _ _
    refine ⟨d₂, ho, ?_⟩
    apply p₁.hom_ext
    · apply p₀.hom_ext
      · calc
          c₀ ≫ c ≫ m ≫ d₂ = a ≫ (i ≫ i') ≫ d₂ := by
            simpa only [Category.assoc] using congrArg (· ≫ d₂) hm₀
          _ = a ≫ f := by rw [ho]
          _ = c₀ ≫ c ≫ g := by simpa only [Category.assoc] using hw
      · simpa only [Category.assoc] using
          (congrArg (· ≫ d₂) hm₁).trans hm
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d₂) hm₂).trans hl)

namespace Shape
open GlobularTheory

theorem composition_realization_isPushout (n : ℕ) :
    IsPushout (realization.map (target n)) (realization.map (source n))
      (realization.map (compositionLeft n)) (realization.map (compositionRight n)) := by
  have h := realization_pushout (globe (n+1)) n (n+1)
    (Nat.lt_succ_self n) (Nat.lt_succ_self n)
  change IsPushout (GlobularPresheaf.face (Nat.lt_succ_self n) true ≫ 𝟙 _)
    (realization.map (source n)) _ _ at h
  rw [Category.comp_id] at h
  exact h

theorem triple_realization_isPushout (n : ℕ) :
    IsPushout (realization.map (target n ≫ compositionRight n))
      (realization.map (source n)) (realization.map (triplePrefix n))
      (realization.map (tripleLast n)) := realization_pushout _ _ _ _ _

theorem appendTwo_realization_isPushout (n : ℕ) (T : Table (n+1)) :
    IsPushout (realization.map (lastArrow ⟨n+1,T⟩)) (realization.map (tripleFirst n))
      (realization.map (appendTwoOld n T)) (realization.map (appendTwoTail n T)) := by
  apply threeChain_pushout (composition_realization_isPushout n)
    (triple_realization_isPushout n)
    (realization_pushout ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n))
    (realization_pushout (attach ⟨n+1,T⟩ n (n+1) (Nat.lt_succ_self n)
      (Nat.lt_succ_self n)) n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n))
  · exact congrArg realization.map (appendTwoTail_first n T)
  · exact congrArg realization.map (appendTwoTail_middle n T)
  · exact congrArg realization.map (appendTwoTail_last n T)

abbrev appendThree (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) : Shape :=
  appendTwo n (Table.attach S.2 b (n+1) hl (by omega))

noncomputable def appendThreeOld (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) :
    S ⟶ appendThree S n b hl hb :=
  S.inl b (n+1) hl (by omega) ≫ appendTwoOld n _

noncomputable def appendThreeTail (S : Shape) (n b : ℕ) (hl : b < S.1) (hb : b < n) :
    tripleShape n ⟶ appendThree S n b hl hb := appendTwoTail n _

theorem appendThree_realization_isPushout (S : Shape) (n b : ℕ)
    (hl : b < S.1) (hb : b < n) :
    IsPushout (realization.map (S.seam hl))
      (realization.map (face (by omega : b < n+1) false ≫ tripleFirst n))
      (realization.map (appendThreeOld S n b hl hb))
      (realization.map (appendThreeTail S n b hl hb)) := by
  have h₂ := appendTwo_realization_isPushout n (Table.attach S.2 b (n+1) hl (by omega))
  change IsPushout (realization.map (S.inr b (n+1) hl (by omega))) _ _ _ at h₂
  exact (realization_pushout S b (n+1) hl (by omega)).paste_vert h₂

theorem linearBlock_gt (n b k : ℕ) (hb : b < n) (hk : b < k) :
    b < (linearBlock n k).1 := by
  by_cases h : k < n
  · rw [linearBlock_low n k h]
    exact hk
  · by_cases h' : k = n
    · rw [linearBlock_center n k h']
      exact Nat.lt_trans hb (Nat.lt_succ_self n)
    · rw [linearBlock_high n k (by omega)]
      exact Nat.lt_trans hb (Nat.lt_succ_self n)

theorem face_lastArrow_transport {b : ℕ} {S T : Shape} (e : S = T)
    (hs : b < S.1) (ht : b < T.1) (ε : Bool) :
    face hs ε ≫ lastArrow S = face ht ε ≫ lastArrow T ≫ eqToHom e.symm := by
  subst T
  simp only [eqToHom_refl, Category.comp_id]

@[reassoc] theorem linear_face_below (n b k : ℕ) (h : b < k) (hb : b < n)
    (hk : k ≤ n+1) (ε : Bool) :
    realization.map (eqToHom (linearBlock_low n b hb).symm) ≫
      (linearGlobularDiagram n).face h hk ε =
    realization.map (face (linearBlock_gt n b k hb h) ε ≫ lastArrow (linearBlock n k)) := by
  by_cases hl : k < n
  · erw [linear_face_low n b k h hl, ← Functor.map_comp]
    congr 1
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [face_lastArrow_transport (linearBlock_low n k hl) _ h]
    rfl
  · by_cases hc : k = n
    · subst k
      erw [linear_face_center n b h, ← Functor.map_comp]
      congr 1
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [face_lastArrow_transport (linearBlock_center n n rfl) _ (by omega : b < n+1)]
      rfl
    · have he : k = n+1 := by omega
      subst k
      erw [linear_face_top_low n b hb, ← Functor.map_comp]
      congr 1
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [face_lastArrow_transport (linearBlock_high n (n+1) (by omega)) _
        (show b < (tripleShape n).1 by exact (by omega : b < n+1))]
      rfl

end Shape

noncomputable def pushoutSpanIso {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D')
    (hf : f ≫ b.hom = a.hom ≫ f') (hg : g ≫ d.hom = a.hom ≫ g') : E ≅ E' :=
  (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).isoIsPushout _ _ p'

@[reassoc (attr := simp)] theorem pushoutSpanIso_inl {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (hf) (hg) :
    i ≫ (pushoutSpanIso p p' a b d hf hg).hom = b.hom ≫ i' := by
  have h := (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).inl_isoIsPushout_hom _ _ p'
  have h' := congrArg (b.hom ≫ ·) h
  simpa only [pushoutSpanIso, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'

@[reassoc (attr := simp)] theorem pushoutSpanIso_inr {K : Type u} [Category.{v} K]
    {A B D E A' B' D' E' : K} {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    {f' : A' ⟶ B'} {g' : A' ⟶ D'} {i' : B' ⟶ E'} {j' : D' ⟶ E'}
    (p : IsPushout f g i j) (p' : IsPushout f' g' i' j')
    (a : A ≅ A') (b : B ≅ B') (d : D ≅ D') (hf) (hg) :
    j ≫ (pushoutSpanIso p p' a b d hf hg).hom = d.hom ≫ j' := by
  have h := (p.of_iso (inl' := b.inv ≫ i) (inr' := d.inv ≫ j) a b d (Iso.refl E) hf hg (by simp) (by simp)).inr_isoIsPushout_hom _ _ p'
  have h' := congrArg (d.hom ≫ ·) h
  simpa only [pushoutSpanIso, ← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'

instance preservesColimits_linearization (n : ℕ) : PreservesColimits (Shape.linearization n) :=
  CoGlobularObject.preservesColimits_realization _

namespace Table
open Shape GlobularTheory

structure LinearData (n : ℕ) {k : ℕ} (T : Table k) (hk : k ≤ n+1) where
  table : Table (linearBlock n k).1
  iso : (linearization n).obj T.realize ≅ table.realize
  port : realization.map (lastArrow (linearBlock n k)) ≫
    (linearGlobeIso n k hk).inv ≫ (linearization n).map T.lastInclusion ≫ iso.hom =
      table.lastInclusion

namespace LinearData

noncomputable def globe (n k : ℕ) (hk : k ≤ n+1) : LinearData n (Table.globe k) hk where
  table := (linearBlock n k).2
  iso := linearGlobeIso n k hk
  port := by
    change _ ≫ (linearGlobeIso n k hk).inv ≫ (linearization n).map (𝟙 _) ≫
      (linearGlobeIso n k hk).hom = _
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
    rfl

noncomputable def extend {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b h : ℕ) (hl : b < k) (hr : b < h) (hh : h ≤ n+1)
    (R : Table (linearBlock n h).1)
    (i : d.table.realize ⟶ R.realize) (j : (linearBlock n h).realize ⟶ R.realize)
    (p : IsPushout
      ((linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
        (linearization n).map T.lastInclusion ≫ d.iso.hom)
      ((linearGlobularDiagram n).face hr hh false) i j)
    (hj : realization.map (lastArrow (linearBlock n h)) ≫ j = R.lastInclusion) :
    LinearData n (T.attach b h hl hr) hh := by
  let P := (Shape.realization_pushout ⟨k,T⟩ b h hl hr).map (linearization n)
  have hf : (linearization n).map (realization.map (Shape.seam ⟨k,T⟩ hl)) ≫ d.iso.hom =
      (linearGlobeIso n b (by omega)).hom ≫
        (linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
          (linearization n).map T.lastInclusion ≫ d.iso.hom := by
    change (linearization n).map (GlobularPresheaf.face hl true ≫ T.lastInclusion) ≫ _ = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    have e := (linearGlobularDiagram n).globeIso_face hl hk true
    have e' := congrArg (fun z => z ≫ (linearGlobeIso n k hk).inv ≫
      (linearization n).map T.lastInclusion ≫ d.iso.hom) e
    erw [Category.assoc, Iso.hom_inv_id_assoc, Category.assoc] at e'
    exact e'
  have hg : (linearization n).map (realization.map (Shape.face hr false)) ≫
      (linearGlobeIso n h hh).hom = (linearGlobeIso n b (by omega)).hom ≫
        (linearGlobularDiagram n).face hr hh false :=
    (linearGlobularDiagram n).globeIso_face hr hh false
  let e := pushoutSpanIso P p (linearGlobeIso n b (by omega)) d.iso
    (linearGlobeIso n h hh) hf hg
  refine ⟨R, e, ?_⟩
  change _ ≫ (linearGlobeIso n h hh).inv ≫
    (linearization n).map (realization.map (Shape.inr ⟨k,T⟩ b h hl hr)) ≫ e.hom = _
  erw [pushoutSpanIso_inr, Iso.inv_hom_id_assoc]
  exact hj

theorem seam_below {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b : ℕ) (hl : b < k) (hb : b < n) :
    realization.map (eqToHom (linearBlock_low n b hb).symm) ≫
      (linearGlobularDiagram n).face hl hk true ≫ (linearGlobeIso n k hk).inv ≫
        (linearization n).map T.lastInclusion ≫ d.iso.hom =
    realization.map (Shape.seam ⟨(linearBlock n k).1,d.table⟩ (linearBlock_gt n b k hb hl)) := by
  let f : (linearBlock n b).realize ⟶ (linearBlock n k).realize :=
    (linearGlobularDiagram n).face hl hk true
  let m : (linearBlock n k).realize ⟶ d.table.realize :=
    (linearGlobeIso n k hk).inv ≫ (linearization n).map T.lastInclusion ≫ d.iso.hom
  have e : realization.map (eqToHom (linearBlock_low n b hb).symm) ≫ f =
      realization.map (Shape.face (linearBlock_gt n b k hb hl) true) ≫
        realization.map (lastArrow (linearBlock n k)) :=
    (linear_face_below n b k hl hb hk true).trans (realization.map_comp _ _)
  have hp : realization.map (lastArrow (linearBlock n k)) ≫ m = d.table.lastInclusion := d.port
  change realization.map (eqToHom (linearBlock_low n b hb).symm) ≫ f ≫ m = _
  erw [← Category.assoc, e, Category.assoc, hp]
  rfl

end LinearData

private theorem lastArrow_isIso_globe {S : Shape} {k : ℕ} (e : S = Shape.globe k) :
    IsIso (lastArrow S) := by
  subst S
  change IsIso (𝟙 (Shape.globe k))
  infer_instance

theorem linearBlock_lastArrow_isIso (n h : ℕ) (hh : h ≤ n) :
    IsIso (lastArrow (linearBlock n h)) := by
  rcases lt_or_eq_of_le hh with hlt | he
  · exact lastArrow_isIso_globe (linearBlock_low n h hlt)
  · subst h
    exact lastArrow_isIso_globe (linearBlock_center n n rfl)

def reindex {k h : ℕ} (e : k = h) (T : Table k) : Table h := e ▸ T

noncomputable def reindexIso {k h : ℕ} (e : k = h) (T : Table k) :
    (T.reindex e).realize ≅ T.realize := by
  subst h
  exact Iso.refl _

@[reassoc] theorem reindexIso_last {k h : ℕ} (e : k = h) (T : Table k) :
    (T.reindex e).lastInclusion ≫ (T.reindexIso e).hom =
      realization.map (eqToHom (congrArg Shape.globe e.symm)) ≫ T.lastInclusion := by
  subst h
  simp only [reindex, reindexIso, Iso.refl_hom, Category.comp_id, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).symm

@[reassoc] theorem lastArrow_transport {S R : Shape} (e : S = R) :
    realization.map (lastArrow S) ≫ realization.map (eqToHom e) =
      realization.map (eqToHom (congrArg Shape.globe (congrArg Sigma.fst e))) ≫
        realization.map (lastArrow R) := by
  subst R
  simp

namespace LinearData

noncomputable def attachLow {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b h : ℕ) (hl : b < k) (hr : b < h) (hh : h ≤ n) :
    LinearData n (T.attach b h hl hr) (by omega) := by
  let S : Shape := ⟨(linearBlock n k).1,d.table⟩
  have hb : b < n := by omega
  let hl' := linearBlock_gt n b k hb hl
  let hr' := linearBlock_gt n b h hb hr
  let R := Table.attach d.table b (linearBlock n h).1 hl' hr'
  let a := realization.mapIso (eqToIso (linearBlock_low n b hb).symm)
  letI := linearBlock_lastArrow_isIso n h hh
  let r := asIso (realization.map (lastArrow (linearBlock n h)))
  let i := realization.map (Shape.inl S b (linearBlock n h).1 hl' hr')
  let j := r.inv ≫ realization.map (Shape.inr S b (linearBlock n h).1 hl' hr')
  apply d.extend b h hl hr (by omega) R i j
  · apply (Shape.realization_pushout S b (linearBlock n h).1 hl' hr').of_iso
      a (Iso.refl _) r (Iso.refl _)
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (d.seam_below b hl hb).symm
    · have h' := (linear_face_below n b h hr hb (by omega) false).symm
      change realization.map _ = _ at h'
      erw [CategoryTheory.Functor.map_comp] at h'
      exact h'
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · exact (r.hom_inv_id_assoc _).symm
  · change r.hom ≫ r.inv ≫ _ = _
    erw [r.hom_inv_id_assoc]
    rfl

noncomputable def attachHighBelow {n k : ℕ} {T : Table k} {hk : k ≤ n+1}
    (d : LinearData n T hk) (b : ℕ) (hl : b < k) (hb : b < n) :
    LinearData n (T.attach b (n+1) hl (by omega)) le_rfl := by
  let S : Shape := ⟨(linearBlock n k).1,d.table⟩
  let hl' := linearBlock_gt n b k hb hl
  let R := Shape.appendThree S n b hl' hb
  let e : (linearBlock n (n+1)).1 = n+1 :=
    congrArg Sigma.fst (linearBlock_high n (n+1) (by omega))
  let a := realization.mapIso (eqToIso (linearBlock_low n b hb).symm)
  let c := realization.mapIso (eqToIso (linearBlock_high n (n+1) (by omega)).symm)
  let r := R.2.reindexIso e.symm
  let i := realization.map (appendThreeOld S n b hl' hb) ≫ r.inv
  let j := c.inv ≫ realization.map (appendThreeTail S n b hl' hb) ≫ r.inv
  apply d.extend b (n+1) hl (by omega) le_rfl (R.2.reindex e.symm) i j
  · apply (appendThree_realization_isPushout S n b hl' hb).of_iso
      a (Iso.refl _) c r.symm
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (d.seam_below b hl hb).symm
    · have hf := linear_face_top_low n b hb false
      rw [← Category.assoc (face _ false), ← face_triple_first_last n b hb false] at hf
      change _ = realization.map (_ ≫ _ ≫ _) at hf
      erw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hf
      change (linearGlobularDiagram n).face (by omega : b < n+1) le_rfl false =
        a.inv ≫ realization.map (face (by omega : b < n+1) false ≫ tripleFirst n) ≫ c.hom at hf
      erw [hf, Iso.hom_inv_id_assoc]
    · simp only [Iso.refl_hom, Category.id_comp]
      rfl
    · change _ ≫ r.inv = c.hom ≫ c.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
  · apply (cancel_mono r.hom).1
    change (realization.map (lastArrow (linearBlock n (n+1))) ≫ c.inv) ≫
      realization.map (appendThreeTail S n b hl' hb) ≫ r.inv ≫ r.hom = _
    erw [Iso.inv_hom_id, Category.comp_id, reindexIso_last]
    have ht := lastArrow_transport (linearBlock_high n (n+1) (by omega))
    have hz := congrArg (fun z => z ≫ realization.map (appendThreeTail S n b hl' hb)) ht
    change _ = realization.map (eqToHom (congrArg Shape.globe e)) ≫ R.2.lastInclusion
    erw [Category.assoc] at hz
    refine hz.trans ?_
    change (_ ≫ realization.map (tripleLast n)) ≫
      realization.map (appendTwoTail n _) = _
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, appendTwoTail_last]
    rfl

theorem face_top_normalized (n : ℕ) (ε : Bool) :
    realization.map (eqToHom (linearBlock_center n n rfl).symm) ≫
      (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl ε =
    realization.map (if ε then tripleLast n else tripleFirst n) ≫
      realization.map (eqToHom (linearBlock_high n (n+1) (by omega)).symm) := by
  erw [linear_face_top, ← CategoryTheory.Functor.map_comp]
  congr 1
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  rfl

noncomputable def attachHighCritical {n : ℕ} {T : Table (n+1)}
    (d : LinearData n T le_rfl) :
    LinearData n (T.attach n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n)) le_rfl := by
  let eh := linearBlock_high n (n+1) (Nat.lt_succ_self n)
  let e : (linearBlock n (n+1)).1 = n+1 := congrArg Sigma.fst eh
  let U : Table (n+1) := d.table.reindex e
  let o := d.table.reindexIso e
  let R := Shape.appendTwo n U
  let a := realization.mapIso (eqToIso (linearBlock_center n n rfl).symm)
  let c := realization.mapIso (eqToIso eh.symm)
  let r := R.2.reindexIso e.symm
  let i := o.inv ≫ realization.map (appendTwoOld n U) ≫ r.inv
  let j := c.inv ≫ realization.map (appendTwoTail n U) ≫ r.inv
  let m : (linearBlock n (n+1)).realize ⟶ d.table.realize :=
    (linearGlobeIso n (n+1) le_rfl).inv ≫ (linearization n).map T.lastInclusion ≫ d.iso.hom
  apply d.extend n (n+1) (Nat.lt_succ_self n) (Nat.lt_succ_self n) le_rfl
    (R.2.reindex e.symm) i j
  · apply (appendTwo_realization_isPushout n U).of_iso a o c r.symm
    · have hface : a.hom ≫ (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl true =
          realization.map (tripleLast n) ≫ c.hom := face_top_normalized n true
      have ht := lastArrow_transport eh.symm
      have hp : realization.map (lastArrow (linearBlock n (n+1))) ≫ m = d.table.lastInclusion := d.port
      change U.lastInclusion ≫ o.hom = a.hom ≫
        (linearGlobularDiagram n).face (Nat.lt_succ_self n) le_rfl true ≫ m
      erw [← Category.assoc a.hom, hface, Category.assoc]
      have ht' := congrArg (· ≫ m) ht
      change (realization.map (tripleLast n) ≫ c.hom) ≫ m =
        (realization.map (eqToHom (congrArg Shape.globe e.symm)) ≫
          realization.map (lastArrow (linearBlock n (n+1)))) ≫ m at ht'
      erw [Category.assoc, Category.assoc, hp] at ht'
      exact (reindexIso_last e d.table).trans ht'.symm
    · exact (face_top_normalized n false).symm
    · change _ ≫ r.inv = o.hom ≫ o.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
    · change _ ≫ r.inv = c.hom ≫ c.inv ≫ _ ≫ r.inv
      erw [Iso.hom_inv_id_assoc]
  · apply (cancel_mono r.hom).1
    change (realization.map (lastArrow (linearBlock n (n+1))) ≫ c.inv) ≫
      realization.map (appendTwoTail n U) ≫ r.inv ≫ r.hom = _
    erw [Iso.inv_hom_id, Category.comp_id, reindexIso_last]
    have ht := lastArrow_transport eh
    have hz := congrArg (fun z => z ≫ realization.map (appendTwoTail n U)) ht
    change _ = realization.map (eqToHom (congrArg Shape.globe e)) ≫ R.2.lastInclusion
    erw [Category.assoc] at hz
    refine hz.trans ?_
    change (_ ≫ realization.map (tripleLast n)) ≫ realization.map (appendTwoTail n U) = _
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, appendTwoTail_last]
    rfl

end LinearData

theorem last_le_height {k : ℕ} (T : Table k) : k ≤ T.height := by
  cases T with
  | globe k => exact le_rfl
  | attach T b h hl hr => exact Nat.le_max_right _ _

noncomputable def linearData (n : ℕ) {k : ℕ} (T : Table k)
    (hT : T.height ≤ n+1) : LinearData n T (T.last_le_height.trans hT) := by
  induction T with
  | globe k => exact LinearData.globe n k hT
  | @attach k T b h hl hr ih =>
    have hprev : T.height ≤ n+1 := (Nat.le_max_left _ _).trans hT
    have hh : h ≤ n+1 := (Nat.le_max_right _ _).trans hT
    let d := ih hprev
    by_cases hlo : h ≤ n
    · exact d.attachLow b h hl hr hlo
    · have eh : h = n+1 := by omega
      subst h
      by_cases hb : b < n
      · exact d.attachHighBelow b hl hb
      · have eb : b = n := by omega
        have ek : k = n+1 := by have := T.last_le_height.trans hprev; omega
        subst b k
        exact d.attachHighCritical

end Table
end Grothendieck

end OAI
