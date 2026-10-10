import OAI.CategoryTheory.Globular.Colimits

namespace OAI

universe u v w

namespace Grothendieck

open CategoryTheory CategoryTheory.Limits Opposite

namespace Globe

def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : Globe.mk m ⟶ Globe.mk n :=
  if e : m = n then e ▸ Face.id m else Face.face (lt_of_le_of_ne h e) side

@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (Globe.mk n) := by
  simp only [faceLE, dite_true]
  rfl

@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE h.le side = face h side := by
  simp [faceLE, h.ne, face]

end Globe

namespace GlobularPresheaf

noncomputable def faceLE {m n : ℕ} (h : m ≤ n) (side : Bool) : disk.{u} m ⟶ disk.{u} n :=
  uliftYoneda.{u}.map (Globe.faceLE h side)

@[simp] theorem faceLE_refl (n : ℕ) (side : Bool) : faceLE (le_refl n) side = 𝟙 (disk.{u} n) := by
  change uliftYoneda.map (Globe.faceLE (le_refl n) side) = 𝟙 _
  rw [Globe.faceLE_refl, uliftYoneda.map_id]

@[simp] theorem faceLE_of_lt {m n : ℕ} (h : m < n) (side : Bool) :
    faceLE.{u} h.le side = face h side := by
  unfold faceLE face
  rw [Globe.faceLE_of_lt]

theorem face_low_bijective {m n k : ℕ} (h : m < n) (hk : k < m) (side : Bool) :
    Function.Bijective ((face.{u} h side).app (op (Globe.mk k))) := by
  constructor
  · rintro ⟨a⟩ ⟨b⟩ he
    cases a with
    | id => omega
    | face ha ba =>
      cases b with
      | id => omega
      | face hb bb =>
        have : ba = bb := by
          change ULift.up (Globe.Face.face (ha.trans h) ba) =
            ULift.up (Globe.Face.face (hb.trans h) bb) at he
          cases he
          rfl
        subst bb
        rfl
  · rintro ⟨a⟩
    cases a with
    | id => omega
    | face ha ba =>
      exact ⟨⟨Globe.Face.face hk ba⟩, rfl⟩

theorem face_low_equal {m n k : ℕ} (h : m < n) (hk : k < m) (b c : Bool) :
    (face.{u} h b).app (op (Globe.mk k)) = (face h c).app (op (Globe.mk k)) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba => rfl

theorem faceLE_low_bijective {m n k : ℕ} (h : m ≤ n) (hk : k < m) (side : Bool) :
    Function.Bijective ((faceLE.{u} h side).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with h | rfl
  · rw [faceLE_of_lt h]
    exact face_low_bijective h hk side
  · rw [faceLE_refl]
    exact Function.bijective_id


theorem face_comp_faceLE {a b c : ℕ} (hab : a < b) (hbc : b ≤ c) (s t : Bool) :
    face.{u} hab s ≫ faceLE hbc t = face (hab.trans_le hbc) s := by
  rcases lt_or_eq_of_le hbc with hbc | rfl
  · rw [faceLE_of_lt hbc]
    change uliftYoneda.map (Globe.face hab s) ≫ uliftYoneda.map (Globe.face hbc t) = _
    rw [← uliftYoneda.map_comp]
    rfl
  · rw [faceLE_refl, Category.comp_id]

theorem globeMap_low_equal {m n k : ℕ} (f g : Globe.mk m ⟶ Globe.mk n) (hk : k < m) :
    (uliftYoneda.{u}.map f).app (op (Globe.mk k)) =
      (uliftYoneda.{u}.map g).app (op (Globe.mk k)) := by
  change Globe.Face m n at f g
  apply ConcreteCategory.hom_ext
  rintro ⟨a⟩
  cases a with
  | id => omega
  | face ha ba =>
    cases f with
    | id =>
      cases g with
      | id => rfl
      | face hg bg => omega
    | face hf bf =>
      cases g with
      | id => omega
      | face hg bg => rfl

theorem disk_hom_ext {n : ℕ} {X : GlobularPresheaf.{u}} {f g : disk n ⟶ X}
    (h : f.app (op (Globe.mk n)) = g.app (op (Globe.mk n))) : f = g := by
  apply uliftYonedaEquiv.injective
  exact ConcreteCategory.congr_hom h _

theorem pushout_comparison_isIso {D : Type u} [Category.{v} D]
    {A B E P A' B' E' P' : D}
    {f : A ⟶ B} {g : A ⟶ E} {i : B ⟶ P} {j : E ⟶ P}
    {f' : A' ⟶ B'} {g' : A' ⟶ E'} {i' : B' ⟶ P'} {j' : E' ⟶ P'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (e : E ⟶ E') (p : P ⟶ P')
    [IsIso a] [IsIso b] [IsIso e]
    (hf : f ≫ b = a ≫ f') (hg : g ≫ e = a ≫ g')
    (hi : i ≫ p = b ≫ i') (hj : j ≫ p = e ≫ j') : IsIso p := by
  let r : P' ⟶ P := h'.desc (inv b ≫ i) (inv e ≫ j) (by
    apply (cancel_epi a).1
    simp only [← Category.assoc, ← hf, ← hg]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact h.w)
  refine ⟨r, ?_, ?_⟩
  · apply h.hom_ext
    · rw [← Category.assoc, hi, Category.assoc]
      simp only [r, IsPushout.inl_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
    · rw [← Category.assoc, hj, Category.assoc]
      simp only [r, IsPushout.inr_desc, IsIso.hom_inv_id_assoc, Category.comp_id]
  · apply h'.hom_ext
    · simp only [r, IsPushout.inl_desc_assoc, hi, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]
    · simp only [r, IsPushout.inr_desc_assoc, hj, Category.assoc,
        IsIso.inv_hom_id_assoc, Category.comp_id]


theorem faceLE_cap_bijective {q d n k : ℕ} (hd : d = min n (q+1))
    (h : d ≤ n) (hk : k ≤ q) :
    Function.Bijective ((faceLE.{u} h false).app (op (Globe.mk k))) := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · apply faceLE_low_bijective
    have : d = q+1 := by omega
    omega
  · rw [faceLE_refl]
    exact Function.bijective_id

theorem face_comp_eq_of_app_eq {m n : ℕ} {X : GlobularPresheaf.{u}}
    (h : m < n) (s : Bool) (a b : disk n ⟶ X)
    (hab : a.app (op (Globe.mk m)) = b.app (op (Globe.mk m))) :
    face h s ≫ a = face h s ≫ b := by
  apply disk_hom_ext
  exact congrArg (fun t => (face h s).app (op (Globe.mk m)) ≫ t) hab

end GlobularPresheaf

namespace Shape

noncomputable def last (S : Shape) : GlobularPresheaf.disk S.1 ⟶ S.realize :=
  S.2.lastInclusion

end Shape

end Grothendieck

end OAI
