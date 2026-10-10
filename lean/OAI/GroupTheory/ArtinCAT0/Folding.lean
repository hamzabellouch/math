import OAI.GroupTheory.ArtinCAT0.Centralizer

namespace OAI

namespace ArtinCAT0.TriangleMesh

variable {F V : Type*}

noncomputable def foldPartner (f g : F) (d : F × Fin 3) : F × Fin 3 := by
  classical
  exact if d.1 = f then (g,-d.2) else if d.1 = g then (f,-d.2) else d

structure Fold (M : TriangleMesh F V) where
  f : F
  g : F
  ne : f ≠ g
  seam : M.mate (f,0) = (g,0)
  internal : ∀ d, (d.1 = f ∨ d.1 = g) →
    ((M.mate d).1 = f ∨ (M.mate d).1 = g) → M.mate d = foldPartner f g d

namespace Fold
variable {M : TriangleMesh F V} (C : M.Fold)

def Removed (d : F × Fin 3) : Prop := d.1 = C.f ∨ d.1 = C.g
abbrev Kept := {f : F // f ≠ C.f ∧ f ≠ C.g}
noncomputable abbrev partner := foldPartner C.f C.g

@[simp] lemma partner_f (i : Fin 3) : C.partner (C.f,i) = (C.g,-i) := by
  simp [partner, foldPartner]
@[simp] lemma partner_g (i : Fin 3) : C.partner (C.g,i) = (C.f,-i) := by
  simp [partner, foldPartner, C.ne.symm]

lemma partner_outside (d : F × Fin 3) (hd : ¬ C.Removed d) : C.partner d = d := by
  simp only [Removed, not_or] at hd
  simp [partner, foldPartner, hd.1, hd.2]

@[simp] lemma partner_partner (d : F × Fin 3) : C.partner (C.partner d) = d := by
  by_cases hf : d.1 = C.f
  · rcases d with ⟨f,i⟩
    dsimp only at hf
    subst f
    simp
  · by_cases hg : d.1 = C.g
    · rcases d with ⟨g,i⟩
      dsimp only at hg
      subst g
      simp
    · rw [C.partner_outside d (by simpa [Removed] using And.intro hf hg)]
      exact C.partner_outside d (by simpa [Removed] using And.intro hf hg)

lemma partner_removed (d : F × Fin 3) (hd : C.Removed d) : C.Removed (C.partner d) := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · simp [Removed]
  · simp [Removed]

lemma partner_ne (d : F × Fin 3) (hd : C.Removed d) : C.partner d ≠ d := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · intro h
    exact C.ne.symm (congrArg Prod.fst (C.partner_f i ▸ h))
  · intro h
    exact C.ne (congrArg Prod.fst (C.partner_g i ▸ h))

@[simp] lemma mate_seam_reverse : M.mate (C.g,0) = (C.f,0) := by
  rw [← C.seam, M.mate_mate]

lemma mate_partner_outside (d : F × Fin 3) (hd : C.Removed d)
    (hm : ¬ C.Removed (M.mate d)) : ¬ C.Removed (M.mate (C.partner d)) := by
  intro h
  have he := C.internal (C.partner d) (C.partner_removed d hd) h
  change M.mate (C.partner d) = C.partner (C.partner d) at he
  rw [C.partner_partner] at he
  have he' := congrArg M.mate he
  rw [M.mate_mate] at he'
  exact hm (he' ▸ C.partner_removed d hd)

noncomputable def splice (d : F × Fin 3) : F × Fin 3 := by
  classical
  exact if C.Removed (M.mate d) then M.mate (C.partner (M.mate d)) else M.mate d

lemma splice_inside (d : F × Fin 3) (h : C.Removed (M.mate d)) :
    C.splice d = M.mate (C.partner (M.mate d)) := by simp [splice, h]
lemma splice_outside (d : F × Fin 3) (h : ¬ C.Removed (M.mate d)) :
    C.splice d = M.mate d := by simp [splice, h]

lemma splice_kept (d : F × Fin 3) (hd : ¬ C.Removed d) : ¬ C.Removed (C.splice d) := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    exact C.mate_partner_outside (M.mate d) hm (by simpa using hd)
  · rw [C.splice_outside d hm]
    exact hm

lemma splice_splice (d : F × Fin 3) (hd : ¬ C.Removed d) : C.splice (C.splice d) = d := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    rw [C.splice_inside _ (by simpa using C.partner_removed (M.mate d) hm)]
    simp
  · rw [C.splice_outside d hm]
    rw [C.splice_outside _ (by simpa using hd)]
    simp

lemma splice_ne (d : F × Fin 3) (_hd : ¬ C.Removed d) : C.splice d ≠ d := by
  by_cases hm : C.Removed (M.mate d)
  · rw [C.splice_inside d hm]
    intro he
    have he' := congrArg M.mate he
    rw [M.mate_mate] at he'
    exact C.partner_ne (M.mate d) hm he'
  · rw [C.splice_outside d hm]
    exact M.mate_ne d

noncomputable def merge (v : V) : V := by
  classical
  exact if v = M.tail (C.g,2) then M.tail (C.f,2) else v

lemma merge_opposite : C.merge (M.tail (C.g,2)) = C.merge (M.tail (C.f,2)) := by
  simp only [merge, ite_true]
  split_ifs <;> rfl

lemma tail_seam : M.tail (C.g,0) = M.tail (C.f,1) := by
  have hh := M.tail_mate (C.f,0)
  simpa [C.seam] using hh

lemma tail_seam_reverse : M.tail (C.g,1) = M.tail (C.f,0) := by
  have hh := M.tail_mate (C.g,0)
  simpa using hh.symm

lemma merge_tail_partner (d : F × Fin 3) (hd : C.Removed d) :
    C.merge (M.tail (rotate (C.partner d))) = C.merge (M.tail d) := by
  rcases d with ⟨f,i⟩
  rcases hd with hf | hf <;> dsimp only at hf <;> subst f
  · fin_cases i
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam_reverse
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using C.merge_opposite
  · fin_cases i
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam.symm
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using congrArg C.merge C.tail_seam_reverse.symm
    · simpa [rotate_apply, Fin.neg_def, Fin.add_def] using C.merge_opposite.symm

abbrev oldDart (d : C.Kept × Fin 3) : F × Fin 3 := (d.1.val,d.2)

lemma oldDart_kept (d : C.Kept × Fin 3) : ¬ C.Removed (C.oldDart d) :=
  not_or.mpr d.1.property

noncomputable def newMate (d : C.Kept × Fin 3) : C.Kept × Fin 3 :=
  (⟨(C.splice (C.oldDart d)).1, not_or.mp (C.splice_kept _ (C.oldDart_kept d))⟩,
    (C.splice (C.oldDart d)).2)

@[simp] lemma oldDart_newMate (d : C.Kept × Fin 3) :
    C.oldDart (C.newMate d) = C.splice (C.oldDart d) := rfl

lemma oldDart_injective : Function.Injective C.oldDart := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have ha : a = b := Subtype.ext (congrArg Prod.fst h)
  have hi : i = j := congrArg Prod.snd h
  simp_all

lemma newMate_involutive : Function.Involutive C.newMate := by
  intro d
  apply C.oldDart_injective
  rw [C.oldDart_newMate, C.oldDart_newMate, C.splice_splice _ (C.oldDart_kept d)]

noncomputable def mesh : TriangleMesh C.Kept V where
  mate := C.newMate_involutive.toPerm
  mate_involutive := C.newMate_involutive
  mate_ne d h := C.splice_ne _ (C.oldDart_kept d) (congrArg C.oldDart h)
  tail d := C.merge (M.tail (C.oldDart d))
  tail_mate d := by
    change C.merge (M.tail (C.splice (C.oldDart d))) = C.merge (M.tail (rotate (C.oldDart d)))
    by_cases hm : C.Removed (M.mate (C.oldDart d))
    · rw [C.splice_inside _ hm, M.tail_mate]
      rw [show (M.tail ((C.partner (M.mate (C.oldDart d))).1,
        (C.partner (M.mate (C.oldDart d))).2+1)) = M.tail (rotate (C.partner (M.mate (C.oldDart d)))) from rfl]
      rw [C.merge_tail_partner _ hm, M.tail_mate]
      rfl
    · rw [C.splice_outside _ hm, M.tail_mate]
      rfl

def toNewDart (d : F × Fin 3) (hd : ¬ C.Removed d) : C.Kept × Fin 3 :=
  (⟨d.1, not_or.mp hd⟩,d.2)

@[simp] lemma oldDart_toNewDart (d : F × Fin 3) (hd : ¬ C.Removed d) :
    C.oldDart (C.toNewDart d hd) = d := rfl

@[simp] lemma toNewDart_oldDart (d : C.Kept × Fin 3) :
    C.toNewDart (C.oldDart d) (C.oldDart_kept d) = d := rfl

noncomputable def sideValue (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if h : C.Removed (M.mate d) then 0 else -w (C.toNewDart (M.mate d) h)

lemma sideValue_partner (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) (d : F × Fin 3) (hd : C.Removed d) :
    C.sideValue w (C.partner d) = -C.sideValue w d := by
  by_cases hm : C.Removed (M.mate d)
  · have he : M.mate d = C.partner d := C.internal d hd hm
    have he' : M.mate (C.partner d) = d := by rw [← he, M.mate_mate]
    simp [sideValue, hm, he', hd]
  · have hm' := C.mate_partner_outside d hd hm
    have hs := ha (C.toNewDart (M.mate d) hm)
    have he : C.newMate (C.toNewDart (M.mate d) hm) =
        C.toNewDart (M.mate (C.partner d)) hm' := by
      apply C.oldDart_injective
      rw [C.oldDart_newMate, C.oldDart_toNewDart, C.oldDart_toNewDart]
      rw [C.splice_inside _ (by simpa using hd), M.mate_mate]
    rw [he] at hs
    simp only [sideValue, dite_eq_right hm, dite_eq_right hm', hs, neg_neg]

noncomputable def extension (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) : ℝ := by
  classical
  exact if d = (C.f,0) then -(C.sideValue w (C.f,1) + C.sideValue w (C.f,2))
    else if d = (C.g,0) then C.sideValue w (C.f,1) + C.sideValue w (C.f,2)
    else if h : C.Removed d then C.sideValue w d else w (C.toNewDart d h)

lemma extension_outside (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3) (hd : ¬ C.Removed d) :
    C.extension w d = w (C.toNewDart d hd) := by
  have hf : d ≠ (C.f,0) := fun h => hd (Or.inl (congrArg Prod.fst h))
  have hg : d ≠ (C.g,0) := fun h => hd (Or.inr (congrArg Prod.fst h))
  simp [extension, hf, hg, hd]

@[simp] lemma extension_f_zero (w : C.Kept × Fin 3 → ℝ) :
    C.extension w (C.f,0) = -(C.sideValue w (C.f,1) + C.sideValue w (C.f,2)) := by
  simp [extension]

@[simp] lemma extension_g_zero (w : C.Kept × Fin 3 → ℝ) :
    C.extension w (C.g,0) = C.sideValue w (C.f,1) + C.sideValue w (C.f,2) := by
  simp [extension, C.ne.symm]

lemma extension_removed_nonzero (w : C.Kept × Fin 3 → ℝ) (d : F × Fin 3)
    (hd : C.Removed d) (hf : d ≠ (C.f,0)) (hg : d ≠ (C.g,0)) :
    C.extension w d = C.sideValue w d := by simp [extension, hf, hg, hd]

lemma extension_mate (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) (d : F × Fin 3) :
    C.extension w (M.mate d) = -C.extension w d := by
  by_cases hf : d = (C.f,0)
  · subst d
    rw [C.seam, C.extension_g_zero, C.extension_f_zero, neg_neg]
  by_cases hg : d = (C.g,0)
  · subst d
    rw [C.mate_seam_reverse, C.extension_f_zero, C.extension_g_zero]
  have hmf : M.mate d ≠ (C.f,0) := by
    intro he
    apply hg
    calc
      d = M.mate (M.mate d) := (M.mate_mate d).symm
      _ = (C.g,0) := by rw [he, C.seam]
  have hmg : M.mate d ≠ (C.g,0) := by
    intro he
    apply hf
    calc
      d = M.mate (M.mate d) := (M.mate_mate d).symm
      _ = (C.f,0) := by rw [he, C.mate_seam_reverse]
  by_cases hd : C.Removed d
  · rw [C.extension_removed_nonzero w d hd hf hg]
    by_cases hm : C.Removed (M.mate d)
    · rw [C.extension_removed_nonzero w _ hm hmf hmg]
      have he : M.mate d = C.partner d := C.internal d hd hm
      rw [he, C.sideValue_partner w ha d hd]
    · rw [C.extension_outside w _ hm]
      simp [sideValue, hm]
  · rw [C.extension_outside w d hd]
    by_cases hm : C.Removed (M.mate d)
    · rw [C.extension_removed_nonzero w _ hm hmf hmg]
      simp [sideValue, hd]
    · rw [C.extension_outside w _ hm]
      have he : C.newMate (C.toNewDart d hd) = C.toNewDart (M.mate d) hm := by
        apply C.oldDart_injective
        rw [C.oldDart_newMate, C.oldDart_toNewDart, C.oldDart_toNewDart, C.splice_outside d hm]
      simpa only [he] using ha (C.toNewDart d hd)

lemma sideValue_g_one (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) :
    C.sideValue w (C.g,1) = -C.sideValue w (C.f,2) := by
  simpa [Fin.neg_def] using C.sideValue_partner w ha (C.f,2) (Or.inl rfl)

lemma sideValue_g_two (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d) :
    C.sideValue w (C.g,2) = -C.sideValue w (C.f,1) := by
  simpa [Fin.neg_def] using C.sideValue_partner w ha (C.f,1) (Or.inl rfl)

lemma extension_face (w : C.Kept × Fin 3 → ℝ)
    (ha : ∀ d, w (C.newMate d) = -w d)
    (hc : ∀ f, ∑ i : Fin 3, w (f,i) = 0) (f : F) :
    ∑ i : Fin 3, C.extension w (f,i) = 0 := by
  classical
  by_cases hf : f = C.f
  · subst f
    simp only [Fin.sum_univ_three, C.extension_f_zero]
    rw [C.extension_removed_nonzero w (C.f,1) (Or.inl rfl) (by simp) (by simp),
      C.extension_removed_nonzero w (C.f,2) (Or.inl rfl) (by simp) (by simp)]
    ring
  by_cases hg : f = C.g
  · subst f
    simp only [Fin.sum_univ_three, C.extension_g_zero]
    rw [C.extension_removed_nonzero w (C.g,1) (Or.inr rfl) (by simp) (by simp),
      C.extension_removed_nonzero w (C.g,2) (Or.inr rfl) (by simp) (by simp),
      C.sideValue_g_one w ha, C.sideValue_g_two w ha]
    ring
  · have hd (i : Fin 3) : ¬ C.Removed (f,i) := not_or.mpr ⟨hf,hg⟩
    simpa only [C.extension_outside w _ (hd _), toNewDart] using hc ⟨f,hf,hg⟩

/-- Deleting the opposite pair preserves exactness of edge cocycles. -/
theorem mesh_exact (he : M.Exact) : C.mesh.Exact := by
  intro w ha hc
  change ∀ d, w (C.newMate d) = -w d at ha
  obtain ⟨p,hp⟩ := he (C.extension w) (C.extension_mate w ha) (C.extension_face w ha hc)
  have hfg : p (M.tail (C.f,2)) = p (M.tail (C.g,2)) := by
    have hf := hp (C.f,1)
    have hg := hp (C.g,2)
    rw [C.extension_removed_nonzero w (C.f,1) (Or.inl rfl) (by simp) (by simp)] at hf
    rw [C.extension_removed_nonzero w (C.g,2) (Or.inr rfl) (by simp) (by simp),
      C.sideValue_g_two w ha] at hg
    change C.sideValue w (C.f,1) = p (M.tail (C.f,2)) - p (M.tail (C.f,1)) at hf
    change -C.sideValue w (C.f,1) = p (M.tail (C.g,0)) - p (M.tail (C.g,2)) at hg
    rw [C.tail_seam] at hg
    linarith
  have hm (v : V) : p (C.merge v) = p v := by
    unfold merge
    split_ifs with h
    · rw [h, hfg]
    · rfl
  refine ⟨p, fun d => ?_⟩
  have hd := hp (C.oldDart d)
  rw [C.extension_outside w _ (C.oldDart_kept d), C.toNewDart_oldDart] at hd
  change w d = p (C.merge (M.tail (rotate (C.oldDart d)))) - p (C.merge (M.tail (C.oldDart d)))
  rw [hm, hm]
  exact hd

end Fold
end ArtinCAT0.TriangleMesh
namespace ArtinCAT0.TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

noncomputable def active : TriangleMesh F (Set.range M.tail) where
  mate := M.mate
  mate_involutive := M.mate_involutive
  mate_ne := M.mate_ne
  tail d := ⟨M.tail d, Set.mem_range_self d⟩
  tail_mate d := Subtype.ext (M.tail_mate d)

lemma active_exact (he : M.Exact) : M.active.Exact := by
  intro w ha hc
  rcases he w ha hc with ⟨p,hp⟩
  exact ⟨fun v => p v.val, hp⟩

lemma active_surjective : Function.Surjective M.active.tail := by
  rintro ⟨v,d,rfl⟩
  exact ⟨d,rfl⟩

def phaseEquiv (c : F → Fin 3) : Equiv.Perm (F × Fin 3) where
  toFun d := (d.1,d.2+c d.1)
  invFun d := (d.1,d.2-c d.1)
  left_inv d := by ext <;> simp
  right_inv d := by ext <;> simp

@[simp] lemma phaseEquiv_apply (c : F → Fin 3) (d : F × Fin 3) :
    phaseEquiv c d = (d.1,d.2+c d.1) := rfl
@[simp] lemma phaseEquiv_symm_apply (c : F → Fin 3) (d : F × Fin 3) :
    (phaseEquiv c).symm d = (d.1,d.2-c d.1) := rfl

lemma phaseEquiv_rotate (c : F → Fin 3) (d : F × Fin 3) :
    phaseEquiv c (rotate d) = rotate (phaseEquiv c d) := by
  ext <;> simp [add_comm, add_left_comm, add_assoc]

noncomputable def rephase (c : F → Fin 3) : TriangleMesh F V where
  mate := (phaseEquiv c).symm * M.mate * phaseEquiv c
  mate_involutive d := by
    change (phaseEquiv c).symm (M.mate (phaseEquiv c ((phaseEquiv c).symm (M.mate (phaseEquiv c d))))) = d
    simp
  mate_ne d h := by
    apply M.mate_ne (phaseEquiv c d)
    have he := congrArg (phaseEquiv c) h
    simpa only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using he
  tail d := M.tail (phaseEquiv c d)
  tail_mate d := by
    change M.tail (phaseEquiv c ((phaseEquiv c).symm (M.mate (phaseEquiv c d)))) =
      M.tail (phaseEquiv c (rotate d))
    rw [Equiv.apply_symm_apply, M.tail_mate, phaseEquiv_rotate]
    rfl

lemma rephase_exact (c : F → Fin 3) (he : M.Exact) : (M.rephase c).Exact := by
  intro w ha hc
  let w' : F × Fin 3 → ℝ := fun d => w ((phaseEquiv c).symm d)
  have ha' : ∀ d, w' (M.mate d) = -w' d := by
    intro d
    simpa only [w', rephase, Equiv.Perm.mul_apply, Equiv.apply_symm_apply] using
      ha ((phaseEquiv c).symm d)
  have hc' : ∀ f, ∑ i : Fin 3, w' (f,i) = 0 := by
    intro f
    let e : Equiv.Perm (Fin 3) :=
      { toFun := fun i => i-c f
        invFun := fun i => i+c f
        left_inv := by intro i; simp
        right_inv := by intro i; simp }
    change ∑ i : Fin 3, w (f,e i) = 0
    rw [show (∑ i : Fin 3, w (f,e i)) = ∑ i : Fin 3, w (f,i) from
      Equiv.sum_comp e (fun i => w (f,i))]
    exact hc f
  rcases he w' ha' hc' with ⟨p,hp⟩
  refine ⟨p, fun d => ?_⟩
  have hh := hp (phaseEquiv c d)
  simpa only [w', Equiv.symm_apply_apply, rephase, phaseEquiv_rotate] using hh

end ArtinCAT0.TriangleMesh
namespace ArtinCAT0

def xLetter (b i : Fin 3) : Fin 9 :=
  if i = 0 then ⟨b.val, by omega⟩ else if i = 1 then ⟨(b+1).val, by omega⟩
  else ⟨3+b.val, by omega⟩

def hLetter (b : Fin 3) : Fin 9 := ⟨6+b.val, by omega⟩

def positiveDirection (q : Fin 9) : LinkDirection := ⟨q.val, by omega⟩
def negativeDirection (q : Fin 9) : LinkDirection := ⟨q.val+9, by omega⟩
def reverseDirection (d : LinkDirection) : LinkDirection := d+9

@[simp] lemma reverseDirection_reverseDirection (d : LinkDirection) :
    reverseDirection (reverseDirection d) = d := by
  unfold reverseDirection
  apply Fin.ext
  omega

/-- Directed sides, retaining the literal nine labels, not just their group values. -/
def cellDirection (b i s t : Fin 3) : LinkDirection :=
  if s = 0 ∧ t = 1 then positiveDirection (xLetter b i)
  else if s = 1 ∧ t = 2 then positiveDirection (xLetter b (i+1))
  else if s = 0 ∧ t = 2 then positiveDirection (hLetter b)
  else if s = 1 ∧ t = 0 then negativeDirection (xLetter b i)
  else if s = 2 ∧ t = 1 then negativeDirection (xLetter b (i+1))
  else negativeDirection (hLetter b)

lemma cellDirection_reverse : ∀ b i s t : Fin 3, s ≠ t →
    cellDirection b i t s = reverseDirection (cellDirection b i s t) := by decide

abbrev CornerOrder := Equiv.Perm (Fin 3)

def cellFlag (b i : Fin 3) (p : CornerOrder) : LinkDirection × LinkDirection :=
  (cellDirection b i (p 0) (p 1), cellDirection b i (p 0) (p 2))

lemma cellFlag_injective : Function.Injective
    (fun z : Fin 3 × Fin 3 × CornerOrder => cellFlag z.1 z.2.1 z.2.2) := by decide

lemma cellFlag_adjacent : ∀ b i : Fin 3, ∀ p : CornerOrder,
    (cellFlag b i p).2 ∈ linkNeighbors (cellFlag b i p).1 := by decide

lemma cellDirection_injective : ∀ b i : Fin 3, ∀ s t s' t' : Fin 3,
    s ≠ t → s' ≠ t' → cellDirection b i s t = cellDirection b i s' t' →
    s = s' ∧ t = t' := by decide

/-- Orientation sign of the vertex correspondence. -/
def cornerSign (p : CornerOrder) : ℤ := if p 1 = p 0 + 1 then 1 else -1

def reverseCorner (p : CornerOrder) : CornerOrder := p * Equiv.swap 1 2

lemma cornerSign_reverse : ∀ p : CornerOrder,
    cornerSign (reverseCorner p) = -cornerSign p := by decide

structure TargetTriangle where
  base : TriangleGroup
  block : Fin 3
  rel : Fin 3

def TargetTriangle.vertex (c : TargetTriangle) (i : Fin 3) : TriangleGroup :=
  c.base * (if i = 0 then 1 else if i = 1 then triangleX c.block c.rel else triangleH c.block)

def TargetTriangle.direction (c : TargetTriangle) (i j : Fin 3) :=
  cellDirection c.block c.rel i j

lemma TargetTriangle.vertex_injective (c : TargetTriangle) : Function.Injective c.vertex := by
  intro i j he
  have h := congrArg (fun g => Multiplicative.toAdd (triangleExponent g)) he
  have hi : Multiplicative.toAdd (triangleExponent (c.vertex i)) =
      Multiplicative.toAdd (triangleExponent c.base) + (i.val : ℤ) := by
    fin_cases i <;> simp [TargetTriangle.vertex]
  have hj : Multiplicative.toAdd (triangleExponent (c.vertex j)) =
      Multiplicative.toAdd (triangleExponent c.base) + (j.val : ℤ) := by
    fin_cases j <;> simp [TargetTriangle.vertex]
  rw [hi,hj] at h
  apply Fin.ext
  omega

namespace TriangleMesh
variable {F V : Type*} (M : TriangleMesh F V)

/-- Complete cell identities and vertex correspondences; compatibility includes
labelled directions rather than merely equal group elements. -/
structure Labeling where
  cell : F → TargetTriangle
  order : F → CornerOrder
  vertex : V → TriangleGroup
  vertex_tail : ∀ d, vertex (M.tail d) = (cell d.1).vertex (order d.1 d.2)
  mate_compatibility : ∀ d,
    (cell (M.mate d).1).direction (order (M.mate d).1 (M.mate d).2)
      (order (M.mate d).1 ((M.mate d).2+1)) =
    reverseDirection ((cell d.1).direction (order d.1 d.2) (order d.1 (d.2+1)))

namespace Labeling
variable {M} (L : M.Labeling)

def direction (d : F × Fin 3) : LinkDirection :=
  (L.cell d.1).direction (L.order d.1 d.2) (L.order d.1 (d.2+1))

@[simp] lemma direction_mate (d : F × Fin 3) :
    L.direction (M.mate d) = reverseDirection (L.direction d) := L.mate_compatibility d

def cornerShift (i : Fin 3) : CornerOrder where
  toFun j := i+j
  invFun j := j-i
  left_inv j := by simp
  right_inv j := by simp

@[simp] lemma cornerShift_apply (i j : Fin 3) : cornerShift i j = i+j := rfl

def cornerAt (d : F × Fin 3) : CornerOrder := L.order d.1 * cornerShift d.2

lemma direction_turn (d : F × Fin 3) :
    L.direction (M.turn d) = (L.cell d.1).direction (L.order d.1 d.2) (L.order d.1 (d.2+2)) := by
  rw [turn_apply, L.direction_mate]
  change reverseDirection (cellDirection _ _ (L.order d.1 (d.2-1))
    (L.order d.1 (d.2-1+1))) = _
  rw [sub_add_cancel, ← cellDirection_reverse]
  · congr 2
    apply Fin.ext
    omega
  · apply (L.order d.1).injective.ne
    intro h
    have := congrArg Fin.val h
    omega

lemma flag_cornerAt (d : F × Fin 3) :
    cellFlag (L.cell d.1).block (L.cell d.1).rel (L.cornerAt d) =
      (L.direction d, L.direction (M.turn d)) := by
  rw [L.direction_turn]
  simp [cellFlag, cornerAt, direction, TargetTriangle.direction]

lemma link_adjacent (d : F × Fin 3) :
    L.direction (M.turn d) ∈ linkNeighbors (L.direction d) := by
  have h := cellFlag_adjacent (L.cell d.1).block (L.cell d.1).rel (L.cornerAt d)
  simpa only [L.flag_cornerAt] using h

include L in
lemma mate_face_ne (d : F × Fin 3) : (M.mate d).1 ≠ d.1 := by
  intro he
  have h := L.direction_mate d
  simp only [direction, he, TargetTriangle.direction] at h
  have hf : ∀ (b i : Fin 3) (p : CornerOrder) (j k : Fin 3),
      cellDirection b i (p j) (p (j+1)) ≠
        reverseDirection (cellDirection b i (p k) (p (k+1))) := by decide
  exact hf _ _ _ _ _ h

lemma cellFlag_reverse (b i : Fin 3) (p : CornerOrder) :
    cellFlag b i (reverseCorner p) = (cellFlag b i p).swap := by
  simp [cellFlag, reverseCorner, show (Equiv.swap (1 : Fin 3) 2) 0 = 0 from by decide]

lemma backtrack_cell (d : F × Fin 3)
    (hb : L.direction (M.turn (M.turn d)) = L.direction d) :
    L.cell (M.turn d).1 = L.cell d.1 ∧
    L.cornerAt (M.turn d) = reverseCorner (L.cornerAt d) := by
  have hf : cellFlag (L.cell (M.turn d).1).block (L.cell (M.turn d).1).rel
      (L.cornerAt (M.turn d)) =
      cellFlag (L.cell d.1).block (L.cell d.1).rel (reverseCorner (L.cornerAt d)) := by
    rw [L.flag_cornerAt, cellFlag_reverse, L.flag_cornerAt, hb]
    rfl
  have hh := cellFlag_injective
    (a₁ := ((L.cell (M.turn d).1).block, (L.cell (M.turn d).1).rel, L.cornerAt (M.turn d)))
    (a₂ := ((L.cell d.1).block, (L.cell d.1).rel, reverseCorner (L.cornerAt d))) hf
  have hblock := congrArg Prod.fst hh
  have hrel := congrArg (fun x => x.2.1) hh
  have hp := congrArg (fun x => x.2.2) hh
  dsimp only at hblock hrel hp
  refine ⟨?_,hp⟩
  have hv : (L.cell (M.turn d).1).vertex (L.order (M.turn d).1 (M.turn d).2) =
      (L.cell d.1).vertex (L.order d.1 d.2) := by
    rw [← L.vertex_tail, ← L.vertex_tail, M.tail_turn]
  have hp0 := Equiv.congr_fun hp 0
  simp only [cornerAt, Equiv.Perm.mul_apply, cornerShift_apply, add_zero,
    reverseCorner, Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 2)] at hp0
  rw [hp0] at hv
  simp only [TargetTriangle.vertex, hblock, hrel, mul_left_inj] at hv
  cases hc : L.cell (M.turn d).1
  cases hd : L.cell d.1
  simp_all

noncomputable def active : M.active.Labeling where
  cell := L.cell
  order := L.order
  vertex v := L.vertex v.val
  vertex_tail := L.vertex_tail
  mate_compatibility := L.mate_compatibility

noncomputable def rephase (c : F → Fin 3) : (M.rephase c).Labeling where
  cell := L.cell
  order f := L.order f * cornerShift (c f)
  vertex := L.vertex
  vertex_tail d := by
    simpa [TriangleMesh.rephase, phaseEquiv, cornerShift, add_comm] using
      L.vertex_tail (d.1,d.2+c d.1)
  mate_compatibility d := by
    have hh := L.mate_compatibility (phaseEquiv c d)
    change cellDirection _ _ _ _ = reverseDirection (cellDirection _ _ _ _) at hh ⊢
    simp only [TriangleMesh.rephase, Equiv.Perm.mul_apply, phaseEquiv_apply,
      phaseEquiv_symm_apply, cornerShift_apply] at *
    simpa [add_comm, add_left_comm, add_assoc] using hh

lemma orders_of_seam {f g : F} (he : L.cell g = L.cell f)
    (hs : M.mate (f,0) = (g,0)) :
    L.order g 0 = L.order f 1 ∧ L.order g 1 = L.order f 0 := by
  have ht0 : M.tail (g,0) = M.tail (f,1) := by
    simpa [hs] using M.tail_mate (f,0)
  have ht1 : M.tail (g,1) = M.tail (f,0) := by
    simpa [hs, rotate_apply] using M.tail_rotate_mate (f,0)
  constructor
  · apply (L.cell f).vertex_injective
    rw [← he, ← L.vertex_tail (g,0), ht0, L.vertex_tail (f,1), he]
  · apply (L.cell f).vertex_injective
    rw [← he, ← L.vertex_tail (g,1), ht1, L.vertex_tail (f,0), he]

lemma order_seam_remaining : ∀ p q : CornerOrder,
    q 0 = p 1 → q 1 = p 0 → q 2 = p 2 := by decide

lemma order_seam_sign : ∀ p q : CornerOrder,
    q 0 = p 1 → q 1 = p 0 → cornerSign q = -cornerSign p := by decide

lemma order_seam_mate : ∀ (b k : Fin 3) (p q : CornerOrder),
    q 0 = p 1 → q 1 = p 0 → ∀ i j : Fin 3,
    cellDirection b k (q j) (q (j+1)) =
      reverseDirection (cellDirection b k (p i) (p (i+1))) → j = -i := by decide

noncomputable def seamFold {f g : F} (he : L.cell g = L.cell f)
    (hs : M.mate (f,0) = (g,0)) : M.Fold where
  f := f
  g := g
  ne := by
    intro h
    have hh := L.mate_face_ne (f,0)
    exact hh (by simpa [hs] using h.symm)
  seam := hs
  internal d hd hm := by
    obtain ⟨h0,h1⟩ := L.orders_of_seam he hs
    rcases d with ⟨a,i⟩
    rcases hm with hm | hm
    · rcases hd with hd | hd
      · dsimp only at *
        exact False.elim (L.mate_face_ne (a,i) (hm.trans hd.symm))
      · dsimp only at hd hm
        subst a
        have hh := L.mate_compatibility (g,i)
        simp only [hm, he, TargetTriangle.direction] at hh
        have hj := order_seam_mate _ _ (L.order g) (L.order f) h1.symm h0.symm i _ hh
        apply Prod.ext
        · simpa [foldPartner, show g ≠ f from fun h => L.mate_face_ne (f,0) (by simp [hs,h])]
        · simpa [foldPartner, show g ≠ f from fun h => L.mate_face_ne (f,0) (by simp [hs,h])] using hj
    · rcases hd with hd | hd
      · dsimp only at hd hm
        subst a
        have hh := L.mate_compatibility (f,i)
        simp only [hm, he, TargetTriangle.direction] at hh
        have hj := order_seam_mate _ _ (L.order f) (L.order g) h0 h1 i _ hh
        apply Prod.ext
        · simpa [foldPartner] using hm
        · simpa [foldPartner] using hj
      · dsimp only at *
        exact False.elim (L.mate_face_ne (a,i) (hm.trans hd.symm))

lemma vertex_merge (C : M.Fold) (he : L.cell C.g = L.cell C.f) (v : V) :
    L.vertex (C.merge v) = L.vertex v := by
  have hh := L.orders_of_seam he C.seam
  have hp := order_seam_remaining (L.order C.f) (L.order C.g) hh.1 hh.2
  unfold Fold.merge
  split_ifs with hv
  · subst v
    rw [L.vertex_tail, L.vertex_tail, he, hp]
  · rfl

lemma direction_partner (C : M.Fold) (he : L.cell C.g = L.cell C.f)
    (d : F × Fin 3) (hd : C.Removed d) :
    L.direction (C.partner d) = reverseDirection (L.direction d) := by
  have hh := L.orders_of_seam he C.seam
  have hc : ∀ (b k : Fin 3) (p q : CornerOrder),
      q 0 = p 1 → q 1 = p 0 → ∀ i : Fin 3,
      cellDirection b k (q (-i)) (q (-i+1)) =
        reverseDirection (cellDirection b k (p i) (p (i+1))) := by decide
  rcases d with ⟨f,i⟩
  rcases hd with hd | hd <;> dsimp only at hd <;> subst f
  · simpa only [C.partner_f, direction, he, TargetTriangle.direction] using
      hc (L.cell C.f).block (L.cell C.f).rel (L.order C.f) (L.order C.g) hh.1 hh.2 i
  · simpa only [C.partner_g, direction, he, TargetTriangle.direction] using
      hc (L.cell C.f).block (L.cell C.f).rel (L.order C.g) (L.order C.f) hh.2.symm hh.1.symm i

noncomputable def folded (C : M.Fold) (he : L.cell C.g = L.cell C.f) : C.mesh.Labeling where
  cell f := L.cell f.val
  order f := L.order f.val
  vertex := L.vertex
  vertex_tail d := by
    change L.vertex (C.merge (M.tail (C.oldDart d))) = _
    rw [L.vertex_merge C he, L.vertex_tail]
  mate_compatibility d := by
    change L.direction (C.splice (C.oldDart d)) = reverseDirection (L.direction (C.oldDart d))
    by_cases hm : C.Removed (M.mate (C.oldDart d))
    · rw [C.splice_inside _ hm, L.direction_mate, L.direction_partner C he _ hm,
        L.direction_mate, reverseDirection_reverseDirection]
    · rw [C.splice_outside _ hm, L.direction_mate]

lemma exists_equal_mates [Fintype F] [Nonempty F] (he : M.Exact) :
    ∃ d, L.cell (M.mate d).1 = L.cell d.1 := by
  classical
  let : Fintype (Set.range M.tail) := Fintype.ofFinite _
  obtain ⟨d,hd⟩ := M.active.exists_link_backtrack (M.active_exact he) M.active_surjective
    L.active.direction L.active.link_adjacent
  have hh := L.active.backtrack_cell d hd
  exact ⟨rotate.symm d, hh.1⟩

lemma exists_phased_seam [Fintype F] [Nonempty F] (he : M.Exact) :
    ∃ (c : F → Fin 3) (f g : F),
      (M.rephase c).mate (f,0) = (g,0) ∧ L.cell g = L.cell f := by
  classical
  obtain ⟨d,hd⟩ := L.exists_equal_mates he
  let f := d.1
  let g := (M.mate d).1
  have hne : g ≠ f := L.mate_face_ne d
  let c : F → Fin 3 := fun a => if a = f then d.2 else if a = g then (M.mate d).2 else 0
  refine ⟨c,f,g,?_,hd⟩
  change (phaseEquiv c).symm (M.mate (phaseEquiv c (f,0))) = (g,0)
  have hcf : c f = d.2 := by simp [c]
  have hcg : c g = (M.mate d).2 := by simp [c,hne]
  have hpf : phaseEquiv c (f,0) = d := by simp [f,hcf]
  rw [hpf]
  change ((M.mate d).1,(M.mate d).2 - c (M.mate d).1) = (g,0)
  rw [hcg]
  simp [g]

lemma cornerSign_shift : ∀ (p : CornerOrder) (i : Fin 3),
    cornerSign (p * cornerShift i) = cornerSign p := by decide

noncomputable def signedSum [Fintype F] (w : TargetTriangle → ℤ) : ℤ :=
  ∑ f, cornerSign (L.order f) * w (L.cell f)

@[simp] lemma signedSum_active [Fintype F] (w : TargetTriangle → ℤ) :
    L.active.signedSum w = L.signedSum w := rfl

@[simp] lemma signedSum_rephase [Fintype F] (c : F → Fin 3) (w : TargetTriangle → ℤ) :
    (L.rephase c).signedSum w = L.signedSum w := by
  simp only [signedSum, rephase, cornerSign_shift]

lemma signedSum_folded [Fintype F] (C : M.Fold) [Fintype C.Kept] (he : L.cell C.g = L.cell C.f)
    (w : TargetTriangle → ℤ) : (L.folded C he).signedSum w = L.signedSum w := by
  classical
  let q : F → ℤ := fun f => cornerSign (L.order f) * w (L.cell f)
  have hs := L.orders_of_seam he C.seam
  have hz : q C.g + q C.f = 0 := by
    dsimp only [q]
    rw [order_seam_sign (L.order C.f) (L.order C.g) hs.1 hs.2, he]
    ring
  have hf := Finset.sum_erase_add Finset.univ q (Finset.mem_univ C.f)
  have hg := Finset.sum_erase_add (Finset.univ.erase C.f) q
    (by simp [C.ne.symm] : C.g ∈ Finset.univ.erase C.f)
  have hh : (∑ x ∈ (Finset.univ.erase C.f).erase C.g, q x) = ∑ f : C.Kept, q f.val :=
    Finset.sum_subtype (Finset.univ.erase C.f |>.erase C.g)
    (p := fun f => f ≠ C.f ∧ f ≠ C.g) (F := inferInstance) (by intro f; simp [and_comm]) q
  change (∑ f : C.Kept, q f.val) = ∑ f, q f
  omega

end Labeling

universe u v

/-- Every exact finite labelled triangular mesh has zero algebraic count on
 each individual target triangle. No manifold or embedding theorem is assumed. -/
theorem signed_counts_zero (w : TargetTriangle → ℤ) :
    ∀ (F : Type u) (V : Type v) [Fintype F] (M : TriangleMesh F V) (L : M.Labeling),
      M.Exact → L.signedSum w = 0 := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (F : Type u) (V : Type v) [Fintype F]
      (M : TriangleMesh F V) (L : M.Labeling),
      Fintype.card F = n → M.Exact → L.signedSum w = 0 by
    intro F V _ M L he
    exact hh (Fintype.card F) F V M L rfl he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F V _ M L hn he
    cases isEmpty_or_nonempty F with
    | inl hi =>
      let := hi
      simp [Labeling.signedSum]
    | inr hi =>
      let := hi
      obtain ⟨c,f,g,hs,hcell⟩ := L.exists_phased_seam he
      let C : (M.rephase c).Fold := (L.rephase c).seamFold hcell hs
      have hc : C.mesh.Exact := C.mesh_exact (M.rephase_exact c he)
      have hl : (L.rephase c).cell C.g = (L.rephase c).cell C.f := hcell
      have hcard : Fintype.card C.Kept < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (x := C.f) (by simp)
      have hp := ih (Fintype.card C.Kept) hcard C.Kept V C.mesh
        ((L.rephase c).folded C hl) rfl hc
      rw [(L.rephase c).signedSum_folded C hl, L.signedSum_rephase] at hp
      exact hp
end TriangleMesh
end ArtinCAT0

end OAI
