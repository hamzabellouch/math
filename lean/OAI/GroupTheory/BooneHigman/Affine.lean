import OAI.GroupTheory.BooneHigman.Steinberg

namespace OAI


/-!
Rank-six affine relations, modules, and finite affine presentations.
-/


/- The rank-six affine presentation. -/
namespace FiniteAlgebraicEnvelopes
namespace AffinePresentation
open scoped commutatorElement

variable {R Q : Type*} [Ring R] [Group Q]
variable (ρ : Steinberg.Group (Fin 6) R →* Q) (p : Fin 6 → Q)

abbrev X (a b : Fin 6) (r : R) := ρ (Steinberg.x a b r)

@[simp] theorem X_zero (a b : Fin 6) : X ρ a b (0 : R) = 1 := by simp [X]
theorem X_add (a b : Fin 6) (r s : R) : X ρ a b (r+s) = X ρ a b r * X ρ a b s := by
  simp only [X, Steinberg.x_add, map_mul]
@[simp] theorem X_neg (a b : Fin 6) (r : R) : X ρ a b (-r) = (X ρ a b r)⁻¹ := by simp [X]
theorem X_chain (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (r s : R) :
    ⁅X ρ a b r, X ρ b c s⁆ = X ρ a c (r*s) := by
  rw [← map_commutatorElement, Steinberg.x_chain a b c hab hbc hac]
theorem X_distant (a b c d : Fin 6) (had : a ≠ d) (hbc : b ≠ c) (r s : R) :
    Commute (X ρ a b r) (X ρ c d s) := (Steinberg.x_distant a b c d had hbc r s).map ρ

private theorem fresh (a b c : Fin 6) : ∃ h : Fin 6, h ≠ a ∧ h ≠ b ∧ h ≠ c := by
  have h : ∃ i ∈ (Finset.univ : Finset (Fin 6)), i ∉ ({a,b,c} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have : ({a,b,c} : Finset (Fin 6)).card ≤ 3 := by
      exact le_trans (Finset.card_insert_le _ _) (by
        simpa only [Finset.card_singleton] using
          Nat.add_le_add_right (Finset.card_insert_le b {c}) 1)
    simpa using (show ({a,b,c} : Finset (Fin 6)).card < 6 by omega)
  simpa only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    not_or] using h

private theorem commutator_commute {a b c : Q} (hb : Commute a b) (hc : Commute a c) :
    Commute a ⁅b,c⁆ := by
  rw [commutatorElement_def]
  exact ((hb.mul_right hc).mul_right hb.inv_right).mul_right hc.inv_right

/-- The finite coefficient relations propagate to every coefficient. -/
theorem coefficients (F : Finset R) (h1 : (1:R) ∈ F)
    (hgen : Subring.closure (↑F : Set R) = ⊤)
    (hc : ∀ r ∈ F, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c)) :
    ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c) := by
  intro r
  have hr : r ∈ Subring.closure (↑F : Set R) := by rw [hgen]; trivial
  induction hr using Subring.closure_induction with
  | mem r hr => exact hc r hr
  | zero => intro a b c _; simp
  | one => exact hc 1 h1
  | add r s _ _ hr hs => intro a b c h; rw [X_add]; exact (hr a b c h).mul_left (hs a b c h)
  | neg r _ hr => intro a b c h; rw [X_neg]; exact (hr a b c h).inv_left
  | mul r s _ _ hr hs =>
    intro a b c hcb
    by_cases hab : a = b
    · subst b; simp [X]
    obtain ⟨h,ha,hb,hc'⟩ := fresh a b c
    rw [← X_chain ρ a h b ha.symm hb hab]
    exact (commutator_commute (hr a h c hc'.symm).symm (hs h b c hcb).symm).symm

variable (hp : ∀ a b, Commute (p a) (p b))
variable (hc : ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c))
variable (hu : ∀ a b, a ≠ b → ⁅X ρ a b 1, p b⁆ = p a)

def wcolumn (a b : Fin 6) (r : R) : Q := ⁅X ρ a b r, p b⁆

private theorem conj_of_commute {x y : Q} (h : Commute x y) : MulAut.conj x y = y := by
  rw [conj_eq_commutatorElement_mul, h.commutator_eq, one_mul]

private theorem mul_eq_commutator (x y : Q) : x*y = ⁅x,y⁆*y*x := by
  simp [commutatorElement_def, mul_assoc]

include hp hc hu

/-- Independence of the auxiliary column in the presentation. -/
theorem wcolumn_independent (a b h : Fin 6) (hab : a ≠ b) (hah : a ≠ h) (hbh : b ≠ h) (r : R) :
    wcolumn ρ p a b r = wcolumn ρ p a h r := by
  have hxy : X ρ a h r * X ρ h b 1 = X ρ a b r * X ρ h b 1 * X ρ a h r := by
    rw [mul_eq_commutator, X_chain ρ a h b hah hbh.symm hab, mul_one]
  have hy : MulAut.conj (X ρ h b 1) (p b) = p h * p b := by
    rw [conj_eq_commutatorElement_mul, hu h b hbh.symm]
  have hx : MulAut.conj (X ρ a h r) (p b) = p b := conj_of_commute (hc r a h b hbh)
  have hz : MulAut.conj (X ρ a b r) (p h) = p h := conj_of_commute (hc r a b h hbh.symm)
  have hh := congrArg (fun q => MulAut.conj q (p b)) hxy
  simp only [map_mul, MulAut.mul_apply] at hh
  simp only [hy, map_mul, hx, hz] at hh
  rw [conj_eq_commutatorElement_mul, conj_eq_commutatorElement_mul] at hh
  have cc : Commute (p h) (wcolumn ρ p a b r) :=
    commutator_commute (hc r a b h hbh.symm).symm (hp h b)
  change (wcolumn ρ p a h r * p h) * p b = p h * (wcolumn ρ p a b r * p b) at hh
  have he : wcolumn ρ p a h r * p h = p h * wcolumn ρ p a b r :=
    mul_right_cancel (by simpa only [mul_assoc] using hh)
  rw [cc.eq] at he
  exact (mul_right_cancel he).symm


noncomputable def other (a : Fin 6) : Fin 6 := (fresh a a a).choose

omit hp hc hu in
theorem other_ne (a : Fin 6) : other a ≠ a := (fresh a a a).choose_spec.1

noncomputable def w (a : Fin 6) (r : R) : Q := wcolumn ρ p a (other a) r

theorem w_eq_column (a b : Fin 6) (hab : a ≠ b) (r : R) :
    w ρ p a r = wcolumn ρ p a b r := by
  by_cases hb : other a = b
  · simp [w, hb]
  · exact wcolumn_independent ρ p hp hc hu a (other a) b (other_ne a).symm hab hb r

theorem w_commute_p (a c : Fin 6) (r : R) : Commute (w ρ p a r) (p c) := by
  obtain ⟨b,ha,hc',_⟩ := fresh a c c
  rw [w_eq_column ρ p hp hc hu a b ha.symm]
  exact (commutator_commute (hc r a b c hc'.symm).symm (hp c b)).symm

theorem w_commute_X (a c d : Fin 6) (hda : d ≠ a) (r s : R) :
    Commute (w ρ p a r) (X ρ c d s) := by
  obtain ⟨b,ha,hb,hbd⟩ := fresh a c d
  rw [w_eq_column ρ p hp hc hu a b ha.symm]
  exact (commutator_commute (X_distant ρ a b c d hda.symm hb r s).symm
    (hc s c d b hbd)).symm

theorem w_commute (a c : Fin 6) (r s : R) : Commute (w ρ p a r) (w ρ p c s) := by
  obtain ⟨b,ha,hb,_⟩ := fresh a c c
  rw [w_eq_column ρ p hp hc hu c b hb.symm]
  exact commutator_commute (w_commute_X ρ p hp hc hu a c b ha r s)
    (w_commute_p ρ p hp hc hu a b r)

omit hp hc hu in
@[simp] theorem w_zero (a : Fin 6) : w ρ p a (0:R) = 1 := by
  simp [w, wcolumn]

theorem w_add (a : Fin 6) (r s : R) : w ρ p a (r+s) = w ρ p a r * w ρ p a s := by
  let b := other a
  have hab := (other_ne a).symm
  rw [w_eq_column ρ p hp hc hu a b hab, wcolumn, X_add,
    commutatorElement_mul_left_eq_conj_mul]
  change MulAut.conj (X ρ a b r) (wcolumn ρ p a b s) * wcolumn ρ p a b r = _
  rw [← w_eq_column ρ p hp hc hu a b hab, ← w_eq_column ρ p hp hc hu a b hab,
    conj_of_commute (w_commute_X ρ p hp hc hu a a b hab.symm s r).symm,
    (w_commute ρ p hp hc hu a a s r).eq]

omit hp hc in
@[simp] theorem w_one (a : Fin 6) : w ρ p a (1:R) = p a :=
  hu a (other a) (other_ne a).symm

noncomputable def wAdd (a : Fin 6) : R →+ Additive Q where
  toFun r := Additive.ofMul (w ρ p a r)
  map_zero' := w_zero ρ p a
  map_add' := w_add ρ p hp hc hu a

/-- This is exactly the elementary action on a column, derived in the presentation. -/
theorem root_conjugation (c a : Fin 6) (hca : c ≠ a) (s r : R) :
    MulAut.conj (X ρ c a s) (w ρ p a r) = w ρ p a r * w ρ p c (s*r) := by
  obtain ⟨b,hba,hbc,_⟩ := fresh a c c
  have hxy : MulAut.conj (X ρ c a s) (X ρ a b r) = X ρ c b (s*r) * X ρ a b r := by
    rw [conj_eq_commutatorElement_mul, X_chain ρ c a b hca hba.symm hbc.symm]
  have hp' : MulAut.conj (X ρ c a s) (p b) = p b := conj_of_commute (hc s c a b hba)
  rw [w_eq_column ρ p hp hc hu a b hba.symm, wcolumn, map_commutatorElement,
    hxy, hp', commutatorElement_mul_left_eq_conj_mul]
  change MulAut.conj (X ρ c b (s*r)) (wcolumn ρ p a b r) * wcolumn ρ p c b (s*r) = _
  rw [← w_eq_column ρ p hp hc hu a b hba.symm,
    ← w_eq_column ρ p hp hc hu c b hbc.symm,
    conj_of_commute (w_commute_X ρ p hp hc hu a c b hba r (s*r)).symm]
  rw [w_eq_column ρ p hp hc hu a b hba.symm]
  rfl

/-- The finite ideal relations imply all relations in the left ideal they generate. -/
theorem w_span (D : Set R) (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d, p b⁆ = 1)
    {r : R} (hr : r ∈ Submodule.span R D) (c : Fin 6) : w ρ p c r = 1 := by
  suffices hh : ∀ c, w ρ p c r = 1 from hh c
  induction hr using Submodule.span_induction with
  | mem d hd' => intro c; exact hd d hd' c (other c) (other_ne c).symm
  | zero => intro c; exact w_zero ρ p c
  | add r s _ _ hr hs => intro c; rw [w_add ρ p hp hc hu, hr, hs, one_mul]
  | smul s r _ hr =>
    intro c
    have h := root_conjugation ρ p hp hc hu c (other c) (other_ne c).symm s r
    rw [hr, map_one, one_mul] at h
    exact h.symm


variable (D : Set R)
variable (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d, p b⁆ = 1)

noncomputable def rowMap (a : Fin 6) : (R ⧸ Submodule.span R D) →+ Additive Q :=
  QuotientAddGroup.lift (Submodule.span R D).toAddSubgroup (wAdd ρ p hp hc hu a) (by
    intro r hr
    exact w_span ρ p hp hc hu D hd hr a)

@[simp] theorem rowMap_mk (a : Fin 6) (r : R) :
    rowMap ρ p hp hc hu D hd a (Submodule.Quotient.mk r) = Additive.ofMul (w ρ p a r) := rfl

noncomputable def translationsAdd : (Fin 6 → R ⧸ Submodule.span R D) →+ Additive Q :=
  AddMonoidHom.noncommPiCoprod (rowMap ρ p hp hc hu D hd) (by
    intro a b _ x y
    obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) x
    obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) y
    exact w_commute ρ p hp hc hu a b r s)

noncomputable def translations : Multiplicative (Fin 6 → R ⧸ Submodule.span R D) →* Q :=
  (MulEquiv.multiplicativeAdditive Q).toMonoidHom.comp
    (AddMonoidHom.toMultiplicative (translationsAdd ρ p hp hc hu D hd))

@[simp] theorem translations_single (a : Fin 6) (x : R ⧸ Submodule.span R D) :
    translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single a x)) =
      (rowMap ρ p hp hc hu D hd a x).toMul := by
  change (translationsAdd ρ p hp hc hu D hd) (Pi.single a x) = _
  exact AddMonoidHom.noncommPiCoprod_single (rowMap ρ p hp hc hu D hd) a x

@[simp] theorem translations_single_mk (a : Fin 6) (r : R) :
    translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single a (Submodule.Quotient.mk r))) = w ρ p a r := by
  rw [translations_single, rowMap_mk]; rfl

end AffinePresentation

namespace AffineAction
open scoped commutatorElement
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- A matrix elementary operation on columns in an arbitrary left module. -/
def transvection (a b : Fin 6) (hab : a ≠ b) (r : R) : (Fin 6 → V) ≃+ (Fin 6 → V) where
  toFun v i := if i = a then v i + r • v b else v i
  invFun v i := if i = a then v i - r • v b else v i
  left_inv v := by
    funext i
    by_cases h : i=a <;> simp [h, hab.symm]
  right_inv v := by
    funext i
    by_cases h : i=a <;> simp [h, hab.symm]
  map_add' v w := by
    funext i
    by_cases h : i=a <;> simp [h,smul_add]; abel

@[simp] theorem transvection_apply (a b : Fin 6) (hab) (r : R) (v : Fin 6 → V) (i) :
    transvection a b hab r v i = if i=a then v i + r • v b else v i := rfl

def elementary (a b : Fin 6) (hab : a ≠ b) (r : R) : MulAut (Multiplicative (Fin 6 → V)) :=
  AddEquiv.toMultiplicative (transvection a b hab r)

@[simp] theorem elementary_apply (a b : Fin 6) (hab) (r : R) (v : Multiplicative (Fin 6 → V)) (i) :
    (elementary a b hab r v).toAdd i = if i=a then v.toAdd i + r • v.toAdd b else v.toAdd i := rfl


/-- The elementary displacement is supported in the one prescribed row. -/
theorem elementary_column (a b : Fin 6) (hab) (r : R) (v : Fin 6 → V) :
    (elementary a b hab r (Multiplicative.ofAdd v)).toAdd = v + Pi.single a (r • v b) := by
  funext i
  simp only [elementary_apply, toAdd_ofAdd, Pi.add_apply, Pi.single_apply]
  by_cases hi : i=a
  · subst i; simp
  · simp [hi]

theorem elementary_add (a b : Fin 6) (hab) (r s : R) :
    elementary (V:=V) a b hab r * elementary a b hab s = elementary a b hab (r+s) := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary a b hab s v)).toAdd i = _
  simp only [elementary_apply]
  by_cases h : i=a <;> simp [h,hab.symm,add_smul]; abel

@[simp] theorem elementary_zero (a b : Fin 6) (hab) : elementary (R:=R) (V:=V) a b hab 0 = 1 := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab (0:R) v).toAdd i = v.toAdd i
  simp only [elementary_apply, zero_smul, add_zero, ite_self]

@[simp] theorem elementary_neg (a b : Fin 6) (hab) (r : R) :
    elementary (V:=V) a b hab (-r) = (elementary a b hab r)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [elementary_add, add_neg_cancel, elementary_zero]

theorem elementary_chain (a b c : Fin 6) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (r s : R) :
    ⁅elementary (V:=V) a b hab r, elementary (V:=V) b c hbc s⁆ = elementary a c hac (r*s) := by
  rw [commutatorElement_def, ← elementary_neg, ← elementary_neg]
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary b c hbc s
    (elementary a b hab (-r) (elementary b c hbc (-s) v)))).toAdd i = _
  simp only [elementary_apply]
  by_cases hi : i=a
  · subst i; simp [hab,hab.symm,hbc.symm,hac.symm,smul_add,smul_smul]; abel
  · by_cases hj : i=b
    · subst i; simp [hab.symm,hbc.symm,hac.symm]
    · simp [hi,hj]

theorem elementary_distant (a b c d : Fin 6) (hab : a ≠ b) (hcd : c ≠ d)
    (had : a ≠ d) (hbc : b ≠ c) (r s : R) :
    Commute (elementary (V:=V) a b hab r) (elementary c d hcd s) := by
  change elementary a b hab r * elementary c d hcd s = elementary c d hcd s * elementary a b hab r
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  funext i
  change (elementary a b hab r (elementary c d hcd s v)).toAdd i =
    (elementary c d hcd s (elementary a b hab r v)).toAdd i
  simp only [elementary_apply]
  simp only [ite_eq_right hbc, ite_eq_right had.symm]
  split_ifs <;> abel

/-- The actual Steinberg action, with its three defining relations verified. -/
def action : Steinberg.Group (Fin 6) R →* MulAut (Multiplicative (Fin 6 → V)) :=
  PresentedGroup.toGroup (f := fun z : Steinberg.Generator (Fin 6) R =>
    elementary z.1.1.1 z.1.1.2 z.1.2 z.2) (by
      intro w hw
      cases hw with
      | additive a b hab r s =>
        simp only [map_mul,map_inv,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        rw [elementary_add,mul_inv_cancel]
      | chain a b c hab hbc hac r s =>
        simp only [map_mul,map_inv,map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        rw [elementary_chain a b c hab hbc hac,mul_inv_cancel]
      | distant a b c d hab hcd had hbc r s =>
        simp only [map_commutatorElement,Steinberg.freeRoot,FreeGroup.lift_apply_of]
        exact (elementary_distant a b c d hab hcd had hbc r s).commutator_eq)

@[simp] theorem action_root (a b : Fin 6) (hab) (r : R) :
    action (V:=V) (Steinberg.root a b hab r) = elementary a b hab r := PresentedGroup.toGroup.of _

abbrev Group := SemidirectProduct (Multiplicative (Fin 6 → V)) (Steinberg.Group (Fin 6) R) (action (R:=R) (V:=V))


/-- It suffices to check equivariance on actual Steinberg generators. -/
theorem equivariant_of_roots {Q : Type*} [_root_.Group Q]
    (τ : Multiplicative (Fin 6 → V) →* Q) (ρ : Steinberg.Group (Fin 6) R →* Q)
    (hr : ∀ a b hab r v, τ (elementary a b hab r v) =
      MulAut.conj (ρ (Steinberg.root a b hab r)) (τ v)) :
    ∀ g v, τ (action (R:=R) (V:=V) g v) = MulAut.conj (ρ g) (τ v) := by
  let C : Subgroup (Steinberg.Group (Fin 6) R) := {
    carrier := {g | ∀ v, τ (action g v) = MulAut.conj (ρ g) (τ v)}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro g h hg hh v
      change ∀ v, _ at hg hh
      simp only [map_mul, MulAut.mul_apply, hg, hh]
    inv_mem' := by
      intro g hg v
      have he := hg (action (g⁻¹) v)
      have he1 : action (R:=R) (V:=V) g (action (g⁻¹) v) = v := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [he1] at he
      have he2 := congrArg (MulAut.conj (ρ (g⁻¹))) he
      have he3 : MulAut.conj (ρ (g⁻¹)) (MulAut.conj (ρ g) (τ (action (g⁻¹) v))) =
          τ (action (g⁻¹) v) := by
        rw [← MulAut.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
        rfl
      rw [he3] at he2
      exact he2.symm }
  have ht : ⊤ ≤ C := by
    rw [← PresentedGroup.closure_range_of]
    apply (Subgroup.closure_le C).mpr
    rintro _ ⟨⟨⟨⟨a,b⟩,hab⟩,r⟩,rfl⟩
    change ∀ v, τ (action (Steinberg.root a b hab r) v) = _
    rw [action_root]
    exact hr a b hab r
  intro g
  exact ht (Subgroup.mem_top g)

end AffineAction

namespace AffinePresentation
open scoped commutatorElement
variable {R Q : Type*} [Ring R] [Group Q]
variable (ρ : Steinberg.Group (Fin 6) R →* Q) (p : Fin 6 → Q)
variable (hp : ∀ a b, Commute (p a) (p b))
variable (hc : ∀ r : R, ∀ a b c : Fin 6, c ≠ b → Commute (X ρ a b r) (p c))
variable (hu : ∀ a b, a ≠ b → ⁅X ρ a b 1, p b⁆ = p a)
variable (D : Set R) (hd : ∀ d ∈ D, ∀ a b, a ≠ b → ⁅X ρ a b d,p b⁆ = 1)

/-- The finite presentation relations build an actual semidirect-product homomorphism. -/
theorem translations_equivariant (g : Steinberg.Group (Fin 6) R) :
    (translations ρ p hp hc hu D hd).comp (AffineAction.action g).toMonoidHom =
      (MulAut.conj (ρ g)).toMonoidHom.comp (translations ρ p hp hc hu D hd) := by
  apply MonoidHom.ext
  change ∀ v, translations ρ p hp hc hu D hd (AffineAction.action g v) = _
  apply AffineAction.equivariant_of_roots
  intro a b hab r
  suffices he : (translations ρ p hp hc hu D hd).comp
      (AffineAction.elementary a b hab r).toMonoidHom =
      (MulAut.conj (ρ (Steinberg.root a b hab r))).toMonoidHom.comp
        (translations ρ p hp hc hu D hd) from DFunLike.congr_fun he
  apply MonoidHom.toAdditive.injective
  apply AddMonoidHom.pi_ext
  intro c x
  obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R D) x
  change translations ρ p hp hc hu D hd
      (AffineAction.elementary a b hab r (Multiplicative.ofAdd (Pi.single c (Submodule.Quotient.mk s)))) =
    MulAut.conj (ρ (Steinberg.root a b hab r))
      (translations ρ p hp hc hu D hd (Multiplicative.ofAdd (Pi.single c (Submodule.Quotient.mk s))))
  rw [translations_single_mk]
  have hx : ρ (Steinberg.root a b hab r) = X ρ a b r := by rw [X, Steinberg.x_of_ne a b hab]
  rw [hx]
  have he := AffineAction.elementary_column a b hab r (Pi.single c (Submodule.Quotient.mk s) : Fin 6 → R ⧸ Submodule.span R D)
  apply_fun Multiplicative.ofAdd at he
  rw [ofAdd_toAdd] at he
  rw [he, ofAdd_add, map_mul, translations_single_mk]
  by_cases hcb : c=b
  · subst c
    simp only [Pi.single_eq_same]
    have hs : r • (Submodule.Quotient.mk s : R ⧸ Submodule.span R D) = Submodule.Quotient.mk (r*s) := rfl
    rw [hs,translations_single_mk,root_conjugation ρ p hp hc hu a b hab]
  · rw [Pi.single_eq_of_ne (Ne.symm hcb),smul_zero,Pi.single_zero,ofAdd_zero,map_one,mul_one]
    exact (conj_of_commute (w_commute_X ρ p hp hc hu c a b (Ne.symm hcb) s r).symm).symm

noncomputable def lift : AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R D) →* Q :=
  SemidirectProduct.lift (translations ρ p hp hc hu D hd) ρ (translations_equivariant ρ p hp hc hu D hd)

end AffinePresentation
namespace AffineAction
open scoped commutatorElement
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Commutators with a root are the elementary displacement, not an assumed action law. -/
theorem root_translation (a b : Fin 6) (hab : a ≠ b) (r : R) (v : Fin 6 → V) :
    ⁅(SemidirectProduct.inr (Steinberg.root a b hab r) : Group (R:=R) (V:=V)),
      (SemidirectProduct.inl (Multiplicative.ofAdd v) : Group (R:=R) (V:=V))⁆ =
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single a (r • v b))) := by
  rw [commutatorElement_def, ← map_inv, ← SemidirectProduct.inl_aut, ← map_inv, ← map_mul]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [action_root]
  change (elementary a b hab r (Multiplicative.ofAdd v)).toAdd + -v = _
  rw [elementary_column]
  abel

end AffineAction

namespace FiniteAffine
open scoped commutatorElement
variable {R : Type*} [Ring R]
abbrev Free (R : Type*) [Ring R] := Monoid.Coprod (Steinberg.Group (Fin 6) R) (FreeGroup (Fin 6))
def freeP (a : Fin 6) : Free R := Monoid.Coprod.inr (FreeGroup.of a)
abbrev freeX (a b : Fin 6) (r : R) : Free R := Monoid.Coprod.inl (Steinberg.x a b r)

def relatorPP (ab : Fin 6 × Fin 6) : Free R := ⁅freeP (R:=R) ab.1,freeP (R:=R) ab.2⁆
def relatorC (F : Finset R) (z : F × Fin 6 × Fin 6 × Fin 6) : Free R :=
  if z.2.2.2 ≠ z.2.2.1 then ⁅freeX z.2.1 z.2.2.1 (z.1 : R),freeP z.2.2.2⁆ else 1
def relatorU (ab : Fin 6 × Fin 6) : Free R :=
  if ab.1 ≠ ab.2 then ⁅freeX ab.1 ab.2 (1:R),freeP ab.2⁆ * (freeP ab.1)⁻¹ else 1
def relatorD (D : Finset R) (z : D × Fin 6 × Fin 6) : Free R :=
  ⁅freeX z.2.1 z.2.2 (z.1 : R),freeP z.2.2⁆
def relators (F D : Finset R) : Set (Free R) :=
  Set.range relatorPP ∪ Set.range (relatorC F) ∪ Set.range relatorU ∪ Set.range (relatorD D)
def N (F D : Finset R) : Subgroup (Free R) := Subgroup.normalClosure (relators F D)
instance (F D : Finset R) : (N F D).Normal := inferInstanceAs (Subgroup.normalClosure _).Normal
abbrev Presentation (F D : Finset R) := Free R ⧸ N F D
noncomputable def base (F D : Finset R) : Steinberg.Group (Fin 6) R →* Presentation F D :=
  (QuotientGroup.mk' (N F D)).comp Monoid.Coprod.inl
noncomputable def p (F D : Finset R) (a : Fin 6) : Presentation F D :=
  QuotientGroup.mk' (N F D) (freeP a)

theorem killRelator (F D : Finset R) {x : Free R} (hx : x ∈ relators F D) :
    QuotientGroup.mk' (N F D) x = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hx)

theorem p_commute (F D : Finset R) (a b : Fin 6) : Commute (p F D a) (p F D b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := killRelator F D (x:=relatorPP (R:=R) (a,b)) (by
    exact Or.inl (Or.inl (Or.inl ⟨(a,b),rfl⟩)))
  simpa only [relatorPP,map_commutatorElement,p] using h

theorem central_finite (F D : Finset R) (r : R) (hr : r ∈ F) (a b c : Fin 6) (hcb : c ≠ b) :
    Commute (AffinePresentation.X (base F D) a b r) (p F D c) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := killRelator F D (x:=relatorC F (⟨r,hr⟩,a,b,c)) (by
    exact Or.inl (Or.inl (Or.inr ⟨(⟨r,hr⟩,a,b,c),rfl⟩)))
  simpa only [relatorC,ite_eq_left hcb,map_commutatorElement,p,AffinePresentation.X,base,MonoidHom.comp_apply] using h

theorem unit (F D : Finset R) (a b : Fin 6) (hab : a ≠ b) :
    ⁅AffinePresentation.X (base F D) a b 1,p F D b⁆ = p F D a := by
  apply mul_inv_eq_one.mp
  have h := killRelator F D (x:=relatorU (R:=R) (a,b)) (by
    exact Or.inl (Or.inr ⟨(a,b),rfl⟩))
  simpa only [relatorU,ite_eq_left hab,map_mul,map_inv,map_commutatorElement,p,
    AffinePresentation.X,base,MonoidHom.comp_apply] using h

theorem ideal (F D : Finset R) (d : R) (hd : d ∈ D) (a b : Fin 6) :
    ⁅AffinePresentation.X (base F D) a b d,p F D b⁆ = 1 := by
  have h := killRelator F D (x:=relatorD D (⟨d,hd⟩,a,b)) (by
    exact Or.inr ⟨(⟨d,hd⟩,a,b),rfl⟩)
  simpa only [relatorD,map_commutatorElement,p,AffinePresentation.X,base,MonoidHom.comp_apply] using h

variable (F D : Finset R) (h1 : (1:R) ∈ F) (hgen : Subring.closure (↑F : Set R) = ⊤)
include h1 hgen in
theorem central : ∀ r : R, ∀ a b c : Fin 6, c ≠ b →
    Commute (AffinePresentation.X (base F D) a b r) (p F D c) :=
  AffinePresentation.coefficients (base F D) (p F D) F h1 hgen (central_finite F D)

noncomputable def fromAffine : AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) →* Presentation F D :=
  AffinePresentation.lift (base F D) (p F D) (p_commute F D) (central F D h1 hgen)
    (unit F D) (↑D : Set R) (fun d hd a b _ => ideal F D d hd a b)

theorem finitelyPresented [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    Group.IsFinitelyPresented (Presentation F D) := by
  apply Group.IsFinitelyPresented.quotient (N F D)
  refine ⟨relators F D, ?_, rfl⟩
  exact (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)


noncomputable def translation (a : Fin 6) (r : R) :
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single a (Submodule.Quotient.mk r)))

@[simp] theorem translation_zero (a : Fin 6) : translation D a (0:R) = 1 := by
  simp [translation]

theorem root_translation (a b c : Fin 6) (hab : a ≠ b) (r s : R) :
    ⁅(SemidirectProduct.inr (Steinberg.root a b hab r) :
      AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R))),translation D c s⁆ =
      translation D a (if b=c then r*s else 0) := by
  rw [translation, AffineAction.root_translation]
  by_cases h : b=c
  · subst c
    simp only [Pi.single_eq_same,ite_true]
    rfl
  · simp [h]

noncomputable def freeMap : Free R →*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  Monoid.Coprod.lift SemidirectProduct.inr (FreeGroup.lift (translation D · 1))
@[simp] theorem freeMap_P (a : Fin 6) : freeMap D (freeP a) = translation D a 1 := by
  simp [freeMap,freeP]
@[simp] theorem freeMap_X (a b : Fin 6) (r : R) :
    freeMap D (freeX a b r) = SemidirectProduct.inr (Steinberg.x a b r) := by
  simp [freeMap]

theorem freeMap_relators : ∀ x ∈ relators F D, freeMap D x = 1 := by
  intro x hx
  rcases hx with ((⟨⟨a,b⟩,rfl⟩ | ⟨⟨⟨r,hr⟩,a,b,c⟩,rfl⟩) | ⟨⟨a,b⟩,rfl⟩) | ⟨⟨⟨d,hd⟩,a,b⟩,rfl⟩
  · simp only [relatorPP,map_commutatorElement,freeMap_P]
    apply Commute.commutator_eq
    exact (Commute.all _ _).map SemidirectProduct.inl
  · simp only [relatorC]
    split_ifs with hcb
    · simp only [map_commutatorElement,freeMap_X,freeMap_P]
      by_cases hab : a=b
      · subst b; simp
      · rw [Steinberg.x_of_ne a b hab,root_translation D a b c hab]
        simp [Ne.symm hcb]
    · exact map_one _
  · simp only [relatorU]
    split_ifs with hab
    · simp only [map_mul,map_inv,map_commutatorElement,freeMap_X,freeMap_P]
      rw [Steinberg.x_of_ne a b hab,root_translation D a b b hab]
      simp
    · exact map_one _
  · simp only [relatorD,map_commutatorElement,freeMap_X,freeMap_P]
    by_cases hab : a=b
    · subst b; simp
    · rw [Steinberg.x_of_ne a b hab,root_translation D a b b hab]
      simp only [ite_true,mul_one,translation]
      have hz : (Submodule.Quotient.mk d : R ⧸ Submodule.span R (↑D : Set R)) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span hd)
      rw [hz,Pi.single_zero,ofAdd_zero,map_one]

noncomputable def toAffine : Presentation F D →*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) :=
  QuotientGroup.lift (N F D) (freeMap D) (by
    apply Subgroup.normalClosure_le_normal
    exact freeMap_relators F D)

@[simp] theorem toAffine_base (x : Steinberg.Group (Fin 6) R) :
    toAffine F D (base F D x) = SemidirectProduct.inr x := by
  change freeMap D (Monoid.Coprod.inl x) = _
  simp [freeMap]
@[simp] theorem toAffine_p (a : Fin 6) : toAffine F D (p F D a) = translation D a 1 := by
  change freeMap D (freeP a) = _
  exact freeMap_P D a

@[simp] theorem fromAffine_inr (x : Steinberg.Group (Fin 6) R) :
    fromAffine F D h1 hgen (SemidirectProduct.inr x) = base F D x := by
  simp only [fromAffine,AffinePresentation.lift,SemidirectProduct.lift_inr]
@[simp] theorem fromAffine_translation (a : Fin 6) (r : R) :
    fromAffine F D h1 hgen (translation D a r) =
      AffinePresentation.w (base F D) (p F D) a r := by
  simp only [fromAffine,AffinePresentation.lift,translation,SemidirectProduct.lift_inl]
  apply AffinePresentation.translations_single_mk

/-- The quotient is generated by its base and its six designated translations. -/
theorem hom_ext {Q : Type*} [Group Q] {f g : Presentation F D →* Q}
    (hb : f.comp (base F D) = g.comp (base F D)) (hp : ∀ a, f (p F D a) = g (p F D a)) : f=g := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (N F D)) |>.mp
  apply Monoid.Coprod.hom_ext
  · exact hb
  · apply FreeGroup.ext_hom
    exact hp

/-- The natural affine quotient has no additional kernel. -/
noncomputable def equivalence : Presentation F D ≃*
    AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R)) := by
  let f := toAffine F D
  let g := fromAffine F D h1 hgen
  have hgf : g.comp f = MonoidHom.id _ := by
    apply hom_ext F D
    · ext x : 1
      simp [f,g]
    · intro a
      simp only [MonoidHom.comp_apply,toAffine_p,fromAffine_translation,MonoidHom.id_apply,f,g]
      exact AffinePresentation.w_one (base F D) (p F D) (unit F D) a
  have hfg : f.comp g = MonoidHom.id _ := by
    apply SemidirectProduct.hom_ext
    · apply MonoidHom.toAdditive.injective
      apply AddMonoidHom.pi_ext
      intro a x
      obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (Submodule.span R (↑D : Set R)) x
      change f (g (translation D a r)) = translation D a r
      rw [fromAffine_translation]
      simp only [AffinePresentation.w,AffinePresentation.wcolumn,map_commutatorElement,
        AffinePresentation.X,toAffine_base,toAffine_p,f]
      rw [Steinberg.x_of_ne a _ (AffinePresentation.other_ne a).symm,root_translation]
      simp
    · ext x : 1
      simp [f,g]
  exact { f with invFun := g, left_inv := DFunLike.congr_fun hgf, right_inv := DFunLike.congr_fun hfg }

include h1 hgen in
theorem affine_finitelyPresented [Group.IsFinitelyPresented (Steinberg.Group (Fin 6) R)] :
    Group.IsFinitelyPresented (AffineAction.Group (R:=R) (V:= R ⧸ Submodule.span R (↑D : Set R))) := by
  let := finitelyPresented F D
  exact Group.IsFinitelyPresented.equiv (equivalence F D h1 hgen)

end FiniteAffine
end FiniteAlgebraicEnvelopes

end OAI
