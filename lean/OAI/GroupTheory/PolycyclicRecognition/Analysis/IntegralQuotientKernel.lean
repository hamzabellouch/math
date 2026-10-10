import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntegralLinearExtension
import Mathlib.GroupTheory.GroupExtension.Basic

namespace OAI

/-! # Removing one coordinate from an integral abelian quotient -/

noncomputable section
namespace PolycyclicRecognition

def integralQuotientDrop (n : ℕ) : IntegralLatticeGroup (n + 1) →* IntegralLatticeGroup n where
  toFun z := Multiplicative.ofAdd (fun j => z.toAdd j.castSucc)
  map_one' := rfl
  map_mul' _ _ := rfl

def integralQuotientLast (n : ℕ) : IntegralLatticeGroup (n + 1) →* Multiplicative ℤ where
  toFun z := Multiplicative.ofAdd (z.toAdd (Fin.last n))
  map_one' := rfl
  map_mul' _ _ := rfl

def integralQuotientInsert (n : ℕ) (z : IntegralLatticeGroup n) (k : Multiplicative ℤ) :
    IntegralLatticeGroup (n + 1) := Multiplicative.ofAdd (Fin.lastCases k.toAdd z.toAdd)

@[simp] theorem integralQuotientDrop_insert (n : ℕ) (z : IntegralLatticeGroup n)
    (k : Multiplicative ℤ) : integralQuotientDrop n (integralQuotientInsert n z k) = z := by
  apply Multiplicative.ext
  funext j
  change Fin.lastCases k.toAdd z.toAdd j.castSucc = z.toAdd j
  exact Fin.lastCases_castSucc j

@[simp] theorem integralQuotientLast_insert (n : ℕ) (z : IntegralLatticeGroup n)
    (k : Multiplicative ℤ) : integralQuotientLast n (integralQuotientInsert n z k) = k := by
  apply Multiplicative.ext
  change Fin.lastCases k.toAdd z.toAdd (Fin.last n) = k.toAdd
  exact Fin.lastCases_last

theorem integralQuotientLast_surjective (n : ℕ) : Function.Surjective (integralQuotientLast n) :=
  fun k => ⟨integralQuotientInsert n 1 k, integralQuotientLast_insert n 1 k⟩

theorem integralQuotient_eq_one {n : ℕ} (z : IntegralLatticeGroup (n + 1))
    (hd : integralQuotientDrop n z = 1) (hl : integralQuotientLast n z = 1) : z = 1 := by
  apply Multiplicative.ext
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · exact congrArg Multiplicative.toAdd hl
  · exact congrFun (congrArg Multiplicative.toAdd hd) k

variable {N G : Type} [Group N] [Group G] {n : ℕ}

def integralLastMap (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    G →* Multiplicative ℤ := (integralQuotientLast n).comp E.rightHom

def integralKernelInl (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    N →* (integralLastMap E).ker := E.inl.codRestrict _ (by
  intro x
  change integralQuotientLast n (E.rightHom (E.inl x)) = 1
  rw [E.rightHom_inl, map_one])

def integralKernelRight (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    (integralLastMap E).ker →* IntegralLatticeGroup n :=
  (integralQuotientDrop n).comp (E.rightHom.comp (integralLastMap E).ker.subtype)

def integralKernelExtension (E : GroupExtension N G (IntegralLatticeGroup (n + 1))) :
    GroupExtension N (integralLastMap E).ker (IntegralLatticeGroup n) where
  inl := integralKernelInl E
  rightHom := integralKernelRight E
  inl_injective := by
    intro x y h
    exact E.inl_injective (congrArg Subtype.val h)
  range_inl_eq_ker_rightHom := by
    ext h
    constructor
    · rintro ⟨x, rfl⟩
      change integralQuotientDrop n (E.rightHom (E.inl x)) = 1
      rw [E.rightHom_inl, map_one]
    · intro hh
      have he : E.rightHom h = 1 := integralQuotient_eq_one _ hh h.property
      have hr : (h : G) ∈ E.inl.range := by
        rw [E.range_inl_eq_ker_rightHom]
        exact he
      obtain ⟨x, hx⟩ := hr
      exact ⟨x, Subtype.ext hx⟩
  rightHom_surjective := by
    intro z
    obtain ⟨g, hg⟩ := E.rightHom_surjective (integralQuotientInsert n z 1)
    have hk : g ∈ (integralLastMap E).ker := by
      change integralQuotientLast n (E.rightHom g) = 1
      rw [hg, integralQuotientLast_insert]
    refine ⟨⟨g, hk⟩, ?_⟩
    change integralQuotientDrop n (E.rightHom g) = z
    rw [hg, integralQuotientDrop_insert]

theorem integralKernelExtension_conjAct
    (E : GroupExtension N G (IntegralLatticeGroup (n + 1)))
    (g : (integralLastMap E).ker) (x : N) :
    (integralKernelExtension E).conjAct g x = E.conjAct (g : G) x := by
  apply E.inl_injective
  have hh := (integralKernelExtension E).inl_conjAct_comm (e := g) (n := x)
  have he := congrArg Subtype.val hh
  exact he.trans E.inl_conjAct_comm.symm

end PolycyclicRecognition

end

end OAI
