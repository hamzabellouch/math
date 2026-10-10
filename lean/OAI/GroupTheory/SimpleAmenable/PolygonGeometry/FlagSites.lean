import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.FlagExchangeAction

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSites
open Classical

noncomputable def scaledOrdinary (D : ℕ) (u : CutRing×CutRing) : ℝ×ℝ :=
  (ordinary u.1/D,ordinary u.2/D)

noncomputable def scaledConjugate (D : ℕ) (u : CutRing×CutRing) : ℝ×ℝ :=
  (conjugate u.1/D,conjugate u.2/D)

theorem scaledOrdinary_injective {D : ℕ} (hD : 0<D) :
    Function.Injective (scaledOrdinary D) := by
  intro u w h
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  apply Prod.ext
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.fst h))
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.snd h))

def InFlagLattice (D : ℕ) (z : ℝ×ℝ) : Prop := ∃ u,scaledOrdinary D u=z

def FlagSite (a m D : ℕ) (v : ℝ×ℝ) :=
  {z : FlagTrackPoint a m v // InFlagLattice D z.2.val}

noncomputable def flagSiteNumerator {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    CutRing×CutRing := z.property.choose

theorem flagSiteNumerator_spec {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    scaledOrdinary D (flagSiteNumerator z)=z.val.2.val := z.property.choose_spec

instance {a m D : ℕ} {v : ℝ×ℝ} : Countable (FlagSite a m D v) := by
  apply Function.Injective.countable (f := fun z : FlagSite a m D v => (z.val.1,flagSiteNumerator z))
  intro z w h
  apply Subtype.ext
  have ht : z.val.1=w.val.1 := congrArg (fun p : Fin m × (CutRing×CutRing) => p.1) h
  have hn : flagSiteNumerator z=flagSiteNumerator w :=
    congrArg (fun p : Fin m × (CutRing×CutRing) => p.2) h
  apply Prod.ext
  · exact ht
  · apply Subtype.ext
    rw [← flagSiteNumerator_spec z,← flagSiteNumerator_spec w,hn]

noncomputable def flagShiftPeriod {a : ℕ} {v : ℝ×ℝ} (u : CutRing×CutRing)
    (z : SquareFlag a v) : ℤ×ℤ :=
  (flagFloor (z.val.1+ordinary u.1) v.1,flagFloor (z.val.2+ordinary u.2) v.2)

noncomputable def flagShiftNumerator (D : ℕ) (n u : CutRing×CutRing) (k : ℤ×ℤ) :
    CutRing×CutRing :=
  (n.1+(D:CutRing)*u.1-(D:CutRing)*(k.1:CutRing),
   n.2+(D:CutRing)*u.2-(D:CutRing)*(k.2:CutRing))

theorem scaledOrdinary_shift {D : ℕ} (hD : 0<D) (n u : CutRing×CutRing) (k : ℤ×ℤ) :
    scaledOrdinary D (flagShiftNumerator D n u k)=
      scaledOrdinary D n+(ordinary u.1,ordinary u.2)-((k.1:ℝ),(k.2:ℝ)) := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  apply Prod.ext <;>
    simp only [scaledOrdinary,flagShiftNumerator,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_add,Prod.snd_add,map_sub,map_add,map_mul,map_natCast,map_intCast] <;>
    field_simp

theorem flagTranslate_lattice {a D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (u : CutRing×CutRing) (z : SquareFlag a v) (hz : InFlagLattice D z.val) :
    InFlagLattice D (flagTranslate u z).val := by
  obtain ⟨n,hn⟩ := hz
  refine ⟨flagShiftNumerator D n u (flagShiftPeriod u z),?_⟩
  rw [scaledOrdinary_shift hD,hn]
  simp only [flagTranslate_val,flagFract_eq,flagShiftPeriod]
  rfl

theorem flagAction_lattice {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagTrackPoint a m v) (hz : InFlagLattice D z.2.val) :
    InFlagLattice D (flagAction g z).2.val :=
  flagTranslate_lattice hD _ _ hz

noncomputable def flagSiteAction {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) : FlagSite a m D v :=
  ⟨flagAction g z.val,flagAction_lattice hD g z.val z.property⟩

@[simp] theorem flagSiteAction_one {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) : flagSiteAction hD 1 z=z :=
  Subtype.ext (flagAction_one z.val)

theorem flagSiteAction_mul {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (f g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteAction hD (f*g) z=flagSiteAction hD f (flagSiteAction hD g z) :=
  Subtype.ext (flagAction_mul f g z.val)

noncomputable def flagSitePermutation {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) : Equiv.Perm (FlagSite a m D v) where
  toFun := flagSiteAction hD g
  invFun := flagSiteAction hD g⁻¹
  left_inv z := by rw [← flagSiteAction_mul,inv_mul_cancel,flagSiteAction_one]
  right_inv z := by rw [← flagSiteAction_mul,mul_inv_cancel,flagSiteAction_one]

noncomputable def flagSiteRepresentation {a m D : ℕ} (hD : 0<D) (v : ℝ×ℝ) :
    polygonFullGroup a m →* Equiv.Perm (FlagSite a m D v) where
  toFun := flagSitePermutation hD
  map_one' := by apply Equiv.ext; intro z; exact flagSiteAction_one hD z
  map_mul' f g := by apply Equiv.ext; intro z; exact flagSiteAction_mul hD f g z

noncomputable def flagSiteConjugate {a m D : ℕ} {v : ℝ×ℝ} (z : FlagSite a m D v) :
    ℝ×ℝ := scaledConjugate D (flagSiteNumerator z)

theorem flagSiteNumerator_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteNumerator (flagSiteAction hD g z)=flagShiftNumerator D (flagSiteNumerator z)
      (flagChart g z.val).shift (flagShiftPeriod (flagChart g z.val).shift z.val.2) := by
  apply scaledOrdinary_injective hD
  rw [flagSiteNumerator_spec,scaledOrdinary_shift hD,flagSiteNumerator_spec]
  change (flagTranslate _ z.val.2).val=_
  simp only [flagTranslate_val,flagFract_eq,flagShiftPeriod]
  rfl

theorem flagSiteConjugate_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagChart g z.val).shift.1,conjugate (flagChart g z.val).shift.2)-
      (((flagShiftPeriod (flagChart g z.val).shift z.val.2).1:ℝ),
       ((flagShiftPeriod (flagChart g z.val).shift z.val.2).2:ℝ)) := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold flagSiteConjugate
  rw [flagSiteNumerator_action hD]
  apply Prod.ext <;>
    simp only [scaledConjugate,flagShiftNumerator,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_add,Prod.snd_add,map_sub,map_add,map_mul,map_natCast,map_intCast] <;>
    field_simp

end FlagSites

end SimpleAmenable
end
end

end OAI
