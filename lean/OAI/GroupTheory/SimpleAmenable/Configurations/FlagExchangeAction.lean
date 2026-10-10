import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FlagTranslation

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagExchangeAction
open Classical

theorem flagMem_top {a : ℕ} {v : ℝ×ℝ} (z : SquareFlag a v) :
    flagMem (⊤ : polygonAlgebra a) z := by
  have h := flagMem_compl (⊥ : polygonAlgebra a) z
  simpa using h.mpr (flagMem_bot z)

theorem flagMem_inf {a : ℕ} {v : ℝ×ℝ} (U V : polygonAlgebra a) (z : SquareFlag a v) :
    flagMem (U⊓V) z ↔ flagMem U z ∧ flagMem V z := by
  have he : U⊓V=(Uᶜ⊔Vᶜ)ᶜ := by simp
  rw [he,flagMem_compl,flagMem_sup,flagMem_compl,flagMem_compl]
  tauto

theorem flagMem_nonempty {a : ℕ} {v : ℝ×ℝ} {U : polygonAlgebra a}
    {z : SquareFlag a v} (hz : flagMem U z) : U.val.Nonempty := by
  obtain ⟨N,hN,hzN,h⟩ := flagMem_iff U z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z hN hzN
  exact ⟨p,(h p hp hpv).mpr hz⟩

abbrev FlagTrackPoint (a m : ℕ) (v : ℝ×ℝ) := Fin m × SquareFlag a v

theorem flagChart_exists {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    ∃ c : TableChart a m, c.Holds g.val ∧ z.1=c.source ∧ flagMem c.domain z.2 := by
  obtain ⟨S,hS,hcover⟩ := g.property
  obtain ⟨p,_,_,hp⟩ := flagValue_finite
    (fun c : S => fun p : GenericSquare a => decide (p∈c.val.domain.val))
    (fun c => polygon_hasSquareArrangement c.val.domain.property)
    z.2 isOpen_univ (Set.mem_univ _)
  obtain ⟨c,hc,htrack,hcp⟩ := hcover (z.1,p)
  refine ⟨c,hS c hc,htrack,?_⟩
  exact (hp ⟨c,hc⟩).symm.trans (decide_eq_true hcp)

theorem flagChart_values_eq {a m : ℕ} {v : ℝ×ℝ} {f : TrackPoint a m → TrackPoint a m}
    {c d : TableChart a m} (hc : c.Holds f) (hd : d.Holds f)
    {z : FlagTrackPoint a m v} (hcs : z.1=c.source) (hds : z.1=d.source)
    (hcz : flagMem c.domain z.2) (hdz : flagMem d.domain z.2) :
    (c.target,flagTranslate c.shift z.2)=(d.target,flagTranslate d.shift z.2) := by
  obtain ⟨p,hp⟩ := flagMem_nonempty ((flagMem_inf c.domain d.domain z.2).mpr ⟨hcz,hdz⟩)
  have hev : (c.target,translate a c.shift p)=(d.target,translate a d.shift p) := by
    have hsource : c.source=d.source := hcs.symm.trans hds
    rw [← hc p hp.1,← hd p hp.2,hsource]
  have ht := congrArg Prod.fst hev
  have hu := orbitRepresentative_eq_of_translate_eq p (congrArg Prod.snd hev)
  refine Prod.ext (show c.target=d.target from ht) ?_
  rw [flagTranslate_reduce c.shift,flagTranslate_reduce d.shift,hu]

noncomputable def flagChart {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : TableChart a m := Classical.choose (flagChart_exists g z)

theorem flagChart_spec {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    (flagChart g z).Holds g.val ∧ z.1=(flagChart g z).source ∧
      flagMem (flagChart g z).domain z.2 := Classical.choose_spec (flagChart_exists g z)

noncomputable def flagAction {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : FlagTrackPoint a m v :=
  ((flagChart g z).target,flagTranslate (flagChart g z).shift z.2)

theorem flagAction_apply {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) (c : TableChart a m) (hc : c.Holds g.val)
    (hcs : z.1=c.source) (hcz : flagMem c.domain z.2) :
    flagAction g z=(c.target,flagTranslate c.shift z.2) := by
  exact flagChart_values_eq (flagChart_spec g z).1 hc (flagChart_spec g z).2.1 hcs
    (flagChart_spec g z).2.2 hcz

@[simp] theorem flagAction_one {a m : ℕ} {v : ℝ×ℝ} (z : FlagTrackPoint a m v) :
    flagAction (1 : polygonFullGroup a m) z=z := by
  let c : TableChart a m := ⟨z.1,z.1,0,⊤⟩
  have hc : c.Holds (1 : polygonFullGroup a m).val := by
    intro p _
    simp [c]
  have h := flagAction_apply 1 z c hc rfl (flagMem_top z.2)
  simpa only [c,flagTranslate_zero,Prod.eta] using h

theorem flagAction_mul {a m : ℕ} {v : ℝ×ℝ} (f g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) : flagAction (f*g) z=flagAction f (flagAction g z) := by
  let d := flagChart g z
  let c := flagChart f (flagAction g z)
  have hd : d.Holds g.val ∧ z.1=d.source ∧ flagMem d.domain z.2 := flagChart_spec g z
  have hc : c.Holds f.val ∧ (flagAction g z).1=c.source ∧
      flagMem c.domain (flagAction g z).2 := flagChart_spec f (flagAction g z)
  have hcd : c.source=d.target := hc.2.1.symm
  have hcomp : (c.comp d).Holds (f*g).val := by
    exact TableChart.comp_holds (f := f.val) (g := g.val) hc.1 hd.1 hcd
  have hcdom : flagMem (c.comp d).domain z.2 := by
    change flagMem (d.domain⊓⟨translate a d.shift ⁻¹' c.domain.val,
      polygon_preimage_translate d.shift c.domain.property⟩) z.2
    rw [flagMem_inf,flagMem_preimage_translate]
    exact ⟨hd.2.2,hc.2.2⟩
  calc
    flagAction (f*g) z = ((c.comp d).target,flagTranslate (c.comp d).shift z.2) :=
      flagAction_apply (f*g) z (c.comp d) hcomp hd.2.1 hcdom
    _ = flagAction f (flagAction g z) := by
      change (c.target,flagTranslate (c.shift+d.shift) z.2)=
        (c.target,flagTranslate c.shift (flagTranslate d.shift z.2))
      rw [flagTranslate_add]

noncomputable def flagPermutation {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    Equiv.Perm (FlagTrackPoint a m v) where
  toFun := flagAction g
  invFun := flagAction g⁻¹
  left_inv z := by rw [← flagAction_mul,inv_mul_cancel,flagAction_one]
  right_inv z := by rw [← flagAction_mul,mul_inv_cancel,flagAction_one]

noncomputable def flagRepresentation (a m : ℕ) (v : ℝ×ℝ) :
    polygonFullGroup a m →* Equiv.Perm (FlagTrackPoint a m v) where
  toFun := flagPermutation
  map_one' := by apply Equiv.ext; intro z; exact flagAction_one z
  map_mul' f g := by apply Equiv.ext; intro z; exact flagAction_mul f g z

end FlagExchangeAction

end SimpleAmenable
end
end

end OAI
