import OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree
import OAI.NumberTheory.PiExponent.Ampleness.AmpleIso
import OAI.NumberTheory.PiExponent.Approximation.TensorSectionOpen

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

def lineTensorPow (L M : LineBundle X) : ∀ n : ℕ,
    ((L.tensor M).pow n).sheaf ≅ ((L.pow n).tensor (M.pow n)).sheaf
  | 0 => (moduleTensorUnit (structureSheaf X)).symm
  | n+1 =>
    moduleTensorIso (Iso.refl _) (lineTensorPow L M n) ≪≫
    lineTensorAssoc L M ((L.pow n).tensor (M.pow n)) ≪≫
    moduleTensorIso (Iso.refl L.sheaf)
      ((lineTensorAssoc M (L.pow n) (M.pow n)).symm ≪≫
        moduleTensorIso (moduleTensorComm M.sheaf (L.pow n).sheaf) (Iso.refl _) ≪≫
        lineTensorAssoc (L.pow n) M (M.pow n)) ≪≫
    (lineTensorAssoc L (L.pow n) (M.pow (n+1))).symm

theorem LineBundle.IsAmple.pow {L : LineBundle X} (hL : L.IsAmple) (d : ℕ) (hd : 0 < d) :
    (L.pow d).IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let e : ((L.pow n).pow d).sheaf ≅ ((L.pow d).pow n).sheaf :=
    linePowerMul L n d ≪≫ eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.mul_comm n d)) ≪≫
      (linePowerMul L d n).symm
  let t := powerSection s d ≫ e.hom
  have ht : sectionOpen X t = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection s d) e).trans
      ((L.pow n).sectionOpen_power s hd)
  exact ⟨n, hn, t, ht.symm ▸ hs, ht.le.trans hsub, ht.symm ▸ ha⟩

theorem LineBundle.IsAmple.tensor {L M : LineBundle X}
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hxs, hsV, _⟩ := hL x V hx
  obtain ⟨m, hm, t, hxt, hts, hta⟩ := hM x (sectionOpen X s) hxs
  let e : ((M.pow m).pow n).sheaf ≅ (M.pow (n*m)).sheaf :=
    linePowerMul M m n ≪≫ eqToIso (congrArg (fun j => (M.pow j).sheaf) (Nat.mul_comm m n))
  let a : structureSheaf X ⟶ (L.pow (n*m)).sheaf :=
    powerSection s m ≫ (linePowerMul L n m).hom
  let b : structureSheaf X ⟶ (M.pow (n*m)).sheaf := powerSection t n ≫ e.hom
  have ha : sectionOpen X a = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul L n m)).trans ((L.pow n).sectionOpen_power s hm)
  have hb : sectionOpen X b = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection t n) e).trans
      ((M.pow m).sectionOpen_power t hn)
  let q := tensorSection a b ≫ (lineTensorPow L M (n*m)).inv
  have hq : sectionOpen X q = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (tensorSection a b) (lineTensorPow L M (n*m)).symm).trans
        ((section_open (L.pow (n*m)) (M.pow (n*m)) a b).trans
          ((congrArg₂ (fun U V : X.Opens => U ⊓ V) ha hb).trans (inf_eq_right.mpr hts)))
  exact ⟨n*m, Nat.mul_pos hn hm, q, hq.symm ▸ hxt,
    hq.le.trans (hts.trans hsV), hq.symm ▸ hta⟩

end PiExponentSeshadri.Geometry

end

end OAI
