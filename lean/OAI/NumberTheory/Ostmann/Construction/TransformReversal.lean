import OAI.NumberTheory.Ostmann.Construction.FavorableHalfRows
import OAI.NumberTheory.Ostmann.Construction.Reversal

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Construction

theorem modFraction_reversal_left (q P Hp Hm D : ℕ) (v w s : ℤ)
    (hq : Nat.Prime q) (hdiv : q∣Hp) (hP : P.Coprime q) (hHm : Hm.Coprime q)
    (heq : Arithmetic.reversalNumerator v w (Hp:ℤ) (Hm:ℤ)=s*(P:ℤ)) :
    modFraction q v ((D*P)*(Hp/q))=modFraction q s ((D*Hm)*(Hp/q)) := by
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hz : (Hp:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  have hP0 : (P:ZMod q)≠0 := (ZMod.isUnit_iff_coprime P q).mpr hP |>.ne_zero
  have hHm0 : (Hm:ZMod q)≠0 := (ZMod.isUnit_iff_coprime Hm q).mpr hHm |>.ne_zero
  have he : (v:ZMod q)*(Hm:ZMod q)-(w:ZMod q)*(Hp:ZMod q)=(s:ZMod q)*(P:ZMod q) := by
    have h := congrArg (fun x : ℤ => (x:ZMod q)) heq
    simpa only [Arithmetic.reversalNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using h
  have hb := reversal_transform_left he hz hP0 hHm0
  simp only [div_eq_mul_inv] at hb
  simp only [modFraction,Nat.cast_mul,mul_inv_rev]
  calc
    _ = ((v:ZMod q)*(P:ZMod q)⁻¹)*((D:ZMod q)⁻¹*((Hp/q:ℕ):ZMod q)⁻¹) := by ring
    _ = ((s:ZMod q)*(Hm:ZMod q)⁻¹)*((D:ZMod q)⁻¹*((Hp/q:ℕ):ZMod q)⁻¹) := by rw [hb]
    _ = _ := by ring

theorem halfTransform_conj (d : Decomposition) (S : Finset ℕ) (D q : ℕ)
    (h : List SmallSlot) (w : ℤ) :
    conj (halfTransform (residueTransform d) (favorableGiantResidueTransform d S) D w q h)=
      halfTransform (residueTransform d) (favorableGiantResidueTransform d S) D (-w) q h := by
  unfold halfTransform
  simp only [map_mul,map_list_prod,List.map_map]
  rw [←favorableGiantResidueTransform_neg]
  congr 1
  · simp only [modFraction,Int.cast_neg,neg_mul]
  · apply congrArg List.prod
    apply List.map_congr_left
    intro z hz
    dsimp only [Function.comp_def]
    rw [←residueTransform_neg]
    simp only [modFraction,Int.cast_neg,neg_mul]

theorem halfTransform_reversal_left (d : Decomposition) (S : Finset ℕ)
    (P Hm D q : ℕ) (h : List SmallSlot) (v w s : ℤ)
    (hq : Nat.Prime q) (hh : ∀z∈h,Nat.Prime z.value)
    (hP : P.Coprime (halfProduct q h)) (hHm : Hm.Coprime (halfProduct q h))
    (heq : Arithmetic.reversalNumerator v w (halfProduct q h:ℤ) (Hm:ℤ)=s*(P:ℤ)) :
    halfTransform (residueTransform d) (favorableGiantResidueTransform d S) (D*P) v q h=
      halfTransform (residueTransform d) (favorableGiantResidueTransform d S) (D*Hm) s q h := by
  unfold halfTransform
  rw [modFraction_reversal_left q P (halfProduct q h) Hm D v w s hq
    (halfProduct_dvd_giant q h) (hP.of_dvd_right (halfProduct_dvd_giant q h))
    (hHm.of_dvd_right (halfProduct_dvd_giant q h)) heq]
  congr 1
  apply congrArg List.prod
  apply List.map_congr_left
  intro z hz
  rw [modFraction_reversal_left z.value P (halfProduct q h) Hm D v w s (hh z hz)
    (halfProduct_dvd_small q h z hz) (hP.of_dvd_right (halfProduct_dvd_small q h z hz))
    (hHm.of_dvd_right (halfProduct_dvd_small q h z hz)) heq]

theorem halfTransforms_reversal (d : Decomposition) (S : Finset ℕ)
    (outside : List ℕ) (P qp qm : ℕ) (hp hm : List SmallSlot) (v w s : ℤ)
    (hqp : Nat.Prime qp) (hqm : Nat.Prime qm)
    (hpp : ∀z∈hp,Nat.Prime z.value) (hmp : ∀z∈hm,Nat.Prime z.value)
    (hPp : P.Coprime (halfProduct qp hp)) (hPm : P.Coprime (halfProduct qm hm))
    (hcross : (halfProduct qp hp).Coprime (halfProduct qm hm))
    (heq : Arithmetic.reversalNumerator v w (halfProduct qp hp:ℤ) (halfProduct qm hm:ℤ)=s*(P:ℤ)) :
    halfTransform (residueTransform d) (favorableGiantResidueTransform d S)
        (outsideProduct outside*P) v qp hp *
      conj (halfTransform (residueTransform d) (favorableGiantResidueTransform d S)
        (outsideProduct outside*P) w qm hm) =
    regularTransform (residueTransform d) (favorableGiantResidueTransform d S) outside
      ⟨s,qp,qm,hp++hm⟩ := by
  have heq' : Arithmetic.reversalNumerator (-w) (-v)
      (halfProduct qm hm:ℤ) (halfProduct qp hp:ℤ)=s*(P:ℤ) := by
    calc
      _ = Arithmetic.reversalNumerator v w (halfProduct qp hp:ℤ) (halfProduct qm hm:ℤ) := by
        unfold Arithmetic.reversalNumerator; ring
      _ = _ := heq
  rw [halfTransform_conj,halfTransform_reversal_left d S P (halfProduct qm hm)
    (outsideProduct outside) qp hp v w s hqp hpp hPp hcross.symm heq,
    halfTransform_reversal_left d S P (halfProduct qp hp) (outsideProduct outside)
      qm hm (-w) (-v) s hqm hmp hPm hcross heq']
  exact (regularTransform_halves (residueTransform d) (favorableGiantResidueTransform d S)
    outside ⟨s,qp,qm,hp++hm⟩ hp hm (List.Perm.refl _) hqp.pos hqm.pos
    (fun z hz => (hpp z hz).pos) (fun z hz => (hmp z hz).pos)).symm

end Ostmann.Construction

end

end OAI
