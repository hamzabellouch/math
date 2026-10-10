import OAI.NumberTheory.Ostmann.Construction.ActualRows
import OAI.NumberTheory.Ostmann.Construction.RowCongruence

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

theorem zmod_inv_nat_mul (n a b : ℕ) (ha : a.Coprime n) (hb : b.Coprime n) :
    ((a*b:ℕ):ZMod n)⁻¹=(a:ZMod n)⁻¹*(b:ZMod n)⁻¹ := by
  apply ZMod.inv_eq_of_mul_eq_one
  rw [Nat.cast_mul]
  calc
    _ = ((a:ZMod n)*(a:ZMod n)⁻¹)*((b:ZMod n)*(b:ZMod n)⁻¹) := by ring
    _ = 1 := by rw [ZMod.coe_mul_inv_eq_one a ha,ZMod.coe_mul_inv_eq_one b hb,one_mul]

theorem castHom_inverse_nat {n m : ℕ} (hn : n∣m) (H : ℕ) (hH : H.Coprime m) :
    ZMod.castHom hn (ZMod n) ((H:ZMod m)⁻¹)=(H:ZMod n)⁻¹ := by
  symm
  apply ZMod.inv_eq_of_mul_eq_one
  have h := congrArg (ZMod.castHom hn (ZMod n)) (ZMod.coe_mul_inv_eq_one H hH)
  simpa only [map_mul,map_natCast,map_one] using h

theorem castHom_modFraction {n m : ℕ} (hn : n∣m) (v : ℤ) (H : ℕ)
    (hH : H.Coprime m) :
    ZMod.castHom hn (ZMod n) (modFraction m v H)=modFraction n v H := by
  simp only [modFraction,map_mul,map_intCast,castHom_inverse_nat hn H hH]

theorem modFraction_extract_local (n P H d : ℕ) (v : ℤ) (hn : 0<n)
    (hdiv : n∣P) (hH : H.Coprime P) (hd : (d*(P/n)).Coprime n) :
    modFraction n v (d*((P*H)/n)) =
      ZMod.castHom hdiv (ZMod n) (modFraction P v H)*((d*(P/n):ℕ):ZMod n)⁻¹ := by
  have hPH : P*H/n=(P/n)*H := by
    obtain ⟨R,rfl⟩ := hdiv
    simp [Nat.mul_assoc,hn.ne']
  rw [hPH,← Nat.mul_assoc,modFraction,zmod_inv_nat_mul n (d*(P/n)) H hd
    (hH.of_dvd_right hdiv),castHom_modFraction hdiv v H hH]
  unfold modFraction
  ring

theorem crt_modFraction_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι→ℕ) (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (v : ℤ) (H : ℕ) (hH : H.Coprime (∏i,p i)) (i : ι) :
    ZMod.prodEquivPi p hcop (modFraction (∏i,p i) v H) i=modFraction (p i) v H := by
  rw [ZMod.prodEquivPi_apply]
  exact castHom_modFraction _ v H hH

theorem actualExtractedRow_modFraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : Decomposition) (p : ι→ℕ) (hp : ∀i,0<p i)
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (D H : ℕ) (hD : ∀i,D.Coprime (p i)) (hH : H.Coprime (∏i,p i))
    (giant : ι→Bool) (v : ℤ) :
    actualExtractedRow d p hcop D hD giant (modFraction (∏i,p i) v H) =
      ∏i,(if giant i then giantResidueTransform d (p i) else residueTransform d (p i))
        (modFraction (p i) v (D*((∏j,p j)*H/(p i)))) := by
  rw [actualExtractedRow_apply]
  apply Finset.prod_congr rfl
  intro i hi
  have hother : (∏j,p j)/(p i)=otherProduct p i := by
    rw [← mul_otherProduct p i]
    simp [(hp i).ne']
  rw [modFraction_extract_local (p i) (∏j,p j) H D v (hp i)
    (Finset.dvd_prod_of_mem p (Finset.mem_univ i)) hH (by
      rw [hother]
      exact (hD i).mul_left (otherProduct_coprime p hcop i)),hother,
    ZMod.prodEquivPi_apply]
  simp only [Nat.cast_mul]

end Ostmann.Construction

end

end OAI
