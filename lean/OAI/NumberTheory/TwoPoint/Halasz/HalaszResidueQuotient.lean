import OAI.NumberTheory.TwoPoint.Halasz.HalaszShiftedLongShort
import OAI.NumberTheory.TwoPoint.Halasz.HalaszEnergyImage

namespace OAI

/-! Quotient coordinates in one positive residue class. Representatives
p*u-a, with 0<=a<p, avoid a boundary point at u=0. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

def halaszResidueQuotient {M : ℕ} (p : ℕ) (x : Fin M) : Fin (M/p+1) :=
  ⟨x.val/p,lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_of_lt x.isLt)) (Nat.lt_succ_self _)⟩

def halaszResidueIndex {M p : ℕ} (hp : 0<p) (x : Fin M) : Fin p :=
  ⟨x.val%p,Nat.mod_lt _ hp⟩

lemma halasz_residue_quotient_recover {M p : ℕ} (hp : 0<p) (b : Fin p)
    (x : Fin M) (hx : halaszResidueIndex hp x=b) :
    p*((halaszResidueQuotient p x).val+1)-(p-1-b.val)=x.val+1 := by
  have hm : x.val%p=b.val := congrArg Fin.val hx
  have hd := Nat.mod_add_div x.val p
  dsimp [halaszResidueQuotient]
  rw [Nat.mul_add,Nat.mul_one]
  omega

lemma halasz_residue_quotient_injOn {M p : ℕ} (hp : 0<p) (b : Fin p) :
    Set.InjOn (halaszResidueQuotient (M := M) p)
      ((univ.filter (fun x : Fin M => halaszResidueIndex hp x=b)) : Set (Fin M)) := by
  intro x hx y hy hxy
  apply Fin.ext
  have hx' : x.val%p=b.val := congrArg Fin.val (mem_filter.mp hx).2
  have hy' : y.val%p=b.val := congrArg Fin.val (mem_filter.mp hy).2
  have hd : x.val/p=y.val/p := congrArg Fin.val hxy
  change x.val/p=y.val/p at hd
  have hdx := Nat.mod_add_div x.val p
  have hdy := Nat.mod_add_div y.val p
  rw [hd] at hdx
  omega

def halaszResidueTupleQuotient {s k N M : ℕ} (p : ℕ)
    (x : (Fin k → Fin N) × (Fin s → Fin M)) :
    (Fin k → Fin N) × (Fin s → Fin (M/p+1)) :=
  (x.1,fun i => halaszResidueQuotient p (x.2 i))

lemma halasz_residue_tuple_quotient_injOn {s k N M p : ℕ} (hp : 0<p)
    (Z : Finset (Fin k → Fin N)) (b : Fin p) :
    Set.InjOn (halaszResidueTupleQuotient (s := s) (k := k) (N := N) (M := M) p)
      ((Z×ˢFintype.piFinset (fun _ : Fin s =>
        univ.filter (fun x => halaszResidueIndex hp x=b))) :
          Finset ((Fin k → Fin N) × (Fin s → Fin M))) := by
  intro x hx y hy hxy
  apply Prod.ext
  · exact congrArg (fun z : (Fin k → Fin N) × (Fin s → Fin (M/p+1)) => z.1) hxy
  · funext i
    apply halasz_residue_quotient_injOn hp b
    · exact Fintype.mem_piFinset.mp (mem_product.mp hx).2 i
    · exact Fintype.mem_piFinset.mp (mem_product.mp hy).2 i
    · exact congrFun (congrArg
        (fun z : (Fin k → Fin N) × (Fin s → Fin (M/p+1)) => z.2) hxy) i

lemma halasz_residue_tuple_trace {s k N M p : ℕ} (hp : 0<p)
    (Z : Finset (Fin k → Fin N)) (b : Fin p)
    (x : (Fin k → Fin N) × (Fin s → Fin M))
    (hx : x∈Z×ˢFintype.piFinset (fun _ : Fin s =>
      univ.filter (fun x => halaszResidueIndex hp x=b))) :
    halaszCommonResidueFrequency p (p-1-b.val) (halaszResidueTupleQuotient p x) =
      fun j => halaszNatPowerFrequency k x.1 j + halaszNatPowerFrequency k x.2 j := by
  funext j
  dsimp [halaszCommonResidueFrequency,halaszResidueTupleQuotient,halaszNatPowerFrequency]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [halasz_residue_quotient_recover hp b (x.2 i)
    (mem_filter.mp (Fintype.mem_piFinset.mp (mem_product.mp hx).2 i)).2]

end TwoPointCorrelations

end OAI
