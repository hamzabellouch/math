import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Prime
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParentCoprime

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

def remainingValues (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (x : RemainingSample sources T giant) : List ℕ :=
  x.1.val :: (assignedSlots sources T x.2).map SmallSlot.value

@[simp] theorem remainingValues_prod (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) :
    (remainingValues sources T giant x).prod=remainingProduct sources T giant x := rfl

theorem remainingValues_prime (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) :
    ∀q∈remainingValues sources T giant x,Nat.Prime q := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact giant.prime _ x.1.property
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq
    exact assignedSlots_prime sources T x.2 a ha

theorem reduced_signed_fraction_unique {v w : ℤ} {H K : ℕ}
    (hH : 0<H) (hK : 0<K) (hv : H.Coprime v.natAbs) (hw : K.Coprime w.natAbs)
    (he : (v:ℚ)/(H:ℚ)=(w:ℚ)/(K:ℚ)) : v=w ∧ H=K := by
  have he' : v*(K:ℤ)=w*(H:ℤ) := by
    exact_mod_cast (div_eq_div_iff (by exact_mod_cast hH.ne' : (H:ℚ)≠0)
      (by exact_mod_cast hK.ne' : (K:ℚ)≠0)).mp he
  have ha : v.natAbs*K=w.natAbs*H := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs he'
  have hHK : H∣K := hv.dvd_of_dvd_mul_left (ha.symm ▸ dvd_mul_left H w.natAbs)
  have hKH : K∣H := hw.dvd_of_dvd_mul_left (ha ▸ dvd_mul_left K v.natAbs)
  have hEq := Nat.dvd_antisymm hHK hKH
  refine ⟨?_,hEq⟩
  rw [←hEq] at he'
  exact mul_right_cancel₀ (by exact_mod_cast hH.ne' : (H:ℤ)≠0) he'

theorem remainingProduct_coprime_frequency (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) {v : ℤ} (hv : v≠0)
    (hlarge : ∀q∈remainingValues sources T giant x,v.natAbs<q) :
    (remainingProduct sources T giant x).Coprime v.natAbs := by
  rw [←remainingValues_prod]
  exact Nat.coprime_list_prod_left_iff.mpr (fun q hq =>
    History.prime_coprime_small_frequency (remainingValues_prime sources T giant x q hq)
      hv (hlarge q hq))

theorem remainingExactTag_eq_iff (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant) {v w : ℤ}
    (hv : v≠0) (hw : w≠0)
    (hx : ∀q∈remainingValues sources T giant x,v.natAbs<q)
    (hy : ∀q∈remainingValues sources T giant y,w.natAbs<q) :
    remainingExactTag sources T giant x v=remainingExactTag sources T giant y w ↔
      v=w ∧ remainingProduct sources T giant x=remainingProduct sources T giant y := by
  constructor
  · exact reduced_signed_fraction_unique (remainingProduct_pos sources T giant x)
      (remainingProduct_pos sources T giant y)
      (remainingProduct_coprime_frequency sources T giant x hv hx)
      (remainingProduct_coprime_frequency sources T giant y hw hy)
  · rintro ⟨rfl,he⟩
    simp only [remainingExactTag,he]

theorem remainingValues_perm_of_product_eq (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x y : RemainingSample sources T giant)
    (he : remainingProduct sources T giant x=remainingProduct sources T giant y) :
    (remainingValues sources T giant x).Perm (remainingValues sources T giant y) := by
  exact perm_of_prod_eq_prod he
    (fun q hq => Nat.prime_iff.mp (remainingValues_prime sources T giant x q hq))
    (fun q hq => Nat.prime_iff.mp (remainingValues_prime sources T giant y q hq))

theorem remainingValues_nodup_of_integrand_ne_zero (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v : AllowedFrequency V l)
    (hx : remainingIntegrand d P sources seed V giant X G bins outside l p u x v≠0) :
    (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).Nodup := by
  have hs := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u x v hx).2.2.2.1
  have hh := remaining_half_pairwise _ _ _ outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)) hs
  have hp := (List.pairwise_append.mp hh).1
  have hprime := remainingValues_prime sources (Template.remainder (l+1) (Template.current seed l)) giant x
  change (remainingValues sources (Template.remainder (l+1) (Template.current seed l)) giant x).Pairwise Nat.Coprime at hp
  exact hp.imp_of_mem (fun {a b} ha hb hab he => by
    subst b
    exact (hprime a ha).ne_one (by simpa only [Nat.Coprime,Nat.gcd_self] using hab))

theorem existsUnique_value_matching {xs ys : List ℕ} (hx : xs.Nodup) (hy : ys.Nodup)
    (hperm : xs.Perm ys) :
    ∃! e : Fin xs.length ≃ Fin ys.length, ∀i,ys.get (e i)=xs.get i := by
  let e : Fin xs.length ≃ Fin ys.length :=
    (hx.getEquiv xs).trans ((Equiv.subtypeEquivRight (fun _ => hperm.mem_iff)).trans
      (hy.getEquiv ys).symm)
  have he : ∀i,ys.get (e i)=xs.get i := by
    intro i
    exact congrArg Subtype.val ((hy.getEquiv ys).apply_symm_apply
      ((Equiv.subtypeEquivRight (fun _ => hperm.mem_iff)) ((hx.getEquiv xs) i)))
  refine ⟨e,he,?_⟩
  intro f hf
  apply Equiv.ext
  intro i
  exact hy.injective_get ((hf i).trans (he i).symm)

end Ostmann.Construction

end

end OAI
