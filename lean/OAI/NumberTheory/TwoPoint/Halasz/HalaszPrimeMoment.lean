import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeEnergyCover
import OAI.NumberTheory.TwoPoint.Halasz.HalaszNonsingularMoment

namespace OAI

/-! The selected-prime cover meets the proved nonsingular moment
estimate, with the original short-variable endpoint retained. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma halasz_residue_good_product (s k N p : ℕ) :
    halaszFiberEnergy
      (halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p)
      (halaszVinogradovFrequency k) =
    halaszFiberEnergy
      ((univ.filter (fun z : Fin k → Fin N => Function.Injective
        (fun i => (((z i).val+1:ℕ):ZMod p))))×ˢ(univ : Finset (Fin s → Fin N)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) := by
  let Z := (univ : Finset (Fin k → Fin N)).filter (fun z => Function.Injective
    (fun i => (((z i).val+1:ℕ):ZMod p)))
  let F := Z×ˢ(univ : Finset (Fin s → Fin N))
  let e := halaszTupleJoin k s N
  have himage : F.image e =
      halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p := by
    ext x
    constructor
    · rintro hx
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
      have hzI := (mem_filter.mp (mem_product.mp hz).1).2
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      simpa only [e,halaszTupleJoin,Equiv.coe_fn_mk,Fin.append_left] using hzI
    · intro hx
      refine mem_image.mpr ⟨e.symm x,?_,e.apply_symm_apply x⟩
      apply mem_product.mpr
      refine ⟨mem_filter.mpr ⟨mem_univ _,?_⟩,mem_univ _⟩
      exact (mem_filter.mp hx).2
  have hf (z : (Fin k → Fin N) × (Fin s → Fin N)) :
      halaszVinogradovFrequency k (e z) =
        (fun j => ((halaszNatPowerFrequency k z.1 j+
          halaszNatPowerFrequency k z.2 j:ℕ):ℤ)) := by
    funext j
    simp only [halaszVinogradovFrequency,e,halaszTupleJoin,Equiv.coe_fn_mk,
      Fin.sum_univ_add,Fin.append_left,Fin.append_right,halaszNatPowerFrequency,
      Nat.cast_add,Nat.cast_sum]
  have he := halasz_fiber_energy_transfer F e e.injective.injOn
    (fun z j => ((halaszNatPowerFrequency k z.1 j+
      halaszNatPowerFrequency k z.2 j:ℕ):ℤ)) (halaszVinogradovFrequency k)
    (fun z _ => hf z)
  rw [halasz_fiber_energy_natCast] at he
  convert he.symm using 1
  congr 1
  convert himage.symm using 1
  ext x
  simp only [mem_image]

theorem halasz_residue_good_moment {s k N p : ℕ} [Fact p.Prime]
    (hs : 0<s) (hk : 0<k) (hkp : k<p) (hNp : N<p^k) :
    halaszFiberEnergy
      (halaszResidueGoodTuples (N := N) (fun i : Fin k => i.castAdd s) p)
      (halaszVinogradovFrequency k) ≤
      p^(2*s)*((k^k*p^(k*(k-1)/2))*(N^k*halaszVinogradovCount s k (N/p+1))) := by
  rw [halasz_residue_good_product]
  have hk1 : k-1+1=k := Nat.sub_add_cancel hk
  have h := halasz_nonsingular_moment (s := s) (M := N) (r := k-1) hs hkp (by omega)
    (by simpa only [hk1] using hNp)
    ((univ : Finset (Fin k → Fin N)).filter (fun z => Function.Injective
      (fun i => (((z i).val+1:ℕ):ZMod p))))
    (fun z hz => (mem_filter.mp hz).2)
  simpa only [hk1] using h

end TwoPointCorrelations

end OAI
