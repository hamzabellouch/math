import OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueQuotient
import OAI.NumberTheory.TwoPoint.Halasz.HalaszResidueAveraging

namespace OAI

/-! The nonsingular branch of the classical complete-system iteration.
All short-variable residue classes are included. -/
namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem halasz_fixed_residue_moment {s k N M p r : ℕ} [Fact p.Prime]
    (hkp : k<p) (hrk : r+1≤k) (hN : N<p^(r+1))
    (Z : Finset (Fin k → Fin N))
    (hZ : ∀ z∈Z, Function.Injective (fun i => (((z i).val+1:ℕ):ZMod p))) (b : Fin p) :
    halaszFiberEnergy
      (Z×ˢFintype.piFinset (fun _ : Fin s =>
        univ.filter (fun x : Fin M => halaszResidueIndex (Fact.out : p.Prime).pos x=b)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) ≤
      (k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1)) := by
  let F := Z×ˢFintype.piFinset (fun _ : Fin s =>
    univ.filter (fun x : Fin M => halaszResidueIndex (Fact.out : p.Prime).pos x=b))
  let q := halaszResidueTupleQuotient (s := s) (k := k) (N := N) (M := M) p
  let I := F.image q
  have hq : Set.InjOn q F := halasz_residue_tuple_quotient_injOn (Fact.out : p.Prime).pos Z b
  have hI : ∀ x∈I, Function.Injective (fun i => (((x.1 i).val+1:ℕ):ZMod p)) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    exact hZ y.1 (mem_product.mp hy).1
  have ha : p-1-b.val<p := by have := b.isLt; omega
  have he := halasz_fiber_energy_transfer F q hq
    (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j)
    (halaszCommonResidueFrequency p (p-1-b.val))
    (fun x hx => halasz_residue_tuple_trace (Fact.out : p.Prime).pos Z b x hx)
  have hb := halasz_common_residue_energy (a := p-1-b.val) (r := r)
    (s := s) (N := N) (Q := M/p+1) hkp hrk ha hN I hI
  apply he.trans_le
  convert hb using 1
  congr 1
  ext z
  simp only [I,mem_image]

theorem halasz_nonsingular_moment {s k N M p r : ℕ} [Fact p.Prime]
    (hs : 0<s) (hkp : k<p) (hrk : r+1≤k) (hN : N<p^(r+1))
    (Z : Finset (Fin k → Fin N))
    (hZ : ∀ z∈Z, Function.Injective (fun i => (((z i).val+1:ℕ):ZMod p))) :
    halaszFiberEnergy (Z×ˢ(univ : Finset (Fin s → Fin M)))
      (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) ≤
      p^(2*s) * ((k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1))) := by
  let f (z : Fin k → Fin N) : Fin k → ℤ := fun j => halaszNatPowerFrequency k z j
  let g (x : Fin M) : Fin k → ℤ := fun j => ((x.val+1)^(j.val+1):ℕ)
  have he (G : Finset (Fin M)) :
      halaszFiberEnergy (Z×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x => f x.1+∑ i, g (x.2 i)) =
      halaszFiberEnergy (Z×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x j => halaszNatPowerFrequency k x.1 j+halaszNatPowerFrequency k x.2 j) := by
    rw [← halasz_fiber_energy_natCast]
    congr 1
    funext x j
    simp only [f,g,Pi.add_apply,Finset.sum_apply,halaszNatPowerFrequency,Nat.cast_add,Nat.cast_sum]
  have hh := halasz_residue_average_energy hs Z (univ : Finset (Fin M))
    (halaszResidueIndex (Fact.out : p.Prime).pos) f g
    ((k^k*p^((r+1)*r/2)) * (N^k*halaszVinogradovCount s k (M/p+1)))
    (by
      intro b
      rw [he]
      exact halasz_fixed_residue_moment hkp hrk hN Z hZ b)
  rw [he] at hh
  simpa only [Fintype.piFinset_univ] using hh

end TwoPointCorrelations

end OAI
