import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionEnergy

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter

theorem exists_root_residue_scaling {K : Type*} [Field K] {u v : K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hs : IsSquare (u*v)) :
    ∃ c : K,c ≠ 0 ∧ u*c^2=v := by
  obtain ⟨s,hs⟩ := hs
  have hsp : s ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hs
    exact mul_ne_zero hu hv hs
  refine ⟨s/u,div_ne_zero hsp hu,?_⟩
  apply (mul_right_inj' hu).mp
  field_simp
  simpa [pow_two,mul_comm] using hs.symm

theorem root_residues_ne_of_prime_separation {p : ℕ} [Fact p.Prime]
    {m h u v x y : ℤ} {tx ty : ℕ}
    (hm : (m:ZMod p) ≠ 0)
    (hx : m*x-h=u*(tx:ℤ)^2) (hy : m*y-h=v*(ty:ℤ)^2)
    (hpsep : Nat.Prime (x-y).natAbs) (hsmall : p < (x-y).natAbs)
    (c : ZMod p) (hc : (u:ZMod p)*c^2=(v:ZMod p)) :
    (tx:ZMod p) ≠ c*(ty:ZMod p) := by
  intro he
  have hx' : (m:ZMod p)*(x:ZMod p)-(h:ZMod p)=(u:ZMod p)*(tx:ZMod p)^2 := by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using
      congrArg (fun z : ℤ => (z:ZMod p)) hx
  have hy' : (m:ZMod p)*(y:ZMod p)-(h:ZMod p)=(v:ZMod p)*(ty:ZMod p)^2 := by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using
      congrArg (fun z : ℤ => (z:ZMod p)) hy
  have heq : (u:ZMod p)*(tx:ZMod p)^2=(v:ZMod p)*(ty:ZMod p)^2 := by
    rw [he]
    calc
      _ = ((u:ZMod p)*c^2)*(ty:ZMod p)^2 := by ring
      _ = _ := by rw [hc]
  have hz : (m:ZMod p)*((x-y:ℤ):ZMod p)=0 := by
    push_cast
    linear_combination hx'-hy'+heq
  have hd : (p:ℤ) ∣ x-y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((mul_eq_zero.mp hz).resolve_left hm)
  have hpdiv : p ∣ (x-y).natAbs := Int.natCast_dvd.mp hd
  have hpe := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hpsep).mp hpdiv
  exact (Nat.ne_of_lt hsmall) hpe

theorem exists_root_residue_scaling_of_jacobi {p : ℕ} [Fact p.Prime]
    {u v : ℤ} (hu : (u:ZMod p) ≠ 0) (hv : (v:ZMod p) ≠ 0)
    (hs : jacobiSym (u*v) p=1) :
    ∃ c : ZMod p,c ≠ 0 ∧ (u:ZMod p)*c^2=(v:ZMod p) := by
  have huv : ((u*v:ℤ):ZMod p) ≠ 0 := by simpa only [Int.cast_mul] using mul_ne_zero hu hv
  have hleg : legendreSym p (u*v)=1 := by
    simpa only [jacobiSym.legendreSym.to_jacobiSym] using hs
  have hsq := (legendreSym.eq_one_iff p huv).mp hleg
  exact exists_root_residue_scaling hu hv (by simpa only [Int.cast_mul] using hsq)

end Ostmann.QuadraticCenter

end

end OAI
