import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionLower
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionNumerics
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionRootSets
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootSplitPrimeMass

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem eventually_no_large_canonical_kernel_roots :
    ∃ etaMax : ℝ,0 < etaMax ∧ etaMax ≤ 1/1000 ∧
      ∀ᶠ X : ℝ in atTop,∀ η : ℝ,0 ≤ η → η ≤ etaMax →
        ∀ (m : ℕ),0 < m → (m:ℝ) ≤ X^η → ∀ h u v : ℤ,
        u ≠ 0 → v ≠ 0 → |(u:ℝ)| ≤ X^η → |(v:ℝ)| ≤ X^η →
        ∀ S T : Finset ℤ,
        (∀ x∈S,∀ y∈T,Nat.Prime (x-y).natAbs) →
        (∀ x∈S,∀ y∈T,X^(9/10:ℝ) ≤ ((x-y).natAbs:ℝ)) →
        (∀ x∈S,∀ y∈S,|(x:ℝ)-(y:ℝ)| ≤ X) →
        (∀ x∈T,∀ y∈T,|(x:ℝ)-(y:ℝ)| ≤ X) →
        X^(1/2-3*η:ℝ) ≤ (canonicalKernelRoots S m h u).card →
        X^(1/2-3*η:ℝ) ≤ (canonicalKernelRoots T m h v).card → False := by
  obtain ⟨ηmax,hηmax,hηsmall,hsplit⟩ := exists_eventually_root_split_prime_sum_lower
  refine ⟨ηmax,hηmax,hηsmall,?_⟩
  filter_upwards [hsplit,rootCollision_eventually_impossible,eventually_gt_atTop (1:ℝ)]
    with X hmass himpossible hX
  intro η hη hηbound m hm hmX h u v hu hv huX hvX S T hprime hseparate hSdiam hTdiam hUc hVc
  classical
  let U := canonicalKernelRoots S m h u
  let V := canonicalKernelRoots T m h v
  let Q : ℕ := ⌊X^(1/2-5*η:ℝ)⌋₊
  let P := Q.primesLE.filter (fun p => ¬p∣4*m*(u*v).natAbs ∧ jacobiSym (u*v) p=1)
  have hU : U.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < U.card := (Real.rpow_pos_of_pos (by linarith) _).trans_le hUc
    exact_mod_cast hh
  have hV : V.Nonempty := by
    apply Finset.card_pos.mp
    have hh : (0:ℝ) < V.card := (Real.rpow_pos_of_pos (by linarith) _).trans_le hVc
    exact_mod_cast hh
  have huvX : |((u*v:ℤ):ℝ)| ≤ X^(2*η) := by
    rw [Int.cast_mul,abs_mul]
    have hh := mul_le_mul huX hvX (abs_nonneg _) (Real.rpow_nonneg (by linarith) _)
    have he : X^η*X^η=X^(2*η) := by rw [← Real.rpow_add (by linarith : 0 < X)];congr 1;ring
    exact hh.trans_eq he
  have hmass' := hmass η hη hηbound (u*v) (mul_ne_zero hu hv) m hm hmX huvX
  have hlocal : ∀ p∈P,4/(p:ℝ) ≤ rootCollisionProbability U p+rootCollisionProbability V p := by
    intro p hp
    obtain ⟨hpQ,hpnd,hjac⟩ := Finset.mem_filter.mp hp
    have hpprime := (Nat.mem_primesLE.mp hpQ).2
    let : Fact p.Prime := ⟨hpprime⟩
    apply canonicalKernelRoots_split_collision S T m h u v hU hV hprime _ hpnd hjac
    intro x hx y hy
    have hpQ_real : (p:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hpQ).1
    have hp_le : (p:ℝ) ≤ X^(1/2-5*η:ℝ) := hpQ_real.trans
      (Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ X) _))
    have hsmall : X^(1/2-5*η:ℝ) < X^(9/10:ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
    have hh := hp_le.trans_lt (hsmall.trans_le (hseparate x hx y hy))
    exact_mod_cast hh
  have hlow := weighted_root_collision_lower U V hU hV Q P (Finset.filter_subset _ _) hlocal
  have hlower : 2*(∑ p∈Q.primesLE,Real.log (p:ℝ)/p)+2*((3/100:ℝ)*Real.log X) ≤
      ∑ p∈Q.primesLE,Real.log (p:ℝ)*(rootCollisionProbability U p+rootCollisionProbability V p) := by
    apply le_trans _ hlow
    have hh := mul_le_mul_of_nonneg_left hmass' (by norm_num : (0:ℝ)≤2)
    simpa only [add_comm] using add_le_add_left hh (2*(∑ p∈Q.primesLE,Real.log (p:ℝ)/p))
  exact himpossible η U V hη (hηbound.trans hηsmall) hU hV hUc hVc
    (canonicalKernelRoots_diameter_scale hu hX.le hη hmX hSdiam)
    (canonicalKernelRoots_diameter_scale hv hX.le hη hmX hTdiam) hlower

end Ostmann.QuadraticCenter

end

end OAI
