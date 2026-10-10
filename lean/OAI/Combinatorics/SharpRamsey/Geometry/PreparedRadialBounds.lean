import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.RadialExceptions

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section

lemma pair_square_budget (P N M J : ℕ) (hJ : 2*J≤M) (hM : 4≤M)
    (hp : P*((M-J)*(M-J-1))≤N^2) : (P:ℝ)*(M:ℝ)^2≤8*(N:ℝ)^2 := by
  have h1 : M≤2*(M-J) := by omega
  have h2 : M≤4*(M-J-1) := by omega
  have h1' : (M:ℝ)≤2*((M-J:ℕ):ℝ) := by exact_mod_cast h1
  have h2' : (M:ℝ)≤4*((M-J-1:ℕ):ℝ) := by exact_mod_cast h2
  have hd : (M:ℝ)^2≤8*((M-J:ℕ):ℝ)*((M-J-1:ℕ):ℝ) := by
    have hh := mul_le_mul h1' h2' (Nat.cast_nonneg M) (by positivity)
    nlinarith
  have hp' : (P:ℝ)*(((M-J:ℕ):ℝ)*((M-J-1:ℕ):ℝ))≤(N:ℝ)^2 := by exact_mod_cast hp
  have hh := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg P)
  nlinarith

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadialBounds_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadialBounds_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedRadialBounds_3 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedRadialBounds_4 : Fintype (Submodule K V) := Fintype.ofFinite _

lemma rich_threshold (X : Finset (Projectivization K V)) (x : Projectivization K V)
    (W : RadialLine x) (a c : ℝ) (hc : 0<c) (ha : a ≤ strength X x c W) :
    ⌈a/c⌉₊≤(X∩planePoints W.1).card := by
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ hc).mpr
  have hsub : radialFiber X x W⊆X∩planePoints W.1 := by
    intro y hy
    have hh := (mem_radialFiber X x y W).mp hy
    exact mem_inter.mpr ⟨hh.1,mem_planePoints.mpr hh.2.2⟩
  exact ha.trans (by
    have hh := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card hsub)) hc.le
    simpa only [strength,mul_comm] using hh)

theorem list_radial_pairs (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c a : ℝ) (hc : 0<c) (ha : 0≤a)
    (hJ : 2*bs.length≤⌈a/c⌉₊) (hM : 4≤⌈a/c⌉₊) :
    (∑ x,((richRadials
      (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c a).card:ℝ))*a^2≤
      8*(c*(GreedyPreparation.removed S planePoints bs).card)^2 := by
  let X := fun x => GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})
  let M := ⌈a/c⌉₊
  let P := ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
    (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card
  have hMJ : bs.length≤M := by dsimp [M]; omega
  have hr : 0<M-bs.length := by dsimp [M]; omega
  have hp := projective_prepared_radial F m S bs h (M-bs.length) hr
  have he : bs.length+(M-bs.length)=M := Nat.add_sub_of_le hMJ
  rw [he] at hp
  change P*((M-bs.length)*(M-bs.length-1))≤_ at hp
  have hp2 := pair_square_budget P (GreedyPreparation.removed S planePoints bs).card M bs.length hJ hM hp
  have hsum : (∑ x,((richRadials (X x) x c a).card:ℝ))≤P := by
    exact_mod_cast sum_richRadials_le_pairs X c a M (fun x W hw => rich_threshold (X x) x W a c hc hw)
  have haM : a≤c*M := by
    have hh := Nat.le_ceil (a/c)
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hsquare : a^2≤c^2*(M:ℝ)^2 := by nlinarith
  have hsum' := mul_le_mul_of_nonneg_right hsum (sq_nonneg a)
  have hPscale := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg P)
  have hfinal := mul_le_mul_of_nonneg_left hp2 (sq_nonneg c)
  change (∑ x,((richRadials (X x) x c a).card:ℝ))*a^2≤_
  nlinarith

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
