import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentCentralRoots
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentQuotientRank

namespace OAI

/-! # Torsion-free upper central quotients

Each upper central term is closed under taking roots. The center of every
resulting quotient therefore embeds faithfully into a finite-dimensional
rational space whenever the original group has finite integral dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative
variable {G : Type} [Group G]

theorem quotient_torsionFree_of_root_closed (N : Subgroup G) [N.Normal]
    (hN : ∀ (g : G) (n : ℕ), n ≠ 0 → g ^ n ∈ N → g ∈ N) :
    HasNoNontrivialTorsion (G ⧸ N) := by
  intro x n hn hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  apply (QuotientGroup.eq_one_iff g).mpr
  apply hN g n hn
  apply (QuotientGroup.eq_one_iff (g ^ n)).mp
  change (QuotientGroup.mk' N) (g ^ n) = 1
  simpa only [map_pow] using hx

theorem nilpotent_upperCentralQuotient_torsionFree [Group.IsNilpotent G]
    (hG : HasNoNontrivialTorsion G) (k : ℕ) :
    HasNoNontrivialTorsion (G ⧸ Subgroup.upperCentralSeries G k) := by
  induction k with
  | zero =>
    apply quotient_torsionFree_of_root_closed
    intro g n hn hgn
    change g ^ n = 1 at hgn
    change g = 1
    exact hG g n hn hgn
  | succ k ih =>
    let U := Subgroup.upperCentralSeries G k
    let q := QuotientGroup.mk' U
    have he : Subgroup.upperCentralSeries G (k + 1) =
        (Subgroup.center (G ⧸ U)).comap q :=
      Subgroup.upperCentralSeriesStep_eq_comap_center U
    apply quotient_torsionFree_of_root_closed
    intro g n hn hgn
    rw [he] at hgn ⊢
    have hp : (q g) ^ n ∈ Subgroup.center (G ⧸ U) := by
      rw [← map_pow]
      exact hgn
    exact nilpotent_mem_center_of_pow_mem_center ih (q g) hn hp

theorem nilpotent_upperCentral_center_rational_finite [Group.IsNilpotent G]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d] (k : ℕ) :
    Module.Finite ℚ
      (RationalAbelianSpace (Subgroup.center (G ⧸ Subgroup.upperCentralSeries G k))) := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [rationalAbelianSpace_rank]
  exact (nilpotent_quotient_abelian_subgroup_rank_le d
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) (Subgroup.center _)).trans_lt
      Cardinal.natCast_lt_aleph0

end PolycyclicRecognition

end

end OAI
