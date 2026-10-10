import OAI.Analysis.CircleDomains.Modulus.NormalFamilyInputs
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Compactness.SigmaCompact

namespace OAI

/-! Compactly supported cutoffs for a varying open exhaustion. The
chosen subsequence is increasing and each fixed compact set eventually
lies in the region on which its cutoff is exactly one. -/
open Set Function Filter Topology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_montel_exhaustion_cutoffs (D : ℕ → Set ℂ)
    (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ φ : ℕ → C(ℂ, ℝ),
      (∀ n x, φ n x ∈ Icc (0 : ℝ) 1) ∧
      (∀ n, tsupport (φ n) ⊆ D (s n)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ ⋃ n, D n →
        ∀ᶠ n in atTop, ∀ x ∈ K, φ n x = 1) := by
  let U := ⋃ n, D n
  have hU : IsOpen U := isOpen_iUnion hD
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  have hK (n : ℕ) : IsCompact (((↑) : U → ℂ) '' K n) :=
    (K.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : ((↑) : U → ℂ) '' K n ⊆ ⋃ n, D n := by
    rintro z ⟨x,_,rfl⟩
    exact x.property
  choose m hm using (fun n => (hK n).elim_directed_cover D hD (hKU n) hmono.directed_le)
  let s : ℕ → ℕ := Nat.rec (m 0) (fun n k => max (k+1) (m (n+1)))
  have hs : StrictMono s := strictMono_nat_of_lt_succ (fun n => by
    change s n < max (s n+1) (m (n+1))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _))
  have hms (n : ℕ) : m n ≤ s n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have hKn (n : ℕ) : ((↑) : U → ℂ) '' K n ⊆ D (s n) :=
    (hm n).trans (hmono (hms n))
  choose φ hone _ hsupp hrange using (fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK n) (hD (s n)) (hKn n))
  refine ⟨s,hs,φ,hrange,hsupp,?_⟩
  intro L hL hLU
  have hLc : IsCompact (((↑) : U → ℂ) ⁻¹' L) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hL
      (by simpa only [Subtype.range_coe] using hLU)
  obtain ⟨N,hN⟩ := K.exists_superset_of_isCompact hLc
  filter_upwards [eventually_ge_atTop N] with n hn
  intro x hx
  apply hone n
  exact ⟨⟨x,hLU hx⟩,K.subset hn (hN hx),rfl⟩

end CircleDomainRigidity

end

end OAI
