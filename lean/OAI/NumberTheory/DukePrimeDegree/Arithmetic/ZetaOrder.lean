import OAI.NumberTheory.DukePrimeDegree.Arithmetic.CyclicSubfields
import OAI.NumberTheory.DukePrimeDegree.Arithmetic.PacketBridge

namespace OAI

/-!
# A choice-independent continued zeta order

Zero orders do not depend on the ordering of the real embeddings or on
the finite set of removed Euler factors. We fix one ordering only to
package the continued zeta order as a function of a number field.
-/

noncomputable section
open Filter Set Module
open scoped NumberField Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

theorem coset_analytic_off_zero_one
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (N : ℕ) : AnalyticOnNhd ℂ (cosetMeromorphic σ hn N) ({0, 1} : Set ℂ)ᶜ := by
  intro z hz
  rw [cosetMeromorphic_eq_factor]
  exact (cosetXiFactor_analyticAt N (by simpa using (not_or.mp hz).1)
    (by simpa using (not_or.mp hz).2)).mul
      ((completedThetaXi_entire σ hn).analyticAt z)

theorem coset_order_independent_of_data
    {d e : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (τ : OrderedEmbeddings (e + 1) K) (he : finrank ℚ K = e + 1)
    (N M : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) =
      meromorphicOrderAt (cosetMeromorphic τ he M) (β : ℂ) := by
  have hanalytic {k : ℕ} (υ : OrderedEmbeddings (k + 1) K)
      (hk : finrank ℚ K = k + 1) (A B : ℕ) :
      AnalyticOnNhd ℂ (removedEulerPolynomial K A * cosetMeromorphic υ hk B)
        ({0, 1} : Set ℂ)ᶜ := by
    intro z hz
    apply ((removedEulerPolynomial_entire K A).analyticAt z).mul
    rw [cosetMeromorphic_eq_factor]
    exact (cosetXiFactor_analyticAt B (by simpa using (not_or.mp hz).1)
      (by simpa using (not_or.mp hz).2)).mul
        ((completedThetaXi_entire υ hk).analyticAt z)
  have heq := analytic_off_zero_one_eq_of_real_eq
    (hanalytic σ hn M N) (hanalytic τ he N M) (fun s hs => by
      simp only [Pi.mul_apply]
      rw [cosetMeromorphic_eq_dedekindZeta σ hn N hs,
        cosetMeromorphic_eq_dedekindZeta τ he M hs]
      ring)
  have hβ : (β : ℂ) ∈ ({0, 1} : Set ℂ)ᶜ := by
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Complex.ofReal_ne_zero.mpr hβ0.ne', by exact_mod_cast hβ1.ne⟩
  have hopen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
    (Set.Finite.isClosed (by simp)).isOpen_compl
  have hv : removedEulerPolynomial K M * cosetMeromorphic σ hn N =ᶠ[𝓝[≠] (β : ℂ)]
      removedEulerPolynomial K N * cosetMeromorphic τ he M := by
    have hu : ∀ᶠ z in 𝓝 (β : ℂ), z ∈ ({0, 1} : Set ℂ)ᶜ := hopen.mem_nhds hβ
    filter_upwards [hu.filter_mono nhdsWithin_le_nhds] with z hz
    exact heq hz
  have H := meromorphicOrderAt_congr hv
  rw [meromorphicOrderAt_mul_of_ne_zero ((removedEulerPolynomial_entire K M).analyticAt _)
      (removedEulerPolynomial_ne_zero K M hβ0),
    meromorphicOrderAt_mul_of_ne_zero ((removedEulerPolynomial_entire K N).analyticAt _)
      (removedEulerPolynomial_ne_zero K N hβ0)] at H
  exact H

def degreePred (K : Type*) [Field K] [NumberField K] : ℕ := finrank ℚ K - 1

theorem degreePred_spec (K : Type*) [Field K] [NumberField K] :
    finrank ℚ K = degreePred K + 1 := by
  have h : 0 < finrank ℚ K := finrank_pos
  dsimp only [degreePred]
  omega

def canonicalRealEmbeddings (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] : OrderedEmbeddings (degreePred K + 1) K := by
  letI : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic K
  letI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  let σ : EmbeddingOrder K (degreePred K + 1) :=
    (Fintype.equivFinOfCardEq (by rw [AlgHom.card, degreePred_spec K])).symm
  exact σ.toRealOrder

/-- The zero order of the continued Dedekind zeta function, using a
fixed embedding ordering and no removed primes. -/
def zetaZeroOrder (K : Type*) [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (β : ℝ) : WithTop ℤ :=
  meromorphicOrderAt
    (cosetMeromorphic (canonicalRealEmbeddings K) (degreePred_spec K) 1) (β : ℂ)

theorem zetaZeroOrder_eq_coset_order
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    (N : ℕ) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = meromorphicOrderAt (cosetMeromorphic σ hn N) (β : ℂ) :=
  coset_order_independent_of_data _ _ σ hn 1 N hβ0 hβ1

theorem zetaZeroOrder_eq_completed_order
    {d : ℕ} (σ : OrderedEmbeddings (d + 1) K) (hn : finrank ℚ K = d + 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    zetaZeroOrder K β = meromorphicOrderAt (completedThetaXi σ hn) (β : ℂ) := by
  rw [zetaZeroOrder_eq_coset_order σ hn 1 hβ0 hβ1,
    cosetMeromorphic_order_eq σ hn 1 hβ0 hβ1]

theorem zetaZeroOrder_finite_nonnegative
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ m : ℕ, zetaZeroOrder K β = (m : WithTop ℤ) := by
  let σ := canonicalRealEmbeddings K
  let hn := degreePred_spec K
  rw [zetaZeroOrder_eq_completed_order σ hn hβ0 hβ1]
  have ha : ∀ z, AnalyticAt ℂ (completedThetaXi σ hn) z :=
    fun z => (completedThetaXi_entire σ hn).analyticAt z
  have hfin : analyticOrderAt (completedThetaXi σ hn) (β : ℂ) ≠ ⊤ := by
    intro H
    have hz := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (β : ℂ) ha).mp H
    exact (completedThetaXi_ne_zero_of_re_gt_one_totallyReal σ hn (s := 2)
      (by norm_num)) (congrFun hz 2)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha (β : ℂ)).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

end DukePrimeDegree

end

end OAI
