import OAI.GroupTheory.Thompson.GlobalColors
import OAI.GroupTheory.Thompson.AffineTransport
import Mathlib.Data.Finset.Union

namespace OAI

/-!
# A fixed finite family of actual affine transports

The set of transports depends only on the branching parameter. Each ordered
separated pair in the actual parent/child family is carried onto the reference
pair. After this set is fixed, one partition level is selected for the given
finite group set and all of its translates by these transports.
-/

noncomputable section

open scoped InnerProductSpace

universe uE

namespace ThompsonNonamenability

local instance : DecidableEq F := Classical.decEq F

variable {D : ℕ}

/-- The ordered separated pairs of actual interval occurrences. -/
def orderedIntervalPairs (D : ℕ) : Finset (IntervalIndex D × IntervalIndex D) := by
  classical
  exact Finset.univ.filter (fun p =>
    (familyInterval D p.1).Before (familyInterval D p.2))

theorem mem_orderedIntervalPairs (D : ℕ) (q r : IntervalIndex D) :
    (q, r) ∈ orderedIntervalPairs D ↔
      (familyInterval D q).Before (familyInterval D r) := by
  classical
  simp only [orderedIntervalPairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An actual Thompson-group witness, chosen only for a genuinely separated pair. -/
def pairTransport (hD : 2 ≤ D) (p : {p // p ∈ orderedIntervalPairs D}) : F :=
  Classical.choose (exists_affine_pair_transport
    (familyInterval_internal D p.val.1) (familyInterval_internal D p.val.2)
    (selectedInterval_internal D (firstIndex hD))
    (selectedInterval_internal D (secondIndex hD))
    ((mem_orderedIntervalPairs D p.val.1 p.val.2).mp p.property)
    (reference_before hD))

theorem pairTransport_spec (hD : 2 ≤ D) (p : {p // p ∈ orderedIntervalPairs D}) :
    CarriesAffinely (pairTransport hD p) (familyInterval D p.val.1)
      (familyInterval D (.inl (firstIndex hD))) ∧
    CarriesAffinely (pairTransport hD p) (familyInterval D p.val.2)
      (familyInterval D (.inl (secondIndex hD))) :=
  Classical.choose_spec (exists_affine_pair_transport
    (familyInterval_internal D p.val.1) (familyInterval_internal D p.val.2)
    (selectedInterval_internal D (firstIndex hD))
    (selectedInterval_internal D (secondIndex hD))
    ((mem_orderedIntervalPairs D p.val.1 p.val.2).mp p.property)
    (reference_before hD))

/-- This actual finite subset of F is fixed before any averaging set. -/
def fixedTransportSet (hD : 2 ≤ D) : Finset F :=
  (orderedIntervalPairs D).attach.image (pairTransport hD)

theorem transport_of_before (hD : 2 ≤ D) (q r : IntervalIndex D)
    (hqr : (familyInterval D q).Before (familyInterval D r)) :
    ∃ h ∈ fixedTransportSet hD,
      CarriesAffinely h (familyInterval D q)
        (familyInterval D (.inl (firstIndex hD))) ∧
      CarriesAffinely h (familyInterval D r)
        (familyInterval D (.inl (secondIndex hD))) := by
  let p : {p // p ∈ orderedIntervalPairs D} :=
    ⟨(q, r), (mem_orderedIntervalPairs D q r).mpr hqr⟩
  refine ⟨pairTransport hD p, ?_, pairTransport_spec hD p⟩
  exact Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩

theorem fixedTransportSet_nonempty (hD : 2 ≤ D) :
    (fixedTransportSet hD).Nonempty := by
  obtain ⟨h, hh, _⟩ := transport_of_before hD
    (.inl (firstIndex hD)) (.inl (secondIndex hD)) (reference_before hD)
  exact ⟨h, hh⟩

/-- The one finite set used to select a common partition level. -/
def transportClosure (S A : Finset F) : Finset F :=
  A ∪ S.biUnion (fun h => leftTranslate h A)

theorem mem_transportClosure_self (S A : Finset F) {g : F} (hg : g ∈ A) :
    g ∈ transportClosure S A := Finset.mem_union_left _ hg

theorem mem_transportClosure_mul (S A : Finset F) {h g : F}
    (hh : h ∈ S) (hg : g ∈ A) : h * g ∈ transportClosure S A := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨h, hh, Finset.mem_image.mpr ⟨g, hg, rfl⟩⟩

/-- A single level works simultaneously on A and on every hA for h in fixed S. -/
theorem exists_transport_admissible (hD : 2 ≤ D) (A : Finset F) :
    ∃ n, (∀ g ∈ A, GlobalAdmissible D n g) ∧
      ∀ h ∈ fixedTransportSet hD, ∀ g ∈ A, GlobalAdmissible D n (h * g) := by
  obtain ⟨n, hn⟩ := exists_common_admissible D
    (transportClosure (fixedTransportSet hD) A)
  exact ⟨n, (fun g hg => hn g (mem_transportClosure_self _ _ hg)),
    fun h hh g hg => hn (h * g) (mem_transportClosure_mul _ _ hh hg)⟩

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Symmetry is used only to orient a separated pair; it introduces no sign
assumption on its real inner product. -/
theorem globalCorrelation_comm (hD : 0 < D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (q r : IntervalIndex D) (g : F) :
    globalCorrelation hD f n q r g = globalCorrelation hD f n r q g := by
  exact real_inner_comm (globalColor hD f n r g : E) (globalColor hD f n q g : E)

/-- All separated correlations are compared with one reference correlation
using only the maximum boundary over the previously fixed finite set. -/
theorem separated_correlation_bound (hD : 2 ≤ D) (f : UnitBall E → UnitBall E)
    (n : ℕ) (A : Finset F) (hA : A.Nonempty)
    (hg : ∀ g ∈ A, GlobalAdmissible D n g)
    (hhg : ∀ h ∈ fixedTransportSet hD, ∀ g ∈ A, GlobalAdmissible D n (h * g))
    (q r : IntervalIndex D)
    (hqr : StrictlySeparated (familyInterval D q) (familyInterval D r)) :
    |realAvg A (globalCorrelation (lt_of_lt_of_le (by decide : 0 < 2) hD) f n q r) -
      realAvg A (globalCorrelation (lt_of_lt_of_le (by decide : 0 < 2) hD) f n
        (.inl (firstIndex hD)) (.inl (secondIndex hD)))| ≤
      boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A := by
  have hDpos : 0 < D := lt_of_lt_of_le (by decide : 0 < 2) hD
  have ordered_bound (u v : IntervalIndex D)
      (huv : (familyInterval D u).Before (familyInterval D v)) :
      |realAvg A (globalCorrelation hDpos f n u v) -
        realAvg A (globalCorrelation hDpos f n
          (.inl (firstIndex hD)) (.inl (secondIndex hD)))| ≤
        boundaryMax (fixedTransportSet hD) (fixedTransportSet_nonempty hD) A := by
    obtain ⟨h, hh, hu, hv⟩ := transport_of_before hD u v huv
    exact (globalCorrelation_translate_bound hDpos f n A hA h u v
      (.inl (firstIndex hD)) (.inl (secondIndex hD)) hu hv hg (hhg h hh)).trans
      (boundaryRatio_le_max _ _ A hh)
  rcases hqr with hqr | hrq
  · exact ordered_bound q r hqr
  · have hsym : realAvg A (globalCorrelation hDpos f n q r) =
        realAvg A (globalCorrelation hDpos f n r q) := by
      exact realAvg_congr A (fun g _ => globalCorrelation_comm hDpos f n q r g)
    rw [hsym]
    exact ordered_bound r q hrq

end ThompsonNonamenability

end

end OAI
