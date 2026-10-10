import OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Restriction of a product law to selected prime coordinates.  The
coordinate laws may depend on the prime; no common-modulus uniformity is
assumed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

lemma independent_average_reindex {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : ι ≃ κ) (μ : κ → FiniteLaw A) (f : (κ → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i => μ (e i))).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent μ).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent μ).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, (μ k).weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, (μ (e i)).weight (x i)) * f (fun k => x (e.symm k))
      congr 1
      simpa only [e.apply_symm_apply] using
        e.symm.prod_comp (fun i => (μ (e i)).weight (x i))

lemma independent_average_restrict {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι) (f : (S → A) → ℝ) :
    (independent μ).average (fun x => f (fun i : S => x i)) =
      (independent (fun i : S => μ i)).average f := by
  rw [independent_average_split μ S]
  simp only [joinCoordinates_mem, average_const]

/-- Independent coordinates retain their individual laws under an
injective change of the index set. -/
lemma independent_average_embedding {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : κ → ι) (he : Function.Injective e) (μ : ι → FiniteLaw A)
    (f : (κ → A) → ℝ) :
    (independent μ).average (fun x => f (fun k => x (e k))) =
      (independent (fun k => μ (e k))).average f := by
  let S : Finset ι := univ.image e
  let E : κ ≃ S := Equiv.ofBijective
    (fun k => ⟨e k, mem_image.mpr ⟨k, mem_univ _, rfl⟩⟩) (by
      constructor
      · intro x y hxy
        exact he (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨k, _, hk⟩ := mem_image.mp y.property
        exact ⟨k, Subtype.ext hk⟩)
  calc
    _ = (independent (fun i : S => μ i)).average
        (fun x => f (fun k => x (E k))) :=
      independent_average_restrict μ S (fun x => f (fun k => x (E k)))
    _ = _ := by
      rw [independent_average_reindex E]
      simp only [E.symm_apply_apply]
      rfl

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

def paddingCoordinate (p : data.Q) : ↥(data.P ∪ data.Q) :=
  ⟨p.val, mem_union_right _ p.property⟩

def paddingRestriction (x : ↥(data.P ∪ data.Q) → Fin B) : data.Q → Fin B :=
  fun p => x (data.paddingCoordinate p)

noncomputable def paddingResidueLaw (B : ℕ)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) : FiniteLaw (data.Q → Fin B) :=
  FiniteLaw.independent (fun p : data.Q =>
    uniformResidueLaw B p.val (data.primeQ _ p.property).pos
      (hB _ (mem_union_right _ p.property)))

lemma residue_average_padding (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : (data.Q → Fin B) → ℝ) :
    (data.residueLaw B hB).average (fun x => f (data.paddingRestriction x)) =
      (data.paddingResidueLaw B hB).average f := by
  have hi : Function.Injective data.paddingCoordinate := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : ↥(data.P ∪ data.Q) => z.val) hpq
  exact FiniteLaw.independent_average_embedding data.paddingCoordinate hi
    (fun p => uniformResidueLaw B p.val (data.prime p).pos (hB _ p.property)) f

lemma exists_padding_residue_origin (x : data.Q → Fin B) :
    ∃ n : ℤ, ∀ p : data.Q, (n : ZMod p.val) = ((x p).val : ZMod p.val) := by
  let (p : data.Q) : NeZero p.val := ⟨(data.primeQ _ p.property).ne_zero⟩
  apply exists_common_integer_residue (fun p : data.Q => p.val)
  intro p q hpq
  exact (Nat.coprime_primes (data.primeQ _ p.property) (data.primeQ _ q.property)).mpr
    (fun he => hpq (Subtype.ext he))

noncomputable def paddingResidueOrigin (x : data.Q → Fin B) : ℤ :=
  (data.exists_padding_residue_origin x).choose

lemma paddingResidueOrigin_spec (x : data.Q → Fin B) (p : data.Q) :
    (data.paddingResidueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_padding_residue_origin x).choose_spec p

/-- Padding-periodic observables at the full CRT lift depend only on the
independent padding coordinates, including after a fixed integer shift. -/
lemma residue_average_padding_shift (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (site : ℤ) (f : ℤ → ℝ)
    (hf : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → f n = f m) :
    (data.residueLaw B hB).average (fun x => f (data.residueOrigin x + site)) =
      (data.paddingResidueLaw B hB).average (fun x =>
        f (data.paddingResidueOrigin x + site)) := by
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        f (data.paddingResidueOrigin (data.paddingRestriction x) + site)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply hf
      intro q hq
      let p : data.Q := ⟨q, hq⟩
      rw [Int.cast_add, Int.cast_add]
      exact congrArg (fun z : ZMod q => z + (site : ZMod q))
        ((data.residueOrigin_spec x (data.paddingCoordinate p)).trans
          (data.paddingResidueOrigin_spec (data.paddingRestriction x) p).symm)
    _ = _ := data.residue_average_padding hB
      (fun x => f (data.paddingResidueOrigin x + site))

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI
