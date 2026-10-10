import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZPipeline
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedPrivate

namespace OAI

/-! Uniform incidence bounds for the actual ordered local reductions.  Every
new site belongs to one input term, while old sites remain in that term's
stored support.  The bound counts zero-coefficient terms as well. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedIncidence
open scoped BigOperators Classical

variable {ι κ : Type} [Fintype κ]

def count (xs : κ → List ι) (q : ι) : ℕ :=
  ∑ e, if q ∈ xs e then 1 else 0

def Bounded (xs : κ → List ι) (D : ℕ) : Prop := ∀ q, count xs q ≤ D

def Origin (xs : κ → List ι) (e : κ) : ι ⊕ κ → Prop :=
  Sum.elim (fun q => q ∈ xs e) (fun f => f = e)

theorem extension_bound {d D : ℕ} (xs : κ → List ι)
    (ys : κ × Fin d → List (ι ⊕ κ)) (hD : 1 ≤ D) (hx : Bounded xs D)
    (hy : ∀ p q, q ∈ ys p → Origin xs p.1 q) : Bounded ys (d*D) := by
  intro q
  cases q with
  | inl q =>
    calc
      count ys (Sum.inl q) ≤ ∑ p : κ × Fin d, if q ∈ xs p.1 then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases h : Sum.inl q ∈ ys p
        · have ho : q ∈ xs p.1 := hy p _ h
          simp only [h,ho,ite_true,le_refl]
        · simp only [h,ite_false,Nat.zero_le]
      _ = d*count xs q := by
        rw [Fintype.sum_prod_type]
        have hi (e : κ) : (∑ _k : Fin d, if q ∈ xs e then 1 else 0) =
            d*(if q ∈ xs e then 1 else 0) := by
          by_cases h : q ∈ xs e <;> simp [h]
        simp_rw [hi]
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ d*D := Nat.mul_le_mul_left d (hx q)
  | inr q =>
    calc
      count ys (Sum.inr q) ≤ ∑ p : κ × Fin d, if q=p.1 then 1 else 0 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases h : Sum.inr q ∈ ys p
        · have ho : q=p.1 := hy p _ h
          rw [ite_eq_left h,ite_eq_left ho]
        · simp only [h,ite_false,Nat.zero_le]
      _ = d := by
        rw [Fintype.sum_prod_type]
        have hi (e : κ) : (∑ _k : Fin d, if q=e then 1 else 0) =
            if q=e then d else 0 := by
          by_cases h : q=e <;> simp [h]
        simp_rw [hi]
        simp
      _ ≤ d*D := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hD

omit [Fintype κ] in
theorem append_origin (xs : κ → List ι) (e : κ) (zs : List ι)
    (hz : ∀ q ∈ zs, q ∈ xs e) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedSubdivision.appendMediator zs e) : Origin xs e q := by
  cases q with
  | inl q =>
    exact hz q (by simpa only [QuantumOrderedSubdivision.appendMediator,
      List.mem_append,List.mem_map,Sum.inl.injEq,exists_eq_right,List.mem_singleton,
      Sum.inl_ne_inr,or_false] using hq)
  | inr q =>
    simpa only [Origin,Sum.elim_inr,QuantumOrderedSubdivision.appendMediator,
      List.mem_append,List.mem_map,Sum.inl_ne_inr,and_false,exists_false,List.mem_singleton,
      Sum.inr.injEq,false_or] using hq

omit [Fintype κ] in
theorem subdivision_origin (xs : κ → List ι) (d : ℕ)
    (p : κ × Fin 4) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedSubdivision.outputSites xs d p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · simp [QuantumOrderedSubdivision.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedSubdivision.outputSites] using hq
    subst q
    rfl
  · exact append_origin xs e _ (fun _ h => List.mem_of_mem_take h) q hq
  · exact append_origin xs e _ (fun _ h => List.mem_of_mem_drop h) q hq

theorem subdivision_bound {D : ℕ} (xs : κ → List ι) (d : ℕ)
    (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedSubdivision.outputSites xs d) (4*D) :=
  extension_bound xs _ hD hx (subdivision_origin xs d)

omit [Fintype κ] in
theorem yy_origin (xs : κ → List ι) (p : κ × Fin 4) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedYY.outputSites xs p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  fin_cases k
  · simp [QuantumOrderedYY.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedYY.outputSites] using hq
    subst q
    rfl
  · exact append_origin xs e _ (fun _ h => h) q hq
  · exact append_origin xs e _ (fun _ h => h) q hq

theorem yy_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedYY.outputSites xs) (4*D) :=
  extension_bound xs _ hD hx (yy_origin xs)

omit [Fintype κ] in
theorem third_origin (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (p : κ × Fin 7) (q : ι ⊕ κ)
    (hq : q ∈ QuantumOrderedThird.outputSites xs w p) : Origin xs p.1 q := by
  rcases p with ⟨e,k⟩
  have hp : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).1, i ∈ xs e := by
    intro i hi
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_left _ hi)
  have hr : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).2, i ∈ xs e := by
    intro i hi
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_right _ hi)
  fin_cases k
  · simp [QuantumOrderedThird.outputSites] at hq
  · have he : q=Sum.inr e := by simpa [QuantumOrderedThird.outputSites] using hq
    subst q
    rfl
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact hp i hi
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
    exact hr i hi
  · exact append_origin xs e _ hr q hq
  · exact append_origin xs e _ (fun i h => hp i (List.mem_of_mem_take h)) q hq
  · exact append_origin xs e _ (fun i h => hp i (List.mem_of_mem_drop h)) q hq

theorem third_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedThird.outputSites xs w) (7*D) :=
  extension_bound xs _ hD hx (third_origin xs w hlen)

theorem xz_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedXZ.sites xs w) (3136*D) := by
  have h1 := subdivision_bound xs 3 hD hx
  have h2 := subdivision_bound (QuantumOrderedSubdivision.outputSites xs 3) 2
    (by omega : 1 ≤ 4*D) h1
  have h3 := third_bound (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeSites_length xs hlen) (by omega : 1 ≤ 4*(4*D)) h2
  have h4 := yy_bound (QuantumOrderedXZ.twoSites xs w) (by omega : 1 ≤ 7*(4*(4*D))) h3
  have h5 := third_bound (QuantumOrderedXZ.xzThreeSites xs w)
    (QuantumOrderedXZ.xzThreeWord xs w) (QuantumOrderedXZ.xzThreeSites_length xs w hlen)
    (by omega : 1 ≤ 4*(7*(4*(4*D)))) h4
  change Bounded (QuantumOrderedXZ.sites xs w) (7*(4*(7*(4*(4*D))))) at h5
  convert h5 using 1
  omega

theorem private_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedPrivate.outputSites xs) (4*D) :=
  subdivision_bound xs 1 hD hx

theorem complete_bound [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    {D : ℕ} (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (hD : 1 ≤ D) (hx : Bounded xs D) :
    Bounded (QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w)) (12544*D) := by
  have h := private_bound (QuantumOrderedXZ.sites xs w)
    (by omega : 1 ≤ 3136*D) (xz_bound xs w hlen hD hx)
  convert h using 1
  omega

end ContinuumCoulomb.QuantumOrderedIncidence

end

end OAI
