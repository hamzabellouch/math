import OAI.Combinatorics.ContingencyTables.Transport.ReflectedSlices

namespace OAI

/-!
# Equality factors under the actual physical coordinate bijection

A bijection of coordinates preserves the line totals and unary products.
Consequently the balanced marginal signature applies to the literal
physical factor family after all cell-index bookkeeping has been proved.
-/

namespace ContingencyTables.EqualityReindex

open scoped BigOperators Classical
open ProductIntegerSignature EqualitySoftening BalancedFamily BalancedBox

variable {C D G : Type*} [Fintype C] [Fintype D] [Fintype G]

omit [Fintype G] in
lemma lineTotal_reindex (e : C ≃ D) (line : D → G) (z : C → ℕ) (g : G) :
    lineTotal (line ∘ e) z g=lineTotal line (z ∘ e.symm) g := by
  unfold lineTotal
  have h := e.sum_comp (fun d => if line d=g then z (e.symm d) else 0)
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h

lemma productWeight_reindex (e : C ≃ D) (line : D → G)
    (a : G → ℕ → ℝ) (b : D → ℕ → ℝ) (z : C → ℕ) :
    productWeight (line ∘ e) a (fun c => b (e c)) z=
      productWeight line a b (z ∘ e.symm) := by
  unfold productWeight
  simp_rw [lineTotal_reindex]
  congr 1
  have h := e.prod_comp (fun d => b d (z (e.symm d)))
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using h

lemma exactWeight_reindex (e : C ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ) (z : C → ℕ) :
    exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e)
      (uslope ∘ e) (cap ∘ e) z=
      exactWeight line root rate offset slope urate ell uslope cap (z ∘ e.symm) := by
  unfold exactWeight
  exact productWeight_reindex e line (exactLineFactor root rate offset slope)
    (unaryFactor urate ell uslope cap) z

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The application needs precisely the raw removal signature of the
actual physical factor marginal, rather than a hypothesis asserting it. -/
theorem physical_marginal_removal (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ)
    (hwidth : ∀ M ∈ Ms, 2≤M) (hrate : ∀ g, 0≤rate g) (hu : ∀ d, 0≤urate d) :
    RemovalSlice (eliminate Ms (fun z =>
      exactWeight line root rate offset slope urate ell uslope cap (z ∘ e.symm))) m R := by
  have heq : (fun z => exactWeight line root rate offset slope urate ell uslope cap
      (z ∘ e.symm))=
      exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) := by
    funext z
    exact (exactWeight_reindex e line root rate offset slope urate ell uslope cap z).symm
  rw [heq]
  exact exact_marginal_removal Ms m R (line ∘ e) root rate offset slope
    (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) hwidth hrate (fun i => hu (e i))

/-- Global physical reflection also preserves the proved marginal
signature, and all balanced pairs are reflected along with small views. -/
theorem physical_marginal_reflected (Ms : List ℕ) (m : S → ℕ) (R : ℕ)
    (e : Coordinates S Ms ≃ D) (line : D → G) (root : G → Bool)
    (rate offset slope : G → ℝ) (urate ell uslope cap : D → ℝ)
    (hwidth : ∀ M ∈ Ms, 2≤M) (hrate : ∀ g, 0≤rate g) (hu : ∀ d, 0≤urate d) :
    RemovalSlice (fun z => eliminate Ms (fun q =>
      exactWeight line root rate offset slope urate ell uslope cap (q ∘ e.symm))
      (IntegerReflection.reflect m z)) m R := by
  have heq : (fun z => exactWeight line root rate offset slope urate ell uslope cap
      (z ∘ e.symm))=
      exactWeight (line ∘ e) root rate offset slope (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) := by
    funext z
    exact (exactWeight_reindex e line root rate offset slope urate ell uslope cap z).symm
  rw [heq]
  exact ReflectedSlices.reflected_exact_marginal Ms m R (line ∘ e) root rate offset slope
    (urate ∘ e) (ell ∘ e) (uslope ∘ e) (cap ∘ e) hwidth hrate (fun i => hu (e i))

end ContingencyTables.EqualityReindex

end OAI
