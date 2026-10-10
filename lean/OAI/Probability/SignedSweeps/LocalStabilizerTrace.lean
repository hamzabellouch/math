import OAI.Probability.SignedSweeps.PairExtension
import OAI.Probability.SignedSweeps.ProjectionTrace
import OAI.Probability.SignedSweeps.DimensionUpperEntropy

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {G E F : Type*} [Monoid G]
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (ρ : Representation ℂ G E) (σ : Representation ℂ G F)
    (P : E →ₗ[ℂ] E) (hcomm : ∀ g, ρ g * P = P * ρ g)

def projectionConstituent
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation) :
    Representation.IntertwiningMap σ ρ :=
  ((projectionSubrepresentation ρ P hcomm).toSubmodule.subtype ∘ₗ f.toLinearMap).intertwiningMap_of_isIntertwiningMap
    σ ρ (fun g x => congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ f g x))

lemma projectionConstituent_nonzero
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation)
    (hf : f ≠ 0) : projectionConstituent ρ σ P hcomm f ≠ 0 := by
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap hz) x

lemma projectionConstituent_fixed (hP : P * P = P)
    (f : Representation.IntertwiningMap σ (projectionSubrepresentation ρ P hcomm).toRepresentation)
    (x : F) : P (projectionConstituent ρ σ P hcomm f x) =
      projectionConstituent ρ σ P hcomm f x := by
  change P (f x : E) = (f x : E)
  obtain ⟨y,hy⟩ := (f x).property
  change P y = (f x : E) at hy
  rw [← hy]
  exact LinearMap.congr_fun hP y

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

theorem signed_local_stabilizer_trace {u v p l n : ℕ} {C : Type*} [Fintype C]
    (h : u+v=p) (hn : u+v+l=n) (a : Partition u) (b : Partition v)
    (ha : a.1.colLen 0 ≤ Fintype.card C) (hb : b.1.colLen 0 ≤ Fintype.card C)
    (i : Fin p ↪ Fin n) (f : SymmetricGroup n → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive)
    (η G : ℝ)
    (hambient : ∀ (lam : Partition n) (c : Partition l), SignedOccurrence hn a b c lam →
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η * signedEntropy a b + G))
    (B : ℕ) (hB : 2*p+2*Fintype.card C+1 ≤ B) :
    (LinearMap.trace ℂ (WordSpace p (C ⊕ C))
      (pairTypeProjection h a b C * coefficientAction (signedWordRepresentation p C)
        (fun g => f (g.viaEmbedding i)))).re ≤
      ((p.factorial : ℝ) / n.factorial) * (Fintype.card (Partition n) : ℝ) *
        (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) *
        Real.exp ((η-1)*signedEntropy a b + G +
          Real.log (p+1 : ℕ) + 1 +
          8*(Fintype.card C : ℝ)*(Real.log (p+1 : ℕ)+1) +
          24*(Fintype.card C : ℝ)^2*Real.log B) := by
  let Q := pairTypeProjection h a b C
  have hcomm (g : SymmetricGroup p) : signedWordRepresentation p C g * Q =
      Q * signedWordRepresentation p C g := (pairTypeProjection_signed_commute h a b g).symm
  let S := projectionSubrepresentation (signedWordRepresentation p C) Q hcomm
  let ρ := S.toRepresentation
  let F := signedEntropy a b
  let E := 4*(Fintype.card C : ℝ)*(Real.log (p+1 : ℕ)+1) +
    12*(Fintype.card C : ℝ)^2*Real.log B
  have hQ : Q * Q = Q := pairTypeProjection_idempotent h a b C
  have hdegree (mu : Partition p)
      (hm : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0) :
      Real.exp (F-E) ≤ (spechtDimension mu : ℝ) := by
    obtain ⟨k,hk⟩ := hm
    let t := projectionConstituent (signedWordRepresentation p C) (spechtRepresentation mu) Q hcomm k
    have ht : t ≠ 0 := projectionConstituent_nonzero _ _ _ _ k hk
    have htQ (x : Specht mu) : Q (t x) = t x := projectionConstituent_fixed _ _ _ _ hQ k x
    obtain ⟨A,j,hj,hint⟩ := pair_sector_constituent_occurrence h a b mu t ht htQ
    have hd := signed_pair_log_dimension_lower h a b mu ha hb (allocationEquiv h A)
      j hj hint B hB
    have hd' : F-E ≤ Real.log (spechtDimension mu : ℝ) := by dsimp [F,E]; linarith
    exact (Real.exp_le_exp.mpr hd').trans_eq (Real.exp_log (by exact_mod_cast spechtDimension_pos mu))
  have hamb (mu : Partition p)
      (hm : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu) ρ, k ≠ 0)
      (lam : Partition n)
      (hlam : ∃ k : Representation.IntertwiningMap (spechtRepresentation mu)
        ((spechtRepresentation lam).comp (Equiv.Perm.viaEmbeddingHom i)), k ≠ 0) :
      (spechtDimension lam : ℝ) *
        (LinearMap.trace ℂ (Specht lam) (coefficientAction (spechtRepresentation lam) f)).re ≤
          Real.exp (η*F+G) := by
    obtain ⟨k,hk⟩ := hm
    obtain ⟨j,hj⟩ := hlam
    let t := projectionConstituent (signedWordRepresentation p C) (spechtRepresentation mu) Q hcomm k
    have ht : t ≠ 0 := projectionConstituent_nonzero _ _ _ _ k hk
    have htQ (x : Specht mu) : Q (t x) = t x := projectionConstituent_fixed _ _ _ _ hQ k x
    obtain ⟨c,hc⟩ := signed_occurrence_of_sector_extension h hn a b mu lam i t ht htQ j hj
    exact hambient lam c hc
  have ht := sector_positive_restriction (E := S.toSubmodule) ρ (Equiv.Perm.viaEmbeddingHom i)
    (viaEmbeddingHom_injective i) f hf (Real.exp (F-E)) (Real.exp (η*F+G))
      (Real.exp_pos _) (Real.exp_nonneg _) hdegree hamb
  rw [projectionSubrepresentation_trace (signedWordRepresentation p C) Q hQ hcomm]
  apply ht.trans
  have hrank := pairTypeProjection_rank_entropy_upper h a b C
  change (finrank ℂ (Q.range) : ℝ) ≤ _ at hrank
  have hr : (finrank ℂ S.toSubmodule : ℝ) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) /
        Real.exp (F-E)^2 ≤
      (Real.exp (F + Real.log (p+1 : ℕ)+1) * (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C))) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) /
        Real.exp (F-E)^2 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrank (by positivity)) (by positivity)
  apply hr.trans_eq
  rw [← Real.exp_nat_mul, div_eq_mul_inv, ← Real.exp_neg]
  have he : (Real.exp (F + Real.log (p+1 : ℕ)+1) * (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C))) *
        (((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) * Real.exp (η*F+G)) *
        Real.exp (-(2*(F-E))) =
      ((p.factorial : ℝ)/n.factorial) * (Fintype.card (Partition n) : ℝ) *
        (p+1 : ℝ)^(2*(Fintype.card C*Fintype.card C)) *
          (Real.exp (F+Real.log (p+1 : ℕ)+1) * Real.exp (η*F+G) * Real.exp (-(2*(F-E)))) := by ring
  rw [Nat.cast_ofNat, he, ← Real.exp_add, ← Real.exp_add]
  congr 2
  dsimp [F,E]
  ring

end SignedSweeps
end

end OAI
