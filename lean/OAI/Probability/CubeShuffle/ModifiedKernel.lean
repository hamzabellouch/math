import OAI.Probability.CubeShuffle.ModifiedDensity
import OAI.Probability.CubeShuffle.FiniteKernel

namespace OAI

namespace CubeShuffle
namespace PairRouting
open scoped BigOperators

lemma tupleProbability_row_sum {ι β Ω : Type*} [Fintype ι] [Fintype β]
    [DecidableEq β] [Fintype Ω] [Nonempty Ω]
    (P : Ω → Equiv.Perm β) (e : ι ↪ β) :
    (∑ f : ι ↪ β, tupleProbability P e f) = 1 := by
  classical
  simp only [tupleProbability]
  rw [←finiteMean_sum]
  have h (ω : Ω) (f : ι ↪ β) : (∀ i, P ω (e i) = f i) ↔ e.trans (P ω).toEmbedding = f := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congrArg (fun g : ι ↪ β => g i) h
  simp_rw [h]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,finiteMean_const]

lemma tupleProbability_inverse {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (e f : ι → β) :
    tupleProbability (fun ω => (P ω)⁻¹) e f = tupleProbability P f e := by
  classical
  apply finiteMean_congr
  intro ω
  congr 1
  apply propext
  constructor
  · intro h i
    have hh := congrArg (P ω) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh.symm
  · intro h i
    have hh := congrArg (fun x => (P ω).symm x) (h i)
    simpa only [Equiv.Perm.inv_def,Equiv.symm_apply_apply] using hh.symm

lemma tupleProbability_equiv {ι β Ω Ω' : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] [Fintype Ω'] (P : Ω → Equiv.Perm β) (τ : Ω ≃ Ω') (e f : ι → β) :
    tupleProbability P e f = tupleProbability (fun ω => P (τ.symm ω)) e f :=
  finiteMean_equiv τ _

lemma tupleProbability_symmetric {ι β Ω : Type*} [Fintype ι] [DecidableEq β]
    [Fintype Ω] (P : Ω → Equiv.Perm β) (τ : Equiv.Perm Ω)
    (hτ : ∀ ω, P (τ ω) = (P ω)⁻¹) (e f : ι → β) :
    tupleProbability P e f = tupleProbability P f e := by
  rw [tupleProbability_equiv P τ.symm]
  simp only [Equiv.symm_symm,hτ]
  exact tupleProbability_inverse P e f

end PairRouting

lemma palindromePerm_reverse (d : ℕ) (ω : BenesCoins d) :
    palindromePerm d (ω.2,ω.1) = (palindromePerm d ω)⁻¹ := by
  simp only [palindromePerm,mul_inv_rev]
  rfl

lemma palindrome_kernel_symmetric (d : ℕ) {ι : Type*} [Fintype ι]
    (e f : ι ↪ Card d) :
    PairRouting.tupleProbability (palindromePerm d) e f =
      PairRouting.tupleProbability (palindromePerm d) f e :=
  PairRouting.tupleProbability_symmetric _ (Equiv.prodComm _ _) (palindromePerm_reverse d) e f

/-- The actual palindrome density estimate combined with the proved finite
Schur/Bessel transfer. The family is an arbitrary orthonormal family in the
literal tuple space, not an assumed representation of the desired theorem. -/
theorem palindrome_density_transfer (d : ℕ) {ι I : Type*} [Fintype ι] [Fintype I]
    [Nonempty I] (e₀ : ι ↪ Card d) (hk : 0 < Fintype.card ι)
    (v : I → EuclideanSpace ℂ (ι ↪ Card d)) (hv : Orthonormal ℂ v)
    (μ : ℝ) (hvμ : ∀ i, μ ≤ ‖DensityTransfer.applyKernel
      (fun e f : ι ↪ Card d => PairRouting.tupleProbability (palindromePerm d) e f) (v i)‖)
    (z : ℝ) (hz : 0 < z) :
    μ ≤ Real.exp (densityConstant*Fintype.card ι*
      ((Fintype.card ι:ℝ)/(2:ℝ)^d)^(1/512:ℝ))*z^(-(1/1000:ℝ))+
      Real.sqrt (z/(Fintype.card I:ℝ)) := by
  let : Nonempty (ι ↪ Card d) := ⟨e₀⟩
  apply DensityTransfer.multiplicity_amplification
    (fun e f : ι ↪ Card d => PairRouting.tupleProbability (palindromePerm d) e f)
    (fun e f => PairRouting.tupleProbability_nonneg _ e f)
    (palindrome_kernel_symmetric d) (PairRouting.tupleProbability_row_sum _)
    (1/1000) z _ (by norm_num) hz (Real.exp_nonneg _) _ v hv μ hvμ
  intro e
  exact palindrome_row_moment_bound d e hk

end CubeShuffle
namespace CubeShuffle

/-- A measure-preserving reversal of the actual modified coin experiment.
At a leaf the redundant output butterfly is kept, while its uniform seed is
inverted and conjugated. At higher nodes the two outer fair fields are swapped. -/
noncomputable def modifiedReverseCoins (L : ℕ) : (r : ℕ) → ModifiedCoins L r → ModifiedCoins L r
  | 0, ω => ((fun u => butterflyPerm L (decodeButterfly L ω.2.1) * (ω.1 u)⁻¹ *
      butterflyPerm L (decodeButterfly L ω.2.1)),ω.2)
  | r+1, ω =>
      let z := modifiedStepEquiv L r ω
      (modifiedStepEquiv L r).symm
        ((modifiedReverseCoins L r z.1.1,modifiedReverseCoins L r z.1.2),(z.2.2,z.2.1))

lemma modifiedReverseCoins_involutive (L r : ℕ) :
    Function.Involutive (modifiedReverseCoins L r) := by
  induction r with
  | zero =>
      intro ω
      apply Prod.ext
      · funext u
        simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp [mul_assoc]
      · rfl
  | succ r ih =>
      change ∀ ω, modifiedReverseCoins L r (modifiedReverseCoins L r ω) = ω at ih
      intro ω
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,ih]
      exact (modifiedStepEquiv L r).symm_apply_apply ω

noncomputable def modifiedReverseEquiv (L r : ℕ) : Equiv.Perm (ModifiedCoins L r) where
  toFun := modifiedReverseCoins L r
  invFun := modifiedReverseCoins L r
  left_inv := modifiedReverseCoins_involutive L r
  right_inv := modifiedReverseCoins_involutive L r

lemma modifiedPerm_reverse (L r : ℕ) (E : Finset (Card r)) (ω : ModifiedCoins L r) :
    modifiedPerm L r E (modifiedReverseCoins L r ω) = (modifiedPerm L r E ω)⁻¹ := by
  induction r with
  | zero =>
      rw [modifiedPerm_zero,modifiedPerm_zero]
      split_ifs
      · simp only [inv_one]
      · simp only [modifiedReverseCoins,mul_inv_rev,inv_inv]
        simp
  | succ r ih =>
      obtain ⟨z,rfl⟩ := (modifiedStepEquiv L r).symm.surjective ω
      rcases z with ⟨⟨ω₀,ω₁⟩,⟨ξ,η⟩⟩
      simp only [modifiedReverseCoins,Equiv.apply_symm_apply,modifiedPerm_step,
        mul_inv_rev,pairSwitch_inv,childLift_inv]
      rw [mul_assoc]
      congr 1
      congr 1
      apply congrArg childLift
      funext b
      cases b <;> simp only [Bool.false_eq_true,↓reduceIte,ih]

lemma modified_kernel_symmetric (L r : ℕ) (E : Finset (Card r))
    {ι : Type*} [Fintype ι] (e f : ι ↪ Card (L+r)) :
    PairRouting.tupleProbability (modifiedPerm L r E) e f =
      PairRouting.tupleProbability (modifiedPerm L r E) f e :=
  PairRouting.tupleProbability_symmetric _ (modifiedReverseEquiv L r)
    (modifiedPerm_reverse L r E) e f

end CubeShuffle

end OAI
