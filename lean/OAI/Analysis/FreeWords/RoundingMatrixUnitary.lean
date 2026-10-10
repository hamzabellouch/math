import Mathlib
import OAI.Analysis.FreeWords.PartitionRefine
import OAI.Analysis.FreeWords.UnitaryFiniteSpectrum

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFreeLiftFrontier KKSpectralSupport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem projection_mul_sum_self {ι A : Type*} [Fintype ι] [Ring A] [StarRing A]
    (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (i : ι) : p i*(∑ j, p j)=p i := by
  classical
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [hp i |>.isIdempotentElem.eq]
  · intro j hj hji; exact ho i j (Ne.symm hji)
  · simp

theorem option_complement_partition {ι A : Type*} [Fintype ι] [Ring A] [StarRing A]
    (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (s : A) (hs : IsStarProjection s)
    (he : s=1-∑ i, p i) :
    (∀ i, IsStarProjection (Option.elim i s p)) ∧
    (∀ i j : Option ι, i≠j → Option.elim i s p*Option.elim j s p=0) ∧
    (∑ i : Option ι, Option.elim i s p)=1 := by
  classical
  have hps (i : ι) : p i*s=0 := by
    rw [he,mul_sub,mul_one,projection_mul_sum_self p hp ho,sub_self]
  have hsp (i : ι) : s*p i=0 := by
    simpa only [star_mul,hs.isSelfAdjoint.star_eq,(hp i).isSelfAdjoint.star_eq,star_zero]
      using congrArg star (hps i)
  refine ⟨?_,?_,?_⟩
  · intro i; cases i with
    | none => exact hs
    | some i => exact hp i
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hsp j
    | some i =>
      cases j with
      | none => exact hps i
      | some j => exact ho i j (fun h => hij (congrArg some h))
  · rw [Fintype.sum_option]
    simpa only [Option.elim_none,Option.elim_some,he] using sub_add_cancel (1:A) (∑ i, p i)

theorem weighted_partition_mul_subprojection {ι : Type*} [Fintype ι]
    {M : VonNeumannAlgebra H} (p : ι → ConcreteAlgebra M)
    (hp : ∀ i, IsStarProjection (p i)) (ho : ∀ i j, i≠j → p i*p j=0)
    (c : ι → ℂ) (i : ι) (q : ConcreteAlgebra M) (hq : IsStarProjection q)
    (hle : q ≤ p i) : (∑ j, c j • p j)*q=c i • q := by
  classical
  rw [Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_assoc,(hq.le_iff_mul_eq_right (hp i)).mp hle]
  · intro j hj hji
    rw [smul_mul_assoc]
    have he : p j*q=0 := by
      calc
        p j*q = p j*(p i*q) := by rw [(hq.le_iff_mul_eq_right (hp i)).mp hle]
        _ = (p j*p i)*q := (mul_assoc _ _ _).symm
        _ = 0 := by rw [ho j i hji,zero_mul]
    rw [he,smul_zero]
  · simp

theorem rounded_unitary_matrix {ι : Type*} [Fintype ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hF : IsFactor M) (hD : IsDiffuse M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (ho : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (c : ι → ℂ) (hc : ∀ i, ‖c i‖=1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (_hn : 0 < n)
      (ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M)
      (v : unitary (Matrix (Fin n) (Fin n) ℂ)),
      Function.Injective ρ ∧ traceNorm τ ((∑ i, c i • p i)-ρ v.val) < ε := by
  classical
  let : Nontrivial (ConcreteAlgebra M) := ⟨⟨0,1,fun h => by
    have ht := congrArg τ.map h
    rw [map_zero,τ.normalized] at ht
    exact zero_ne_one ht⟩⟩
  obtain ⟨n,hn,k,r,q,s,hkr,hq,hqp,hqo,hτq,hs,hseq,hτs,hsmall⟩ :=
    round_projection_partition M τ hD p hp ho h1 (ε^2/4) (by positivity)
  let p' : Option ι → ConcreteAlgebra M := fun i => Option.elim i s q
  let k' : Option ι → ℕ := fun i => Option.elim i r k
  let c' : Option ι → ℂ := fun i => Option.elim i 1 c
  obtain ⟨hp',ho',h1'⟩ := option_complement_partition q hq hqo s hs hseq
  have hτ' (i : Option ι) : τ.map (p' i)=(k' i:ℂ)*(((n:ℝ)⁻¹:ℝ):ℂ) := by
    simp only [Complex.ofReal_inv,Complex.ofReal_natCast]
    cases i with
    | none => exact hτs
    | some i => exact hτq i
  obtain ⟨e,he,heo,he1,heτ,hes⟩ := refine_projection_partition M τ hD p' hp' ho' h1'
    k' (n:ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) hτ'
  have hc' (i : Option ι) : ‖c' i‖=1 := by
    cases i with
    | none => exact norm_one
    | some i => exact hc i
  obtain ⟨m,hm,ρ,v,hρ,hv⟩ := unitary_of_equal_partition M τ hF e he heo he1
    (fun i j => (heτ i).trans (heτ j).symm) (fun i => c' i.1) (fun i => hc' i.1)
  have hv' : ρ v.val=s+∑ i, c i • q i := by
    rw [hv,Fintype.sum_sigma]
    simp only [← Finset.smul_sum,hes]
    rw [Fintype.sum_option]
    simp only [c',p',Option.elim_none,Option.elim_some,one_smul]
  let w := ∑ i, c i • p i
  have hw : w ∈ unitary _ := phase_partition_unitary p hp ho h1 c hc
  have hnw : ‖w‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul (⟨w,hw⟩ : unitary _) (1 : ConcreteAlgebra M)
    simpa only [mul_one,norm_one] using h.le
  have hws : w*s=w-∑ i, c i • q i := by
    rw [hseq,mul_sub,mul_one,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact weighted_partition_mul_subprojection p hp ho c i (q i) (hq i) (hqp i)
  have herr : w-ρ v.val=(w-1)*s := by
    rw [hv',sub_mul,one_mul,hws]
    abel
  have hns : 0 ≤ traceNorm τ s := traceNorm_nonneg τ s
  have hsq : (traceNorm τ s)^2 < ε^2/4 := by
    rw [traceNorm_projection_sq τ hs]
    exact hsmall
  have hlt : 2*traceNorm τ s < ε := by nlinarith
  refine ⟨m,hm,ρ,v,hρ,?_⟩
  change traceNorm τ (w-ρ v.val) < ε
  rw [herr]
  calc
    traceNorm τ ((w-1)*s) ≤ ‖w-1‖*traceNorm τ s := traceNorm_mul_le τ _ _
    _ ≤ 2*traceNorm τ s := mul_le_mul_of_nonneg_right
      ((norm_sub_le _ _).trans (by rw [norm_one]; linarith)) hns
    _ < ε := hlt

end

end KKProjectionSupport
end

end OAI
