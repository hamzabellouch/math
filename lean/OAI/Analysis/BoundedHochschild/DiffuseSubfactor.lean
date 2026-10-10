import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.WitnessClosure

namespace OAI

/-! Countably generated diffuse subfactors obtained from matrix witnesses and small projections. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildLocalization
open BoundedHochschild HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem exists_countable_matrix_witnesses
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (D : Set M) (hD : D.Countable) :
    ∃ S : Set M, S.Countable ∧ D ⊆ S ∧ wordSet S ⊆ S ∧
      ∀ a ∈ S, ∀ k : ℕ, ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧
        (∀ i j, E.entry i j ∈ S) ∧
        ‖τ.toPreGNS (E.expectation (a-(τ a) • (1:M)))‖ < 1/((k:ℝ)+1) := by
  classical
  have hchoice (a : M) (k : ℕ) : ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧
      ‖τ.toPreGNS (E.expectation (a-(τ a) • (1:M)))‖ < 1/((k:ℝ)+1) := by
    obtain ⟨n,E,hn,hE⟩ := HochschildQuantization.exists_small_matrix_expectations e τ
      hτ h1 htr hfaith hfactor hdiff (fun _ : Unit => a-(τ a) • (1:M))
      (by intro i; simp [map_sub,map_smul,h1])
      (show 0 < (1:ℝ)/((k:ℝ)+1) by positivity)
    exact ⟨n,E,hn,hE ()⟩
  choose n E hn hE using hchoice
  let W (a : M) (k : ℕ) : Set M := Set.range (fun ij : Fin (n a k) × Fin (n a k) => (E a k).entry ij.1 ij.2)
  obtain ⟨S,hS,hDS,hword,hW⟩ := exists_countable_witness_closure D hD W (fun _ _ => Set.countable_range _)
  refine ⟨S,hS,hDS,hword,?_⟩
  intro a ha k
  refine ⟨n a k,E a k,hn a k,?_,hE a k⟩
  intro i j
  exact hW a ha k ⟨⟨i,j⟩,rfl⟩

end HochschildLocalization

open Filter Topology
open scoped ComplexOrder
namespace HochschildLocalization
open BoundedHochschild HochschildMatrixSystems HochschildPatching
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

theorem weakClosure_factor_of_matrix_witnesses
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (S : Set M) (hword : wordSet S ⊆ S)
    (hmat : ∀ a ∈ S, ∀ k : ℕ, ∃ (n : ℕ) (E : MatrixSystem M n), 0<n ∧
      (∀ i j, E.entry i j ∈ S) ∧
      ‖τ.toPreGNS (E.expectation (a-(τ a) • (1:M)))‖ < 1/((k:ℝ)+1)) :
    ∀ x : WeakAlgebra.closure e (StarAlgebra.adjoin ℂ S) hL hR P hP,
      (∀ b, Commute x b) → ∃ c : ℂ, x=c • 1 := by
  let A := StarAlgebra.adjoin ℂ S
  let N := WeakAlgebra.closure e A hL hR P hP
  intro x hx
  let yN : N := x-(τ (x:M)) • 1
  let y : M := yN
  have hy : τ y=0 := by simp [y,yN,map_sub,map_smul,h1]
  have hys : τ (star y)=0 := by simp only [map_star,hy,star_zero]
  have hc (b : N) : Commute (star yN) b := by
    have hh := congrArg star (hx (star b)).eq
    change _=_
    dsimp [yN]
    simpa only [star_mul,star_star,star_sub,star_smul,star_one,sub_mul,mul_sub,
      smul_mul_assoc,mul_smul_comm,one_mul,mul_one] using congrArg (fun z : N => z-(star (τ (x:M))) • b) hh.symm
  have hmem (a : M) (ha : a ∈ S) : a ∈ N :=
    WeakAlgebra.mem_linearClosure e A (StarAlgebra.subset_adjoin ℂ S ha)
  have hgen (a : M) (ha : a ∈ S) : τ (star y*a)=0 := by
    have hid : τ (star y*a)=τ ((a-(τ a) • (1:M))*star y) := by
      rw [htr]
      simp only [sub_mul,smul_mul_assoc,one_mul,map_sub,map_smul,hys,smul_zero,sub_zero]
    have hbound (k : ℕ) : ‖τ (star y*a)‖ ≤ (1/((k:ℝ)+1))*‖τ.toPreGNS (star y)‖ := by
      obtain ⟨n,E,hn,he,hsmall⟩ := hmat a ha k
      have hfix : E.expectation (star y)=star y := by
        apply E.expectation_eq_self (Nat.ne_of_gt hn)
        intro i j
        exact congrArg Subtype.val (hc ⟨E.entry i j,hmem _ (he i j)⟩).eq
      rw [hid,← hfix,← E.trace_adjoint τ htr,hfix]
      exact (norm_trace_mul_le_gns τ htr _ _).trans
        (mul_le_mul_of_nonneg_right hsmall.le (norm_nonneg _))
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖τ.toPreGNS (star y)‖
    exact ge_of_tendsto' (by simpa using ht) hbound
  have hA (a : M) (ha : a ∈ A) : τ (star y*a)=0 := by
    have hm : a ∈ Submodule.span ℂ (wordSet S) := by
      dsimp only [wordSet]
      rw [← StarAlgebra.adjoin_eq_span]
      exact ha
    clear ha
    induction hm using Submodule.span_induction with
    | mem a ha => exact hgen a (hword ha)
    | zero => simp
    | add a b _ _ ha hb => simp only [mul_add,map_add,ha,hb,add_zero]
    | smul c a _ ha => simp only [mul_smul_comm,map_smul,ha,smul_zero]
  have heval : ∀ f ∈ WeakAlgebra.linearClosure e A, f (traceVector e τ hL hτ y)=0 := by
    apply closure_minimal _ (isClosed_eq (WeakDual.eval_continuous (𝕜 := ℂ) _) continuous_const)
    rintro f ⟨a,ha,rfl⟩
    change e.symm a (traceVector e τ hL hτ y)=0
    rw [traceVector_spec,hA a ha,star_zero]
  have hyzero : y=0 := by
    apply hfaith
    apply star_eq_zero.mp
    rw [← traceVector_spec e τ hL hτ y y]
    exact heval ((WeakAlgebra.weakEquiv e).symm y) yN.property
  refine ⟨τ (x:M),?_⟩
  apply Subtype.ext
  exact sub_eq_zero.mp hyzero

end HochschildLocalization

open scoped ComplexOrder
namespace HochschildLocalization
open BoundedHochschild HochschildComparison HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem diffuse_of_small_projections
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hsmall : ∀ ε : ℝ, 0<ε → ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ (τ q).re<ε) :
    NoMinimalProjections M := by
  intro p hp hp0
  obtain ⟨q,hq,hq0,hqt⟩ := hsmall (τ p).re (projection_trace_pos τ hfaith hp hp0)
  obtain ⟨a,ha⟩ := exists_nonzero_corner e τ (HochschildSakai.mul_hasPreadjoint e)
    hτ htr hfaith h1 hfactor hp hq hp0 hq0
  obtain ⟨v,hv,hi,hf⟩ := partialIso_of_nonzero_corner e hp hq (p*a*q) ha
    (by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq])
    (by rw [mul_assoc,hq.isIdempotentElem.eq])
  refine ⟨v.final,v.final_proj,hf,?_,?_⟩
  · intro hz
    apply hv
    apply hfaith
    rw [htr]
    change τ v.final=0
    rw [hz,map_zero]
  · intro hz
    have hle : (τ v.initial).re ≤ (τ q).re := Complex.re_le_re (τ.monotone hi)
    have ht : τ v.final=τ v.initial := htr _ _
    rw [hz] at ht
    rw [← ht] at hle
    linarith

theorem exists_small_projection_sequence
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hdiff : NoMinimalProjections M) :
    ∃ q : ℕ → M, (∀ k, IsStarProjection (q k)) ∧ (∀ k, q k ≠ 0) ∧
      ∀ k, (τ (q k)).re=1/((k:ℝ)+1) := by
  have hex (k : ℕ) : ∃ q : M, IsStarProjection q ∧ q ≤ 1 ∧ (τ q).re=1/((k:ℝ)+1) := by
    apply exists_projection_of_trace τ e (HochschildSakai.mul_hasPreadjoint e)
      hτ htr hfaith hdiff (IsStarProjection.one M) _ (by positivity)
    rw [h1,Complex.one_re]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  choose q hq hq1 ht using hex
  refine ⟨q,hq,?_,ht⟩
  intro k hz
  have hp : 0 < (1:ℝ)/((k:ℝ)+1) := by positivity
  have hh := ht k
  rw [hz,map_zero,Complex.zero_re] at hh
  linarith

end HochschildLocalization

open Filter Topology
open scoped ComplexOrder
namespace HochschildLocalization
open BoundedHochschild HochschildMatrixSystems HochschildPatching
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ a : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M a))
  (hR : ∀ a : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip a))
  (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

theorem exists_countably_generated_diffuse_subfactor
    (hτ : TraceInPredual e τ) (h1 : τ 1=1)
    (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfactor : ∀ a : M, (∀ x : M, Commute a x) → ∃ c : ℂ, a=c • (1 : M))
    (hdiff : HochschildDiffuse.NoMinimalProjections M)
    (D : Set M) (hD : D.Countable) :
    ∃ S : Set M, S.Countable ∧ D ⊆ S ∧
      (∀ x : WeakAlgebra.closure e (StarAlgebra.adjoin ℂ S) hL hR P hP,
        (∀ b, Commute x b) → ∃ c : ℂ, x=c • 1) ∧
      HochschildDiffuse.NoMinimalProjections
        (WeakAlgebra.closure e (StarAlgebra.adjoin ℂ S) hL hR P hP) := by
  classical
  obtain ⟨q,hq,hq0,hqt⟩ := exists_small_projection_sequence e τ hτ h1 htr hfaith hdiff
  obtain ⟨S,hS,hDS,hword,hmat⟩ := exists_countable_matrix_witnesses e τ hτ h1 htr hfaith
    hfactor hdiff (D ∪ Set.range q) (hD.union (Set.countable_range _))
  have hfN := weakClosure_factor_of_matrix_witnesses e τ hL hR P hP hτ h1 htr hfaith S hword hmat
  refine ⟨S,hS,fun a ha => hDS (Or.inl ha),hfN,?_⟩
  let A := StarAlgebra.adjoin ℂ S
  let N := WeakAlgebra.closure e A hL hR P hP
  let Y := X ⧸ WeakSubspace.preannihilator (WeakAlgebra.linearClosure e A)
  let eN : StrongDual ℂ Y ≃ₗᵢ⋆[ℂ] N := WeakAlgebra.predualEquiv e A hL hR P hP
  let τN : N →ₚ[ℂ] ℂ := WeakAlgebra.inheritedTrace e τ A hL hR P hP
  have hτN := WeakAlgebra.inheritedTrace_normal e τ A hL hR P hP hτ
  have htrN := WeakAlgebra.inheritedTrace_tracial e τ A hL hR P hP htr
  have hfaithN := WeakAlgebra.inheritedTrace_faithful e τ A hL hR P hP hfaith
  apply diffuse_of_small_projections eN τN hτN h1 htrN hfaithN hfN
  intro ε hε
  obtain ⟨k,hk⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)).exists
  have hmem : q k ∈ N := WeakAlgebra.mem_linearClosure e A
    (StarAlgebra.subset_adjoin ℂ S (hDS (Or.inr ⟨k,rfl⟩)))
  refine ⟨⟨q k,hmem⟩,⟨Subtype.ext (hq k).isIdempotentElem.eq,
    Subtype.ext (hq k).isSelfAdjoint.star_eq⟩,?_,?_⟩
  · intro hz
    exact hq0 k (congrArg Subtype.val hz)
  · change (τ (q k)).re<ε
    rwa [hqt]

end HochschildLocalization

end

end OAI
