import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import OAI.Analysis.FactorGeneration.WordCorrelation

namespace OAI

noncomputable section

namespace Generator

/-! Exact 2 ell signed coefficients in each formal row. In particular the
identity prefix label is still a nonidentity basis letter in the formal group. -/
section
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators InnerProductSpace
open FreeConvolution

theorem pairLabel_right_injective {ell : ℕ} (k : Fin ell) :
    Function.Injective (pairLabel k) := by
  intro i j hij
  have h := congrArg Subtype.val hij
  change freePrefix (k.val+1)*(freePrefix (i.val+1))⁻¹=
    freePrefix (k.val+1)*(freePrefix (j.val+1))⁻¹ at h
  have he := freePrefix_injective (inv_injective (mul_left_cancel h))
  exact Fin.ext (Nat.add_right_cancel he)

def rowSignedWord {ell : ℕ} (k : Fin ell) (a : Fin ell × Bool) :
    FreeGroup (PrefixLabel ell) := letter (pairLabel k a.1,a.2)

theorem rowSignedWord_injective {ell : ℕ} (k : Fin ell) :
    Function.Injective (rowSignedWord k) := by
  intro a b hab
  have h := letter_injective hab
  exact Prod.ext (pairLabel_right_injective k (congrArg Prod.fst h)) (congrArg (fun x : PrefixLabel ell × Bool => x.2) h)

theorem finitePerturbationRow_signed {ell : ℕ} (α : ℝ) (k : Fin ell) :
    finitePerturbationRow α k=
      ∑ a : Fin ell × Bool, (if a.2 then ((α/(2*ell) : ℝ) : ℂ) else -((α/(2*ell) : ℝ) : ℂ)) •
        MonoidAlgebra.single (rowSignedWord k a) 1 := by
  rw [finitePerturbationRow,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,rowSignedWord,letter_true,letter_false,
    Bool.false_eq_true,ite_false,ite_true,neg_smul,← sub_eq_add_neg,← smul_sub,← Finset.smul_sum]
  exact (IsScalarTower.algebraMap_smul ℂ (α/(2*ell) : ℝ) _).symm

theorem finitePerturbationRow_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ell : ℕ} (α : ℝ) (k : Fin ell)
    (Ψ : MonoidAlgebra ℂ (FreeGroup (PrefixLabel ell)) →ₗ[ℂ] E)
    (hΨ : Orthonormal ℂ (fun g => Ψ (MonoidAlgebra.single g 1))) :
    ‖Ψ (finitePerturbationRow α k)‖^2=2*ell*(α/(2*ell))^2 := by
  have hv : Orthonormal ℂ (fun a => Ψ (MonoidAlgebra.single (rowSignedWord k a) 1)) :=
    hΨ.comp (rowSignedWord k) (rowSignedWord_injective k)
  rw [finitePerturbationRow_signed,map_sum]
  simp only [map_smul]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),hv.inner_sum,map_sum]
  calc
    _ = ∑ a : Fin ell × Bool, ‖(if a.2 then ((α/(2*ell) : ℝ) : ℂ)
        else -((α/(2*ell) : ℝ) : ℂ))‖^2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [mul_comm]
      exact inner_self_eq_norm_sq (𝕜 := ℂ)
        (if a.2 then ((α/(2*ell) : ℝ) : ℂ) else -((α/(2*ell) : ℝ) : ℂ))
    _ = _ := by
      simp only [Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,
        norm_neg,Complex.norm_real,Real.norm_eq_abs,sq_abs,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul]
      ring

end

/-! Exact trace-two-norm of the single common logarithmic perturbation. -/
namespace Tracial

section
attribute [local instance] Classical.propDecidable Classical.decEq
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

theorem quotient_norm_unitary_mul (g : unitary (Q τ ω)) (a : Q τ ω) :
    ‖(g : Q τ ω)*a‖=‖a‖ := by
  rw [← quotient_norm_star,star_mul,quotient_norm_mul_unitary τ ω _ (star (g : Q τ ω)),
    quotient_norm_star]
  simpa only [star_star] using g.property.1

theorem SuccessiveCoordinateHaar.commonPerturbation_norm_sq
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) :
    ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖^2=
      2*ell*(α/(2*ell))^2 := by
  let k : Fin ell := ⟨0,hell⟩
  let Ψ := (sequenceInclusion τ ω).toLinearMap.comp (F.perturbationMap τ ω u z ell).toLinearMap
  have ho := coordinateGroupRing_orthonormal τ ω _ _ (F.coordinateConjugates_quotient τ ω u z ell)
    (F.conjugate_trace τ ω _ _ hu hz ell)
  have hr := finitePerturbationRow_norm_sq α k Ψ ho
  have hn : ‖Ψ (finitePerturbationRow α k)‖=
      ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖ := by
    change ‖sequenceInclusion τ ω (F.perturbationMap τ ω u z ell (finitePerturbationRow α k))‖=_
    rw [sequenceInclusion_apply,LinearIsometry.norm_map,F.perturbationMap_row,map_mul,map_mul,map_star]
    let g := sequenceUnitaryQuotient τ ω (F.coordinatePrefix τ ω u (k.val+1))
    change ‖(g : Q τ ω)*sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)*star (g : Q τ ω)‖=_
    rw [quotient_norm_mul_unitary τ ω _ (star (g : Q τ ω)),quotient_norm_unitary_mul]
    simpa only [star_star] using g.property.1
  rwa [hn] at hr

theorem SuccessiveCoordinateHaar.commonPerturbation_norm
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 ≤ α) :
    ‖sequenceQuotient τ ω (F.commonPerturbation τ ω u z ell α)‖=
      α/Real.sqrt (2*ell) := by
  have hn : (0 : ℝ)<2*ell := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg hα (Real.sqrt_nonneg _))).mp
  rw [F.commonPerturbation_norm_sq τ ω u z hu hz ell hell α]
  simp only [div_pow,Real.sq_sqrt hn.le]
  field_simp [ne_of_gt hn]

end

/-! Sharp trace-two-norm displacement of a skew-adjoint exponential, via the
real path t ↦ exp(t K). This proves the scalar-calculus estimate used in the
manuscript without an extra exponential factor. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def traceVectorCLM : M.toStarSubalgebra →L[ℂ] H :=
  ({ toFun := fun a => (a : H →L[ℂ] H) τ.vector
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M.toStarSubalgebra →ₗ[ℂ] H).mkContinuous 1
    (fun a => by
      change τ.norm₂ a ≤ 1*‖a‖
      simpa only [one_mul] using τ.norm₂_le_norm a)

theorem norm₂_exp_sub_one_le (K : M.toStarSubalgebra) (hK : star K = -K) :
    τ.norm₂ (NormedSpace.exp K-1) ≤ τ.norm₂ K := by
  let V := (traceVectorCLM τ).restrictScalars ℝ
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => V (NormedSpace.exp (s • K)))
      (V (NormedSpace.exp (t • K)*K)) t :=
    V.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const K t)
  have hb (t : ℝ) : ‖V (NormedSpace.exp (t • K)*K)‖ ≤ τ.norm₂ K := by
    have hu : NormedSpace.exp (t • K) ∈ unitary M.toStarSubalgebra := by
      apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
      rw [skewAdjoint.mem_iff,star_smul,star_trivial,hK]
      exact smul_neg _ _
    have hn := unitary_norm_le (NormedSpace.exp (t • K)) hu.1
    change τ.norm₂ (NormedSpace.exp (t • K)*K) ≤ _
    calc
      _ ≤ ‖NormedSpace.exp (t • K)‖*τ.norm₂ K := τ.norm₂_mul_le _ _
      _ ≤ 1*τ.norm₂ K := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := one_mul _
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t)
  change ‖V (NormedSpace.exp K-1)‖ ≤ _
  rw [map_sub]
  simpa only [one_smul,zero_smul,NormedSpace.exp_zero] using h

theorem norm₂_exp_mul_sub_le (K : M.toStarSubalgebra) (hK : star K = -K)
    (u : unitary M.toStarSubalgebra) :
    τ.norm₂ (NormedSpace.exp K*(u : M.toStarSubalgebra)-u) ≤ τ.norm₂ K := by
  have he : NormedSpace.exp K*(u : M.toStarSubalgebra)-u=
      (NormedSpace.exp K-1)*(u : M.toStarSubalgebra) := by rw [sub_mul,one_mul]
  rw [he]
  have hn := unitary_norm_le (u : M.toStarSubalgebra) u.property.1
  calc
    _ ≤ τ.norm₂ (NormedSpace.exp K-1)*‖(u : M.toStarSubalgebra)‖ := τ.norm₂_mul_le_right _ _
    _ ≤ τ.norm₂ (NormedSpace.exp K-1)*1 := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ ≤ τ.norm₂ K := by rw [mul_one]; exact norm₂_exp_sub_one_le τ K hK

end

/-! A single coordinate satisfies the size and correlation bounds for the
literal word. Its P-valued unitary letters are the retained construction. -/
section
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable {hNM : N ≤ M} {seed : Set (Q τ ω)}

def unitaryCoordinate (a : unitary (Sequences M)) (n : ℕ) : unitary M.toStarSubalgebra :=
  ⟨(a : Sequences M) n,⟨congrArg (fun b : Sequences M => b n) a.property.1,
    congrArg (fun b : Sequences M => b n) a.property.2⟩⟩

def SuccessiveCoordinateHaar.retainedUnitary (F : SuccessiveCoordinateHaar τ ω hNM seed)
    (j n : ℕ) : unitary N.toStarSubalgebra :=
  ⟨(F.step j).coordinates.val n,(F.step j).unitary_coordinates n⟩

theorem SuccessiveCoordinateHaar.perturbedUnitary_apply
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    (F.perturbedUnitary τ ω u z ell α : Sequences M) n=
      NormedSpace.exp (F.commonPerturbation τ ω u z ell α n)*(u : M.toStarSubalgebra) := by
  change (NormedSpace.exp (F.commonPerturbation τ ω u z ell α)) n*(u : M.toStarSubalgebra)=_
  rw [sequence_exp_apply]

theorem SuccessiveCoordinateHaar.perturbedUnitary_distance
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    τ.norm₂ ((F.perturbedUnitary τ ω u z ell α : Sequences M) n-u) ≤
      τ.norm₂ (F.commonPerturbation τ ω u z ell α n) := by
  rw [F.perturbedUnitary_apply]
  exact norm₂_exp_mul_sub_le τ _
    (congrArg (fun a : Sequences M => a n) (F.commonPerturbation_skew τ ω u z ell α)) u

theorem SuccessiveCoordinateHaar.perturbedWord_apply
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (ell : ℕ) (α : ℝ) (n : ℕ) :
    (F.perturbedWord τ ω u z ell α : Sequences M) n=
      coordinateInclusion hNM (F.retainedUnitary τ ω 0 n : N.toStarSubalgebra)*
        ((List.range ell).map (fun j =>
          (F.perturbedUnitary τ ω u z ell α : Sequences M) n*
            coordinateInclusion hNM (F.retainedUnitary τ ω (j+1) n : N.toStarSubalgebra))).prod := by
  change sequenceEval n (F.perturbedWord τ ω u z ell α : Sequences M)=_
  simp only [perturbedWord,Submonoid.coe_mul,Submonoid.coe_list_prod,map_mul,map_list_prod,
    List.map_map,Function.comp_def]
  change (F.haarSequence τ ω 0 : Sequences M) n*
    ((List.range ell).map (fun j => (F.perturbedUnitary τ ω u z ell α : Sequences M) n*
      (F.haarSequence τ ω (j+1) : Sequences M) n)).prod=_
  simp only [F.haarSequence_apply,retainedUnitary]

theorem SuccessiveCoordinateHaar.select_perturbation_coordinate
    (F : SuccessiveCoordinateHaar τ ω hNM seed) (u z : unitary M.toStarSubalgebra)
    (xi : M.toStarSubalgebra)
    (hu : (constantQuotientUnitary τ ω u : Q τ ω) ∈ seed)
    (hz : (constantQuotientUnitary τ ω z : Q τ ω) ∈ seed) (hxi : constantQuotient τ ω xi ∈ seed)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ∃ n : ℕ,
      τ.norm₂ ((F.perturbedUnitary τ ω u z ell α : Sequences M) n-u) <
        α/Real.sqrt (2*ell)+1/(ell : ℝ) ∧
      ‖τ.trace (star xi*(F.perturbedWord τ ω u z ell α : Sequences M) n)-
        (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ <
          τ.norm₂ xi*(4*α^2/(1-2*α))+1/(ell : ℝ) := by
  have hε : (0 : ℝ)<1/(ell : ℝ) := by positivity
  have hc := F.perturbedWord_correlation τ ω u z (constantQuotient τ ω xi) hu hz hxi ell hell α hα hhalf
  have hb : ‖inner ℂ (sequenceInclusion τ ω (constantSequence xi))
      (sequenceInclusion τ ω (F.perturbedWord τ ω u z ell α : Sequences M))-
      (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ ≤ τ.norm₂ xi*(4*α^2/(1-2*α)) := by
    have ht : quotientTrace τ ω (star (constantQuotient τ ω xi)*
        (constantQuotientUnitary τ ω z : Q τ ω))=τ.trace (star xi*(z : M.toStarSubalgebra)) := by
      change quotientTrace τ ω (star (constantQuotient τ ω xi)*
        constantQuotient τ ω (z : M.toStarSubalgebra))=_
      rw [← map_star,← map_mul,constantQuotient_trace]
    rw [ht,constantQuotient_norm] at hc
    rw [sequenceInclusion_apply,sequenceInclusion_apply,inclusion_inner]
    exact hc
  obtain ⟨n,hn,ht⟩ := select_coordinate_with_bounds τ ω
    (F.commonPerturbation τ ω u z ell α) (constantSequence xi)
    (F.perturbedWord τ ω u z ell α : Sequences M)
    (α/Real.sqrt (2*ell)) (τ.norm₂ xi*(4*α^2/(1-2*α))) (1/(ell : ℝ))
    ((α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))) hε
    (F.commonPerturbation_norm τ ω u z hu hz ell hell α hα.le).le hb
  exact ⟨n,(F.perturbedUnitary_distance τ ω u z ell α n).trans_lt hn,ht⟩

end

/-! The manuscript's two perturbation inequalities, constructed under explicit
faithful vector-trace, irreducibility, diffuseness and trace-vector separability
data. No perturbation endpoint or free-moment premise is assumed. -/
open UltrapowerBridge Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_represented_perturbation (hω : (ω : Filter ℕ) ≤ atTop)
    (u z : unitary M.toStarSubalgebra) (xi : M.toStarSubalgebra)
    (ell : ℕ) (hell : 0 < ell) (α : ℝ) (hα : 0 < α) (hhalf : α < 1/2) :
    ∃ u' : unitary M.toStarSubalgebra, ∃ t : ℕ → unitary N.toStarSubalgebra,
      τ.norm₂ ((u' : M.toStarSubalgebra)-u) ≤ α/Real.sqrt (2*ell)+1/(ell : ℝ) ∧
      ‖τ.trace (star xi*(coordinateInclusion hNM (t 0 : N.toStarSubalgebra)*
        ((List.range ell).map (fun j => (u' : M.toStarSubalgebra)*
          coordinateInclusion hNM (t (j+1) : N.toStarSubalgebra))).prod))-
        (α : ℂ)/2*τ.trace (star xi*(z : M.toStarSubalgebra))‖ ≤
          τ.norm₂ xi*(4*α^2/(1-2*α))+1/(ell : ℝ) := by
  obtain ⟨F⟩ := nonempty_successiveCoordinateHaar τ ω hNM hfactor hdiff hirr hsep hω
    {(constantQuotientUnitary τ ω u : Q τ ω),(constantQuotientUnitary τ ω z : Q τ ω),
      constantQuotient τ ω xi}
    (((Set.countable_singleton (constantQuotient τ ω xi)).insert _).insert _)
  obtain ⟨n,hn,ht⟩ := F.select_perturbation_coordinate τ ω u z xi
    (by simp) (by simp) (by simp) ell hell α hα hhalf
  refine ⟨unitaryCoordinate (F.perturbedUnitary τ ω u z ell α) n,
    (fun j => F.retainedUnitary τ ω j n),hn.le,?_⟩
  have he := F.perturbedWord_apply τ ω u z ell α n
  simpa only [unitaryCoordinate,he] using ht.le

end Tracial

end Generator

end

end OAI
