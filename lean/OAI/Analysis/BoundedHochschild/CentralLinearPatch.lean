import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.BoundedHochschild.TypeIICorners
import OAI.Analysis.BoundedHochschild.CenterPowers

namespace OAI

/-! Central spectral cuts and simultaneous linear norm control. -/

noncomputable section

open scoped ComplexOrder
namespace HochschildCentralQuantization
open BoundedHochschild HochschildSakai HochschildRigidity FinitePathMain HochschildMatrixSystems
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
variable {I : Type v} [Fintype I]

include e hτ htr hfaith in
lemma exists_central_norm_cut (h1 : τ 1=1) (b : I → M)
    (hb : ∀ i x, Commute (b i) x) {ε : ℝ} (hε : 0<ε)
    (hs : (∑ i, ‖τ.toPreGNS (b i)‖^2)<ε^2) :
    ∃ c : M, IsStarProjection c ∧ c ≠ 0 ∧ (∀ x : M, Commute c x) ∧
      ∀ i, ‖c*b i‖≤ε := by
  classical
  let a : M := (ε^2) • (1:M) - ∑ i, star (b i)*b i
  have ha : IsSelfAdjoint a := by
    apply IsSelfAdjoint.sub
    · exact (IsSelfAdjoint.all (ε^2)).smul (IsSelfAdjoint.one M)
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg (fun i _ => star_mul_self_nonneg _))
  have hac : ∀ x : M, Commute a x := by
    intro x
    apply Commute.sub_left
    · exact (Commute.one_left x).smul_left (ε^2)
    · exact Commute.sum_left Finset.univ _ x (fun i _ =>
        (central_star (hb i) x).mul_left (hb i x))
  have hat : 0<(τ a).re := by
    have hh : τ ((ε^2) • (1:M))=((ε^2:ℝ):ℂ) := by
      rw [← Complex.coe_smul,map_smul,h1,smul_eq_mul,mul_one]
    dsimp only [a]
    rw [map_sub,Complex.sub_re,hh,map_sum,Complex.re_sum]
    simp only [trace_star_mul_self_re,Complex.ofReal_re]
    linarith
  obtain ⟨c,hc,hcz,hca,hca0⟩ := exists_central_positive_cut e τ hτ htr hfaith ha hac hat
  have hc0 : c≠0 := by intro hz; apply hca0; rw [hz,zero_mul]
  have hid (i : I) : star (c*b i)*(c*b i)=c*(star (b i)*b i) := by
    rw [star_mul,hc.isSelfAdjoint.star_eq]
    calc
      _ = star (b i)*(c*c)*b i := by simp only [mul_assoc]
      _ = c*(star (b i)*b i) := by
        rw [hc.isIdempotentElem.eq,← (hcz (star (b i))).eq,mul_assoc]
  have hsum : (∑ i,star (c*b i)*(c*b i))≤(ε^2) • c := by
    apply sub_nonneg.mp
    convert hca using 1
    dsimp [a]
    simp only [mul_sub,mul_smul_comm,mul_one,Finset.mul_sum,hid]
  refine ⟨c,hc,hc0,hcz,fun i => ?_⟩
  have hi : star (c*b i)*(c*b i) ≤ (ε^2) • (1:M) := by
    calc
      _ ≤ ∑ j,star (c*b j)*(c*b j) := Finset.single_le_sum
        (fun j _ => star_mul_self_nonneg _) (Finset.mem_univ i)
      _ ≤ (ε^2) • c := hsum
      _ ≤ (ε^2) • (1:M) := smul_le_smul_of_nonneg_left hc.le_one (sq_nonneg ε)
  have hn : ‖star (c*b i)*(c*b i)‖≤ε^2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg ε)
      (star_mul_self_nonneg _)).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using hi
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (c*b i)]

include e hτ htr hfaith in
theorem exists_unitary_central_linear_patch (h1 : τ 1=1) (hII : TypeII1 M)
    (a : I → M) (k : I → ℤ) (hk : ∀ i, k i ≠ 0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : unitary M, ∃ c : M, IsStarProjection c ∧ c ≠ 0 ∧
      (∀ x : M, Commute c x) ∧ ∀ i,
      ‖c*centerExpectation e τ hτ htr hfaith (a i*(u^(k i) : unitary M) : M)‖≤ε := by
  classical
  let K : ℝ := Fintype.card I+1
  have hK : 0<K := by dsimp [K]; positivity
  obtain ⟨u,hu⟩ := exists_unitary_center_weak_powers e τ hτ h1 htr hfaith hII a k hk
    (div_pos hε hK)
  let b : I → M := fun i => centerExpectation e τ hτ htr hfaith
    (a i*(u^(k i) : unitary M) : M)
  have hb (i : I) (x : M) : Commute (b i) x := centerPart_central e τ hτ htr hfaith _ x
  have hs : (∑ i, ‖τ.toPreGNS (b i)‖^2)<ε^2 := by
    have hh : (∑ i, ‖τ.toPreGNS (b i)‖^2)≤(Fintype.card I:ℝ)*(ε/K)^2 := by
      calc
        _ ≤ ∑ _i : I,(ε/K)^2 := Finset.sum_le_sum (fun i _ =>
          le_of_lt ((sq_lt_sq₀ (norm_nonneg _) (div_pos hε hK).le).mpr (hu i)))
        _ = _ := by simp
    have hcast : (0:ℝ)≤Fintype.card I := by positivity
    have hlt : (Fintype.card I:ℝ)<K^2 := by dsimp [K]; nlinarith
    have hpos : 0<(ε/K)^2 := sq_pos_of_pos (div_pos hε hK)
    have he : K^2*(ε/K)^2=ε^2 := by field_simp
    exact hh.trans_lt (by nlinarith [mul_lt_mul_of_pos_right hlt hpos])
  obtain ⟨c,hc,hc0,hcz,hcb⟩ := exists_central_norm_cut e τ hτ htr hfaith h1 b hb hε hs
  exact ⟨u,c,hc,hc0,hcz,hcb⟩

end HochschildCentralQuantization

end

end OAI
