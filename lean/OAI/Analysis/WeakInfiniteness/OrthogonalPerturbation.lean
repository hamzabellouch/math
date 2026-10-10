import Mathlib
import OAI.Analysis.WeakInfiniteness.UniformPerturbation

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma norm_selfadjoint_of_square_zero (x : A) (hx : x*x=0) :
    ‖x+star x‖=‖x‖ := by
  have hxs : star x*star x=0 := by
    simpa only [star_mul,star_zero] using congrArg star hx
  have hsa : IsSelfAdjoint (x+star x) := by
    show star (x+star x)=x+star x
    rw [star_add,star_star,add_comm]
  have horth : (star x*x)*(x*star x)=0 := by
    calc
      (star x*x)*(x*star x)=star x*(x*x)*star x := by noncomm_ring
      _ = 0 := by rw [hx,mul_zero,zero_mul]
  have hsum : (x+star x)*(x+star x)=star x*x+x*star x := by
    noncomm_ring [hx,hxs]
  have hn := (CStarRing.norm_star_mul_self (x := x+star x))
  rw [hsa.star_eq] at hn
  rw [hsum] at hn
  rw [(IsSelfAdjoint.star_mul_self x).norm_add_eq_max
    (IsSelfAdjoint.mul_star_self x) horth] at hn
  rw [CStarRing.norm_star_mul_self,CStarRing.norm_self_mul_star,max_self] at hn
  nlinarith [norm_nonneg (x+star x),norm_nonneg x]

lemma isSelfAdjoint_add_star (x : A) : IsSelfAdjoint (x+star x) := by
  show star (x+star x)=x+star x
  rw [star_add,star_star,add_comm]

variable [PartialOrder A] [StarOrderedRing A]

lemma orthogonal_selfadjoint_test (p q y : A) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hpq : p*q=0) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1) (hyn : ‖y‖ ≤ 1) :
    ‖p*y*q+star (p*y*q)‖ ≤ 1 ∧
      p*(p*y*q+star (p*y*q))*q=(p*p)*y*(q*q) := by
  have hqp : q*p=0 := by
    simpa only [star_mul,hp.star_eq,hq.star_eq,star_zero] using congrArg star hpq
  have hz : (p*y*q)*(p*y*q)=0 := by
    calc
      (p*y*q)*(p*y*q)=p*y*(q*p)*y*q := by noncomm_ring
      _ = 0 := by rw [hqp,mul_zero,zero_mul,zero_mul]
  constructor
  · rw [norm_selfadjoint_of_square_zero _ hz]
    calc
      ‖p*y*q‖ ≤ (‖p‖*‖y‖)*‖q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*1)*1 := by gcongr
      _ = 1 := by norm_num
  · have hc : p*star (p*y*q)*q=0 := by
      rw [star_mul,star_mul,hp.star_eq,hq.star_eq]
      calc
        p*(q*(star y*p))*q=(p*q)*star y*(p*q) := by noncomm_ring
        _ = 0 := by rw [hpq,zero_mul,zero_mul]
    rw [mul_add,add_mul,hc,add_zero]
    noncomm_ring

variable {A : Type 1} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfadjoint_uniform_perturbation_of_gap_one
    {γ σ : ℝ} (hσ : 0 ≤ σ) (hσγ : 2*σ ≤ γ)
    (hgap : ∀ (B : Type 1) [CStarAlgebra B] (v : B), ‖v‖ ≤ 1 → Exact B →
      ¬ FiniteContractionModels B v γ)
    (hA : Exact A) {n : ℕ} (hn : 1 ≤ n)
    (hpi : ∀ a : A, 0 ≤ a → a ≠ 0 → ProperlyInfinite (diagonalCopies n a))
    (p q h k c : A) (hpn : ‖p‖ ≤ 1) (hqn : ‖q‖ ≤ 1)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p*q=0)
    (hh : 0 ≤ h) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hph : star p*p*h=h) (hqk : q*star q*k=k)
    (hch : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 h))
    (hck : CuntzSubequiv (diagonalCopies n c) (diagonalCopies 1 k))
    (T : A) {η α : ℝ} (hη : 0 < η) (hα : 0 < α) :
    ∃ y : A, ‖y‖ ≤ 1 ∧ IsSelfAdjoint y ∧
      (∃ z : A, y=p*z*q+star (p*z*q)) ∧
      ∀ (H : ComplexHilbert.{1}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
        α ≤ ‖π c‖ → σ*η ≤ ‖π (T+(η : ℂ) • (p*y*q))‖ := by
  have hpp : p*p*h=h := by simpa only [hp.star_eq] using hph
  have hqq : q*q*k=k := by simpa only [hq.star_eq] using hqk
  have hp4 : star (p*p)*(p*p)*h=h := by
    rw [star_mul,hp.star_eq]
    calc
      (p*p)*(p*p)*h=(p*p)*(p*p*h) := by noncomm_ring
      _ = h := by rw [hpp,hpp]
  have hq4 : (q*q)*star (q*q)*k=k := by
    rw [star_mul,hq.star_eq]
    calc
      (q*q)*(q*q)*k=(q*q)*(q*q*k) := by noncomm_ring
      _ = k := by rw [hqq,hqq]
  have hppn : ‖p*p‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg p])
  have hqqn : ‖q*q‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg q])
  obtain ⟨z,hzn,hz⟩ := uniform_perturbation_of_gap_one hσ hσγ hgap hA hn hpi
    (p*p) (q*q) h k c hppn hqqn hh hk hc hp4 hq4 hch hck T hη hα
  have hy := orthogonal_selfadjoint_test p q z hp hq hpq hpn hqn hzn
  refine ⟨p*z*q+star (p*z*q),hy.1,isSelfAdjoint_add_star _,⟨z,rfl⟩,?_⟩
  intro H π hπc
  rw [hy.2]
  exact hz H π hπc

end

end WeakPureInfiniteness
end

end OAI
