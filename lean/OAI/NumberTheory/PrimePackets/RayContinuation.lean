import Mathlib
import OAI.NumberTheory.PrimePackets.RayUnramified

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

 

def IsNonprincipal : Prop :=
  ∃ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥),
    IsCoprime I (rationalModulusIdeal (𝓞 K) N) ∧
      ψ.idealHom (integralIdealFractionalUnit I hI) ≠ 1

lemma conjugate_isNonprincipal (hψ : ψ.IsNonprincipal) : ψ.conjugate.IsNonprincipal := by
  obtain ⟨I,hI,hc,hv⟩ := hψ
  refine ⟨I,hI,hc,?_⟩
  intro H
  apply hv
  apply Units.ext
  have HH := congrArg (fun z : ℂˣ => conj (z : ℂ)) H
  change conj (conj (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)) = conj 1 at HH
  change (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ) = (1 : ℂ)
  simpa only [Complex.conj_conj, map_one] using HH

variable [NeZero N]

lemma classCharacter_ne_one_of_nonprincipal (hψ : ψ.residue = 1)
    (h : ψ.IsNonprincipal) : ψ.classCharacter hψ ≠ 1 := by
  obtain ⟨I,hI,hc,hv⟩ := h
  intro H
  apply hv
  apply Units.ext
  have HE := congrArg (fun χ : ClassGroup (𝓞 K) →* ℂ =>
    χ (ClassGroup.mk K (integralIdealFractionalUnit I hI))) H
  change (ψ.classValue (ClassGroup.mk K (integralIdealFractionalUnit I hI)) : ℂ) = 1 at HE
  rw [ψ.idealHom_eq_classValue hψ I hI hc]
  exact HE

 

def nonprincipalContinued {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) : ℂ → ℂ :=
  if hr : ψ.residue = 1 then ψ.unramifiedContinued σ hn hr else ψ.continued σ

theorem nonprincipalContinued_entire {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1) :
    Differentiable ℂ (ψ.nonprincipalContinued σ hn) := by
  unfold nonprincipalContinued
  split_ifs with hr
  · exact ψ.unramifiedContinued_entire σ hn hr
  · exact ψ.continued_entire σ hn hr

theorem nonprincipalContinued_eq_dirichlet {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.nonprincipalContinued σ hn s = ψ.dirichlet s := by
  unfold nonprincipalContinued
  split_ifs with hr
  · exact ψ.unramifiedContinued_eq_dirichlet σ hn hr
      (ψ.classCharacter_ne_one_of_nonprincipal hr hψ) hs
  · exact ψ.continued_eq_dirichlet σ hn hr hs

lemma nonprincipalContinued_ne_zero_right {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.IsNonprincipal) {s : ℂ} (hs : 1 < s.re) :
    ψ.nonprincipalContinued σ hn s ≠ 0 := by
  rw [ψ.nonprincipalContinued_eq_dirichlet σ hn hψ hs]
  exact ψ.dirichlet_ne_zero hs

lemma nonprincipalContinued_ne_zero {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.IsNonprincipal) : ψ.nonprincipalContinued σ hn ≠ 0 := by
  intro H
  have HB := ψ.nonprincipalContinued_ne_zero_right σ hn hψ (s := 2) (by norm_num)
  exact HB (congrFun H 2)

 

theorem nonprincipalContinued_finite_nonnegative_order {d : ℕ}
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hψ : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.nonprincipalContinued σ hn) β = (m : WithTop ℤ) := by
  have ha : ∀ z, AnalyticAt ℂ (ψ.nonprincipalContinued σ hn) z :=
    fun z => (ψ.nonprincipalContinued_entire σ hn).analyticAt z
  have hfin : analyticOrderAt (ψ.nonprincipalContinued σ hn) β ≠ ⊤ := by
    intro H
    exact ψ.nonprincipalContinued_ne_zero σ hn hψ
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero β ha).mp H)
  obtain ⟨m,hm⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨m, ?_⟩
  rw [(ha β).meromorphicOrderAt_eq, ← hm, ENat.map_natCast]
  rfl

 

theorem nonprincipalContinued_conjugation {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.IsNonprincipal) (s : ℂ) :
    ψ.conjugate.nonprincipalContinued σ hn (conj s) =
      conj (ψ.nonprincipalContinued σ hn s) := by
  have H : Differentiable ℂ (conj ∘ ψ.nonprincipalContinued σ hn ∘ conj) := by
    intro z
    apply differentiableAt_conj_conj_iff.mpr
    exact ψ.nonprincipalContinued_entire σ hn _
  have HE := entire_eq_of_real_eq H
    (ψ.conjugate.nonprincipalContinued_entire σ hn) (fun r hr => by
      simp only [Function.comp_apply, Complex.conj_ofReal]
      rw [ψ.nonprincipalContinued_eq_dirichlet σ hn hψ hr,
        ψ.conjugate.nonprincipalContinued_eq_dirichlet σ hn
          (ψ.conjugate_isNonprincipal hψ) hr, ψ.dirichlet_conj_real])
  have Hs := congrFun HE (conj s)
  simpa using Hs.symm

theorem nonprincipalContinued_order_conjugation {d : ℕ} [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hψ : ψ.IsNonprincipal) (s : ℂ) :
    meromorphicOrderAt (ψ.conjugate.nonprincipalContinued σ hn) (conj s) =
      meromorphicOrderAt (ψ.nonprincipalContinued σ hn) s := by
  have he : ψ.conjugate.nonprincipalContinued σ hn =
      conj ∘ ψ.nonprincipalContinued σ hn ∘ conj := by
    funext z
    simpa only [Function.comp_apply, Complex.conj_conj] using
      ψ.nonprincipalContinued_conjugation σ hn hψ (conj z)
  have ha := (ψ.nonprincipalContinued_entire σ hn).analyticAt s
  have hac := (ψ.conjugate.nonprincipalContinued_entire σ hn).analyticAt (conj s)
  rw [hac.meromorphicOrderAt_eq, ha.meromorphicOrderAt_eq, he]
  congr 1
  simpa only [Complex.conj_conj] using analyticOrderAt_reflection
    (by simpa only [Complex.conj_conj] using ha :
      AnalyticAt ℂ (ψ.nonprincipalContinued σ hn) (conj (conj s)))

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
