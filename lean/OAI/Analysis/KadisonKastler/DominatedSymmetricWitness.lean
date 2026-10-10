import OAI.Analysis.KadisonKastler.HaagerupProjectionWitness
import OAI.Analysis.KadisonKastler.DominatedVectorState

namespace OAI

/-! # Dominated symmetric vectors belong to the bounded modular core

The bounded commutant intertwiner becomes a left algebra element after
conjugation. Thus the constructed projection witnesses apply exactly to
every symmetric vector whose state is dominated by the reference state.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem exists_symmetric_algebra_vector_of_domination
    (hcyc : DenseRange (algebraVectorMap M Ω)) (η : H) (hη : d.conjugation η=η)
    (C : ℝ) (hdom : ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val Ω‖) :
    ∃ a : Algebra M, a.val Ω=η ∧ a.val Ω=d.rightAction (star a) Ω := by
  let R := dominatedVectorIntertwiner M Ω η
  have hRM : R ∈ M.commutant := dominatedVectorIntertwiner_commutant Ω η hcyc C hdom
  have hRv : R Ω=η := dominatedVectorIntertwiner_vector Ω η hcyc C hdom
  rw [← d.commutant] at hRM
  change R ∈ conjugationOperator d.conjugation '' (M : Set (H →L[ℂ] H)) at hRM
  obtain ⟨A,hAM,hAR⟩ := hRM
  let a : Algebra M := ⟨A,hAM⟩
  have hv : a.val Ω=η := by
    have he := congrArg d.conjugation hRv
    rw [← hAR] at he
    change d.conjugation (d.conjugation (A (d.conjugation Ω)))=d.conjugation η at he
    rw [d.fixes_vector,d.involutive,hη] at he
    exact he
  refine ⟨a,hv,?_⟩
  have he := d.rightAction_conjugation a Ω
  rw [d.fixes_vector,hv,hη] at he
  exact hv.trans he.symm

theorem dominated_symmetric_projection_witness
    (h : HaagerupCommutatorWitnesses d)
    (hcyc : DenseRange (algebraVectorMap M Ω)) (η : H) (hη : d.conjugation η=η)
    (hunit : ‖η‖=1) (horth : inner ℂ Ω η=0)
    (C : ℝ) (hdom : ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val Ω‖)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ‖p.val.val Ω‖^2+‖p.val.val η‖^2 <
        2048*‖centralVectorDefect d.conjugation η p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation η p.val.val‖^2 := by
  obtain ⟨a,ha,hbal⟩ := d.exists_symmetric_algebra_vector_of_domination hcyc η hη C hdom
  have hzero : productVectorState Ω a.val=0 := by
    change inner ℂ Ω (a.val Ω)=0
    rwa [ha]
  have hnorm : ‖a.val Ω‖=1 := ha ▸ hunit
  obtain ⟨p,hp⟩ := d.symmetric_vector_nonzero_projection_witness h a hbal hzero hnorm hα
  rw [ha] at hp
  exact ⟨p,hp⟩

end ModularConjugationData

end

end KadisonKastler

end OAI
