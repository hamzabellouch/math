import OAI.Analysis.KadisonKastler.DominatedSymmetricWitness
import OAI.Analysis.KadisonKastler.NondominatedVectorWitness

namespace OAI

/-! # Projection witnesses for every symmetric unit vector

The dominated and nondominated cases complete the fixed-reference version
of Haagerup's Lemma 2.13. The projection-family amplification is separate.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H} {Ω : H}

theorem ModularConjugationData.symmetric_projection_witness
    (d : ModularConjugationData M Ω) (hM : TypeIIIFactor M)
    (h : HaagerupCommutatorWitnesses d) (hcyc : DenseRange (algebraVectorMap M Ω))
    (η : H) (hη : d.conjugation η=η) (hunit : ‖η‖=1) (horth : inner ℂ Ω η=0)
    {α : ℝ} (hα : 0 < α) :
    ∃ p : AlgebraProjection M, p.val ≠ 0 ∧
      ‖p.val.val Ω‖^2+‖p.val.val η‖^2 <
        2048*‖centralVectorDefect d.conjugation η p.val.val‖^2 ∧
      ‖centralVectorDefect d.conjugation Ω p.val.val‖^2 <
        α*‖centralVectorDefect d.conjugation η p.val.val‖^2 := by
  by_cases hdom : ∃ C : ℝ, ∀ a : Algebra M, ‖a.val η‖ ≤ C*‖a.val Ω‖
  · obtain ⟨C,hC⟩ := hdom
    exact d.dominated_symmetric_projection_witness h hcyc η hη hunit horth C hC hα
  · obtain ⟨p,hp,hc⟩ := exists_projection_of_relative_two_vector d.conjugation d.involutive
      (d.right_mem le_rfl) Ω η d.fixes_vector hη
      (fun _ hε => exists_nondominated_two_vector_witness hM d.conjugation Ω η
        d.fixes_vector hη hdom hε) hα
    refine ⟨p,?_,hp,hc⟩
    intro hz
    have hzv : p.val.val=0 := congrArg Subtype.val hz
    have he : (0 : ℝ) < 0 := by
      simpa only [hzv,map_zero,norm_zero,pow_two,mul_zero] using hc
    exact (lt_irrefl 0) he

end

end KadisonKastler

end OAI
