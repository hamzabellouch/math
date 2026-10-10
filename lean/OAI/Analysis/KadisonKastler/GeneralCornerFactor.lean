import OAI.Analysis.KadisonKastler.FactorCornerCentralProjection
import OAI.Analysis.KadisonKastler.CornerFactorStructure
import OAI.Analysis.KadisonKastler.CenterAlgebra

namespace OAI

/-! # Scalar center for arbitrary represented factor corners -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

theorem scalarCenter_representedCorner_general (N : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ N) (hN : ScalarCenter N) :
    ScalarCenter (representedCorner E N hE) := by
  let Q := representedCorner E N hE
  let hp := isStarProjection_starProjection (U := E)
  let p : AlgebraProjection N := ⟨⟨E.starProjection, hE⟩,
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩⟩
  have hproj : ∀ q : Algebra Q, IsStarProjection q →
      (∀ a : Algebra Q, a * q = q * a) → q = 0 ∨ q = 1 := by
    intro q hq hc
    let q0 : Algebra N := ⟨cornerExtension E q.val, q.property⟩
    have hq0 : IsStarProjection q0 := by
      constructor
      · apply Subtype.ext
        change cornerExtension E q.val * cornerExtension E q.val = cornerExtension E q.val
        rw [← cornerExtension_mul]
        exact congrArg (cornerExtension E) (congrArg Subtype.val hq.isIdempotentElem.eq)
      · apply Subtype.ext
        change star (cornerExtension E q.val) = cornerExtension E q.val
        rw [← cornerExtension_star]
        exact congrArg (cornerExtension E) (congrArg Subtype.val hq.isSelfAdjoint.star_eq)
    let qP : AlgebraProjection N := ⟨q0, hq0⟩
    have hqp : qP ≤ p := by
      apply Subtype.ext
      exact starProjection_mul_cornerExtension E q.val
    have hc0 : ∀ a : Algebra N, qP.val * (p.val * a * p.val) =
        (p.val * a * p.val) * qP.val := by
      intro a
      let b : Algebra Q := ⟨cornerCompression E a.val, cornerCompression_mem E hE a.property⟩
      have hh := congrArg (fun x : Algebra Q => cornerExtension E x.val) (hc b)
      change cornerExtension E ((cornerCompression E a.val) * q.val) =
        cornerExtension E (q.val * cornerCompression E a.val) at hh
      rw [cornerExtension_mul, cornerExtension_mul, cornerExtension_compression] at hh
      exact Subtype.ext hh.symm
    rcases factor_corner_central_projection hN p qP hqp hc0 with hz | he
    · left
      apply Subtype.ext
      apply cornerExtension_injective
      exact congrArg Subtype.val hz
    · right
      apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E q.val = cornerExtension E 1
      rw [cornerExtension_one]
      exact congrArg (fun a : AlgebraProjection N => a.val.val) he
  intro T hT hc
  obtain ⟨z, hz⟩ := scalar_center_of_trivial_central_projections Q hproj ⟨T, hT⟩
    (fun a => Subtype.ext (hc a.val a.property))
  exact ⟨z, congrArg Subtype.val hz⟩

end

end KadisonKastler

end OAI
