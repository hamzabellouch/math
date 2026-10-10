import Mathlib

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

lemma ideal_prime_of_integral_subscheme {X : Scheme} (I : X.IdealSheafData)
    [IsIntegral I.subscheme] (U : X.affineOpens) (x : X)
    (hx : x ∈ U.1) (hI : x ∈ I.support) : (I.ideal U).IsPrime := by
  have hmem : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hI
  obtain ⟨z,hz⟩ := hmem
  let : Nonempty (I.subschemeι ⁻¹ᵁ U.1) := ⟨⟨z,by change I.subschemeι z ∈ U.1; rwa [hz]⟩⟩
  rw [← I.ker_subschemeι_app U]
  exact RingHom.ker_isPrime _

end
end MaximalSeshadri.Projective
end


end
end

end OAI
