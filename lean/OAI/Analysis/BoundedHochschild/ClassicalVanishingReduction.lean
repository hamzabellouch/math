import OAI.Analysis.BoundedHochschild.InfiniteCentralReduction

namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildCorners

universe u

def ProperlyInfiniteVanishingInput : Prop :=
  ∀ (N : Type u) [CStarAlgebra N] [PartialOrder N] [StarOrderedRing N],
    WStarAlgebra N → NoFiniteCentralSummand N →
    ∀ (n : ℕ) (f : Cochain N (n + 2)), (∀ x, differentialValue f x = 0) →
      ∃ g : Cochain N (n + 1), ∀ x, differentialValue g x = f x

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma primitive_from_central_corner {p : M} (hp : IsStarProjection p)
    (hc : ∀ a : M, p * a = a * p) {n : ℕ} (f : Cochain M (n + 1))
    (hf : ∀ x, differentialValue f x = 0) (b : Cochain (Corner p hp) n)
    (hb : ∀ x, differentialValue b x = CentralCorner.restrict p hp hc f x) :
    ∃ g : Cochain M n, ∀ x, differentialValue g x = p * f x := by
  have hs (x : Fin (n + 1) → M) : p * centralOutput p f x = centralOutput p f x := by
    simp only [centralOutput_apply, ← mul_assoc, hp.isIdempotentElem.eq]
  have hpf (x : Fin (n + 2) → M) : differentialValue (centralOutput p f) x = 0 := by
    rw [← central_differential_values p hc f (centralOutput p f) (fun _ => rfl), hf, mul_zero]
  obtain ⟨a, _, _, ha⟩ := central_cocycle_correction p hp hc (centralOutput p f) hs hpf
  refine ⟨CentralCorner.extend p hp hc b + a, fun x => ?_⟩
  rw [differentialValue_add, CentralCorner.extend_primitive p hp hc f b hb, ha]
  change _ = centralOutput p f x
  abel

theorem classical_primitive_of_properlyInfinite_input
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hproper : ProperlyInfiniteVanishingInput.{u})
    (hno : NoTypeII1Summand M) {n : ℕ} (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x := by
  obtain ⟨p, hp, hc, hfin, hcomp⟩ := exists_finite_central_cut_noFiniteSummand e
  have hcc (a : M) : (1 - p) * a = a * (1 - p) := by
    simp only [sub_mul, mul_sub, one_mul, mul_one, hc]
  obtain ⟨b, _, hb⟩ := finite_noTypeII1_primitive (cornerPredualEquiv p hp e) hfin
    (noTypeII1_centralCorner hno hp hc) (CentralCorner.restrict p hp hc f)
    (CentralCorner.restrict_cocycle p hp hc f hf)
  let N := Corner (1 - p) hp.one_sub
  let eN := cornerPredualEquiv (1 - p) hp.one_sub e
  let : WStarAlgebra N := ⟨⟨CornerPredual (1 - p) hp.one_sub e,
    inferInstance, inferInstance, inferInstance, ⟨eN⟩⟩⟩
  obtain ⟨c, hcoc⟩ := hproper N inferInstance hcomp n
    (CentralCorner.restrict (1 - p) hp.one_sub hcc f)
    (CentralCorner.restrict_cocycle _ _ _ f hf)
  obtain ⟨g, hg⟩ := primitive_from_central_corner hp hc f hf b hb
  obtain ⟨h, hh⟩ := primitive_from_central_corner hp.one_sub hcc f hf c hcoc
  refine ⟨g + h, fun x => ?_⟩
  rw [differentialValue_add, hg, hh]
  noncomm_ring

theorem classicalVanishing_of_properlyInfinite (hproper : ProperlyInfiniteVanishingInput.{u}) :
    ClassicalVanishingInput.{u} := by
  intro M hM hPO hSO hW hno n f hf
  let := hW
  obtain ⟨X, hX, hXS, hXC, ⟨e⟩⟩ := WStarAlgebra.exists_predual (M := M)
  let := hX
  let := hXS
  let := hXC
  exact classical_primitive_of_properlyInfinite_input e hproper hno f hf

theorem primitive_of_properlyInfinite_input (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hproper : ProperlyInfiniteVanishingInput.{u}) {n : ℕ} (f : Cochain M (n + 2))
    (hf : ∀ x, differentialValue f x = 0) :
    ∃ g : Cochain M (n + 1), ∀ x, differentialValue g x = f x :=
  primitive_of_classical_vanishing e (classicalVanishing_of_properlyInfinite hproper) f hf

end BoundedHochschild.KadisonRingrose

end

end OAI
