import Mathlib
import OAI.Analysis.Commutator.CornerSymmetrization
import OAI.Analysis.Commutator.FreeNormalizer
import OAI.Analysis.Commutator.MatrixCompactGroup

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

abbrev factorOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  (t.functional.gnsStarAlgHom.comp f).range

def ambientOperators : StarSubalgebra ℂ (t.functional.GNS →L[ℂ] t.functional.GNS) :=
  StarSubalgebra.centralizer ℂ ↑(StarSubalgebra.centralizer ℂ (generatedOperators t S : Set (t.functional.GNS →L[ℂ] t.functional.GNS)))

lemma mem_ambientOperators {a : t.functional.GNS →L[ℂ] t.functional.GNS} :
    a∈ambientOperators t S ↔ a ∈ Set.centralizer (Set.centralizer (generatedOperators t S : Set _)) := by
  change a ∈ (ambientOperators t S : Set _) ↔ _
  rw [ambientOperators,StarSubalgebra.coe_centralizer_centralizer,StarMemClass.star_coe_eq,Set.union_self]

lemma innerRepresentation_conj_mem_factor (u : unitary D)
    {a : t.functional.GNS →L[ℂ] t.functional.GNS} (ha : a∈factorOperators t f) :
    (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv a ∈ factorOperators t f := by
  obtain ⟨b,rfl⟩ := ha
  change (innerRepresentation t ht f S i hS hfree hgen u).conjStarAlgEquiv
    (t.functional.gnsStarAlgHom (f b)) ∈ factorOperators t f
  rw [innerRepresentation_conj_generator t ht f S i hS hfree hgen u i (f b)
    (by rw [hS]; exact ⟨b,rfl⟩),innerFamily_self]
  refine ⟨(u:D)*b*star (u:D),?_⟩
  change t.functional.gnsStarAlgHom (f ((u:D)*b*star (u:D)))=_
  simp only [map_mul,map_star]

lemma innerRepresentation_commutes_other (hji : j≠i) (u : unitary D) (a : A) (ha : a∈S j) :
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
      t.functional.gnsStarAlgHom a = t.functional.gnsStarAlgHom a*
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS) := by
  let W := innerRepresentation t ht f S i hS hfree hgen u
  have h := innerRepresentation_conj_generator t ht f S i hS hfree hgen u j a ha
  rw [innerFamily_other f i u hji] at h
  ext x
  have hh := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS => T (W x)) h
  change W (t.functional.gnsStarAlgHom a (W.symm (W x)))=t.functional.gnsStarAlgHom a (W x) at hh
  change W (t.functional.gnsStarAlgHom a x)=t.functional.gnsStarAlgHom a (W x)
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

abbrev baseSpace : Submodule ℂ t.functional.GNS :=
  cyclicSubspace ((S j).map t.functional.gnsStarAlgHom) (TracialGNS.vacuum t.functional)

lemma innerRepresentation_fixes_base (hji : j≠i) (u : unitary D)
    {x : t.functional.GNS} (hx : x∈baseSpace t S j) :
    innerRepresentation t ht f S i hS hfree hgen u x=x := by
  let W := innerRepresentation t ht f S i hS hfree hgen u
  apply closure_minimal (t := {x | W x=x}) ?_ (isClosed_eq W.continuous continuous_id) hx
  rintro y ⟨a,⟨b,hb,rfl⟩,rfl⟩
  have h := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS =>
    T (TracialGNS.vacuum t.functional))
    (innerRepresentation_commutes_other t ht f S i j hS hfree hgen hji u b hb)
  change W (t.functional.gnsStarAlgHom b (TracialGNS.vacuum t.functional))=
    t.functional.gnsStarAlgHom b (W (TracialGNS.vacuum t.functional)) at h
  rw [innerRepresentation_vacuum t ht f S i hS hfree hgen u] at h
  exact h

lemma innerRepresentation_fixes_baseProjection (hji : j≠i) (u : unitary D) :
    (innerRepresentation t ht f S i hS hfree hgen u : t.functional.GNS →L[ℂ] t.functional.GNS)*
      (baseSpace t S j).starProjection=(baseSpace t S j).starProjection := by
  ext x
  exact innerRepresentation_fixes_base t ht f S i j hS hfree hgen hji u
    ((baseSpace t S j).starProjection_apply_mem x)

end Kadison.FreeBlocks

namespace Kadison.TracialGNS

variable {D : Type*} [CStarAlgebra D]

variable {I : Type*} [Fintype I] [DecidableEq I]

def stageUnitaryHom (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) : unitary (Matrix I I ℂ) →* unitary D where
  toFun := stageUnitary φ
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a:Matrix I I ℂ) (b:Matrix I I ℂ))

lemma stageUnitaryHom_continuous (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) : Continuous (stageUnitaryHom φ) := by
  exact (φ.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

end Kadison.TracialGNS

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] D)

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a)=φ n a)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (hGL : ∀ a : D, G*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*G)

variable (ε : ℝ) (hε : 0≤ε) (r : ℂ)

variable (hC : ∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
    (TracialGNS.vacuum t.functional) r x → ‖G*x-x*G‖≤ε*‖x‖)

variable (s : A) (hs : s∈S j) (hji : j≠i)

omit [PartialOrder D] [StarOrderedRing D] in
include he hGL hε hC hs hji in
theorem exists_free_symmetrization : ∃ V : t.functional.GNS →L[ℂ] t.functional.GNS,
    ‖V‖≤‖G‖ ∧
    (∀ n u, V*(innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)=
      (innerRepresentation t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) u) : t.functional.GNS →L[ℂ] t.functional.GNS)*V) ∧
    (∀ a : D, V*t.functional.gnsStarAlgHom (f a)=t.functional.gnsStarAlgHom (f a)*V) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V*x-x*V‖≤ε*‖x‖) ∧
    (∀ x, CornerSymmetrization.CornerElement (factorOperators t f) (ambientOperators t S)
      (TracialGNS.vacuum t.functional) r x → ‖V.adjoint*x-x*V.adjoint‖≤ε*‖x‖) ∧
    (baseSpace t S j).starProjection*(V*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*V)*
      (baseSpace t S j).starProjection=
    (baseSpace t S j).starProjection*(G*t.functional.gnsStarAlgHom s-t.functional.gnsStarAlgHom s*G)*
      (baseSpace t S j).starProjection := by
  let Γ := fun n : ℕ => ↥(unitary (Matrix (I n) (I n) ℂ))
  let : ∀ n, MeasurableSpace (Γ n) := fun n => borel (Γ n)
  let : ∀ n, BorelSpace (Γ n) := fun _ => ⟨rfl⟩
  let U : ∀ n, Γ n →* (t.functional.GNS ≃ₗᵢ[ℂ] t.functional.GNS) := fun n =>
    (innerRepresentation t ht f S i hS hfree hgen).comp (TracialGNS.stageUnitaryHom (φ n))
  have hU : ∀ n x, Continuous fun g => U n g x := by
    intro n x
    exact (innerRepresentation_continuous t ht f S i hS hfree hgen x).comp
      (TracialGNS.stageUnitaryHom_continuous (φ n))
  have hnest : ∀ n m, n ≤ m → ∀ g : Γ n, ∃ k : Γ m, U m k=U n g := by
    intro n m h g
    refine ⟨TracialGNS.stageUnitary (e h) g,?_⟩
    apply congrArg (innerRepresentation t ht f S i hS hfree hgen)
    exact Subtype.ext (he n m h (g:Matrix (I n) (I n) ℂ))
  obtain ⟨V,hV,hVU,hVF,hVC,hVCs,hVQ⟩ := CornerSymmetrization.exists_symmetrization Γ U hU hnest
    (fun n => compactHaarProbability (Γ n)) (factorOperators t f) (ambientOperators t S)
    (TracialGNS.vacuum t.functional) r
    (fun n g => innerRepresentation_vacuum t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) g))
    (fun n g _ ha => innerRepresentation_conj_mem_factor t ht f S i hS hfree hgen
      (TracialGNS.stageUnitary (φ n) g) ha)
    (fun n g _ ha => (mem_ambientOperators t S).mpr
      (innerRepresentation_conj_mem_bicommutant t ht f S i hS hfree hgen
        (TracialGNS.stageUnitary (φ n) g) ((mem_ambientOperators t S).mp ha)))
    G ε hε (fun _ ⟨a,ha⟩ => by subst ha; exact hGL a) hC
    (baseSpace t S j).starProjection (t.functional.gnsStarAlgHom s)
    (isSelfAdjoint_starProjection _) 
    (fun n g => innerRepresentation_fixes_baseProjection t ht f S i j hS hfree hgen hji
      (TracialGNS.stageUnitary (φ n) g))
    (fun n g => innerRepresentation_commutes_other t ht f S i j hS hfree hgen hji
      (TracialGNS.stageUnitary (φ n) g) s hs)
  exact ⟨V,hV,hVU,(fun a => hVF _ ⟨a,rfl⟩),hVC,hVCs,hVQ⟩

end Kadison.FreeBlocks

end

end
end

end OAI
