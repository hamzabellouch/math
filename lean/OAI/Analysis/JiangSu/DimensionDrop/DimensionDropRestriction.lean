import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropPureFibres
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropPolynomialNorm
import OAI.Analysis.JiangSu.CStarAlgebras.ClosedSubalgebraCP

namespace OAI


noncomputable section
namespace DimensionDropRelations.Witness
open CompletelyPositiveOperations
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)

instance generated_closed : IsClosed (w.generated : Set B) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance generated_cstar : CStarAlgebra w.generated := by
  letI : SubringClass (StarSubalgebra ℂ B) B := @StarSubalgebra.subringClass ℂ B _ _ _ _ _ _
  exact StarSubalgebra.cstarAlgebra _
instance (priority := 1100) : LE w.generated := (CStarAlgebra.spectralOrder _).toLE
instance (priority := 1100) : Preorder w.generated := (CStarAlgebra.spectralOrder _).toPreorder
instance (priority := 1100) : PartialOrder w.generated := CStarAlgebra.spectralOrder _
instance : StarOrderedRing w.generated := CStarAlgebra.spectralOrderedRing _
lemma phi_mem (M : CStarMatrix I I ℂ) : w.φ M∈w.generated :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨M,rfl⟩))
lemma s_mem : w.s∈w.generated :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl))
 def restrictPhi : CStarMatrix I I ℂ →CP w.generated :=
  ClosedSubalgebraCP.reflect (StarSubalgebra.subtype _) Subtype.val_injective w.φ
    { toFun := fun M => ⟨w.φ M,w.phi_mem M⟩
      map_add' := fun M N => Subtype.ext (map_add w.φ M N)
      map_smul' := fun r M => Subtype.ext (map_smul w.φ r M) } (fun _ => rfl)
 def restrict : Witness (B := w.generated) p where
  φ := w.restrictPhi
  contractive M := w.contractive M
  orderZero M N := Subtype.ext (w.orderZero M N)
  s := ⟨w.s,w.s_mem⟩
  small := Subtype.ext w.small
  support := Subtype.ext w.support
lemma restrict_image_generators : (StarSubalgebra.subtype w.generated) '' w.restrict.generators=w.generators := by
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨M,rfl⟩|hx := hx
    · exact Or.inl ⟨M,rfl⟩
    · have he : x=w.restrict.s := Set.mem_singleton_iff.mp hx
      rw [he]
      exact Or.inr rfl
  · intro ha
    obtain ⟨M,rfl⟩|ha := ha
    · exact ⟨w.restrict.φ M,Or.inl ⟨M,rfl⟩,rfl⟩
    · have he : a=w.s := Set.mem_singleton_iff.mp ha
      subst a
      exact ⟨w.restrict.s,Or.inr rfl,rfl⟩
 theorem restrict_generated : w.restrict.generated=⊤ := by
  have hmap : (w.restrict.generated).map (StarSubalgebra.subtype w.generated)=w.generated := by
    change ((StarAlgebra.adjoin ℂ w.restrict.generators).topologicalClosure).map
      (StarSubalgebra.subtype w.generated)=w.generated
    rw [←StarSubalgebra.topologicalClosure_map _ _
      (w.generated_closed.isClosedEmbedding_subtypeVal.isClosedMap) (by fun_prop),
      StarAlgHom.map_adjoin,w.restrict_image_generators]
    rfl
  apply top_unique
  intro x _
  have hx : (x:B)∈(w.restrict.generated).map (StarSubalgebra.subtype w.generated) := by
    rw [hmap]; exact x.property
  obtain ⟨y,hy,he⟩ := hx
  have hxy : y=x := Subtype.ext he
  rwa [hxy] at hy

end DimensionDropRelations.Witness

end


noncomputable section
open scoped CStarAlgebra ComplexOrder

local instance (priority := 2000) functionSemiring {I : Type*} [Fintype I] [DecidableEq I] :
    Semiring C(DimensionDropModel.Interval,DimensionDropModel.Mat I) :=
  (inferInstance : Ring C(DimensionDropModel.Interval,DimensionDropModel.Mat I)).toSemiring
local instance functionContinuousStar {I : Type*} [Fintype I] [DecidableEq I] :
    ContinuousStar C(DimensionDropModel.Interval,DimensionDropModel.Mat I) := by
  let : CStarAlgebra C(DimensionDropModel.Interval,DimensionDropModel.Mat I) := inferInstance
  infer_instance
namespace DimensionDropModel
open StarTerms

variable {I : Type*} [Fintype I] [DecidableEq I]
 def functionValues (p : I) (g : Gen I) : C(Interval,Mat I) := realization p (.gen g)
lemma realization_eq_eval (p : I) (e : StarTerms.Term (Gen I)) : realization p e=e.eval (functionValues p) := by
  apply ContinuousMap.ext
  intro t
  induction e with
  | scalar z => rfl
  | gen g => rfl
  | add e f he hf => exact congrArg₂ (·+·) he hf
  | mul e f he hf => exact congrArg₂ (·*·) he hf
  | adjoint e he => exact congrArg star he
 def generated (p : I) : StarSubalgebra ℂ C(Interval,Mat I) :=
  (evalRange (functionValues p)).topologicalClosure
end DimensionDropModel
namespace DimensionDropRelations.Witness
open DimensionDropModel StarTerms
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {B : Type} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {p : I} (w : Witness (B := B) p)
 theorem polynomial_norm (e : Term (Gen I)) :
    ‖e.eval w.interpret‖≤‖e.eval (functionValues p)‖ := by
  have hi : (StarSubalgebra.subtype w.generated)∘w.restrict.interpret=w.interpret := by
    funext g; cases g <;> rfl
  have h := w.restrict.polynomial_norm_of_generated w.restrict_generated e
  change ‖(StarSubalgebra.subtype w.generated) (e.eval w.restrict.interpret)‖≤_ at h
  rw [e.map_eval,hi,realization_eq_eval] at h
  exact h
end DimensionDropRelations.Witness

end


noncomputable section
namespace DimensionDropModel
open ConcreteMatrixUnits
open scoped ComplexOrder CStarAlgebra

variable {I : Type*} [Fintype I] [DecidableEq I]
lemma phi_amplify (t : ℝ) (i j : I) :
    phi t i j=t • unit (none,i) (none,j)+amplify (J := I) (unit (some i) (some j)) := by
  rw [amplify_unit]; rfl
lemma s_amplify (p : I) (t : ℝ) : s p t=Real.sqrt (1-t) • amplify (J := I) (unit (some p) none) := by
  rw [amplify_unit]; rfl
lemma upper_mul_bridge (i j p : I) :
    unit (none,i) (none,j)*amplify (J := I) (unit (some p) none)=0 := by
  rw [amplify_unit,Finset.mul_sum]
  simp only [unit_mul,Prod.mk.injEq,reduceCtorEq,false_and,ite_false,Finset.sum_const_zero]
lemma phi_mul_s (t : ℝ) (i p : I) : phi t i p*s p t=s i t := by
  rw [phi_amplify,s_amplify,s_amplify,add_mul,mul_smul_comm,smul_mul_assoc,
    upper_mul_bridge,smul_zero,smul_zero,zero_add,mul_smul_comm,←map_mul,unit_mul,ite_eq_left rfl]
lemma s_mul_star (t : ℝ) (ht : t≤1) (i j : I) :
    s i t*star (s j t)=(1-t) • amplify (J := I) (unit (some i) (some j)) := by
  rw [s_amplify,s_amplify,star_smul,star_trivial,←map_star,unit_star,
    smul_mul_assoc,mul_smul_comm,←map_mul,unit_mul,ite_eq_left rfl,smul_smul,
    ←sq,Real.sq_sqrt (sub_nonneg.mpr ht)]
lemma sum_blocks : (∑ i : I,unit (none,i) (none,i))+
    ∑ i : I,amplify (J := I) (unit (some i) (some i))=1 := by
  rw [←amplify_unit,←map_sum,←map_add]
  have he : unit (none : Option I) none+∑ i : I,unit (some i) (some i)=1 := by
    have h := unit_sum_diag (ι := Option I)
    rw [Fintype.sum_option] at h
    exact h
  rw [he,map_one]
 theorem parameter_formula (p : I) (t : ℝ) (ht : t≤1) :
    (∑ i : I,phi t i i)-∑ i : I,(phi t i p*s p t)*star (phi t i p*s p t)=t • (1:Mat I) := by
  simp only [phi_mul_s]
  simp only [s_mul_star t ht]
  simp only [phi_amplify,Finset.sum_add_distrib,←Finset.smul_sum]
  rw [sub_smul,one_smul]
  calc
    _=t • ((∑ i : I,unit (none,i) (none,i))+∑ i : I,amplify (J := I) (unit (some i) (some i))) := by
      rw [smul_add]
      abel
    _=t • (1:Mat I) := by rw [sum_blocks]
end DimensionDropModel

end

end OAI
