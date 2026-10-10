import OAI.Algebra.Finitistic.Bimodule.BimoduleLeftNaturality
import OAI.Algebra.Finitistic.Bimodule.BimoduleExactRows
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ) [∀ q, Projective (Z.X q)]
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- Fixed-input finite tensor total as an actual functor on bimodule complexes. -/
def leftTotalFunctor : BiComplex k B ⥤ CochainComplex (ModuleCat.{u} B) ℤ where
  obj P := total k B P p hp Z
  map f := leftTotalMap f Z p hp
  map_id _ := leftTotalMap_id p hp Z
  map_comp f g := leftTotalMap_comp p hp f g Z

instance leftTotalFunctor_preservesZeroMorphisms : (leftTotalFunctor k B Z p hp).PreservesZeroMorphisms where
  map_zero := by
    intros P P'
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change tensorAcross (0 : P.X (p i) ⟶ P'.X (p i)) (𝟙 (Z.X (n + -(p i)))) (x i) = 0
    rw [tensorAcross_zero_left,LinearMap.zero_apply]

/-- Short exact sequences of bimodules remain short exact after the finite total
on an input complex of projective left modules. -/
theorem leftTotal_shortExact (S : ShortComplex (BiComplex k B)) (hS : S.ShortExact) :
    (S.map (leftTotalFunctor k B Z p hp)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hs (i : Fin l) :
      ((S.map (HomologicalComplex.eval _ (.up ℤ) (p i))).map
        (BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i))))).ShortExact := by
    let : Module.Projective B (ComplexTensor.leftTerm k B Z (n + -(p i))) :=
      inferInstanceAs (Module.Projective B (Z.X (n + -(p i))))
    let := BimoduleBalancedTensor.projectiveInput_preservesHomology k B
      (ComplexTensor.leftTerm k B Z (n + -(p i)))
    let F := BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))
    let := Functor.preservesMonomorphisms_of_map_exact F
      (BimoduleBalancedTensor.projectiveInput_mapsExact k B _)
    let := Functor.preservesEpimorphisms_of_map_exact F
      (BimoduleBalancedTensor.projectiveInput_mapsExact k B _)
    have hSe := hS.map (HomologicalComplex.eval _ (.up ℤ) (p i))
    let := hSe.mono_f
    let := hSe.epi_g
    exact hSe.map F
  have hf (i : Fin l) : Function.Injective
      (leftTermMap S.f Z (p i) (n + -(p i))) := by
    have := (hs i).mono_f
    rw [leftTermMap,tensorAcross_right_id]
    exact (ModuleCat.mono_iff_injective
      ((BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map (S.f.f (p i)))).mp (hs i).mono_f
  have hg (i : Fin l) : Function.Surjective
      (leftTermMap S.g Z (p i) (n + -(p i))) := by
    have := (hs i).epi_g
    rw [leftTermMap,tensorAcross_right_id]
    exact (ModuleCat.epi_iff_surjective
      ((BimoduleBalancedTensor.functor k B (ComplexTensor.leftTerm k B Z (n + -(p i)))).map (S.g.f (p i)))).mp (hs i).epi_g
  have he (i : Fin l) : Function.Exact
      (leftTermMap S.f Z (p i) (n + -(p i)))
      (leftTermMap S.g Z (p i) (n + -(p i))) := by
    rw [leftTermMap,leftTermMap,tensorAcross_right_id,tensorAcross_right_id]
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hs i).exact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    have hyi (i : Fin l) : leftTermMap S.g Z (p i) (n + -(p i)) (y i) = 0 :=
      congrArg (fun x => x i) hy
    choose x hx using fun i => (he i (y i)).mp (hyi i)
    exact ⟨x,funext hx⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x y h
    funext i
    exact hf i (congrArg (fun x => x i) h)
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    choose x hx using fun i => hg i (y i)
    exact ⟨x,funext hx⟩
end LittleFinitistic.BimoduleTotal

end

end OAI
