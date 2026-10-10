import OAI.Analysis.Naimark.Recursion
import OAI.Analysis.Naimark.Operators

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder
namespace TracialStage

variable (X : TracialStage) {B : Type} [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B] [TopologicalSpace.SeparableSpace B]
  (hB : IsSimpleCStar B) (ψ : CAR →⋆ₐ[ℂ] B) (φ : B →⋆ₐ[ℂ] X)
  (hφ : Function.Injective φ) (hbase : ∀ a, φ (ψ a) = X.base a)
  (hU : PureUEP φ) (f : X →L[ℂ] ℂ) (hf : IsPureState f)
  (hfr : IsPureState (restrictState φ f))

include hB hφ hbase hU hf hfr in

theorem exists_supported_peak_pair_unconditional :
    ∃ Q : PeakingPairData X,
      (∀ a, Q.trace a = X.trace a) ∧ Q.state false = X.reference ∧
      Q.state true = f ∧ (∀ n, Q.peak false n = X.base (carPeak n)) ∧
      (∀ i n, Q.peak i n ∈ Set.range φ) := by
  have hp := core_reference_peaks X ψ φ hbase
  have hpr := (hp.restrict φ hφ).1.isPureState
  obtain ⟨γ,hγ⟩ := KOS.homogeneity hB
    (core_infinite X ψ φ hbase) (restrictState φ f)
    (restrictState φ X.reference) hfr hpr
  have he : restrictState γ.toStarAlgHom (restrictState φ f) =
      restrictState φ X.reference := by
    ext a
    exact hγ a
  let Q := homogeneousCARPeakPair ψ φ hφ X.reference f hp hfr hf.1 hU γ he
    X.positiveTrace X.tracial X.positiveTrace_normalized X.positiveTrace_faithful
  refine ⟨Q,fun _ => rfl,rfl,rfl,fun n => hbase _,?_⟩
  intro i n
  cases i
  · exact ⟨ψ (carPeak n),rfl⟩
  · exact ⟨γ (ψ (carPeak n)),rfl⟩

include hB hφ hbase hU hf hfr in

theorem exists_joining_successor_unconditional :
    ∃ Y : TracialStage, ∃ j : Hom X Y,
      ∃ F : Y →L[ℂ] ℂ, ∃ hF : IsPureState F,
        restrictState j.map F = f ∧
        PureStateEquivalent Y.reference Y.reference_spec.1 F hF := by
  classical
  by_cases he : PureStateEquivalent X.reference X.reference_spec.1 f hf
  · exact ⟨X,Hom.id X,f,hf,rfl,he⟩
  · obtain ⟨Q,ht,h0,h1,_,_⟩ := exists_supported_peak_pair_unconditional X hB ψ φ hφ hbase hU f hf hfr
    have hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
        (Q.state true) (Q.peaks true).isPureState := by
      simpa only [h0,h1] using he
    let hs := Q.separated_of_inequivalent hne
    obtain ⟨F,hF,hr,hjoin⟩ := hnn_reference_join X Q hs ht f hf h0 h1
    exact ⟨hnn X Q hs,hnnHom X Q hs ht,F,hF,hr,hjoin⟩

end TracialStage

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
namespace ChronologicalStage
variable (X : ChronologicalStage)

lemma exists_supported_pair_unconditional
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ S : Set Ordinal.{0}, S.Countable ∧ S ⊆ Set.Iio X.height ∧
      ∃ Q : PeakingPairData X.stage,
        (∀ a,Q.trace a = X.stage.trace a) ∧ Q.state false = X.stage.reference ∧
        Q.state true = f ∧ (∀ n,Q.peak false n = X.stage.base (carPeak n)) ∧
        (∀ i n,Q.peak i n ∈ X.history.algebra S) := by
  obtain ⟨S,hSc,hS,hclosed,hsep,hsimple,hfr,_⟩ := X.history.countable_determination f hf
  let : TopologicalSpace.SeparableSpace (X.history.algebra S) := hsep.separableSpace
  let ψ := X.coreBase S
  let φ := (X.history.algebra S).subtype
  have hbase : ∀ a,φ (ψ a) = X.stage.base a := fun _ => rfl
  obtain ⟨Q,ht,h0,h1,hl,hp⟩ := TracialStage.exists_supported_peak_pair_unconditional X.stage
    hsimple ψ φ Subtype.val_injective hbase (X.history.pureUEP S hS hclosed) f hf hfr
  refine ⟨S,hSc,hS,Q,ht,h0,h1,hl,?_⟩
  intro i n
  obtain ⟨a,ha⟩ := hp i n
  exact ha ▸ a.property

theorem exists_joining_successor_unconditional
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ Y : ChronologicalStage, ∃ j : Hom X Y,
      Y.height = X.height+1 ∧
      ∃ F : Y.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
        restrictState j.embedding.map F = f ∧
        PureStateEquivalent Y.stage.reference Y.stage.reference_spec.1 F hF := by
  by_cases he : PureStateEquivalent X.stage.reference X.stage.reference_spec.1 f hf
  · exact ⟨X.inactiveSuccessor,X.inactiveHom,rfl,f,hf,rfl,he⟩
  · obtain ⟨S,hSc,hS,Q,ht,h0,h1,hl,hp⟩ := X.exists_supported_pair_unconditional f hf
    have hne : ¬ PureStateEquivalent (Q.state false) (Q.peaks false).isPureState
        (Q.state true) (Q.peaks true).isPureState := by
      simpa only [h0,h1] using he
    let hs := Q.separated_of_inequivalent hne
    obtain ⟨F,hF,hr,hjoin⟩ := TracialStage.hnn_reference_join X.stage Q hs ht f hf h0 h1
    exact ⟨X.hnnSuccessor Q hs ht hl S hS hSc hp hne,
      X.hnnHom Q hs ht hl S hS hSc hp hne,rfl,F,hF,hr,hjoin⟩

end ChronologicalStage
end

open CategoryTheory Cardinal Classical
namespace ChronologicalStage
variable (X : ChronologicalStage)

def joiningChoice_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    Σ Y : ChronologicalStage, Hom X Y :=
  ⟨(X.exists_joining_successor_unconditional f hf).choose,
    (X.exists_joining_successor_unconditional f hf).choose_spec.choose⟩

lemma joiningChoice_height_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    (joiningChoice_unconditional X f hf).1.height = X.height+1 :=
  (X.exists_joining_successor_unconditional f hf).choose_spec.choose_spec.1

lemma joiningChoice_treated_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ F : (joiningChoice_unconditional X f hf).1.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
      restrictState (joiningChoice_unconditional X f hf).2.embedding.map F = f ∧
      PureStateEquivalent (joiningChoice_unconditional X f hf).1.stage.reference
        (joiningChoice_unconditional X f hf).1.stage.reference_spec.1 F hF :=
  (X.exists_joining_successor_unconditional f hf).choose_spec.choose_spec.2

variable (K : Type) (hK : 𝔠 ≤ #K)
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]
  (σ : J × K → J) (hσ : ∀ p,p.1 ≤ σ p)

def scheduledRule_unconditional : SuccessorRule J := fun j _ D =>
  joiningChoice_unconditional (D.obj ⟨j,le_rfl⟩) (scheduledTarget K hK σ hσ j D)
    (scheduledTarget_pure K hK σ hσ j D)

omit succOrderJ orderBotJ in
lemma scheduledRule_height_unconditional [SuccOrder J] [OrderBot J] (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage) :
    (scheduledRule_unconditional K hK σ hσ j hj D).1.height =
      (D.obj ⟨j,le_rfl⟩).height+1 :=
  joiningChoice_height_unconditional _ _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]
variable (K : Type) (hK : 𝔠 ≤ #K) (σ : J × K → J) (hσ : ∀ p,p.1 ≤ σ p)

omit succOrderJ orderBotJ in
lemma scheduledRule_treated_unconditional [SuccOrder J] [OrderBot J] (hi : Function.Injective σ) (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage)
    (p : J × K) (hp : σ p = j) :
    Treated K hK p.2 (Arrow.mk
      ((D.map (homOfLE ((hσ p).trans_eq hp) :
        ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)) ≫
          (scheduledRule_unconditional K hK σ hσ j hj D).2)) := by
  obtain ⟨F,hF,hr,he⟩ := joiningChoice_treated_unconditional (D.obj ⟨j,le_rfl⟩)
    (scheduledTarget K hK σ hσ j D) (scheduledTarget_pure K hK σ hσ j D)
  refine ⟨F,hF,?_,he⟩
  change restrictState ((scheduledRule_unconditional K hK σ hσ j hj D).2.embedding.map.comp
    (D.map (homOfLE ((hσ p).trans_eq hp))).embedding.map) F = _
  exact (restrictState_comp _ _ F).symm.trans
    ((congrArg (restrictState (D.map (homOfLE ((hσ p).trans_eq hp) :
      ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding.map) hr).trans
      (scheduledTarget_restrict K hK σ hσ j D hi p hp))

variable [WellFoundedLT J]

theorem recursiveTower_treated_unconditional (hi : Function.Injective σ) (p : J × K) (hj : ¬ IsMax (σ p)) :
    Treated K hK p.2
      (Arrow.mk ((recursiveTower J (scheduledRule_unconditional K hK σ hσ)).map
        (homOfLE ((hσ p).trans (Order.le_succ (σ p)))))) := by
  rw [recursiveTower_through_succ_arrow (scheduledRule_unconditional K hK σ hσ) (σ p) hj p.1 (hσ p)]
  exact scheduledRule_treated_unconditional K hK σ hσ hi (σ p) hj _ p rfl

end ChronologicalStage

open CategoryTheory Cardinal
namespace ChronologicalStage

abbrev FullRule_unconditional
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) :=
  scheduledRule_unconditional ConstructionIndex constructionIndex_cardinal σ hσ

abbrev fullTower_unconditional
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p) := recursiveTower ConstructionIndex (FullRule_unconditional σ hσ)

variable
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p)

lemma fullTower_height_unconditional (j : ConstructionIndex) :
    ((fullTower_unconditional σ hσ).obj j).height ≤ (j:Ordinal) :=
  recursiveTower_height_le _ _ (scheduledRule_height_unconditional _ _ _ _)
    (fun j => (j:Ordinal)) constructionIndex_bot
    (fun j _ => constructionIndex_succ_bound j) constructionIndex_monotone j

lemma fullTower_count_unconditional (j : ConstructionIndex) :
    ((fullTower_unconditional σ hσ).obj j).height.card ≤ 𝔠 :=
  (Ordinal.card_le_card (fullTower_height_unconditional σ hσ j)).trans (construction_initial_cardinal_le j)

theorem fullTower_pure_reference_unconditional (hi : Function.Injective σ)
    (f : limitStage (fullTower_unconditional σ hσ) →L[ℂ] ℂ) (hf : IsPureState f) :
    PureStateEquivalent f hf (limitStage (fullTower_unconditional σ hσ)).reference
      (limitStage (fullTower_unconditional σ hσ)).reference_spec.1 := by
  let F := fullTower_unconditional σ hσ
  let X := limitStage F
  let into := fun j => (limitEmbedding F j).map
  let incl := fun {i j : ConstructionIndex} (h : i ≤ j) => (F.map (homOfLE h)).embedding.map
  have hcomp : ∀ {i j} (h : i ≤ j), (into j).comp (incl h) = into i := by
    intro i j h
    ext a
    exact limit_embedding_compatible F i j h a
  have hfp : ∀ j, IsPureState (restrictState (into j) X.reference) := by
    intro j
    rw [(limitEmbedding F j).reference_map]
    exact (F.obj j).stage.reference_spec.1
  apply scheduled_pure_equivalent_to_reference (fun j => (F.obj j).stage)
    into (fun j => (limitEmbedding F j).injective) incl hcomp
    (fun j => (limitEmbedding F j).uep) X.reference X.reference_spec.1 hfp
    (fun j => pureList ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j => pureList_pure ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j g hg => pureList_covers ConstructionIndex constructionIndex_cardinal (F.obj j)
      (fullTower_count_unconditional σ hσ j) g hg)
    σ hσ Order.succ Order.le_succ ?_ f hf (limit_eventual_pure F f hf)
  intro j η
  obtain ⟨G,hG,hr,he⟩ := recursiveTower_treated_unconditional ConstructionIndex constructionIndex_cardinal
    σ hσ hi (j,η) (not_isMax _)
  refine ⟨G,hG,hr,?_⟩
  change PureStateEquivalent G hG
    (restrictState (limitEmbedding F _).map (limitStage F).reference) _
  simp only [TracialStage.Hom.reference_map]
  exact he.symm

end ChronologicalStage

universe u v w

theorem main :
    ∃ (A : Type u) (_ : CStarAlgebra A),
      IsSimpleCStar A ∧ ¬ FiniteDimensional ℂ A ∧
      (∃ τ : A →L[ℂ] ℂ, IsFaithfulTracialState τ) ∧
      HasUniqueIrreducibleRepresentation.{u, v, w} A ∧
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ¬ IsIsomorphicToCompacts A H := by
  obtain ⟨σ,hi,hσ⟩ := exists_pair_schedule constructionCardinal.{0} constructionCardinal_regular
  let X := ChronologicalStage.limitStage (ChronologicalStage.fullTower_unconditional σ hσ)
  have hall : ∀ (f g : X →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      PureStateEquivalent f hf g hg := by
    intro f g hf hg
    exact (ChronologicalStage.fullTower_pure_reference_unconditional σ hσ hi f hf).trans
      (ChronologicalStage.fullTower_pure_reference_unconditional σ hσ hi g hg).symm
  let A := ULift.{u} X
  let e : X ≃⋆ₐ[ℂ] A := liftStarAlgEquiv X
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hinf : ¬ FiniteDimensional ℂ A := by
    intro h
    exact X.infinite (FiniteDimensional.of_injective e.toAlgEquiv.toLinearEquiv.toLinearMap e.injective)
  refine ⟨A,inferInstance,X.simple.of_equiv e,hinf,?_,?_,?_⟩
  · refine ⟨restrictState e.symm.toStarAlgHom X.trace,
      isState_restrict _ _ X.traceState,?_,?_⟩
    · intro a b
      change X.trace (e.symm (a*b)) = X.trace (e.symm (b*a))
      rw [map_mul e.symm a b, map_mul e.symm b a]
      exact X.tracial _ _
    · intro a ha
      change 0 < (X.trace (e.symm (star a*a))).re
      rw [map_mul e.symm (star a) a, map_star e.symm a]
      exact X.traceFaithful _ (fun h => ha (e.symm.injective (h.trans (map_zero e.symm).symm)))
  · intro H _ _ _ K _ _ _ π ρ hπ hρ
    exact all_irreducibles_equivalent_of_pure_states (pureHomogeneity_of_equiv e hall) π hπ ρ hρ
  · intro H _ _ _
    exact not_isIsomorphicToCompacts hinf H

end NaimarkZFC

end

end OAI
