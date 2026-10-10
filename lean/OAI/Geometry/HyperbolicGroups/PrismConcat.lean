import Mathlib

namespace OAI

section


/-! Continuous concatenation of literal prisms, with pointwise restriction
identities. No change in the endpoint maps is hidden by homotopy classes. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.PrismConcat
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

def endpoint (F : C(I × Y,X)) (t : I) : C(Y,X) := F.comp ⟨fun y => (t,y),by fun_prop⟩
def homotopy (F : C(I × Y,X)) : (endpoint F 0).Homotopy (endpoint F 1) where
  toContinuousMap := F
  map_zero_left _ := rfl
  map_one_left _ := rfl

def continuation (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) :
    (endpoint F 1).Homotopy (endpoint G 1) where
  toContinuousMap := G
  map_zero_left y := (h y).symm
  map_one_left _ := rfl

def concat (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) : C(I × Y,X) :=
  ((homotopy F).trans (continuation F G h)).toContinuousMap

lemma initial (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) (y : Y) :
    concat F G h (0,y) = F (0,y) := by
  unfold concat
  exact ContinuousMap.Homotopy.map_zero_left _ y
lemma final (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y)) (y : Y) :
    concat F G h (1,y) = G (1,y) := by
  unfold concat
  exact ContinuousMap.Homotopy.map_one_left _ y

lemma agree (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y))
    (F' G' : C(I × Z,X)) (h' : ∀ y, F' (1,y) = G' (0,y))
    (y : Y) (z : Z) (hF : ∀ t, F (t,y) = F' (t,z)) (hG : ∀ t, G (t,y) = G' (t,z)) (t : I) :
    concat F G h (t,y) = concat F' G' h' (t,z) := by
  unfold concat
  simp only [ContinuousMap.Homotopy.coe_toContinuousMap,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

lemma constant_at (F G : C(I × Y,X)) (h : ∀ y, F (1,y) = G (0,y))
    (y : Y) (x : X) (hF : ∀ t, F (t,y) = x) (hG : ∀ t, G (t,y) = x) (t : I) :
    concat F G h (t,y) = x := by
  unfold concat
  simp only [ContinuousMap.Homotopy.coe_toContinuousMap,ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact hF _
  · exact hG _

end HyperbolicObstruction.PrismConcat
end
end

section

end

end OAI
