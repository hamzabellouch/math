import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledFiniteChains
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CoarseGroupRingCohomology

namespace OAI

/-! # Coarse invariance of uniformly controlled cycle fillings

Only finite chains occur here. A fixed input scale must admit a fixed filling
scale for every cycle. This quantitative condition is stronger than ordinary
acyclicity of the standard resolution and is the condition needed in the
remaining finiteness argument.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory HomologicalComplex
variable {R G H J : Type} [CommRing R] [Group G] [Group H] [Group J] {n : ℕ}

def HasControlledCycleFillings (R G : Type) [CommRing R] [Group G] (n : ℕ) : Prop :=
  ∀ S : Set G, S.Finite → ∃ T : Set G, T.Finite ∧
    ∀ c : MonoidAlgebra R (Fin (n + 2) → G), c ∈ controlledChainSpan R G (n + 1) S →
      (tupleChainComplex R G).d (n + 1) n c = 0 →
      ∃ b : MonoidAlgebra R (Fin (n + 3) → G),
        b ∈ controlledChainSpan R G (n + 2) T ∧
          (tupleChainComplex R G).d (n + 2) (n + 1) b = c

omit [Group G] in
theorem tupleChainMap_id : tupleChainMap (R := R) (id : G → G) = 𝟙 _ := by
  let F : SimplicialObject Type ⥤ ChainComplex (ModuleCat R) ℕ :=
    (SimplicialObject.whiskering Type (ModuleCat R)).obj (ModuleCat.monoidAlgebraFree R) ⋙
      AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)
  have h : tupleSimplicialMap (id : G → G) = 𝟙 (tupleSimplicial G) := rfl
  change F.map (tupleSimplicialMap id) = 𝟙 _
  exact (congrArg F.map h).trans (F.map_id _)

omit [Group G] [Group H] [Group J] in
theorem tupleChainMap_comp (f : G → H) (g : H → J) :
    tupleChainMap (R := R) (g ∘ f) = tupleChainMap f ≫ tupleChainMap g := by
  let F : SimplicialObject Type ⥤ ChainComplex (ModuleCat R) ℕ :=
    (SimplicialObject.whiskering Type (ModuleCat R)).obj (ModuleCat.monoidAlgebraFree R) ⋙
      AlgebraicTopology.alternatingFaceMapComplex (ModuleCat R)
  have h : tupleSimplicialMap (g ∘ f) = tupleSimplicialMap f ≫ tupleSimplicialMap g := rfl
  change F.map (tupleSimplicialMap (g ∘ f)) =
    F.map (tupleSimplicialMap f) ≫ F.map (tupleSimplicialMap g)
  exact (congrArg F.map h).trans (F.map_comp _ _)

omit [Group G] [Group H] in
theorem tupleChainMap_cycle (f : G → H) (c : MonoidAlgebra R (Fin (n + 2) → G))
    (hc : (tupleChainComplex R G).d (n + 1) n c = 0) :
    (tupleChainComplex R H).d (n + 1) n ((tupleChainMap f).f (n + 1) c) = 0 := by
  have h := congrArg (fun f => f.hom c) ((tupleChainMap (R := R) f).comm (n + 1) n).symm
  change (tupleChainMap f).f n ((tupleChainComplex R G).d (n + 1) n c) =
    (tupleChainComplex R H).d (n + 1) n ((tupleChainMap f).f (n + 1) c) at h
  rw [hc, map_zero] at h
  exact h.symm

omit [Group G] [Group H] in
theorem tupleChainPrism_cycle (f g : G → H) (c : MonoidAlgebra R (Fin (n + 2) → G))
    (hc : (tupleChainComplex R G).d (n + 1) n c = 0) :
    (tupleChainMap f).f (n + 1) c =
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainPrism f g).hom (n + 1) (n + 2) c) +
      (tupleChainMap g).f (n + 1) c := by
  have h := (tupleChainPrism (R := R) f g).comm (n + 1)
  rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
    prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
  have hh := congrArg (fun f => f.hom c) h
  change (tupleChainMap f).f (n + 1) c =
    (tupleChainPrism f g).hom n (n + 1) ((tupleChainComplex R G).d (n + 1) n c) +
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainPrism f g).hom (n + 1) (n + 2) c) +
      (tupleChainMap g).f (n + 1) c at hh
  simpa only [hc, map_zero, zero_add] using hh

theorem HasControlledCycleFillings.of_coarse (e : GroupCoarseEquivalence G H)
    (hG : HasControlledCycleFillings R G n) : HasControlledCycleFillings R H n := by
  intro S hS
  obtain ⟨SG, hSG, hback⟩ := controlledChainSpan_pushforward (R := R) (n := n + 1)
    e.invFun e.bornologous_invFun S hS
  obtain ⟨TG, hTG, hfill⟩ := hG SG hSG
  obtain ⟨TH, hTH, hforward⟩ := controlledChainSpan_pushforward (R := R) (n := n + 2)
    e.toFun e.bornologous_toFun TG hTG
  obtain ⟨U, hU, hprism⟩ := controlledChainSpan_prism (R := R) (n := n + 1)
    (GroupCoarseEquivalence.refl H) (e.symm.trans e) e.right_error S hS
  refine ⟨TH ∪ U, hTH.union hU, ?_⟩
  intro c hc hcycle
  obtain ⟨b, hb, hdb⟩ := hfill _ (hback c hc) (tupleChainMap_cycle e.invFun c hcycle)
  let p := (tupleChainPrism (R := R) id (e.toFun ∘ e.invFun)).hom (n + 1) (n + 2) c
  refine ⟨(tupleChainMap e.toFun).f (n + 2) b + p, ?_, ?_⟩
  · exact Submodule.add_mem _
      (controlledChainSpan_mono Set.subset_union_left (hforward b hb))
      (controlledChainSpan_mono Set.subset_union_right (hprism c hc))
  · have hmap := congrArg (fun f => f.hom b)
      ((tupleChainMap (R := R) e.toFun).comm (n + 2) (n + 1)).symm
    change (tupleChainMap e.toFun).f (n + 1)
        ((tupleChainComplex R G).d (n + 2) (n + 1) b) =
      (tupleChainComplex R H).d (n + 2) (n + 1)
        ((tupleChainMap e.toFun).f (n + 2) b) at hmap
    rw [hdb] at hmap
    have hp := tupleChainPrism_cycle (R := R) id (e.toFun ∘ e.invFun) c hcycle
    simp only [tupleChainMap_id, tupleChainMap_comp] at hp
    change c = (tupleChainComplex R H).d (n + 2) (n + 1) p +
      (tupleChainMap e.toFun).f (n + 1) ((tupleChainMap e.invFun).f (n + 1) c) at hp
    rw [map_add, ← hmap]
    exact (add_comm _ _).trans hp.symm

theorem controlledCycleFillings_coarse_iff (e : GroupCoarseEquivalence G H) :
    HasControlledCycleFillings R G n ↔ HasControlledCycleFillings R H n :=
  ⟨fun h => h.of_coarse e, fun h => h.of_coarse e.symm⟩

end PolycyclicRecognition

end

end OAI
