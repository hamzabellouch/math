import Mathlib
import OAI.Probability.CoordinateSweeps.PlacementMoment
import OAI.RepresentationTheory.Young.Restriction
import OAI.Probability.CoordinateSweeps.Induction

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def removedPlacement : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) where
  toFun i := e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i)))
  inj' := by
    intro i j hij
    have h₁ := e.symm.injective hij
    have h₂ := (boxesSplit μ p).injective h₁
    exact (Fintype.equivFin _).symm.injective (Sum.inr.inj h₂)
def retainedMap : Equiv.Perm (Boxes (hookPart μ p)) →* H.stabilizer :=
  H.stabilizerFreeEquiv.symm.toMonoidHom.comp
    (e.symm.permCongrHom.toMonoidHom.comp (leftPerm (boxesSplit μ p)))
lemma retainedMap_fixed (g : Equiv.Perm (Boxes (hookPart μ p))) :
    H.placementAction (H.retainedMap μ p e g) (H.removedPlacement μ p e)=H.removedPlacement μ p e := by
  apply Function.Embedding.ext
  intro i
  change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
    (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g)))
    (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm i))))=_
  rw [MulEquiv.apply_symm_apply]
  simp [leftPerm,removedPlacement]
  rfl
def retainedInto : Equiv.Perm (Boxes (hookPart μ p)) →*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer where
  toFun g := ⟨H.retainedMap μ p e g,H.retainedMap_fixed μ p e g⟩
  map_one' := by apply Subtype.ext; exact map_one (H.retainedMap μ p e)
  map_mul' g g' := by apply Subtype.ext; exact map_mul (H.retainedMap μ p e) g g'
lemma retainedInto_bijective : Function.Bijective (H.retainedInto μ p e) := by
  constructor
  · intro g g' hh
    have heq := congrArg (fun t => e.permCongrHom (H.stabilizerFreeEquiv t.val)) hh
    change e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g))))=
      e.permCongrHom (H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g')))) at heq
    simp only [MulEquiv.apply_symm_apply] at heq
    have hleft : leftPerm (boxesSplit μ p) g=leftPerm (boxesSplit μ p) g' := by simpa using heq
    apply Equiv.ext
    intro x
    have hx := congrArg (fun t : Equiv.Perm (Boxes μ) => (boxesSplit μ p).symm (t (boxesSplit μ p (Sum.inl x)))) hleft
    simpa [leftPerm] using hx
  · intro g
    have hfix : ∀ z : Boxes (removedPart μ p),
        e.permCongrHom (H.stabilizerFreeEquiv g.val) (boxesSplit μ p (Sum.inr z))=boxesSplit μ p (Sum.inr z) := by
      intro z
      have hh := congrArg (fun u : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => e (u ((Fintype.equivFin _) z))) g.property
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))))=e (e.symm (boxesSplit μ p (Sum.inr ((Fintype.equivFin _).symm ((Fintype.equivFin _) z))))) at hh
      change e ((H.stabilizerFreeEquiv g.val) (e.symm (boxesSplit μ p (Sum.inr z))))=_
      simpa only [Equiv.symm_apply_apply,Equiv.apply_symm_apply] using hh
    obtain ⟨a,ha⟩ := leftPerm_range_of_fix_right (boxesSplit μ p)
      (e.permCongrHom (H.stabilizerFreeEquiv g.val)) hfix
    refine ⟨a,?_⟩
    apply Subtype.ext
    apply H.stabilizerFreeEquiv.injective
    change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
      (e.symm.permCongrHom (leftPerm (boxesSplit μ p) a)))=H.stabilizerFreeEquiv g.val
    rw [MulEquiv.apply_symm_apply,ha]
    apply Equiv.ext
    intro y
    simp
/- Actual retained-hook subgroup chart inside the original hole stabilizer. -/
def retainedEquiv : Equiv.Perm (Boxes (hookPart μ p)) ≃*
    (H.placementChart (H.removedPlacement μ p e)).stabilizer :=
  MulEquiv.ofBijective (H.retainedInto μ p e) (H.retainedInto_bijective μ p e)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.UnitaryIrrep
variable {Γ Λ : Type*} [Group Γ] [Group Λ]
lemma asRepresentation_pullback (ρ : UnitaryIrrep Γ) (e : Λ ≃* Γ) :
    (ρ.pullback e).asRepresentation=ρ.asRepresentation.comp e.toMonoidHom := rfl
lemma dimension_eq_finrank (ρ : UnitaryIrrep Γ) :
    Module.finrank ℂ (Fin ρ.dimension → ℂ)=ρ.dimension := by simp
end CoordinateSweeps.UnitaryIrrep

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def boxesChart : Equiv.Perm (Boxes μ) ≃* H.stabilizer :=
  e.symm.permCongrHom.trans H.stabilizerFreeEquiv.symm

lemma retained_restrict (τ : UnitaryIrrep H.stabilizer) :
    (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype)).comp
        (H.retainedEquiv μ p e).toMonoidHom=
      (τ.pullback (H.boxesChart μ e)).asRepresentation.comp (leftPerm (boxesSplit μ p)) := rfl

/- Source06:eq22 and genuine retained-hook Hom multiplicity simultaneously,
on the literal placement stabilizer used by the conditional induced cycle. -/
theorem exists_retained_irrep (τ : UnitaryIrrep H.stabilizer)
    (hτ : hasShape μ (Equiv.refl _) (τ.pullback (H.boxesChart μ e)).asRepresentation) :
    ∃ ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p e)).stabilizer,
      hasShape (hookPart μ p) (Equiv.refl _)
        (ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom) ∧
      Module.finrank ℂ (shapeSubrep (removedPart μ p) (Equiv.refl _)).toSubmodule ≤
        Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
          (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype))) ∧
      τ.dimension ≤ (Fintype.card (Boxes μ))^(Fintype.card (Boxes (removedPart μ p)))*ρ.dimension := by
  let τB := (τ.pullback (H.boxesChart μ e)).asRepresentation
  let δ := (shapeSubrep (removedPart μ p) (Equiv.refl _)).toRepresentation
  obtain ⟨S,hSi,hSh,hm⟩ := hook_removed_multiplicity μ p τB hτ δ (shapeSubrep_hasShape _ _)
  let : S.toRepresentation.IsIrreducible := hSi
  obtain ⟨σ,⟨eS⟩⟩ := UnitaryRealization.exists_unitary S.toRepresentation
  have hSdim : Module.finrank ℂ S.toSubmodule=σ.dimension := by
    have hh := eS.toLinearEquiv.finrank_eq
    simpa using hh
  have hS : S ≠ ⊥ := by
    intro hh
    rw [hh] at hSdim
    have hz : Module.finrank ℂ (⊥ : Submodule ℂ (Fin τ.dimension → ℂ))=0 := by simp
    have he : σ.dimension=0 := hSdim.symm.trans hz
    exact σ.positive.ne' he
  let ρ := σ.pullback (H.retainedEquiv μ p e).symm
  have hρ : ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom=σ.asRepresentation := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change σ.asRepresentation ((H.retainedEquiv μ p e).symm (H.retainedEquiv μ p e g)) v=σ.asRepresentation g v
    rw [MulEquiv.symm_apply_apply]
  refine ⟨ρ,?_,?_,?_⟩
  · rw [hρ]
    exact hasShape_equiv _ _ _ _ eS hSh
  · have hsource := (Representation.IntertwiningMap.sourceEquiv eS
        (τB.comp (leftPerm (boxesSplit μ p)))).finrank_eq
    have hreparam := (Representation.IntertwiningMap.reparamEquiv ρ.asRepresentation
      (matrixRepresentation (τ.matrix.comp (H.placementChart (H.removedPlacement μ p e)).stabilizer.subtype))
        (H.retainedEquiv μ p e)).finrank_eq
    rw [hρ,H.retained_restrict μ p e τ] at hreparam
    exact hm.trans_eq (hsource.trans hreparam.symm)
  · have hh := hook_dimension_upper μ p τB S hS
    rw [hSdim] at hh
    change Module.finrank ℂ (Fin τ.dimension → ℂ) ≤ _ at hh
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hh
    exact hh
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def retainedSite : Boxes (hookPart μ p) ↪ H.FreeAt 0 where
  toFun a := e.symm (boxesSplit μ p (Sum.inl a))
  inj' := by intro a b hh; exact Sum.inl.inj ((boxesSplit μ p).injective (e.symm.injective hh))
lemma retainedSite_ne_removed (a : Boxes (hookPart μ p))
    (i : Fin (Fintype.card (Boxes (removedPart μ p)))) :
    H.retainedSite μ p e a ≠ H.removedPlacement μ p e i := by
  intro hh
  have he := (boxesSplit μ p).injective (e.symm.injective hh)
  cases he
lemma retainedMap_site (g : Equiv.Perm (Boxes (hookPart μ p))) (a : Boxes (hookPart μ p)) :
    H.stabilizerFreeEquiv (H.retainedMap μ p e g) (H.retainedSite μ p e a)=H.retainedSite μ p e (g a) := by
  change H.stabilizerFreeEquiv (H.stabilizerFreeEquiv.symm
    (e.symm.permCongrHom (leftPerm (boxesSplit μ p) g))) (e.symm (boxesSplit μ p (Sum.inl a)))=_
  rw [MulEquiv.apply_symm_apply]
  simp [leftPerm,retainedSite]
  rfl

def augmentedRetainedEmbedding
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ↪ (H.augmented x ω₀).FreeAt 0 where
  toFun a := ⟨(H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
    (H.retainedSite μ p e a)).val,by
    intro i
    cases i using Fin.addCases with
    | left i =>
      simpa only [augmented,augment_old] using
        (H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)
          (H.retainedSite μ p e a)).property i
    | right i =>
      simp only [augmented,augment_new,Grid.pathBetween_zero]
      intro he
      have hr := congrArg (fun y : H.Placement (k := Fintype.card (Boxes (removedPart μ p))) => (y i).val)
        ((H.placementChart (H.removedPlacement μ p e)).reaches x)
      change ((H.placementChart (H.removedPlacement μ p e)).rep x).val
        ((H.removedPlacement μ p e i).val)=(x i).val at hr
      have hh := ((H.placementChart (H.removedPlacement μ p e)).rep x).val.injective (he.trans hr.symm)
      exact H.retainedSite_ne_removed μ p e a i (Subtype.ext hh)⟩
  inj' := by
    intro a b hh
    have he := congrArg Subtype.val hh
    exact (H.retainedSite μ p e).injective
      ((H.stabilizerFreeEquiv ((H.placementChart (H.removedPlacement μ p e)).rep x)).injective (Subtype.ext he))

lemma augmentedRetainedEmbedding_surjective
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Function.Surjective (H.augmentedRetainedEmbedding μ p e x ω₀) := by
  have hc : Fintype.card (Boxes (hookPart μ p))=Fintype.card ((H.augmented x ω₀).FreeAt 0) := by
    have hsplit := split_card μ p
    have he := Fintype.card_congr e
    rw [H.card_freeAt] at he
    rw [(H.augmented x ω₀).card_freeAt]
    omega
  by_contra hn
  have hh := Fintype.card_lt_of_injective_not_surjective _
    (H.augmentedRetainedEmbedding μ p e x ω₀).injective hn
  omega

def augmentedRetainedEquiv
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Boxes (hookPart μ p) ≃ (H.augmented x ω₀).FreeAt 0 :=
  Equiv.ofBijective (H.augmentedRetainedEmbedding μ p e x ω₀)
    ⟨(H.augmentedRetainedEmbedding μ p e x ω₀).injective,
      H.augmentedRetainedEmbedding_surjective μ p e x ω₀⟩
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open YoungCorner PlacementInduction UnitaryIrrep
variable {G : Grid} {h : ℕ} (H : G.Holes h) (μ : YoungDiagram) (p : ℕ)
    (e : H.FreeAt 0 ≃ Boxes μ)
def augmentedRetainedChart
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    Equiv.Perm (Boxes (hookPart μ p)) ≃* (H.augmented x ω₀).stabilizer :=
  (H.augmentedRetainedEquiv μ p e x ω₀).permCongrHom.trans (H.augmented x ω₀).stabilizerFreeEquiv.symm
lemma augmentedRetainedChart_eq
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) (g : Equiv.Perm (Boxes (hookPart μ p))) :
    H.augmentedRetainedChart μ p e x ω₀ g=
      H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
        ω₀.val ω₀.property (fun _ => rfl)
        ((H.placementChart (H.removedPlacement μ p e)).pointEquiv x (H.retainedEquiv μ p e g)) := by
  apply (H.augmented x ω₀).stabilizerFreeEquiv.injective
  change (H.augmented x ω₀).stabilizerFreeEquiv
    ((H.augmented x ω₀).stabilizerFreeEquiv.symm ((H.augmentedRetainedEquiv μ p e x ω₀).permCongrHom g))=_
  rw [MulEquiv.apply_symm_apply]
  apply Equiv.ext
  intro y
  obtain ⟨a,rfl⟩ := (H.augmentedRetainedEquiv μ p e x ω₀).surjective y
  apply Subtype.ext
  change ((H.augmentedRetainedEquiv μ p e x ω₀)
    (g ((H.augmentedRetainedEquiv μ p e x ω₀).symm ((H.augmentedRetainedEquiv μ p e x ω₀) a)))).val=_
  rw [Equiv.symm_apply_apply]
  change ((H.placementChart (H.removedPlacement μ p e)).rep x).val ((H.retainedSite μ p e (g a)).val)=
    (((H.placementChart (H.removedPlacement μ p e)).rep x).val *
      (H.retainedMap μ p e g).val * (((H.placementChart (H.removedPlacement μ p e)).rep x).val)⁻¹)
      (((H.placementChart (H.removedPlacement μ p e)).rep x).val ((H.retainedSite μ p e a).val))
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  have hh := congrArg Subtype.val (H.retainedMap_site μ p e g a)
  change (H.retainedMap μ p e g).val ((H.retainedSite μ p e a).val)=(H.retainedSite μ p e (g a)).val at hh
  rw [hh]

/- The transported fiber is the same retained Young type on the *actual*
remaining sites. This rules out any unsupported abstract symmetric-group relabeling. -/
theorem augmented_hasShape
    (ρ : UnitaryIrrep (H.placementChart (H.removedPlacement μ p e)).stabilizer)
    (hρ : hasShape (hookPart μ p) (Equiv.refl _)
      (ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom))
    (x : H.Placement (k := Fintype.card (Boxes (removedPart μ p))))
    (ω₀ : {ω : G.Choices // H.Compatible ω}) :
    hasShape (hookPart μ p) (Equiv.refl _)
      ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).pullback
        (H.augmentedRetainedChart μ p e x ω₀)).asRepresentation := by
  have he : ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).pullback
        (H.augmentedRetainedChart μ p e x ω₀)).asRepresentation=
      ρ.asRepresentation.comp (H.retainedEquiv μ p e).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change Matrix.toLinAlgEquiv' ((H.augmentedIrrep (H.removedPlacement μ p e) x ω₀ ρ).matrix
      (H.augmentedRetainedChart μ p e x ω₀ g))=Matrix.toLinAlgEquiv' (ρ.matrix (H.retainedEquiv μ p e g))
    rw [H.augmentedRetainedChart_eq]
    change Matrix.toLinAlgEquiv' (ρ.matrix
      (((H.placementChart (H.removedPlacement μ p e)).pointEquiv x).symm
        ((H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
          ω₀.val ω₀.property (fun _ => rfl)).symm
          ((H.augmentFixEquiv (H.removedPlacement μ p e) x (fun i => G.sweep ω₀.val (x i).val)
            ω₀.val ω₀.property (fun _ => rfl))
            ((H.placementChart (H.removedPlacement μ p e)).pointEquiv x (H.retainedEquiv μ p e g))))))=_
    simp only [MulEquiv.symm_apply_apply]
  rw [he]
  exact hρ
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! New work: the actual alternating placement kernel from 04-sparse:eq7.
The preceding definitions/proofs are reused verbatim from the pinned support.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Reused exact conditional transition/potential support from pinned root-02. -/

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

theorem extraProbability_nonneg (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    0 ≤ H.extraProbability x y A μ := by
  apply Finset.prod_nonneg
  intro j _
  apply Finset.prod_nonneg
  intro L _
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro σ _ <;>
    split_ifs <;> first | exact (μ j).nonneg σ | exact le_rfl

/- Faithful finite-event application of the transition comparison: the selected
extra paths are appended to the holes only when their joint event is possible. -/
theorem scaled_extraProbability_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz') ≤
      Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
  classical
  rw [H.extraProbability_eq_conditionalEndpoint]
  by_cases he : ∃ ω, H.Compatible ω ∧ G.endpointEvent x y A ω
  · obtain ⟨ω,hω,he⟩ := he
    let u := fun i => x (selected A i)
    let v := fun i => y (selected A i)
    have hv : ∀ i, G.sweep ω (u i) = v i := (endpointEvent_iff_selected x y A ω).mp he
    let J := H.augment u v (H.validInput_selected x hx A) ω hω hv
    have heq : H.conditionalEndpointProbability x y A (fun j => lineLaw (G.bits j) z hz hz') =
        J.probability z / H.probability z := by
      unfold conditionalEndpointProbability
      rw [H.lineMass_hole_normalizer hz hz']
      congr 1
      rw [← J.lineMass_hole_normalizer hz hz']
      apply Finset.sum_congr rfl
      intro ν _
      have hj : J.Compatible ν ↔ H.Compatible ν ∧ G.endpointEvent x y A ν := by
        dsimp [J]
        rw [H.augment_compatible_iff, endpointEvent_iff_selected]
      simp only [hj]
    rw [heq]
    have ht := J.conditional_transition_bound H
      (H.augment_extends u v (H.validInput_selected x hx A) ω hω hv) hz hz' hlo hhi
    have hs : (0 : ℝ) < G.size := by
      unfold Grid.size
      positivity
    have hpow : (G.size : ℝ)^A.card = Real.exp ((A.card : ℝ)*Real.log G.size) := by
      rw [Real.exp_nat_mul, Real.exp_log hs]
    calc
      _ ≤ (G.size : ℝ)^A.card *
          Real.exp (-(A.card : ℝ)*Real.log G.size + J.cost-H.cost +
            Real.log 4*(A.card : ℝ)*G.b) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = Real.exp (J.cost-H.cost + Real.log 4*(A.card : ℝ)*G.b) := by
        rw [hpow, ← Real.exp_add]
        congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hAk : (A.card : ℝ) ≤ k := by exact_mod_cast (show A.card ≤ k by simpa using Finset.card_le_univ A)
        have hc := J.cost_le
        have hn := H.cost_nonneg
        have hb : (0 : ℝ) ≤ G.b := by positivity
        have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
        have hbk := mul_le_mul_of_nonneg_left hAk hb
        have hlk := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAk hl) hb
        push_cast at hc
        nlinarith
  · have hn : ∀ ω, ¬ (H.Compatible ω ∧ G.endpointEvent x y A ω) := by
      simpa only [not_exists] using he
    simp only [conditionalEndpointProbability, ite_eq_right (hn _), Finset.sum_const_zero,
      zero_div, mul_zero]
    exact (Real.exp_pos _).le

/- Source 04:eq8, with an explicit absolute constant in place of O(·).
Only valid input placements are needed; impossible output events contribute zero. -/
theorem scaled_placementKernel_abs_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    |(G.size : ℝ)^k * H.placementKernel x y (fun j => lineLaw (G.bits j) z hz hz')| ≤
      (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
  classical
  have hs : (G.size : ℝ) ≠ 0 := by
    unfold Grid.size
    positivity
  rw [placementKernel, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        |(-1 : ℝ)^(k-A.card) * (G.size : ℝ)^A.card *
          H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz')| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        (G.size : ℝ)^A.card * H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz') := by
      apply Finset.sum_congr rfl
      intro A _
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity : 0 ≤ (G.size : ℝ)^A.card),
        abs_of_nonneg (H.extraProbability_nonneg _ _ _ _)]
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
      apply Finset.sum_le_sum
      intro A _
      exact H.scaled_extraProbability_le x y hx A hz hz' hlo hhi
    _ = _ := by simp

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

def ValidOutput (H : G.Holes h) (y : Fin k → G.Slot) : Prop :=
  Function.Injective y ∧ ∀ i a, y i ≠ H.path a (Fin.last G.b)

/- Counting-measure Hilbert--Schmidt square on the actual free placements. -/
def placementHSsq (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : ℝ :=
  ∑ x : Fin k → G.Slot, ∑ y : Fin k → G.Slot,
    if H.ValidInput x ∧ H.ValidOutput y then (H.placementKernel x y μ)^2 else 0

/- The full endpoint product weight is exactly s^(-2k). -/
theorem endpoint_productMass (p : Fin k → G.Slot × G.Slot) :
    Coverage.productMass G.endpointWeight p = (G.size : ℝ)⁻¹^(2*k) := by
  simp [Coverage.productMass, Grid.endpointWeight, FiniteLaw.uniform,
    Fintype.card_prod, G.card_slot, mul_pow, pow_mul, mul_comm, pow_two]

/- Rewriting the counting norm using independent full-grid endpoints never
conditions the auxiliary trajectories on being valid placements. -/
theorem placementHSsq_eq_full (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.placementHSsq (k := k) μ =
      ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
  classical
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hterm (p : Fin k → G.Slot × G.Slot) :
      (if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0) =
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
    rw [endpoint_productMass]
    split_ifs
    · have hid : (G.size : ℝ)⁻¹^(2*k) * ((G.size : ℝ)^k)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm k 2, ← mul_pow, inv_mul_cancel₀ hs, one_pow]
      rw [mul_pow, ← mul_assoc, hid, one_mul]
    · simp
  let e : (Fin k → G.Slot × G.Slot) ≃ ((Fin k → G.Slot) × (Fin k → G.Slot)) :=
    ⟨fun p => (fun i => (p i).1, fun i => (p i).2),
      fun p i => (p.1 i, p.2 i), fun _ => rfl, fun _ => rfl⟩
  calc
    _ = ∑ p : (Fin k → G.Slot) × (Fin k → G.Slot),
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ p : Fin k → G.Slot × G.Slot,
        if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0 :=
      (Equiv.sum_comp e (fun p =>
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0)).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => hterm p)

/- Source 04:eqs8--9 combined, with an explicit counting HS estimate.
This is the direct, unweakened many-coordinate sparse-kernel estimate. -/
theorem placementHSsq_le (H : G.Holes h) (hH : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (hsmall : ((k+h : ℕ) : ℝ)*G.lineSharingRate ≤ 1) :
    H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz') ≤
      ((2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b))^2 *
        ((2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.lineSharingRate)^((k : ℝ)/2)) := by
  classical
  let μ := fun j => lineLaw (G.bits j) z hz hz'
  let M := (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b)
  have hM : 0 ≤ M := by positivity
  rw [H.placementHSsq_eq_full]
  calc
    _ ≤ ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p *
          if H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ ≠ 0 then M^2 else 0 := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _
        (Coverage.productMass_nonneg G.endpointWeight G.endpointWeight_nonneg p)
      by_cases he : H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ = 0
      · simp only [μ] at he
        simp [μ, he]
      · rw [ite_eq_left he]
        split_ifs with hp
        · have h := H.scaled_placementKernel_abs_le (fun i => (p i).1) (fun i => (p i).2) hp.1 hz hz' hlo hhi
          have hh := (sq_le_sq₀ (abs_nonneg _) hM).mpr h
          simpa only [sq_abs] using hh
        · positivity
    _ = M^2 * Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
        H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ ≠ 0) := by
      rw [Coverage.probability, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (H.probability_nonzero_placementKernel_le hH z hz hz' hsmall) (sq_nonneg M)

end CoordinateSweeps.Grid.Holes

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
end
end
open scoped Matrix.Norms.L2Operator

end OAI
