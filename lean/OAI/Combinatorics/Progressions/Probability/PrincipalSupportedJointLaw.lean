import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable {A : Type*} [Fintype A] (e : A → D) (he : Function.Injective e)
variable (hsize : ∀ a b v, (Fintype.card α + 1) * q ≤ L ⟨e a, b, v⟩)

local notation "conditioned" => FiniteProbabilityWeights.toPMF (FiniteProbabilityWeights.condition
  (principalTupleWeights (α := α) B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell)
local notation "sources" => fun a => principalSupportedAxisSources B h L hL q hq r (e a) (hsize a)

include he in
theorem principalSupportedResidue_axes_marginal :
    (conditioned).map (fun y a (b : B (e a)) (v : Fin (h (e a))) => y ⟨e a, b, v⟩) =
      dependentProductPMF (fun a => dependentProductPMF (fun b =>
        dependentProductPMF (fun v => ((sources) a b v).source.toPMF))) := by
  have hinj : Function.Injective
      (fun t : Σ a : A, B (e a) × Fin (h (e a)) => (⟨e t.1, t.2⟩ : PrincipalTupleIndex B h)) := by
    rintro ⟨a, u⟩ ⟨b, v⟩ hab
    have hab' : a = b := he (congrArg Sigma.fst hab)
    subst b
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
  have hp := principalSupportedResidue_marginal B h L hL q hq r hcell
    (fun t : Σ a : A, B (e a) × Fin (h (e a)) => ⟨e t.1, t.2⟩) hinj
    (fun t => hsize t.1 t.2.1 t.2.2)
  have ht := congrArg (fun p => p.map (fun x a b v => x ⟨a, b, v⟩)) hp
  rw [PMF.map_comp] at ht
  exact ht.trans (dependentProductPMF_sigma_curry (fun a b v => ((sources) a b v).source.toPMF))

include hq he hsize in
theorem principalSupportedResidue_axes_bind
    {Y : A → Type*} [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)]
    [∀ a, MeasurableSingletonClass (Y a)]
    (F : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a, b, v⟩)) →
      PMF (Y a)) :
    (conditioned).bind (fun y => dependentProductPMF (fun a => F a (fun b v => y ⟨e a, b, v⟩))) =
      dependentProductPMF (fun a => (conditioned).bind (fun y => F a (fun b v => y ⟨e a, b, v⟩))) := by
  have hj := principalSupportedResidue_axes_marginal B h L hL q hq r hcell e he hsize
  have ht := congrArg (fun p => p.bind (fun x => dependentProductPMF (fun a => F a (x a)))) hj
  rw [PMF.bind_map] at ht
  have hbind := dependentProductPMF_bind_finite
    (fun a => dependentProductPMF (fun b =>
      dependentProductPMF (fun v => ((sources) a b v).source.toPMF))) F
  refine ht.trans (hbind.trans ?_)
  apply congrArg dependentProductPMF
  funext a
  have ha := principalSupportedResidue_axis_marginal B h L hL q hq r (e a) (hsize a) hcell
  have hb := congrArg (fun p => p.bind (F a)) ha
  rw [PMF.bind_map] at hb
  exact hb.symm

end Erdos3

end

end OAI
