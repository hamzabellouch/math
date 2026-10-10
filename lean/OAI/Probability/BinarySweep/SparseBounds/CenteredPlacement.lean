import Mathlib
import OAI.Probability.BinarySweep.Conditional.AugmentedComplement

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

omit [DecidableEq I] [Fintype X] [DecidableEq X] in
lemma subPlacement_univ_injective :
    Function.Injective (subPlacement (X:=X) (Finset.univ : Finset I)) := by
  intro x y he
  ext i
  exact congrArg (fun t => t ⟨i,Finset.mem_univ _⟩) he

 def partialPlacement (A : Finset I) (g : Equiv.Perm X) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) where
  toFun v y := placementMarginal A v (movePlacement g⁻¹ (subPlacement A y))
  map_add' v w := by ext y; simp only [map_add,Pi.add_apply]
  map_smul' c v := by ext y; simp only [map_smul,RingHom.id_apply,Pi.smul_apply]

omit [DecidableEq I] in
lemma partialPlacement_apply (A : Finset I) (g : Equiv.Perm X)
    (v : (I ↪ X) → ℂ) (y : I ↪ X) :
    partialPlacement A g v y = ∑x : I ↪ X,
      if subPlacement A (movePlacement g x)=subPlacement A y then v x else 0 := by
  simp only [partialPlacement,placementMarginal,LinearMap.coe_mk,AddHom.coe_mk,
    move_sub_eq_iff]

omit [DecidableEq I] in
lemma partialPlacement_univ (g : Equiv.Perm X) :
    partialPlacement (Finset.univ : Finset I) g = placementRep g := by
  apply LinearMap.ext
  intro v
  funext y
  change (∑x : I ↪ X,
    if subPlacement Finset.univ x=movePlacement g⁻¹ (subPlacement Finset.univ y)
    then v x else 0)=v (movePlacement g⁻¹ y)
  simp only [← subPlacement_move,subPlacement_univ_injective.eq_iff]
  simp

 def placementAverage (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) := ∑g, p g • placementRep g

 def partialPlacementAverage (A : Finset I) (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) := ∑g, p g • partialPlacement A g

 def centeredPlacement (s : ℂ) (p : Equiv.Perm X → ℂ) :
    ((I ↪ X) → ℂ) →ₗ[ℂ] ((I ↪ X) → ℂ) :=
  ∑A ∈ (Finset.univ : Finset I).powerset,
    ((-1:ℂ)^(Fintype.card I-A.card)*s^A.card/s^Fintype.card I) • partialPlacementAverage A p

lemma partialPlacement_specht_zero (μ : YoungDiagram) (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (g : G μ) (v : SpechtSpace μ) :
    partialPlacement A g (spechtPlacement μ v)=0 := by
  ext y
  change placementMarginal A (spechtPlacement μ v) _=0
  rw [spechtPlacement_marginal_zero μ A hA]
  rfl

lemma partialPlacementAverage_specht_zero (μ : YoungDiagram) (A : Finset (Tail μ))
    (hA : A≠Finset.univ) (p : G μ → ℂ) (v : SpechtSpace μ) :
    partialPlacementAverage A p (spechtPlacement μ v)=0 := by
  simp only [partialPlacementAverage,LinearMap.sum_apply,LinearMap.smul_apply,
    partialPlacement_specht_zero μ A hA,smul_zero,Finset.sum_const_zero]

theorem centeredPlacement_specht (μ : YoungDiagram) (s : ℂ) (hs : s≠0)
    (p : G μ → ℂ) (v : SpechtSpace μ) :
    centeredPlacement s p (spechtPlacement μ v) =
      placementAverage p (spechtPlacement μ v) := by
  unfold centeredPlacement
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  rw [Finset.sum_eq_single Finset.univ]
  · simp only [Finset.card_univ,Nat.sub_self,pow_zero,one_mul,
      div_self (pow_ne_zero _ hs),one_smul,partialPlacementAverage,
      partialPlacement_univ,placementAverage,LinearMap.sum_apply,LinearMap.smul_apply]
  · intro A _ hA
    rw [partialPlacementAverage_specht_zero μ A hA,smul_zero]
  · intro hn
    exact (hn (Finset.mem_powerset.mpr (Finset.Subset.refl _))).elim

lemma placementAverage_specht (μ : YoungDiagram) (p : G μ → ℂ) (v : SpechtSpace μ) :
    placementAverage p (spechtPlacement μ v)=
      spechtPlacement μ (∑g, p g • spechtRep μ g v) := by
  simp only [placementAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    spechtPlacement_intertwines]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

 def placementCoeffs : EuclideanSpace ℂ (I ↪ X) ≃ₗ[ℂ] ((I ↪ X) → ℂ) :=
  WithLp.linearEquiv 2 ℂ _
 def partialHilbert (A : Finset I) (g : Equiv.Perm X) :
    EuclideanSpace ℂ (I ↪ X) →ₗ[ℂ] EuclideanSpace ℂ (I ↪ X) :=
  placementCoeffs.symm.conj (partialPlacement A g)
 def partialKernel (A : Finset I) (g : Equiv.Perm X) : Matrix (I ↪ X) (I ↪ X) ℂ :=
  fun y x => if subPlacement A (movePlacement g x)=subPlacement A y then 1 else 0

omit [DecidableEq I] in
lemma partialKernel_toLin (A : Finset I) (g : Equiv.Perm X) :
    (partialKernel A g).toEuclideanLin=partialHilbert A g := by
  apply LinearMap.ext
  intro v
  apply (placementCoeffs (I:=I) (X:=X)).injective
  funext y
  change (∑x, partialKernel A g y x*v x)=partialPlacement A g (placementCoeffs v) y
  rw [partialPlacement_apply]
  apply Finset.sum_congr rfl
  intro x _
  dsimp [partialKernel]
  split_ifs <;> simp [placementCoeffs]

omit [Fintype I] [DecidableEq I] [Fintype X] in
lemma partialKernel_adjoint (A : Finset I) (g : Equiv.Perm X) :
    (partialKernel A g).conjTranspose=partialKernel A g⁻¹ := by
  ext y x
  have he : subPlacement A (movePlacement g y)=subPlacement A x ↔
      subPlacement A (movePlacement g⁻¹ x)=subPlacement A y := by
    rw [move_sub_eq_iff,← subPlacement_move]
    exact eq_comm
  simp only [Matrix.conjTranspose_apply,partialKernel,he]
  split_ifs <;> simp

omit [DecidableEq I] in
lemma partialHilbert_adjoint (A : Finset I) (g : Equiv.Perm X) :
    (partialHilbert A g).adjoint=partialHilbert A g⁻¹ := by
  rw [← partialKernel_toLin,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    partialKernel_adjoint,partialKernel_toLin]

 def centeredHilbert (s : ℝ) (p : Equiv.Perm X → ℂ) :
    EuclideanSpace ℂ (I ↪ X) →ₗ[ℂ] EuclideanSpace ℂ (I ↪ X) :=
  placementCoeffs.symm.conj (centeredPlacement (s:ℂ) p)

omit [DecidableEq I] in
lemma centeredHilbert_sum (s : ℝ) (p : Equiv.Perm X → ℂ) :
    centeredHilbert (I:=I) s p = ∑A ∈ (Finset.univ : Finset I).powerset,
      ((-1:ℂ)^(Fintype.card I-A.card)*(s:ℂ)^A.card/(s:ℂ)^Fintype.card I) •
        ∑g, p g • partialHilbert A g := by
  simp only [centeredHilbert,centeredPlacement,partialPlacementAverage,map_sum,map_smul,
    partialHilbert]

omit [DecidableEq I] in
lemma centeredHilbert_adjoint (s : ℝ) (p : Equiv.Perm X → ℂ) :
    (centeredHilbert (I:=I) s p).adjoint=centeredHilbert s (fun g => star (p g⁻¹)) := by
  simp only [centeredHilbert_sum,map_sum,map_smulₛₗ,partialHilbert_adjoint,
    map_div₀,map_mul,map_pow,map_neg,map_one,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro A _
  congr 1
  have he := Equiv.sum_comp (Equiv.inv (Equiv.Perm X)) (fun g => star (p g⁻¹) • partialHilbert A g)
  simp only [starRingEnd_apply]
  simpa only [Equiv.inv_apply,inv_inv] using he

 def spechtPlacementHilbert (μ : YoungDiagram) :
    SpechtHilbert μ →ₗ[ℂ] EuclideanSpace ℂ (Tail μ ↪ Cell μ) :=
  placementCoeffs.symm.toLinearMap.comp ((spechtPlacement μ).comp (spechtHilbertEquiv μ).symm.toLinearMap)

lemma spechtPlacementHilbert_injective (μ : YoungDiagram) :
    Function.Injective (spechtPlacementHilbert μ) :=
  placementCoeffs.symm.injective.comp ((spechtPlacement_injective μ).comp (spechtHilbertEquiv μ).symm.injective)

lemma centeredHilbert_specht (μ : YoungDiagram) (s : ℝ) (hs : s≠0)
    (p : G μ → ℂ) (v : SpechtHilbert μ) :
    centeredHilbert s p (spechtPlacementHilbert μ v)=
      spechtPlacementHilbert μ (Irrep.groupAverage (hilbertSpecht μ) p v) := by
  obtain ⟨u,rfl⟩ := (spechtHilbertEquiv μ).surjective v
  apply placementCoeffs.injective
  simp only [centeredHilbert,spechtPlacementHilbert,LinearMap.comp_apply,
    LinearEquiv.conj_apply,LinearEquiv.coe_coe,LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  change centeredPlacement (s:ℂ) p (spechtPlacement μ u)=
    spechtPlacement μ ((spechtHilbertEquiv μ).symm (Irrep.groupAverage (hilbertSpecht μ) p
      (spechtHilbertEquiv μ u)))
  rw [centeredPlacement_specht μ _ (by exact_mod_cast hs),placementAverage_specht]
  congr 1
  simp only [Irrep.groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  change spechtRep μ g u=(spechtHilbertEquiv μ).symm
    ((spechtHilbertEquiv μ) (spechtRep μ g ((spechtHilbertEquiv μ).symm ((spechtHilbertEquiv μ) u))))
  simp only [LinearEquiv.symm_apply_apply]

end BinaryCoordinateSweeps.Young

end

end OAI
