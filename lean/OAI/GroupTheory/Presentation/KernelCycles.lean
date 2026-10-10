import OAI.Topology.EilenbergGanea.PresentationAlignment
import OAI.AlgebraicTopology.Cubical.PathChains
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff



namespace EilenbergGanea.KernelCycles
open Classical
variable {G A : Type*} [Group G] (a : A → G)
abbrev Kernel := (wordValue a).ker
abbrev AbKernel := Additive (Abelianization (Kernel a))

def kernelChainHom : Kernel a →* Multiplicative (cycles a) where
  toFun w := Multiplicative.ofAdd ⟨pathChain a w.val 1,by
    change edgeBoundary a (pathChain a w.val 1) = 0
    rw [edgeBoundary_pathChain,w.property,mul_one,sub_self]⟩
  map_one' := by apply (Equiv.refl _ : Multiplicative (cycles a) ≃ cycles a).injective; apply Subtype.ext; exact pathChain_one a 1
  map_mul' w z := by
    apply (Equiv.refl _ : Multiplicative (cycles a) ≃ cycles a).injective
    apply Subtype.ext
    change pathChain a (w.val*z.val) 1 = pathChain a w.val 1 + pathChain a z.val 1
    rw [pathChain_mul,w.property,mul_one]

def abKernelToCycles : AbKernel a →ₗ[ℤ] cycles a :=
  (Abelianization.lift (kernelChainHom a)).toAdditive.toIntLinearMap

@[simp] theorem abKernelToCycles_of (w : Kernel a) :
    (abKernelToCycles a (Additive.ofMul (Abelianization.of w))).val = pathChain a w.val 1 := rfl

variable (t : G → FreeGroup A) (ht : ∀ g, wordValue a (t g) = g)

def bridge (w : FreeGroup A) (g : G) : Kernel a :=
  ⟨t g * w * (t (g * wordValue a w))⁻¹,by
    change wordValue a (t g * w * (t (g * wordValue a w))⁻¹) = 1
    simp only [map_mul,map_inv,ht]
    group⟩

@[simp] theorem bridge_one (g : G) : bridge a t ht 1 g = 1 := by
  apply Subtype.ext
  simp [bridge]

theorem bridge_mul (w z : FreeGroup A) (g : G) :
    bridge a t ht (w*z) g = bridge a t ht w g * bridge a t ht z (g * wordValue a w) := by
  apply Subtype.ext
  simp only [bridge,Subgroup.coe_mul,map_mul,mul_assoc]
  group

theorem bridge_inv (w : FreeGroup A) (g : G) :
    bridge a t ht w⁻¹ g = (bridge a t ht w (g * (wordValue a w)⁻¹))⁻¹ := by
  apply Subtype.ext
  simp only [bridge,Subgroup.coe_inv,map_inv]
  simp only [inv_mul_cancel_right]
  group

def bridgeAb (w : FreeGroup A) (g : G) : AbKernel a :=
  Additive.ofMul (Abelianization.of (bridge a t ht w g))
@[simp] theorem bridgeAb_one (g : G) : bridgeAb a t ht 1 g = 0 := by simp [bridgeAb]
theorem bridgeAb_mul (w z : FreeGroup A) (g : G) :
    bridgeAb a t ht (w*z) g = bridgeAb a t ht w g + bridgeAb a t ht z (g * wordValue a w) := by
  unfold bridgeAb
  rw [bridge_mul,map_mul]
  rfl

theorem bridgeAb_inv (w : FreeGroup A) (g : G) :
    bridgeAb a t ht w⁻¹ g = -bridgeAb a t ht w (g * (wordValue a w)⁻¹) := by
  unfold bridgeAb
  rw [bridge_inv,map_inv]
  rfl

def chainsToKernel : BasedChains G A →ₗ[ℤ] AbKernel a :=
  Finsupp.linearCombination ℤ (fun p => bridgeAb a t ht (FreeGroup.of p.2) p.1)

@[simp] theorem chainsToKernel_single (g : G) (x : A) (n : ℤ) :
    chainsToKernel a t ht (Finsupp.single (g,x) n) = n • bridgeAb a t ht (FreeGroup.of x) g := by
  simp [chainsToKernel]

theorem chainsToKernel_pathChain (w : FreeGroup A) (g : G) :
    chainsToKernel a t ht (pathChain a w g) = bridgeAb a t ht w g := by
  induction w using FreeGroup.induction_on generalizing g with
  | one => simp
  | of x => simp
  | inv_of x => rw [pathChain_inv,map_neg,bridgeAb_inv]; simp
  | mul w z hw hz => rw [pathChain_mul,map_add,hw,hz,bridgeAb_mul]

theorem bridgeAb_kernel (w : Kernel a) : bridgeAb a t ht w.val 1 = Additive.ofMul (Abelianization.of w) := by
  let u : Kernel a := ⟨t 1,ht 1⟩
  have he : bridge a t ht w.val 1 = u*w*u⁻¹ := by
    apply Subtype.ext
    change t 1 * w.val * (t (1 * wordValue a w.val))⁻¹ = t 1 * w.val * (t 1)⁻¹
    rw [w.property,mul_one]
  change Additive.ofMul (Abelianization.of (bridge a t ht w.val 1)) = _
  apply congrArg Additive.ofMul
  rw [he,map_mul,map_mul,map_inv]
  simp [mul_comm]

theorem chains_kernel_inverse (w : AbKernel a) :
    chainsToKernel a t ht (abKernelToCycles a w).val = w := by
  revert w
  change ∀ w : Abelianization (Kernel a),
    chainsToKernel a t ht (abKernelToCycles a (Additive.ofMul w)).val = Additive.ofMul w
  intro w
  induction w using QuotientGroup.induction_on with
  | H w =>
    change chainsToKernel a t ht (abKernelToCycles a (Additive.ofMul (Abelianization.of w))).val = Additive.ofMul (Abelianization.of w)
    rw [abKernelToCycles_of,chainsToKernel_pathChain,bridgeAb_kernel]

def anchors : (G →₀ ℤ) →ₗ[ℤ] BasedChains G A := Finsupp.linearCombination ℤ (fun g => pathChain a (t g) 1)

theorem bridge_chain (w : FreeGroup A) (g : G) :
    pathChain a (bridge a t ht w g).val 1 =
      pathChain a (t g) 1 + pathChain a w g - pathChain a (t (g * wordValue a w)) 1 := by
  change pathChain a (t g*w*(t (g*wordValue a w))⁻¹) 1 = _
  rw [pathChain_mul,pathChain_mul,pathChain_inv]
  simp only [ht,map_mul,one_mul,mul_inv_cancel,sub_eq_add_neg]

theorem kernel_chains_identity (c : BasedChains G A) :
    (abKernelToCycles a (chainsToKernel a t ht c)).val = c - anchors a t (edgeBoundary a c) := by
  have he : (cycles a).subtype.comp ((abKernelToCycles a).comp (chainsToKernel a t ht)) =
      LinearMap.id - (anchors a t).comp (edgeBoundary a) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,x⟩ n
    simp only [LinearMap.comp_apply,chainsToKernel_single,map_smul,LinearMap.sub_apply,
      LinearMap.id_apply,edgeBoundary_single]
    change n • pathChain a (bridge a t ht (FreeGroup.of x) g).val 1 =
      Finsupp.single (g,x) n - n • anchors a t (Finsupp.single (g*a x) 1 - Finsupp.single g 1)
    rw [bridge_chain]
    simp only [pathChain_of,wordValue,FreeGroup.lift_apply_of,anchors,map_sub,Finsupp.linearCombination_single,one_smul]
    rw [← Finsupp.smul_single_one (g,x) n]
    simp only [smul_add,smul_sub]
    abel
  exact LinearMap.congr_fun he c

/-- The exact integral abelianized-kernel/Cayley-cycle comparison, with its
literal Fox/path-chain coefficients. No graph realization is assumed. -/
def abKernelCycleEquiv : AbKernel a ≃ₗ[ℤ] cycles a :=
  LinearEquiv.ofLinearMap (abKernelToCycles a) ((chainsToKernel a t ht).comp (cycles a).subtype)
    (by apply LinearMap.ext; intro c; apply Subtype.ext; exact (kernel_chains_identity a t ht c.val).trans (by rw [c.property,map_zero,sub_zero]; rfl))
    (by apply LinearMap.ext; intro w; exact chains_kernel_inverse a t ht w)

end EilenbergGanea.KernelCycles


namespace EilenbergGanea.PresentationAlgebra
open Classical
universe u
variable {H : Type u} {G R : Type*} [Group H] [Group G]
variable (φ : H →* G) (hf : Function.Surjective φ)
variable (r : R → H) (hr : ∀ j, φ (r j) = 1)

include hf in
/-- A kernel basis with genuine conjugate coefficients becomes the literal
Cayley relator-chain basis after choosing a free generating alphabet. -/
theorem boundary_basis_of_free [IsFreeGroup H]
    (hp : φ.ker = Subgroup.normalClosure (Set.range r))
    (B : BasedChains G R ≃ₗ[ℤ] Additive (Abelianization φ.ker))
    (hB : ∀ g j, ∃ k : H, φ k = g ∧ B (Finsupp.single (g,j) 1) =
      Additive.ofMul (Abelianization.of (⟨k*r j*k⁻¹,by
        change φ (k*r j*k⁻¹) = 1
        rw [map_mul,map_mul,map_inv,hr,mul_one,mul_inv_cancel]⟩ : φ.ker))) :
    ∃ (A : Type u) (a : A → G), Function.Surjective (wordValue a) ∧
      ∃ (s : R → FreeGroup A), (∀ j, wordValue a (s j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range s) ∧
        ∃ E : BasedChains G R ≃ₗ[ℤ] cycles a,
          ∀ c, (E c : BasedChains G A) = relatorChainMap a s c := by
  let A := IsFreeGroup.Generators H
  let e : FreeGroup A ≃* H := IsFreeGroup.mulEquiv H
  let a : A → G := fun x => φ (e (FreeGroup.of x))
  have ha : wordValue a = φ.comp e.toMonoidHom := by
    apply FreeGroup.ext_hom
    intro x
    simp only [wordValue,FreeGroup.lift_apply_of,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,a]
  have hsur : Function.Surjective (wordValue a) := by rw [ha]; exact hf.comp e.surjective
  let s : R → FreeGroup A := fun j => e.symm (r j)
  have hs : ∀ j, wordValue a (s j) = 1 := by
    intro j
    rw [ha]
    change φ (e (e.symm (r j))) = 1
    rw [e.apply_symm_apply,hr]
  have hnormal : (wordValue a).ker = Subgroup.normalClosure (Set.range s) := by
    change (wordValue a).ker = Subgroup.normalClosure (Set.range (e.symm ∘ r))
    rw [Set.range_comp]
    change (wordValue a).ker = Subgroup.normalClosure (e.symm.toMonoidHom '' Set.range r)
    rw [← Subgroup.map_normalClosure _ e.symm.toMonoidHom e.symm.surjective,← hp]
    ext w
    constructor
    · intro hw
      refine ⟨e w,?_,e.symm_apply_apply w⟩
      change φ (e w) = 1
      change (φ.comp e.toMonoidHom) w = 1
      rw [← ha]
      exact hw
    · rintro ⟨v,hv,rfl⟩
      change wordValue a (e.symm v) = 1
      rw [ha]
      exact (congrArg φ (e.apply_symm_apply v)).trans hv
  let ke : φ.ker ≃* (wordValue a).ker :=
    { toFun := fun k => ⟨e.symm k.val,by change wordValue a (e.symm k.val) = 1; rw [ha]; exact (congrArg φ (e.apply_symm_apply k.val)).trans k.property⟩
      invFun := fun k => ⟨e k.val,by change (φ.comp e.toMonoidHom) k.val = 1; rw [← ha]; exact k.property⟩
      left_inv := fun k => Subtype.ext (e.apply_symm_apply k.val)
      right_inv := fun k => Subtype.ext (e.symm_apply_apply k.val)
      map_mul' := fun k l => Subtype.ext (map_mul e.symm _ _) }
  let t : G → FreeGroup A := fun g => (hsur g).choose
  have ht : ∀ g, wordValue a (t g) = g := fun g => (hsur g).choose_spec
  let E : BasedChains G R ≃ₗ[ℤ] cycles a :=
    B.trans (ke.abelianizationCongr.toAdditive.toIntLinearEquiv.trans
      (KernelCycles.abKernelCycleEquiv a t ht))
  refine ⟨A,a,hsur,s,hs,hnormal,E,?_⟩
  have he : (cycles a).subtype.comp E.toLinearMap = relatorChainMap a s := by
    apply Finsupp.lhom_ext
    rintro ⟨g,j⟩ n
    rw [← Finsupp.smul_single_one (g,j) n,map_smul,map_smul]
    congr 1

    obtain ⟨k,hk,hkj⟩ := hB g j
    change (E (Finsupp.single (g,j) 1)).val = _
    change ((KernelCycles.abKernelCycleEquiv a t ht)
      (ke.abelianizationCongr.toAdditive.toIntLinearEquiv (B (Finsupp.single (g,j) 1)))).val = _
    rw [hkj]
    change pathChain a (e.symm (k*r j*k⁻¹)) 1 = relatorChainMap a s (Finsupp.single (g,j) 1)
    rw [map_mul,map_mul,map_inv,pathChain_conjugate a _ _ (hs j),one_mul,relatorChainMap_single,one_smul]
    congr 1
    rw [ha]
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using hk
  intro c
  exact LinearMap.congr_fun he c

include hf in
/-- The same literal kernel-basis criterion is invariant under a specified
isomorphism of the quotient group. No new presentation is assumed. -/
theorem boundary_basis_of_free_target [IsFreeGroup H]
    (hp : φ.ker = Subgroup.normalClosure (Set.range r))
    (B : BasedChains G R ≃ₗ[ℤ] Additive (Abelianization φ.ker))
    (hB : ∀ g j, ∃ k : H, φ k = g ∧ B (Finsupp.single (g,j) 1) =
      Additive.ofMul (Abelianization.of (⟨k*r j*k⁻¹,by
        change φ (k*r j*k⁻¹) = 1
        rw [map_mul,map_mul,map_inv,hr,mul_one,mul_inv_cancel]⟩ : φ.ker)))
    {K : Type*} [Group K] (χ : G ≃* K) :
    ∃ (A : Type u) (a : A → K), Function.Surjective (wordValue a) ∧
      ∃ (s : R → FreeGroup A), (∀ j, wordValue a (s j) = 1) ∧
        (wordValue a).ker = Subgroup.normalClosure (Set.range s) ∧
        ∃ E : BasedChains K R ≃ₗ[ℤ] cycles a,
          ∀ c, (E c : BasedChains K A) = relatorChainMap a s c := by
  let ψ := χ.toMonoidHom.comp φ
  have hψ : Function.Surjective ψ := χ.surjective.comp hf
  have hrψ : ∀ j, ψ (r j) = 1 := by intro j; change χ (φ (r j)) = 1; rw [hr,map_one]
  have hk : ψ.ker = φ.ker := by
    ext k
    change χ (φ k) = 1 ↔ φ k = 1
    exact χ.map_eq_one_iff
  let ke : φ.ker ≃* ψ.ker :=
    { toFun := fun k => ⟨k.val,by rw [hk]; exact k.property⟩
      invFun := fun k => ⟨k.val,by rw [← hk]; exact k.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let B' : BasedChains K R ≃ₗ[ℤ] Additive (Abelianization ψ.ker) :=
    (Finsupp.domLCongr (Equiv.prodCongr χ.symm.toEquiv (Equiv.refl R))).trans
      (B.trans ke.abelianizationCongr.toAdditive.toIntLinearEquiv)
  apply boundary_basis_of_free ψ hψ r hrψ (hk.trans hp) B'
  intro g j
  obtain ⟨k,hk,hkj⟩ := hB (χ.symm g) j
  refine ⟨k,?_,?_⟩
  · change χ (φ k) = g
    rw [hk,χ.apply_symm_apply]
  · simp only [B',LinearEquiv.trans_apply,Finsupp.domLCongr_single]
    change ke.abelianizationCongr.toAdditive.toIntLinearEquiv
      (B (Finsupp.single (χ.symm g,j) 1)) = _
    rw [hkj]
    rfl

end EilenbergGanea.PresentationAlgebra


end

end OAI
