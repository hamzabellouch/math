import OAI.Dynamics.SmoothObstruction.ProductCoordinates
import OAI.Dynamics.SmoothObstruction.MinorTransfer
import OAI.Dynamics.SmoothObstruction.AsymptoticSplitting

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EndpointFrame
open Set Matrix
open scoped EuclideanGeometry
variable {d p : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Finite endpoint coordinates are selected from a genuine ambient orthonormal
basis, including the empty and full-dimensional endpoint groups. -/
theorem exists_frame (W : Submodule ℝ E) (hdim : Module.finrank ℝ W=p) :
    ∃ (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p),
      (∀ j∈r,b j∈W) ∧ (∀ j∉r,b j∈Wᗮ) ∧
      (∀ x∈W,∀ j∉r,b.repr x j=0) := by
  classical
  let V : Bool → Submodule ℝ E := fun q => if q then W else Wᗮ
  have hV : DirectSum.IsInternal V := by
    apply (DirectSum.isInternal_submodule_iff_isCompl V (i:=true) (j:=false) (by decide)
      (by ext q; cases q <;> simp)).mpr
    exact W.isCompl_orthogonal
  have horth : OrthogonalFamily ℝ (fun q => V q) (fun q => (V q).subtypeₗᵢ) := by
    intro i j hij x y
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Submodule.inner_left_of_mem_orthogonal y.property x.property
    · exact Submodule.inner_right_of_mem_orthogonal x.property y.property
    · exact (hij rfl).elim
  have hn : Module.finrank ℝ E=d := finrank_euclideanSpace_fin
  let b := hV.subordinateOrthonormalBasis hn horth
  let c : Fin d → Bool := fun j => hV.subordinateOrthonormalBasisIndex hn j horth
  let r₀ : Finset (Fin d) := Finset.univ.filter (fun j => c j=true)
  have hc : r₀.card=p := by
    exact (hV.card_filter_subordinateOrthonormalBasisIndex_eq hn horth true).trans hdim
  let r : powersetCard (Fin d) p := ⟨r₀,hc⟩
  have hb (j : Fin d) : b j∈V (c j) :=
    hV.subordinateOrthonormalBasis_subordinate hn j horth
  have hmem (j : Fin d) : j∈r ↔ c j=true := by
    change j∈r₀ ↔ c j=true
    simp only [r₀,Finset.mem_filter,Finset.mem_univ,true_and]
  have hy (j : Fin d) (hj : j∈r) : b j∈W := by
    simpa only [(hmem j).mp hj,V,ite_true] using hb j
  have hz (j : Fin d) (hj : j∉r) : b j∈Wᗮ := by
    have ht : c j=false := Bool.eq_false_of_not_eq_true (fun h => hj ((hmem j).mpr h))
    simpa only [ht,V,Bool.false_eq_true,ite_false] using hb j
  refine ⟨b,r,hy,hz,?_⟩
  intro x hx j hj
  rw [b.repr_apply_apply]
  exact Submodule.inner_left_of_mem_orthogonal hx (hz j hj)

/-- The actual selected orthonormal coordinates, not a formal minor proxy. -/
noncomputable def coordinates (b : OrthonormalBasis (Fin d) ℝ E)
    (r : powersetCard (Fin d) p) : E →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap {
    toFun x := WithLp.toLp 2 (fun i => b.repr x (powersetCard.ofFinEmbEquiv.symm r i))
    map_add' x y := by ext i; simp
    map_smul' c x := by ext i; simp }

@[simp] lemma coordinates_apply (b : OrthonormalBasis (Fin d) ℝ E)
    (r : powersetCard (Fin d) p) (x : E) (i : Fin p) :
    coordinates b r x i=b.repr x (powersetCard.ofFinEmbEquiv.symm r i) := rfl

lemma coordinates_projection (W : Submodule ℝ E)
    (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (x : E) :
    coordinates b r (W.starProjection x)=coordinates b r x := by
  ext i
  simp only [coordinates_apply,b.repr_apply_apply]
  have hi : powersetCard.ofFinEmbEquiv.symm r i∈r :=
    (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem r _).mp ⟨i,rfl⟩
  have hh := W.inner_orthogonalProjectionOnto_eq_of_mem_left
    (⟨b (powersetCard.ofFinEmbEquiv.symm r i),hr _ hi⟩ : W) x
  exact hh

/-- Endpoint-coordinate equality is precisely the reference projected
endpoint datum used by the genuine boundary-value problem. -/
lemma coordinates_eq_iff (W : Submodule ℝ E)
    (b : OrthonormalBasis (Fin d) ℝ E) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hz : ∀ x∈W,∀ j∉r,b.repr x j=0) (x y : E) :
    coordinates b r x=coordinates b r y ↔ W.starProjection x=W.starProjection y := by
  classical
  constructor
  · intro h
    apply b.repr.injective
    ext j
    by_cases hj : j∈r
    · obtain ⟨i,rfl⟩ := (powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem r j).mpr hj
      have he := (coordinates_projection W b r hr x).trans
        (h.trans (coordinates_projection W b r hr y).symm)
      exact congrArg (fun z : EuclideanSpace ℝ (Fin p) => z i) he
    · rw [hz _ (W.starProjection_apply_mem x) _ hj,hz _ (W.starProjection_apply_mem y) _ hj]
  · intro h
    rw [←coordinates_projection W b r hr x,←coordinates_projection W b r hr y,h]
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ProductBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
lemma blockMap_basis_inl (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (i : ι) :
    blockMap U V h bU bV (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inl i))=bU i := by
  classical
  rw [blockMap_apply]
  have he : EuclideanSpace.sumEquivProd (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inl i))=
      (EuclideanSpace.basisFun ι ℝ i,0) := by
    ext j <;> simp [EuclideanSpace.basisFun_apply,EuclideanSpace.sumEquivProd]
  rw [he]
  simp only [map_zero,Submodule.coe_zero,add_zero]
  exact congrArg Subtype.val (bU.repr.symm_apply_eq.mpr (bU.repr_self i).symm)

lemma blockMap_basis_inr (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis ι ℝ U) (bV : OrthonormalBasis κ ℝ V) (i : κ) :
    blockMap U V h bU bV (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inr i))=bV i := by
  classical
  rw [blockMap_apply]
  have he : EuclideanSpace.sumEquivProd (EuclideanSpace.basisFun (ι⊕κ) ℝ (Sum.inr i))=
      (0,EuclideanSpace.basisFun κ ℝ i) := by
    ext j <;> simp [EuclideanSpace.basisFun_apply,EuclideanSpace.sumEquivProd]
  rw [he]
  simp only [map_zero,Submodule.coe_zero,zero_add]
  exact congrArg Subtype.val (bV.repr.symm_apply_eq.mpr (bV.repr_self i).symm)
end SmoothObstruction.ProductBasis

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

noncomputable def joint (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (f g : E → E) (x : E) : F :=
  EuclideanSpace.sumEquivProd.symm (coordinates bF rF (f x),coordinates bP rP (g x))

noncomputable def jointLinear (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) : E →L[ℝ] F :=
  EuclideanSpace.sumEquivProd.symm.toContinuousLinearMap.comp
    (((coordinates bF rF).comp A).prod ((coordinates bP rP).comp B))

lemma joint_hasFDerivAt (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    {f g : E → E} {x : E} {A B : E →L[ℝ] E}
    (hf : HasFDerivAt f A x) (hg : HasFDerivAt g B x) :
    HasFDerivAt (joint bF bP rF rP f g) (jointLinear bF bP rF rP A B) x := by
  exact (EuclideanSpace.sumEquivProd.symm.hasFDerivAt).comp x
    (((coordinates bF rF).hasFDerivAt.comp x hf).prodMk
      ((coordinates bP rP).hasFDerivAt.comp x hg))

lemma joint_matrix (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
    (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin p ⊕ Fin q) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin p ⊕ Fin q) ℝ).toBasis
      ((jointLinear bF bP rF rP A B).comp (blockMap U V h bU bV).toContinuousLinearMap).toLinearMap=
    Matrix.fromBlocks (endpointMatrix bF p rF A (fun i => (bU i:E)))
      (endpointMatrix bF p rF A (fun i => (bV i:E)))
      (endpointMatrix bP q rP B (fun i => (bU i:E)))
      (endpointMatrix bP q rP B (fun i => (bV i:E))) := by
  have hL (j : Fin p) : blockMap U V h bU bV (EuclideanSpace.single (Sum.inl j) 1)=(bU j:E) :=
    by simpa only [EuclideanSpace.basisFun_apply] using blockMap_basis_inl U V h bU bV j
  have hR (j : Fin q) : blockMap U V h bU bV (EuclideanSpace.single (Sum.inr j) 1)=(bV j:E) :=
    by simpa only [EuclideanSpace.basisFun_apply] using blockMap_basis_inr U V h bU bV j
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [LinearMap.toMatrix_apply,jointLinear,hL,hR,
      endpointMatrix,EuclideanSpace.sumEquivProd]

/-- The determinant of the actual joint endpoint differential in the common
product input coordinates is exactly the block determinant estimated by the
maximal-minor algebra. No leading volume lower floor is asserted. -/
lemma joint_det (U V : Submodule ℝ E) (h : IsCompl U V)
    (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
    (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    (A B : E →L[ℝ] E) :
    ((jointLinear bF bP rF rP A B).comp (blockMap U V h bU bV).toContinuousLinearMap).det=
    (Matrix.fromBlocks (endpointMatrix bF p rF A (fun i => (bU i:E)))
      (endpointMatrix bF p rF A (fun i => (bV i:E)))
      (endpointMatrix bP q rP B (fun i => (bU i:E)))
      (endpointMatrix bP q rP B (fun i => (bV i:E)))).det := by
  rw [←joint_matrix U V h bU bV bF bP rF rP A B,LinearMap.det_toMatrix]
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def derivative (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) : (E×E) ≃L[ℝ] (E×E) :=
  ((A.prodCongr B).trans σ).trans (C.prodCongr D).symm

/-- Smooth local solution of all four endpoint equations, with its ACTUAL
nondegenerate derivative. This statement is insensitive to zero-dimensional
endpoint groups and keeps all four endpoint derivatives separate. -/
theorem local_branch (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
    (A B C D : E ≃L[ℝ] E) (σ : (E×E) ≃L[ℝ] (E×E))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ (A : E →L[ℝ] E) x)
    (hB : HasFDerivAt f₁ (B : E →L[ℝ] E) y)
    (hC : HasFDerivAt g₀ (C : E →L[ℝ] E) z)
    (hD : HasFDerivAt g₁ (D : E →L[ℝ] E) w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y))) :
    ∃ Φ : E×E → E×E, Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      HasFDerivAt Φ (derivative A B C D σ : (E×E) →L[ℝ] (E×E)) (x,y) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  let F := Prod.map f₀ f₁
  let G := Prod.map g₀ g₁
  have hF : ContDiffAt ℝ ∞ F (x,y) := hf₀.prodMap hf₁
  have hG : ContDiffAt ℝ ∞ G (z,w) := hg₀.prodMap hg₁
  have hFd : HasFDerivAt F (A.prodCongr B : (E×E) →L[ℝ] (E×E)) (x,y) :=
    hA.prodMap (x,y) hB
  have hGd : HasFDerivAt G (C.prodCongr D : (E×E) →L[ℝ] (E×E)) (z,w) :=
    hC.prodMap (z,w) hD
  have hn : (∞ : ℕ∞ω)≠0 := by simp
  let ψ := hG.localInverse hGd hn
  let Φ := ψ ∘ σ ∘ F
  have hψ : ContDiffAt ℝ ∞ ψ (G (z,w)) := hG.to_localInverse hGd hn
  have hψd : HasFDerivAt ψ ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)) (G (z,w)) :=
    (hG.hasStrictFDerivAt' hGd hn).to_localInverse.hasFDerivAt
  have hmid : ContDiffAt ℝ ∞ (σ ∘ F) (x,y) := σ.contDiff.contDiffAt.comp (x,y) hF
  have hmidD := σ.hasFDerivAt.comp (x,y) hFd
  have hpt : G (z,w)=(σ ∘ F) (x,y) := heq
  refine ⟨Φ,?_,?_,?_,?_⟩
  · change ψ ((σ ∘ F) (x,y))=(z,w)
    rw [←hpt]
    exact hG.localInverse_apply_image hGd hn
  · rw [hpt] at hψ
    exact hψ.comp (x,y) hmid
  · rw [hpt] at hψd
    exact hψd.comp (x,y) hmidD
  · have hh := (hG.hasStrictFDerivAt' hGd hn).eventually_right_inverse
    rw [hpt] at hh
    exact hmid.continuousAt.tendsto.eventually hh

section Determinant
variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
lemma derivative_det (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) :
    (derivative A B C D σ : (E×E) →L[ℝ] (E×E)).det =
      (σ : (E×E) →L[ℝ] (E×E)).det * (A : E →L[ℝ] E).det *
        (B : E →L[ℝ] E).det / ((C : E →L[ℝ] E).det*(D : E →L[ℝ] E).det) := by
  change LinearMap.det (((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).toLinearMap.comp
    ((σ : (E×E) →L[ℝ] (E×E)).toLinearMap.comp
      ((A.prodCongr B : (E×E) →L[ℝ] (E×E)).toLinearMap)))=_
  rw [LinearMap.det_comp,LinearMap.det_comp]
  have hinv := LinearEquiv.det_coe_symm (C.prodCongr D).toLinearEquiv
  change ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).det =
    ((C.prodCongr D : (E×E) →L[ℝ] (E×E)).det)⁻¹ at hinv
  change ((C.prodCongr D).symm : (E×E) →L[ℝ] (E×E)).det *
    ((σ : (E×E) →L[ℝ] (E×E)).det *
      ((A.prodCongr B : (E×E) →L[ℝ] (E×E)).det))=_
  rw [hinv]
  change ((C : E →L[ℝ] E).toLinearMap.prodMap (D : E →L[ℝ] E).toLinearMap).det⁻¹ *
    ((σ : (E×E) →L[ℝ] (E×E)).det *
      ((A : E →L[ℝ] E).toLinearMap.prodMap (B : E →L[ℝ] E).toLinearMap).det)=_
  rw [LinearMap.det_prodMap,LinearMap.det_prodMap]
  ring

omit [CompleteSpace E] in
lemma derivative_abs_det (A B C D : E ≃L[ℝ] E)
    (σ : (E×E) ≃L[ℝ] (E×E)) (hσ : |(σ : (E×E) →L[ℝ] (E×E)).det|=1) :
    |(derivative A B C D σ : (E×E) →L[ℝ] (E×E)).det| =
      |(A : E →L[ℝ] E).det| * |(B : E →L[ℝ] E).det| /
        (|(C : E →L[ℝ] E).det| * |(D : E →L[ℝ] E).det|) := by
  rw [derivative_det,abs_div,abs_mul,abs_mul,abs_mul,hσ,one_mul]
end Determinant

section Exchange
variable {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Exchange the past coordinates and leave the future coordinates fixed. -/
def exchange : ((F×P)×(F×P)) ≃L[ℝ] ((F×P)×(F×P)) where
  toFun u := ((u.1.1,u.2.2),(u.2.1,u.1.2))
  invFun u := ((u.1.1,u.2.2),(u.2.1,u.1.2))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

lemma exchange_abs_det [FiniteDimensional ℝ F] [FiniteDimensional ℝ P] :
    |(exchange (F:=F) (P:=P) : ((F×P)×(F×P)) →L[ℝ] ((F×P)×(F×P))).det|=1 := by
  let e := exchange (F:=F) (P:=P)
  have hh := e.toLinearEquiv.det_mul_det_symm
  change (e : ((F×P)×(F×P)) →L[ℝ] ((F×P)×(F×P))).det *
    (e : ((F×P)×(F×P)) →L[ℝ] ((F×P)×(F×P))).det=1 at hh
  have h := congrArg abs hh
  rw [abs_mul,abs_one] at h
  nlinarith [abs_nonneg ((e : ((F×P)×(F×P)) →L[ℝ] ((F×P)×(F×P))).det)]
end Exchange
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.JacobianBounds

lemma abs_ratio_bounds {a b : ℝ} (hb : b≠0) (h : |a/b-1|≤(1/10:ℝ)) :
    (9/10:ℝ)*|b|≤|a| ∧ |a|≤(11/10:ℝ)*|b| := by
  have ha : abs (abs (a/b) - 1)≤(1/10:ℝ) := by
    simpa only [abs_one] using (abs_abs_sub_abs_le_abs_sub (a/b) 1).trans h
  have hlo : (9/10:ℝ)≤|a/b| := by linarith [(abs_le.mp ha).1]
  have hup : |a/b|≤(11/10:ℝ) := by linarith [(abs_le.mp ha).2]
  rw [abs_div] at hlo hup
  exact ⟨(le_div_iff₀ (abs_pos.mpr hb)).mp hlo,(div_le_iff₀ (abs_pos.mpr hb)).mp hup⟩

/-- Four relative maximal-minor errors cancel the actual leading volumes
individually. Rates of the two input orbits never need to be compared. -/
theorem four_cancel
    (a b c d u v w z : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (hu : |u/(a*b)-1|≤(1/10:ℝ)) (hv : |v/(c*d)-1|≤(1/10:ℝ))
    (hw : |w/(a*d)-1|≤(1/10:ℝ)) (hz : |z/(c*b)-1|≤(1/10:ℝ)) :
    w≠0 ∧ z≠0 ∧ (81/121:ℝ)≤|u| *|v| /(|w| *|z|) ∧
      |u| *|v| /(|w| *|z|)≤(121/81:ℝ) := by
  have hU := abs_ratio_bounds (mul_ne_zero ha.ne' hb.ne') hu
  have hV := abs_ratio_bounds (mul_ne_zero hc.ne' hd.ne') hv
  have hW := abs_ratio_bounds (mul_ne_zero ha.ne' hd.ne') hw
  have hZ := abs_ratio_bounds (mul_ne_zero hc.ne' hb.ne') hz
  simp only [abs_of_pos (mul_pos ha hb)] at hU
  simp only [abs_of_pos (mul_pos hc hd)] at hV
  simp only [abs_of_pos (mul_pos ha hd)] at hW
  simp only [abs_of_pos (mul_pos hc hb)] at hZ
  have hwpos : 0 < |w| := lt_of_lt_of_le (by positivity) hW.1
  have hzpos : 0 < |z| := lt_of_lt_of_le (by positivity) hZ.1
  refine ⟨abs_pos.mp hwpos,abs_pos.mp hzpos,?_,?_⟩
  · apply (le_div_iff₀ (mul_pos hwpos hzpos)).mpr
    have hUV := mul_le_mul hU.1 hV.1 (by positivity) (abs_nonneg u)
    have hWZ := mul_le_mul hW.2 hZ.2 (abs_nonneg z) (by positivity)
    nlinarith
  · apply (div_le_iff₀ (mul_pos hwpos hzpos)).mpr
    have hUV := mul_le_mul hU.2 hV.2 (abs_nonneg v) (by positivity)
    have hWZ := mul_le_mul hW.1 hZ.1 (by positivity) (abs_nonneg w)
    nlinarith

/-- A mild smooth-density error leaves enough room for the unnormalized
factor-two pushforward estimate. -/
theorem density_lower {J din dout : ℝ} (hdin : 0≤din)
    (hJ : (81/121:ℝ)≤J) (hd : (3/4:ℝ)*din≤dout) : din≤2*(J*dout) := by
  have hdout : 0≤dout := le_trans (by positivity) hd
  have hh := mul_le_mul hJ hd (by positivity) (by linarith : 0≤J)
  nlinarith

end SmoothObstruction.JacobianBounds

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def equiv_of_det (A : E →L[ℝ] E) (hA : A.det≠0) : E ≃L[ℝ] E :=
  (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)).toContinuousLinearEquiv

omit [CompleteSpace E] in
@[simp] lemma equiv_of_det_coe (A : E →L[ℝ] E) (hA : A.det≠0) :
    (equiv_of_det A hA : E →L[ℝ] E)=A := by
  ext x
  exact LinearMap.equivOfIsUnitDet_apply _ x

/-- Construct the true smooth branch from four *absolute*, relative
endpoint-minor estimates. None of the four endpoint derivatives is
assumed invertible, and no leading volume is bounded away from zero. -/
theorem controlled_branch (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
    (A B C D : E →L[ℝ] E) (σ : (E×E) ≃L[ℝ] (E×E))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ A x) (hB : HasFDerivAt f₁ B y)
    (hC : HasFDerivAt g₀ C z) (hD : HasFDerivAt g₁ D w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y)))
    (hσ : |(σ : (E×E) →L[ℝ] (E×E)).det|=1)
    (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (haA : |(|A.det| / (a*b)-1)|≤(1/10:ℝ))
    (hbB : |(|B.det| / (c*d)-1)|≤(1/10:ℝ))
    (hcC : |(|C.det| / (a*d)-1)|≤(1/10:ℝ))
    (hdD : |(|D.det| / (c*b)-1)|≤(1/10:ℝ)) :
    ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      (81/121:ℝ) ≤ |(fderiv ℝ Φ (x,y)).det| ∧
      |(fderiv ℝ Φ (x,y)).det| ≤ (121/81:ℝ) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  have hAn : A.det≠0 := by intro h; norm_num [h] at haA
  have hBn : B.det≠0 := by intro h; norm_num [h] at hbB
  have hCn : C.det≠0 := by intro h; norm_num [h] at hcC
  have hDn : D.det≠0 := by intro h; norm_num [h] at hdD
  obtain ⟨Φ,hpt,hcd,hder,he⟩ := local_branch f₀ f₁ g₀ g₁ x y z w
    (equiv_of_det A hAn) (equiv_of_det B hBn) (equiv_of_det C hCn) (equiv_of_det D hDn) σ
    hf₀ hf₁ hg₀ hg₁ (by simpa only [equiv_of_det_coe] using hA)
    (by simpa only [equiv_of_det_coe] using hB)
    (by simpa only [equiv_of_det_coe] using hC)
    (by simpa only [equiv_of_det_coe] using hD) heq
  have hdet : |(fderiv ℝ Φ (x,y)).det|=|A.det| * |B.det| / (|C.det| * |D.det|) := by
    rw [hder.fderiv,derivative_abs_det _ _ _ _ σ hσ]
    simp only [equiv_of_det_coe]
  have hbound := (JacobianBounds.four_cancel a b c d |A.det| |B.det| |C.det| |D.det|
    ha hb hc hd haA hbB hcC hdD).2.2
  simp only [abs_abs] at hbound
  exact ⟨Φ,hpt,hcd,hdet.symm ▸ hbound.1,hdet.symm ▸ hbound.2,he⟩
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {p q : ℕ}
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

/-- The exact future/past exchange in the orthonormal sum coordinates used
for the endpoint block matrices. -/
noncomputable def sumExchange : (F×F) ≃L[ℝ] (F×F) :=
  let e : F ≃L[ℝ] (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
    EuclideanSpace.sumEquivProd
  (e.prodCongr e).trans (exchange.trans (e.prodCongr e).symm)

lemma sumExchange_abs_det : |(sumExchange (p:=p) (q:=q) : (F×F) →L[ℝ] (F×F)).det|=1 := by
  let e := sumExchange (p:=p) (q:=q)
  have he : e.symm=e := by
    ext x i <;> rfl
  have hh := e.toLinearEquiv.det_mul_det_symm
  change (e : (F×F) →L[ℝ] (F×F)).det * (e.symm : (F×F) →L[ℝ] (F×F)).det=1 at hh
  rw [he] at hh
  have hab := congrArg abs hh
  rw [abs_mul,abs_one] at hab
  nlinarith [abs_nonneg ((e : (F×F) →L[ℝ] (F×F)).det)]

/-- Signed relative determinants give precisely the absolute, relative
volume estimates required by the actual inverse-function branch. -/
lemma absolute_relative {u a b ε : ℝ} (h : |u/(a*b)-1|≤ε) :
    |(|u|/(|a| * |b|))-1|≤ε := by
  have hh := (abs_abs_sub_abs_le_abs_sub (u/(a*b)) 1).trans h
  simpa only [abs_div,abs_mul,abs_one] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The common starting-basis determinant cancels exactly, without either
orthogonality between the two summands or a determinant lower bound. -/
lemma conjugate_det (L : E ≃L[ℝ] F) (A : E →L[ℝ] E) :
    (L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).det=A.det := by
  let b := (EuclideanSpace.basisFun (Fin p ⊕ Fin q) ℝ).toBasis
  let c := b.map L.symm.toLinearEquiv
  change LinearMap.det ((L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).toLinearMap)=LinearMap.det A.toLinearMap
  rw [←LinearMap.det_toMatrix b,←LinearMap.det_toMatrix c]
  congr 1
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointBranch
open Filter Topology
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

lemma linear_conjugate_det (L : E ≃L[ℝ] F) (A : E →L[ℝ] E) :
    (L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).det=A.det := by
  let b := Module.finBasis ℝ F
  let c := b.map L.symm.toLinearEquiv
  change LinearMap.det ((L.toContinuousLinearMap.comp (A.comp L.symm.toContinuousLinearMap)).toLinearMap)=LinearMap.det A.toLinearMap
  rw [←LinearMap.det_toMatrix b,←LinearMap.det_toMatrix c]
  congr 1

variable [CompleteSpace F] [FiniteDimensional ℝ E]
/-- The controlled endpoint branch in the original physical coordinates.
The same (possibly badly conditioned) starting basis is used for all four
endpoint maps, and cancels exactly from the joint Jacobian. -/
theorem physical_controlled_branch (L : F ≃L[ℝ] E)
    (f₀ f₁ g₀ g₁ : E → F) (x y z w : E)
    (A B C D : E →L[ℝ] F) (σ : (F×F) ≃L[ℝ] (F×F))
    (hf₀ : ContDiffAt ℝ ∞ f₀ x) (hf₁ : ContDiffAt ℝ ∞ f₁ y)
    (hg₀ : ContDiffAt ℝ ∞ g₀ z) (hg₁ : ContDiffAt ℝ ∞ g₁ w)
    (hA : HasFDerivAt f₀ A x) (hB : HasFDerivAt f₁ B y)
    (hC : HasFDerivAt g₀ C z) (hD : HasFDerivAt g₁ D w)
    (heq : Prod.map g₀ g₁ (z,w)=σ (Prod.map f₀ f₁ (x,y)))
    (hσ : |(σ : (F×F) →L[ℝ] (F×F)).det|=1)
    (a b c d : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (haA : |(|(A.comp L.toContinuousLinearMap).det| / (a*b)-1)|≤(1/10:ℝ))
    (hbB : |(|(B.comp L.toContinuousLinearMap).det| / (c*d)-1)|≤(1/10:ℝ))
    (hcC : |(|(C.comp L.toContinuousLinearMap).det| / (a*d)-1)|≤(1/10:ℝ))
    (hdD : |(|(D.comp L.toContinuousLinearMap).det| / (c*b)-1)|≤(1/10:ℝ)) :
    ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
      (81/121:ℝ) ≤ |(fderiv ℝ Φ (x,y)).det| ∧
      |(fderiv ℝ Φ (x,y)).det| ≤ (121/81:ℝ) ∧
      ∀ᶠ u in 𝓝 (x,y),Prod.map g₀ g₁ (Φ u)=σ (Prod.map f₀ f₁ u) := by
  let T := L.prodCongr L
  have cd {f : E → F} {u : E} (h : ContDiffAt ℝ ∞ f u) :
      ContDiffAt ℝ ∞ (f ∘ L) (L.symm u) := by
    have h' : ContDiffAt ℝ ∞ f (L (L.symm u)) := by simpa using h
    exact h'.comp _ L.contDiff.contDiffAt
  have der {f : E → F} {u : E} {K : E →L[ℝ] F} (h : HasFDerivAt f K u) :
      HasFDerivAt (f ∘ L) (K.comp L.toContinuousLinearMap) (L.symm u) := by
    have h' : HasFDerivAt f K (L (L.symm u)) := by simpa using h
    exact h'.comp _ L.hasFDerivAt
  obtain ⟨ψ,hpt,hcd,hlo,hup,he⟩ := controlled_branch (f₀ ∘ L) (f₁ ∘ L)
    (g₀ ∘ L) (g₁ ∘ L) (L.symm x) (L.symm y) (L.symm z) (L.symm w)
    (A.comp L.toContinuousLinearMap) (B.comp L.toContinuousLinearMap)
    (C.comp L.toContinuousLinearMap) (D.comp L.toContinuousLinearMap) σ
    (cd hf₀) (cd hf₁) (cd hg₀) (cd hg₁) (der hA) (der hB) (der hC) (der hD)
    (by simpa only [Prod.map_apply,Function.comp_apply,L.apply_symm_apply] using heq)
    hσ a b c d ha hb hc hd haA hbB hcC hdD
  let Φ := T ∘ ψ ∘ T.symm
  have hψd := (hcd.differentiableAt (by norm_num)).hasFDerivAt
  have hΦcd : ContDiffAt ℝ ∞ Φ (x,y) :=
    T.contDiff.contDiffAt.comp (x,y) (hcd.comp (x,y) T.symm.contDiff.contDiffAt)
  have hΦd : HasFDerivAt Φ
      (T.toContinuousLinearMap.comp ((fderiv ℝ ψ (L.symm x,L.symm y)).comp T.symm.toContinuousLinearMap))
      (x,y) := T.hasFDerivAt.comp (x,y) (hψd.comp (x,y) T.symm.hasFDerivAt)
  have hdet : (fderiv ℝ Φ (x,y)).det=(fderiv ℝ ψ (L.symm x,L.symm y)).det := by
    rw [hΦd.fderiv]
    exact linear_conjugate_det T _
  refine ⟨Φ,?_,hΦcd,hdet.symm ▸ hlo,hdet.symm ▸ hup,?_⟩
  · change T (ψ (L.symm x,L.symm y))=(z,w)
    rw [hpt]
    exact T.apply_symm_apply (z,w)
  · have hT : ContinuousAt T.symm (x,y) := T.symm.continuousAt
    have hh := hT.tendsto.eventually he
    filter_upwards [hh] with u hu
    simpa [Φ,T,Function.comp_def,Prod.map] using hu
end SmoothObstruction.EndpointBranch

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability
open scoped ContDiff
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma joint_contDiffAt (bF bP : OrthonormalBasis (Fin d) ℝ E)
    (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
    {f g : E → E} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (joint bF bP rF rP f g) x := by
  exact EuclideanSpace.sumEquivProd.symm.contDiff.contDiffAt.comp x
    (((coordinates bF rF).contDiff.contDiffAt.comp x hf).prodMk
      ((coordinates bP rP).contDiff.contDiffAt.comp x hg))

/-- The true joint endpoint differential inherits the four-volume relative
bound from the genuine selected endpoint minors. The modulus is chosen only
from the dimensions, and permits either group to be empty. -/
theorem joint_controlled_det : ∃ δ : ℝ,0<δ ∧
    ∀ (U V : Submodule ℝ E) (h : IsCompl U V)
      (bU : OrthonormalBasis (Fin p) ℝ U) (bV : OrthonormalBasis (Fin q) ℝ V)
      (bF bP : OrthonormalBasis (Fin d) ℝ E)
      (rF : powersetCard (Fin d) p) (rP : powersetCard (Fin d) q)
      (f g : E → E) (x : E) (A₀ : Matrix (Fin p) (Fin p) ℝ)
      (D₀ : Matrix (Fin q) (Fin q) ℝ),
      DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
      A₀.det≠0 → D₀.det≠0 →
      let A := endpointMatrix bF p rF (fderiv ℝ f x) (fun i => (bU i:E))
      let B := endpointMatrix bF p rF (fderiv ℝ f x) (fun i => (bV i:E))
      let C := endpointMatrix bP q rP (fderiv ℝ g x) (fun i => (bU i:E))
      let D := endpointMatrix bP q rP (fderiv ℝ g x) (fun i => (bV i:E))
      |A.det/A₀.det-1|≤(1/100:ℝ) → |D.det/D₀.det-1|≤(1/100:ℝ) →
      (∀ i j,|(A⁻¹*B) i j|≤δ) → (∀ i j,|(D⁻¹*C) i j|≤δ) →
      |(|((fderiv ℝ (joint bF bP rF rP f g) x).comp
        (blockMap U V h bU bV).toContinuousLinearMap).det| /
        (|A₀.det| * |D₀.det|)-1)|≤(1/10:ℝ) := by
  obtain ⟨δ,hδ,hbound⟩ := MinorGraph.joint_relative_transfer (m:=Fin p) (n:=Fin q)
  refine ⟨δ,hδ,?_⟩
  intro U V h bU bV bF bP rF rP f g x A₀ D₀ hf hg hA₀ hD₀ A B C D hA hD hAB hDC
  have hder := joint_hasFDerivAt bF bP rF rP hf.hasFDerivAt hg.hasFDerivAt
  rw [hder.fderiv,joint_det U V h bU bV bF bP rF rP]
  exact EndpointBranch.absolute_relative (hbound A₀ D₀ A B C D hA₀ hD₀ hA hD hAB hDC)
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.EndpointFrame
open Set Matrix ProductBasis ExteriorStability Filter Topology
open scoped ContDiff
variable {d p q : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin p ⊕ Fin q)

/-- The same leading minor is used at the old and perturbed point. -/
def GoodEndpoint {r s : ℕ} (δ : ℝ)
    (b : OrthonormalBasis (Fin d) ℝ E) (a : powersetCard (Fin d) r)
    (u : Fin r → E) (v : Fin s → E) (f : E → E) (x : E)
    (D₀ : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ContDiffAt ℝ ∞ f x ∧ D₀.det≠0 ∧
    |(endpointMatrix b r a (fderiv ℝ f x) u).det/D₀.det-1|≤(1/100:ℝ) ∧
    ∀ i j,|((endpointMatrix b r a (fderiv ℝ f x) u)⁻¹*
      endpointMatrix b r a (fderiv ℝ f x) v) i j|≤δ

/-- Four actual endpoint maps produce one smooth two-point exchange germ.
This is a relative determinant statement at all ranks, in the original
physical coordinates. The common nonorthogonal input-basis determinant
cancels, including when either block has rank zero. -/
theorem four_endpoint_branch : ∃ δ : ℝ,0<δ ∧
    ∀ (U V : Submodule ℝ E) (_ : IsCompl U V)
      (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V)
      (b₀ b₁ c₀ c₁ : OrthonormalBasis (Fin d) ℝ E)
      (r₀ r₁ : powersetCard (Fin d) p) (s₀ s₁ : powersetCard (Fin d) q)
      (f₀ f₁ g₀ g₁ : E → E) (x y z w : E)
      (A₀ A₁ : Matrix (Fin p) (Fin p) ℝ) (D₀ D₁ : Matrix (Fin q) (Fin q) ℝ),
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ x A₀ →
      GoodEndpoint δ b₀ r₀ (fun i => (u i:E)) (fun i => (v i:E)) f₀ z A₀ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ y A₁ →
      GoodEndpoint δ b₁ r₁ (fun i => (u i:E)) (fun i => (v i:E)) f₁ w A₁ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ x D₀ →
      GoodEndpoint δ c₀ s₀ (fun i => (v i:E)) (fun i => (u i:E)) g₀ w D₀ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ y D₁ →
      GoodEndpoint δ c₁ s₁ (fun i => (v i:E)) (fun i => (u i:E)) g₁ z D₁ →
      coordinates b₀ r₀ (f₀ z)=coordinates b₀ r₀ (f₀ x) →
      coordinates b₁ r₁ (f₁ w)=coordinates b₁ r₁ (f₁ y) →
      coordinates c₀ s₀ (g₀ w)=coordinates c₀ s₀ (g₀ x) →
      coordinates c₁ s₁ (g₁ z)=coordinates c₁ s₁ (g₁ y) →
      ∃ Φ : E×E → E×E,Φ (x,y)=(z,w) ∧ ContDiffAt ℝ ∞ Φ (x,y) ∧
        (81/121:ℝ)≤|(fderiv ℝ Φ (x,y)).det| ∧
        |(fderiv ℝ Φ (x,y)).det|≤(121/81:ℝ) ∧
        ∀ᶠ t in 𝓝 (x,y),
          coordinates b₀ r₀ (f₀ (Φ t).1)=coordinates b₀ r₀ (f₀ t.1) ∧
          coordinates b₁ r₁ (f₁ (Φ t).2)=coordinates b₁ r₁ (f₁ t.2) ∧
          coordinates c₀ s₀ (g₀ (Φ t).2)=coordinates c₀ s₀ (g₀ t.1) ∧
          coordinates c₁ s₁ (g₁ (Φ t).1)=coordinates c₁ s₁ (g₁ t.2) := by
  obtain ⟨δ,hδ,hdet⟩ := joint_controlled_det (d:=d) (p:=p) (q:=q)
  refine ⟨δ,hδ,?_⟩
  intro U V h u v b₀ b₁ c₀ c₁ r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ x y z w A₀ A₁ D₀ D₁
    hxF hzF hyF hwF hxP hwP hyP hzP heF heF' heP heP'
  let F₀ := joint b₀ c₀ r₀ s₀ f₀ g₀
  let F₁ := joint b₁ c₁ r₁ s₁ f₁ g₁
  let G₀ := joint b₀ c₁ r₀ s₁ f₀ g₁
  let G₁ := joint b₁ c₀ r₁ s₀ f₁ g₀
  have hd {b c : OrthonormalBasis (Fin d) ℝ E}
      {r : powersetCard (Fin d) p} {s : powersetCard (Fin d) q}
      {f g : E → E} {t : E} {A : Matrix (Fin p) (Fin p) ℝ}
      {D : Matrix (Fin q) (Fin q) ℝ}
      (hf : GoodEndpoint δ b r (fun i => (u i:E)) (fun i => (v i:E)) f t A)
      (hg : GoodEndpoint δ c s (fun i => (v i:E)) (fun i => (u i:E)) g t D) :=
    hdet U V h u v b c r s f g t A D
      (hf.1.differentiableAt (by simp)) (hg.1.differentiableAt (by simp))
      hf.2.1 hg.2.1 hf.2.2.1 hg.2.2.1 hf.2.2.2 hg.2.2.2
  have hF₀ := joint_contDiffAt b₀ c₀ r₀ s₀ hxF.1 hxP.1
  have hF₁ := joint_contDiffAt b₁ c₁ r₁ s₁ hyF.1 hyP.1
  have hG₀ := joint_contDiffAt b₀ c₁ r₀ s₁ hzF.1 hzP.1
  have hG₁ := joint_contDiffAt b₁ c₀ r₁ s₀ hwF.1 hwP.1
  have he : Prod.map G₀ G₁ (z,w)=EndpointBranch.sumExchange (Prod.map F₀ F₁ (x,y)) := by
    ext i <;> cases i <;>
      simp [F₀,F₁,G₀,G₁,joint,EndpointBranch.sumExchange,EndpointBranch.exchange,
        EuclideanSpace.sumEquivProd,heF,heF',heP,heP']
  obtain ⟨Φ,hΦ,hcd,hlo,hup,heq⟩ := EndpointBranch.physical_controlled_branch
    (blockMap U V h u v) F₀ F₁ G₀ G₁ x y z w
    (fderiv ℝ F₀ x) (fderiv ℝ F₁ y) (fderiv ℝ G₀ z) (fderiv ℝ G₁ w)
    EndpointBranch.sumExchange hF₀ hF₁ hG₀ hG₁
    (hF₀.differentiableAt (by simp)).hasFDerivAt
    (hF₁.differentiableAt (by simp)).hasFDerivAt
    (hG₀.differentiableAt (by simp)).hasFDerivAt
    (hG₁.differentiableAt (by simp)).hasFDerivAt he EndpointBranch.sumExchange_abs_det
    |A₀.det| |D₀.det| |A₁.det| |D₁.det|
    (abs_pos.mpr hxF.2.1) (abs_pos.mpr hxP.2.1)
    (abs_pos.mpr hyF.2.1) (abs_pos.mpr hyP.2.1)
    (hd hxF hxP) (hd hyF hyP) (hd hzF hzP) (hd hwF hwP)
  refine ⟨Φ,hΦ,hcd,hlo,hup,?_⟩
  filter_upwards [heq] with t ht
  have h₀ := congrArg (fun t : F×F => EuclideanSpace.sumEquivProd t.1) ht
  have h₁ := congrArg (fun t : F×F => EuclideanSpace.sumEquivProd t.2) ht
  simp only [G₀,G₁,F₀,F₁,EndpointBranch.sumExchange,
    ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.prodCongr_apply] at h₀ h₁
  exact ⟨congrArg Prod.fst h₀,congrArg Prod.fst h₁,congrArg Prod.snd h₁,congrArg Prod.snd h₀⟩
end SmoothObstruction.EndpointFrame

namespace SmoothObstruction.ExteriorStability
open Set Matrix EndpointFrame
variable {d p q : ℕ}
local notation "E₀" => EuclideanSpace ℝ (Fin d)

lemma endpointMatrix_projection (W : Submodule ℝ E₀)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (A : E₀ →L[ℝ] E₀) (v : Fin q → E₀) :
    endpointMatrix b p r (W.starProjection*A) v=endpointMatrix b p r A v := by
  ext i j
  exact congrArg (fun z : EuclideanSpace ℝ (Fin p) => z i)
    (coordinates_projection W b r hr (A (v j)))
end SmoothObstruction.ExteriorStability

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d p q : ℕ}
local notation "E₀" => EuclideanSpace ℝ (Fin d)
/-- Actual endpoint-coordinate matrices with a common input frame. The old
leading volume, its perturbed relative value, and every true graph entry are
controlled together. No lower volume floor, rate sign, positive rank, or
orthogonality between the two input groups is required. -/
theorem endpoint_bounds
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) (hSp : S.card=p) (n : ℕ) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U 0‖≤Real.exp K) (hUt : ‖U n‖≤Real.exp K)
    (hVs : ‖V 0‖≤Real.exp K) (hVt : ‖V n‖≤Real.exp K)
    (hpoly : ∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (W G Gslow : Submodule ℝ E₀) (hdim : Module.finrank ℝ W=p)
    (hend : ‖(groupSpace (U n) (V n) (hUV n) (hVU n) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) S).starProjection-G.starProjection‖≤δ)
    (hstartSlow : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin p → E₀) (horth : Orthonormal ℝ v) (hv : ∀ i,v i∈G)
    (z : Fin q → E₀) (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E := E₀) p*δ)*
      (1+((C*(Real.exp K)^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))))≤1/2)
    (B : E₀ →L[ℝ] E₀) {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^p)^2*(C*2^p))*C*ζ*‖continuousWedge (E := E₀) p‖<1)
    (hdiff : ‖exterior p B-
      exterior p (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n))‖≤
        ζ*Real.exp ((n:ℝ)*(∑ j∈S,lam j))) :
    let A₀ := endpointMatrix b p r
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n)) v
    let A := endpointMatrix b p r B v
    let H := endpointMatrix b p r B z
    let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
    let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))
    let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p):ℝ)*‖continuousWedge (E := E₀) p‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
    A₀.det≠0 ∧ A.det≠0 ∧ |A.det/A₀.det-1|≤ε ∧ ∀ i j,|(A⁻¹*H) i j|≤(θ+ε)/(1-ε) := by
  subst p
  have hl := common_leading_relative_transfer U V lam hUV hVU S (Nat.zero_le n)
    hg hK hC hδ hfast hslow hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords
    v horth hv hsmall B hζ hpert (by simpa only [Nat.cast_zero,sub_zero] using hdiff)
  have hh := common_perturbed_endpoint_graph_bound U V lam hUV hVU S (Nat.zero_le n)
    hg hK hC hδ hfast hslow hUs hUt hVs hVt hpoly W G hdim hend hstart b r hcoords
    v horth hv Gslow hstartSlow z hz hznorm hsmall B hζ hpert
    (by simpa only [Nat.cast_zero,sub_zero] using hdiff)
  dsimp only at hl hh ⊢
  simp only [←endpointMatrix_det,endpointMatrix_projection W b r hr] at hl
  simp only [endpointMatrix_projection W b r hr,Nat.cast_zero,sub_zero] at hh
  exact ⟨hl.1,hl.2.1,hl.2.2,hh.2⟩
end SmoothObstruction.EuclideanSplitting

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric EuclideanSplitting ExteriorStability EndpointFrame
open scoped ContDiff Matrix.Norms.L2Operator
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

/-- A genuine old-chart endpoint map has the controlled minor used in the
four-equation inverse theorem. Every nonlinear derivative estimate is derived
from the original orbit tube and the real one-step gauge. Constants precede
all ranks, bins, times and gauge choices. -/
theorem actual_endpoint_minor (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (L : ι → Set M)
    (hL : ∀ i,IsCompact (L i)) (hLU : ∀ i,L i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r K₀ Crel C₁ : ℝ,0<r ∧ 1≤K₀ ∧ 0≤Crel ∧ 0≤C₁ ∧
      ∀ {p q : ℕ} (c : M → ι) (x y : M) (m : ℕ)
        (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
        (T : Finset (Fin d)) (_ : T.card=p) (γ g K b n R C δ β : ℝ),
        (∀ z,z∈L (c z)) → 0≤b → 0≤n → 1≤b*n → 0≤R →
        0≤g → 0≤K → K≤Dg*(b*n) → (m : ℝ)≤2*n → 0≤C → 0≤δ →
        ∀ (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1),
        (∀ t < m,(Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ)).symm
          (coord I S (a (c (S^[t] x))) (a (c (S^[t+1] x))) (S^[t] x))*U t=
            U (t+1)*rate lam 1) →
        (∀ i,|lam i|≤R) → (∀ j∈T,γ+g≤lam j) → (∀ j∉T,lam j≤γ-g) →
        (∀ t ≤ m,‖U t‖≤Real.exp K) → (∀ t ≤ m,‖V t‖≤Real.exp K) →
        K₀*Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤1 →
        Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)≤r →
        (∀ t ≤ m,(S^[t]) y∈(extChartAt I (a (c (S^[t] x)))).source) →
        (∀ t ≤ m,‖(extChartAt I (a (c (S^[t] x)))) (S^[t] y)-
          (extChartAt I (a (c (S^[t] x)))) (S^[t] x)‖≤
            Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)) →
        (∀ t ≤ m,closedBall ((extChartAt I (a (c (S^[t] x)))) (S^[t] x))
          (Real.exp (-(3/2:ℝ)*SmoothScales.B b*n))⊆interior (range I)) →
        (∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p) →
        ∀ (W G Gslow : Submodule ℝ E₀) (_ : Module.finrank ℝ W=p),
        (‖(groupSpace (U m) (V m) (hUV m) (hVU m) T).starProjection-
          W.starProjection‖≤1/2) →
        (‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) T).starProjection-
          G.starProjection‖≤δ) →
        (‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Tᶜ).starProjection-
          Gslow.starProjection‖≤δ) →
        ∀ (bE : OrthonormalBasis (Fin d) ℝ E₀) (rE : powersetCard (Fin d) p),
        (∀ j∈rE,bE j∈W) → (∀ v∈W,∀ j∉rE,bE.repr v j=0) →
        ∀ (v : Fin p → E₀) (z : Fin q → E₀),Orthonormal ℝ v →
        (∀ i,v i∈G) → (∀ j,z j∈Gslow) → (∀ j,‖z j‖≤1) →
        let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
        let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p) : ℝ))
        let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p) : ℝ)*‖continuousWedge (E := E₀) p‖
        let ζ := RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n *
          Real.exp (RelativeAsymptotics.envelope Crel 0 C₁ (d*R) K₀ b n)
        let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
        let θ := 2*L₀*(N₁*Real.exp (-2*g*m)+N₀*unitWedgeConstant (E := E₀) p*δ)
        (frameWedgeConstant (E := E₀) p*δ)*(1+L₀*N₀)≤1/2 →
        ε≤1/100 → (θ+ε)/(1-ε)≤β →
        let F := extChartAt I (a (c (S^[m] x))) ∘ S^[m] ∘ (extChartAt I (a (c x))).symm
        GoodEndpoint β bE rE v z F ((extChartAt I (a (c x))) y)
          (endpointMatrix bE p rE (fderiv ℝ F ((extChartAt I (a (c x))) x)) v) := by
  obtain ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,hrel⟩ :=
    actual_endpoint_relative I hclosed S a L hL hLU Dg hDg
  refine ⟨r,K₀,Crel,C₁,hr,hK₀,hCrel,hC₁,?_⟩
  intro p q c x y m U V lam T hTp γ g K b n R C δ β hc hb hn hbn hR
    hg hK hKD hm hC hδ hUV hVU hstep hlam hfast hslow hU hV hε hεr
    hychart htube hsafe hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hcoords
    v z horth hv hz hznorm L₀ N₀ N₁ ζ ε θ hsmall hεsmall hgraph F
  subst p
  let p := T.card
  let ca (t : ℕ) := a (c (S^[t] x))
  have hxchart (t : ℕ) : S^[t] x∈(extChartAt I (ca t)).source := by
    simpa only [extChartAt_source,ca] using hLU (c (S^[t] x)) (hc (S^[t] x))
  have hxint (t : ℕ) (ht : t ≤ m) :
      (extChartAt I (ca t)) (S^[t] x)∈interior (range I) :=
    hsafe t ht (mem_closedBall_self (Real.exp_nonneg _))
  have hyint (t : ℕ) (ht : t ≤ m) :
      (extChartAt I (ca t)) (S^[t] y)∈interior (range I) :=
    hsafe t ht (mem_closedBall.mpr (by simpa only [dist_eq_norm] using htube t ht))
  have hd := actual_endpoint_differential I S ca x m U V lam
    (fun t _ => hxchart t) hxint hUV hVU hstep
  have hcd := actual_endpoint_smooth I S ca y m hychart hyint
  have hdf := hd.fderiv
  change fderiv ℝ F ((extChartAt I (a (c x))) x)=_ at hdf
  have hpert := hrel c x y m U V lam T γ g K b n 0 R hc hb hn hbn (by norm_num)
    hR hg hK hKD hm hUV hVU hstep hlam hfast hslow hU hV hε hεr hychart htube hsafe
  simp only [zero_mul,sub_zero] at hpert
  rw [hdf] at hpert
  have hdiff : ‖exterior p (fderiv ℝ F ((extChartAt I (a (c x))) y))-
      exterior p (Matrix.toEuclideanCLM (n:=Fin d) (𝕜:=ℝ) (transition U V lam 0 m))‖≤
      ζ*Real.exp ((m : ℝ)*(∑ j∈T,lam j)) := by
    simpa only [F,ζ,mul_comm (m : ℝ)] using (div_le_iff₀ (Real.exp_pos _)).mp hpert
  have hζ : 0≤ζ := by dsimp [ζ,RelativeAsymptotics.envelope]; positivity
  have heps : ε<1 := lt_of_le_of_lt hεsmall (by norm_num)
  have hminor := endpoint_bounds U V lam hUV hVU T rfl m hg hK hC hδ hfast hslow
    (hU 0 (Nat.zero_le m)) (hU m le_rfl) (hV 0 (Nat.zero_le m)) (hV m le_rfl)
    hpoly W G Gslow hdim hend hstart hstartSlow bE rE hrE hcoords
    v horth hv z hz hznorm hsmall (fderiv ℝ F ((extChartAt I (a (c x))) y)) hζ heps hdiff
  change ContDiffAt ℝ ∞ F ((extChartAt I (a (c x))) y) at hcd
  dsimp only [GoodEndpoint]
  rw [hdf]
  exact ⟨hcd,hminor.1,hminor.2.2.1.trans hεsmall,
    fun i j => (hminor.2.2.2 i j).trans hgraph⟩
end SmoothObstruction.ManifoldCoordinates

end

end OAI
