import OAI.Analysis.RotationWeights.TensorBasis

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
lemma continuous_bounded_lp_field {X : Type uX} [TopologicalSpace X]
    (A : X → FiberOperator) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖A x‖ ≤ C)
    (hc : ∀ k : ℤ, Continuous (fun x ↦ A x (lp.single 2 k 1)))
    (u : FiberHilbert) : Continuous (fun x ↦ A x u) := by
  classical
  let v : Finset ℤ → FiberHilbert := fun s ↦ ∑ k ∈ s, lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  have hunif : TendstoUniformly (fun s x ↦ A x (v s)) (fun x ↦ A x u) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have hε' : 0 < ε/(C+1) := div_pos hε (by linarith)
    filter_upwards [Metric.tendsto_nhds.mp hv _ hε'] with s hs x
    rw [dist_eq_norm, ← map_sub]
    have ht := (A x).le_opNorm (u-v s)
    have hn : ‖u-v s‖ < ε/(C+1) := by simpa [dist_eq_norm, norm_sub_rev] using hs
    calc
      _ ≤ C * ‖u-v s‖ := ht.trans (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))
      _ ≤ (C+1) * ‖u-v s‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1) * (ε/(C+1)) := mul_lt_mul_of_pos_left hn (by linarith)
      _ = ε := mul_div_cancel₀ _ (by linarith)
  apply hunif.continuous
  apply Filter.Eventually.frequently
  exact Filter.Eventually.of_forall fun s ↦ by
    simp only [v, map_sum]
    apply continuous_finsetSum
    intro k _
    have he : lp.single (E := fun _ : ℤ ↦ ℂ) 2 k (u k) = (u k) • lp.single 2 k (1 : ℂ) := by
      simpa using (lp.single_smul (E := fun _ : ℤ ↦ ℂ) 2 k (u k) (1 : ℂ))
    simp only [he, map_smul]
    exact (hc k).const_smul (u k)

lemma lpDiagonal_norm_le {a : ℤ → ℂ} (B : ℝ≥0) (ha : ∀ k, ‖a k‖ ≤ B) :
    ‖lpDiagonal a B ha‖ ≤ B := by
  refine (lpDiagonal a B ha).opNorm_le_bound B.coe_nonneg ?_
  intro u
  calc
    _ ≤ ‖(B : ℂ) • u‖ := lp.norm_mono (by norm_num) (by
      intro k
      simp only [lpDiagonal_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg B.coe_nonneg]
      exact mul_le_mul_of_nonneg_right (ha k) (norm_nonneg _))
    _ = (B : ℝ) * ‖u‖ := by rw [norm_smul]; simp

abbrev CircleFiberL2 := Lp FiberHilbert 2 (AddCircle.haarAddCircle (T := (1:ℝ)))
abbrev CircleFiberOperator := CircleFiberL2 →L[ℂ] CircleFiberL2
def fiberBasis : HilbertBasis ℤ ℂ FiberHilbert :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ FiberHilbert)
@[simp] lemma fiberBasis_apply (a : ℤ) : fiberBasis a = lp.single 2 a 1 := by
  simpa [fiberBasis] using (fiberBasis.repr_self a)

def circleFiberBasis : HilbertBasis (ℤ×ℤ) ℂ CircleFiberL2 :=
  tensorL2Basis AddCircle.haarAddCircle fiberBasis fourierBasis

lemma circleFiberBasis_coe (a b : ℤ) :
    circleFiberBasis (a,b) =ᵐ[AddCircle.haarAddCircle] fun x ↦
      fourier b x • lp.single 2 a 1 := by
  simp only [circleFiberBasis,tensorL2Basis_apply]
  filter_upwards [pureL2_coe (AddCircle.haarAddCircle (T := (1:ℝ))) (fourierBasis b) (fiberBasis a),
    coeFn_fourierLp (T := (1:ℝ)) 2 b] with x h1 h2
  simpa only [coe_fourierBasis,h2,fiberBasis_apply] using h1

def continuousPiField (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX) : FiberOperator :=
  lpDiagonal (fun k ↦ g (x+k•θ)) ⟨‖g‖,norm_nonneg g⟩
    (fun k ↦ ContinuousMap.norm_coe_le_norm g (x+k•θ))

@[simp] lemma continuousPiField_apply (θ : CircleX) (g : C(CircleX,ℂ))
    (x : CircleX) (v : FiberHilbert) (k : ℤ) :
    continuousPiField θ g x v k = g (x+k•θ)*v k := rfl

lemma continuousPiField_bound (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX) :
    ‖continuousPiField θ g x‖ ≤ ‖g‖ := by
  exact lpDiagonal_norm_le ⟨‖g‖,norm_nonneg g⟩ _

lemma continuousPiField_continuous (θ : CircleX) (g : C(CircleX,ℂ)) (v : FiberHilbert) :
    Continuous (fun x ↦ continuousPiField θ g x v) := by
  apply continuous_bounded_lp_field _ (norm_nonneg g) (continuousPiField_bound θ g) _ v
  intro k
  have he : (fun x ↦ continuousPiField θ g x (lp.single 2 k 1)) =
      (fun x ↦ g (x+k•θ) • lp.single 2 k 1) := by
    funext x
    ext j
    simp only [continuousPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
    by_cases h : j=k
    · subst j; rfl
    · simp [lp.single_apply,Pi.single_eq_of_ne h]
  rw [he]
  exact (g.continuous.comp (continuous_id.add continuous_const)).smul continuous_const

def continuousPi (θ : CircleX) (g : C(CircleX,ℂ)) : CircleFiberOperator :=
  fieldMulL2 AddCircle.haarAddCircle (continuousPiField θ g)
    (fun v ↦ (continuousPiField_continuous θ g v).aestronglyMeasurable)
    ‖g‖ (Eventually.of_forall (continuousPiField_bound θ g))

lemma continuousPi_coe (θ : CircleX) (g : C(CircleX,ℂ)) (f : CircleFiberL2) :
    continuousPi θ g f =ᵐ[AddCircle.haarAddCircle] fun x ↦ continuousPiField θ g x (f x) :=
  fieldMulL2_coe _ _ _ _ _ _

lemma continuousPi_norm_le (θ : CircleX) (g : C(CircleX,ℂ)) :
    ‖continuousPi θ g‖ ≤ ‖g‖ :=
  fieldMulL2_norm_le _ _ _ _ _ (norm_nonneg _)

lemma continuousPi_add (θ : CircleX) (g h : C(CircleX,ℂ)) :
    continuousPi θ (g+h) = continuousPi θ g + continuousPi θ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (g+h) f,continuousPi_coe θ g f,
    continuousPi_coe θ h f,Lp.coeFn_add (continuousPi θ g f) (continuousPi θ h f)] with x h1 h2 h3 h4
  change (continuousPi θ (g+h) f) x = ((continuousPi θ g f)+(continuousPi θ h f)) x
  rw [h1,h4]
  simp only [Pi.add_apply,h2,h3]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.add_apply,lp.coeFn_add,Pi.add_apply,add_mul]

lemma continuousPi_mul (θ : CircleX) (g h : C(CircleX,ℂ)) :
    continuousPi θ (g*h) = continuousPi θ g * continuousPi θ h := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (g*h) f,continuousPi_coe θ h f,
    continuousPi_coe θ g (continuousPi θ h f)] with x h1 h2 h3
  change (continuousPi θ (g*h) f) x = (continuousPi θ g (continuousPi θ h f)) x
  rw [h1,h3,h2]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.mul_apply,mul_assoc]

lemma continuousPi_one (θ : CircleX) : continuousPi θ 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ 1 f] with x hx
  rw [hx]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.one_apply,one_mul]
  rfl

lemma continuousPi_zero (θ : CircleX) : continuousPi θ 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ 0 f,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  change (continuousPi θ 0 f) x = (0 : CircleFiberL2) x
  rw [hx,hz]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.zero_apply,zero_mul,Pi.zero_apply,lp.coeFn_zero]

lemma continuousPi_smul (θ : CircleX) (g : C(CircleX,ℂ)) (c : ℂ) :
    continuousPi θ (c•g) = c•continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (c•g) f,continuousPi_coe θ g f,
    Lp.coeFn_smul c (continuousPi θ g f)] with x h1 h2 h3
  change (continuousPi θ (c•g) f) x = (c•continuousPi θ g f) x
  rw [h1,h3]
  simp only [Pi.smul_apply,h2]
  ext k
  simp only [continuousPiField_apply,ContinuousMap.smul_apply,lp.coeFn_smul,
    Pi.smul_apply,smul_eq_mul,mul_assoc]

lemma continuousPiField_inner_star (θ : CircleX) (g : C(CircleX,ℂ)) (x : CircleX)
    (u v : FiberHilbert) :
    inner ℂ (continuousPiField θ (star g) x u) v = inner ℂ u (continuousPiField θ g x v) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro k
  simp only [continuousPiField_apply,RCLike.inner_apply,ContinuousMap.star_apply,map_mul,
    starRingEnd_apply,star_star]
  ring

lemma continuousPi_star (θ : CircleX) (g : C(CircleX,ℂ)) :
    continuousPi θ (star g) = star (continuousPi θ g) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  change inner ℂ (continuousPi θ (star g) f) h =
    inner ℂ ((continuousPi θ g).adjoint f) h
  rw [ContinuousLinearMap.adjoint_inner_left,L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousPi_coe θ (star g) f,continuousPi_coe θ g h] with x h1 h2
  rw [h1,h2]
  exact continuousPiField_inner_star θ g x (f x) (h x)

def continuousPiHom (θ : CircleX) : C(CircleX,ℂ) →⋆ₐ[ℂ] CircleFiberOperator where
  toFun := continuousPi θ
  map_zero' := continuousPi_zero θ
  map_one' := continuousPi_one θ
  map_add' := continuousPi_add θ
  map_mul' := continuousPi_mul θ
  commutes' := by
    intro c
    simp only [Algebra.algebraMap_eq_smul_one,continuousPi_smul,continuousPi_one]
  map_star' := continuousPi_star θ

lemma continuous_continuousPiHom (θ : CircleX) : Continuous (continuousPiHom θ) := by
  exact (LinearMap.mkContinuous (continuousPiHom θ).toLinearMap 1
    (by
      intro g
      change ‖continuousPi θ g‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using continuousPi_norm_le θ g)).continuous

end


def fiberShiftL2 (n : ℤ) : CircleFiberOperator :=
  (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 AddCircle.haarAddCircle

lemma fiberShiftL2_coe (n : ℤ) (f : CircleFiberL2) :
    fiberShiftL2 n f =ᵐ[AddCircle.haarAddCircle] fun x ↦ fiberShift n (f x) :=
  (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL f

lemma fiberShift_single (n a : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 a c) = lp.single 2 (n+a) c := by
  ext k
  simp only [fiberShift_apply,lp.single_apply,Pi.single_apply]
  have he : k-n=a ↔ k=n+a := by omega
  simp only [he]

lemma fiberShiftL2_basis (n a b : ℤ) :
    fiberShiftL2 n (circleFiberBasis (a,b)) = circleFiberBasis (n+a,b) := by
  apply Lp.ext
  filter_upwards [fiberShiftL2_coe n (circleFiberBasis (a,b)),
    circleFiberBasis_coe a b,circleFiberBasis_coe (n+a) b] with x h1 h2 h3
  rw [h1,h2,h3,map_smul,fiberShift_single]

lemma circleFiberBasis_ext {A B : CircleFiberOperator}
    (h : ∀ a b, A (circleFiberBasis (a,b)) = B (circleFiberBasis (a,b))) : A=B := by
  have he : A.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      B.comp circleFiberBasis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro k
    apply ContinuousLinearMap.ext
    intro c
    change A (circleFiberBasis.repr.symm (lp.single 2 k c)) =
      B (circleFiberBasis.repr.symm (lp.single 2 k c))
    have hc : lp.single (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c = c•lp.single 2 k 1 := by
      simpa using lp.single_smul (E := fun _ : ℤ×ℤ ↦ ℂ) 2 k c 1
    rw [hc,map_smul,map_smul,map_smul,HilbertBasis.repr_symm_single,h k.1 k.2]
  apply ContinuousLinearMap.ext
  intro f
  simpa only [ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.symm_apply_apply] using
    DFunLike.congr_fun he (circleFiberBasis.repr f)

lemma regularShift_single (n a b : ℤ) (c : ℂ) :
    regularShift n (lp.single 2 (a,b) c) = lp.single 2 (n+a,b) c := by
  ext ⟨k,l⟩
  simp only [regularShift_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  have he : k-n=a ∧ l=b ↔ k=n+a ∧ l=b := by omega
  simp only [he]

lemma circleFiberBasis_conj_U :
    circleFiberBasis.repr.symm.conjStarAlgEquiv (regularU : RegularOperator) = fiberShiftL2 1 := by
  apply circleFiberBasis_ext
  intro a b
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_symm,
    HilbertBasis.repr_self]
  change circleFiberBasis.repr.symm (regularShift 1 (lp.single 2 (a,b) 1)) = _
  rw [regularShift_single,HilbertBasis.repr_symm_single,fiberShiftL2_basis]

lemma continuousPi_basis (θ : CircleX) (a b : ℤ) :
    continuousPi θ (fourier 1) (circleFiberBasis (a,b)) =
      (fourier 1 (a•θ)) • circleFiberBasis (a,b+1) := by
  apply Lp.ext
  filter_upwards [continuousPi_coe θ (fourier 1) (circleFiberBasis (a,b)),
    circleFiberBasis_coe a b,circleFiberBasis_coe a (b+1),
    Lp.coeFn_smul (fourier 1 (a•θ)) (circleFiberBasis (a,b+1))] with x h1 h2 h3 h4
  rw [h1,h2,h4]
  simp only [Pi.smul_apply,h3]
  ext k
  simp only [continuousPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hk : k=a
  · subst k
    simp only [lp.single_apply,Pi.single_eq_same,mul_one]
    rw [fourier_add]
    simp only [fourier_one, AddCircle.toCircle_add,Circle.coe_mul]
    ring
  · simp [lp.single_apply,Pi.single_eq_of_ne hk]

lemma regularMagnetic_single (u : unitary ℂ) (a b : ℤ) (c : ℂ) :
    regularMagnetic u 1 (lp.single 2 (a,b) c) =
      ((u^a : unitary ℂ) : ℂ) • lp.single 2 (a,b+1) c := by
  ext ⟨k,l⟩
  simp only [regularMagnetic_apply,one_mul,lp.coeFn_smul,Pi.smul_apply,
    lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  have he : k=a ∧ l-1=b ↔ k=a ∧ l=b+1 := by omega
  simp only [he]
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · simp

lemma fourier_one_real (θ : ℝ) : fourier 1 (θ : CircleX) = (rotationScalar θ : ℂ) := by
  simp only [fourier_one,AddCircle.toCircle_apply_mk,Circle.coe_exp,div_one]
  simp only [rotationScalar,Complex.ofReal_mul,Complex.ofReal_ofNat]

lemma fourier_one_zsmul_real (θ : ℝ) (a : ℤ) :
    fourier 1 (a • (θ : CircleX)) = ((rotationScalar θ)^a : unitary ℂ) := by
  rw [fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  rw [← fourier_one, fourier_one_real, Unitary.coe_zpow]

lemma circleFiberBasis_conj_V (θ : ℝ) :
    circleFiberBasis.repr.symm.conjStarAlgEquiv (regularV (rotationScalar θ) : RegularOperator) =
      continuousPi (θ : CircleX) (fourier 1) := by
  apply circleFiberBasis_ext
  intro a b
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_symm,
    HilbertBasis.repr_self]
  change circleFiberBasis.repr.symm (regularMagnetic (rotationScalar θ) 1
    (lp.single 2 (a,b) 1)) = _
  rw [regularMagnetic_single,map_smul,HilbertBasis.repr_symm_single,continuousPi_basis,
    fourier_one_zsmul_real]



end ContinuousCircleWeight

end

end OAI
