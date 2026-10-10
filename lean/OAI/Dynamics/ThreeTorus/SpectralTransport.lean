import OAI.Dynamics.ThreeTorus.PhysicalBasis

namespace OAI

/-! Measure-preserving torus transport, full mean-zero L2 isometry, ergodicity, and full circle spectral representation. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus
namespace SmoothDynamics
variable (D : SmoothDynamics)

/-- The produced physical action in the fixed torus coordinate convention. -/
def torusMap (k : ℤ) : Equiv.Perm Torus :=
  (torusTriple.toEquiv.trans (D.homeo k).toEquiv).trans torusTriple.symm.toEquiv
lemma torusMap_apply (k : ℤ) (x : Torus) : D.torusMap k x=
    torusTriple.symm (D.map k (torusTriple x)) := rfl
lemma torusMap_zero : D.torusMap 0=1 := by
  ext x
  simp only [torusMap_apply,D.zero,torusTriple.symm_apply_apply,Equiv.Perm.one_apply]
lemma torusMap_add (k j : ℤ) : D.torusMap (k+j)=D.torusMap k*D.torusMap j := by
  ext x
  simp only [torusMap_apply,Equiv.Perm.mul_apply,torusTriple.apply_symm_apply,D.add]

def torusAction : Multiplicative ℤ →* Equiv.Perm Torus where
  toFun k := D.torusMap k.toAdd
  map_one' := D.torusMap_zero
  map_mul' k j := D.torusMap_add k.toAdd j.toAdd

lemma torusMap_zpow (k : ℤ) : (D.torusMap 1)^k=D.torusMap k := by
  have hh := (D.torusAction).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
  simpa [torusAction, zsmul_eq_mul] using hh.symm
lemma torusMap_inv (k : ℤ) : (D.torusMap k)⁻¹=D.torusMap (-k) := by
  have hh := (D.torusAction).map_inv (Multiplicative.ofAdd k)
  exact hh.symm
lemma torusMap_symm (k : ℤ) : (D.torusMap k).symm=D.torusMap (-k) := D.torusMap_inv k

lemma torusMap_mp (k : ℤ) : MeasurePreserving (D.torusMap k) μ μ :=
  ((MeasurePreserving.symm torusTriple measurePreserving_torusTriple).comp (D.mp k)).comp
    measurePreserving_torusTriple

lemma torusMap_smooth (k : ℤ) : Smooth (D.torusMap k) := by
  intro x
  refine ⟨univ,isOpen_univ,mem_univ x,D.lift k,(D.smooth k).contDiffOn,?_⟩
  intro y _
  apply torusTriple.injective
  change torusTriple (torusTriple.symm (D.map k (torusTriple (project y))))=
    torusTriple (project (D.lift k y))
  rw [torusTriple.apply_symm_apply]
  exact (D.graph k y).symm

end SmoothDynamics
end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- The coordinate change is a genuine isometry on the full L2 spaces. -/
def physicalToTorus : PhysicalL2 →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ torusTriple measurePreserving_torusTriple
def torusToPhysical : H →ₗᵢ[ℂ] PhysicalL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ torusTriple.symm
    (MeasurePreserving.symm torusTriple measurePreserving_torusTriple)
lemma physicalToTorus_ae (f : PhysicalL2) : physicalToTorus f =ᵐ[μ]
    fun x => f (torusTriple x) := Lp.coeFn_compMeasurePreserving f measurePreserving_torusTriple
lemma torusToPhysical_ae (g : H) : torusToPhysical g =ᵐ[tripleVolume]
    fun x => g (torusTriple.symm x) := Lp.coeFn_compMeasurePreserving g
      (MeasurePreserving.symm torusTriple measurePreserving_torusTriple)
lemma physicalToTorus_torusToPhysical (g : H) : physicalToTorus (torusToPhysical g)=g := by
  apply Lp.ext
  filter_upwards [physicalToTorus_ae (torusToPhysical g),
    measurePreserving_torusTriple.quasiMeasurePreserving.ae (torusToPhysical_ae g)] with x hx hy
  simpa only [torusTriple.symm_apply_apply] using hx.trans hy
lemma torusToPhysical_physicalToTorus (f : PhysicalL2) : torusToPhysical (physicalToTorus f)=f := by
  apply Lp.ext
  filter_upwards [torusToPhysical_ae (physicalToTorus f),
    (MeasurePreserving.symm torusTriple measurePreserving_torusTriple).quasiMeasurePreserving.ae
      (physicalToTorus_ae f)] with x hx hy
  simpa only [torusTriple.apply_symm_apply] using hx.trans hy

lemma physicalToTorus_centered_iff (f : PhysicalL2) : physicalToTorus f ∈ meanZero ↔ f ∈ physicalMeanZero := by
  change (∫ x, physicalToTorus f x ∂μ)=0 ↔ _
  rw [mem_physicalMeanZero,integral_congr_ae (physicalToTorus_ae f),
    measurePreserving_torusTriple.integral_comp' ]
lemma torusToPhysical_centered_iff (g : H) : torusToPhysical g ∈ physicalMeanZero ↔ g ∈ meanZero := by
  rw [← physicalToTorus_centered_iff,physicalToTorus_torusToPhysical]

def physicalZeroToTorus : physicalMeanZero →ₗᵢ[ℂ] H₀ where
  toFun f := ⟨physicalToTorus f,(physicalToTorus_centered_iff f).mpr f.property⟩
  map_add' f g := Subtype.ext (map_add physicalToTorus (f:PhysicalL2) (g:PhysicalL2))
  map_smul' a f := Subtype.ext (map_smul physicalToTorus a (f:PhysicalL2))
  norm_map' f := physicalToTorus.norm_map f
lemma physicalZeroToTorus_surjective : Surjective physicalZeroToTorus := by
  intro g
  refine ⟨⟨torusToPhysical g,(torusToPhysical_centered_iff g).mpr g.property⟩,?_⟩
  exact Subtype.ext (physicalToTorus_torusToPhysical g)
def physicalZeroEquiv : physicalMeanZero ≃ₗᵢ[ℂ] H₀ :=
  LinearIsometryEquiv.ofSurjective physicalZeroToTorus physicalZeroToTorus_surjective

/-- Ambient closure equal to the centered kernel gives density in its actual
subspace topology, not merely in some smaller abstract copy. -/
lemma physical_subtype_dense (v : ℤ → physicalMeanZero)
    (h : (Submodule.span ℂ (Set.range (fun n => (v n : PhysicalL2)))).topologicalClosure=physicalMeanZero) :
    Dense (Submodule.span ℂ (Set.range v) : Set physicalMeanZero) := by
  let S := Submodule.span ℂ (Set.range v)
  have hS : S.map physicalMeanZero.subtype=Submodule.span ℂ (Set.range (fun n => (v n : PhysicalL2))) := by
    rw [Submodule.map_span,← Set.range_comp]
    rfl
  intro g
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hg : (g:PhysicalL2) ∈ closure (Submodule.span ℂ (Set.range (fun n => (v n : PhysicalL2))) : Set PhysicalL2) := by
    rw [← Submodule.topologicalClosure_coe,h]
    exact g.property
  obtain ⟨x,hx,hd⟩ := Metric.mem_closure_iff.mp hg ε hε
  rw [← hS] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨y,hy,hd⟩

lemma physicalZeroEquiv_dense_span (v : ℤ → physicalMeanZero)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set physicalMeanZero)) :
    Dense (Submodule.span ℂ (Set.range (fun n => physicalZeroEquiv (v n))) : Set H₀) := by
  intro g
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨x,hx,hxg⟩ := Metric.mem_closure_iff.mp (hd (physicalZeroEquiv.symm g)) ε hε
  refine ⟨physicalZeroEquiv x,?_,?_⟩
  · have hm : (Submodule.span ℂ (Set.range v)).map physicalZeroEquiv.toLinearEquiv.toLinearMap =
        Submodule.span ℂ (Set.range (fun n => physicalZeroEquiv (v n))) := by
      rw [Submodule.map_span,← Set.range_comp]; rfl
    rw [← hm]
    exact ⟨x,hx,rfl⟩
  · simpa only [← physicalZeroEquiv.dist_map,physicalZeroEquiv.apply_symm_apply] using hxg

end ThreeTorus
end
end

section

noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace ThreeTorus

lemma integral_eq_inner_one (f : H) :
    (∫ x, f x ∂μ) = inner ℂ (Lp.const 2 μ (1 : ℂ)) f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℂ)] with x hx
  simp only [hx, Function.const_apply, RCLike.inner_apply, map_one, mul_one]

lemma meanZero_closed : IsClosed (meanZero : Set H) := by
  change IsClosed {f : H | ∫ x, f x ∂μ = 0}
  simp_rw [integral_eq_inner_one]
  exact isClosed_eq (innerSL ℂ (Lp.const 2 μ (1 : ℂ))).continuous continuous_const

instance : CompleteSpace H₀ :=
  @IsClosed.completeSpace_coe H _ _ (meanZero : Set H) meanZero_closed

lemma integral_comp_preserving {T : Torus → Torus} (hT : MeasurePreserving T μ μ) (g : H) :
    (∫ x, g (T x) ∂μ) = ∫ x, g x ∂μ := by
  have hm : AEStronglyMeasurable g (Measure.map T μ) := by
    rw [hT.map_eq]
    exact (Lp.memLp g).aestronglyMeasurable
  rw [← integral_map hT.measurable.aemeasurable hm, hT.map_eq]

/-- The actual Koopman operator, restricted to the full centered subspace. -/
def koopman {T : Torus → Torus} (hT : MeasurePreserving T μ μ) : H₀ →ₗᵢ[ℂ] H₀ where
  toFun f := ⟨Lp.compMeasurePreserving T hT f.1, by
    change ∫ x, Lp.compMeasurePreserving T hT f.1 x ∂μ = 0
    rw [integral_congr_ae (Lp.coeFn_compMeasurePreserving f.1 hT)]
    exact (integral_comp_preserving hT f.1).trans f.2⟩
  map_add' f g := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c f := by apply Subtype.ext; exact (Lp.compMeasurePreservingₗ ℂ T hT).map_smul c f.1
  norm_map' f := Lp.norm_compMeasurePreserving f.1 hT

lemma koopman_ae {T : Torus → Torus} (hT : MeasurePreserving T μ μ) (f : H₀) :
    (koopman hT f).1 =ᵐ[μ] fun x => f.1 (T x) :=
  Lp.coeFn_compMeasurePreserving f.1 hT

lemma koopman_orbit_step {T : Equiv.Perm Torus} (hT : MeasurePreserving T μ μ)
    {f : H₀} {v : ℤ → H₀}
    (hv : ∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T^n) x)) (n : ℤ) :
    koopman hT (v n) = v (n+1) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [koopman_ae hT (v n), hT.quasiMeasurePreserving.ae (hv n), hv (n+1)] with x hx₀ hx₁ hx₂
  rw [hx₀, hx₁, hx₂, zpow_add, zpow_one]
  rfl

/-- Circle coordinate multiplication, constructed on L² representatives. -/
def circleMul (n : ℤ) (f : CircleH) : CircleH :=
  ((Lp.memLp f).congr_norm
    ((fourier n).continuous.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun z => by
      change ‖f z‖ = ‖fourier n z * f z‖
      rw [norm_mul, show ‖fourier n z‖ = 1 from Circle.norm_coe _, one_mul]))).toLp (fun z => fourier n z * f z)

lemma circleMul_ae (n : ℤ) (f : CircleH) :
    circleMul n f =ᵐ[AddCircle.haarAddCircle] fun z => fourier n z * f z :=
  MemLp.coeFn_toLp _

def circleMulLI (n : ℤ) : CircleH →ₗᵢ[ℂ] CircleH where
  toFun := circleMul n
  map_add' f g := by
    apply Lp.ext
    filter_upwards [circleMul_ae n (f+g), circleMul_ae n f, circleMul_ae n g,
      Lp.coeFn_add f g, Lp.coeFn_add (circleMul n f) (circleMul n g)] with z h₀ h₁ h₂ h₃ h₄
    simp only [Pi.add_apply] at h₃ h₄
    rw [h₀,h₄,h₁,h₂,h₃,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [circleMul_ae n (c • f), circleMul_ae n f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (circleMul n f)] with z h₀ h₁ h₂ h₃
    change circleMul n (c • f) z = (c • circleMul n f) z
    simp only [Pi.smul_apply, smul_eq_mul] at h₂ h₃
    rw [h₀,h₃,h₁,h₂]
    ring
  norm_map' f := by
    simp only [Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [circleMul_ae n f] with z hz
    change ‖circleMul n f z‖ = ‖f z‖
    rw [hz, norm_mul, show ‖fourier n z‖ = 1 from Circle.norm_coe _, one_mul]

lemma circleMul_fourier (m n : ℤ) :
    circleMulLI m (fourierLp 2 n) = fourierLp 2 (m+n) := by
  apply Lp.ext
  filter_upwards [circleMul_ae m (fourierLp 2 n), coeFn_fourierLp 2 n,
    coeFn_fourierLp 2 (m+n)] with z h₀ h₁ h₂
  change circleMul m (fourierLp 2 n) z = _
  rw [h₀,h₁,h₂,fourier_add]

/-- The bilateral full-space basis determines the stated circle unitary.
This is the spectral-model completion step only, not existence of the basis. -/
lemma spectral_model_of_basis {T : Equiv.Perm Torus} (hT : MeasurePreserving T μ μ)
    {f : H₀} {v : ℤ → H₀}
    (hv : ∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T^n) x))
    (ho : Orthonormal ℂ v) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H₀)) :
    ∃ W : H₀ ≃ₗᵢ[ℂ] CircleH,
      (∀ n : ℤ, W (v n) = fourierLp 2 n) ∧
      ∀ g : H₀, ∃ h : H₀,
        (∀ᵐ x ∂μ, h.1 x = g.1 (T x)) ∧
        (∀ᵐ z ∂AddCircle.haarAddCircle, W h z = fourier 1 z * W g z) := by
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range v)).topologicalClosure := by
    intro x _
    exact hd x
  let b := HilbertBasis.mk ho hsp
  let W : H₀ ≃ₗᵢ[ℂ] CircleH := b.repr.trans fourierBasis.repr.symm
  have hW (n : ℤ) : W (v n) = fourierLp 2 n := by
    have hb : b n = v n := congrFun (HilbertBasis.coe_mk ho hsp) n
    rw [← hb]
    change fourierBasis.repr.symm (b.repr (b n)) = _
    rw [HilbertBasis.repr_self, HilbertBasis.repr_symm_single, coe_fourierBasis]
  refine ⟨W,hW,?_⟩
  have he : W.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (koopman hT).toContinuousLinearMap =
      (circleMulLI 1).toContinuousLinearMap.comp W.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on hd
    rintro x ⟨n,rfl⟩
    change W (koopman hT (v n)) = circleMulLI 1 (W (v n))
    rw [koopman_orbit_step hT hv, hW, hW, circleMul_fourier, add_comm n 1]
  intro g
  refine ⟨koopman hT g,koopman_ae hT g,?_⟩
  have he' := DFunLike.congr_fun he g
  change W (koopman hT g) = circleMulLI 1 (W g) at he'
  rw [he']
  exact circleMul_ae 1 (W g)

/-- Multiplication by the circle coordinate has no nonzero fixed vector. -/
lemma circleMul_one_fixed {g : CircleH} (hg : circleMulLI 1 g = g) : g = 0 := by
  have hznull : AddCircle.haarAddCircle ({0} : Set UnitAddCircle) = 0 := by
    have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
      simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
    rw [← hv]
    have hb := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := (0 : UnitAddCircle)) 0
    simpa using hb
  have hzAE : ∀ᵐ z ∂AddCircle.haarAddCircle, z ≠ (0 : UnitAddCircle) := by
    rw [ae_iff]
    convert hznull using 2
    ext z
    simp
  apply Lp.ext
  filter_upwards [circleMul_ae 1 g, Lp.coeFn_zero ℂ 2
    (AddCircle.haarAddCircle (T := (1 : ℝ))),
    hzAE]
    with z hz hzero hz₀
  change circleMulLI 1 g z = fourier 1 z * g z at hz
  rw [hg] at hz
  have hne : fourier 1 z ≠ (1 : ℂ) := by
    intro h
    apply hz₀
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa only [fourier_one, AddCircle.toCircle_zero, Circle.coe_one] using h
  rw [hzero]
  by_contra hgz
  exact hne ((mul_eq_right₀ hgz).1 hz.symm)

/-- The circle model excludes invariant vectors in the full centered space. -/
lemma koopman_no_fixed_of_basis {T : Equiv.Perm Torus} (hT : MeasurePreserving T μ μ)
    {f : H₀} {v : ℤ → H₀}
    (hv : ∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T^n) x))
    (ho : Orthonormal ℂ v) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H₀))
    {g : H₀} (hg : koopman hT g = g) : g = 0 := by
  obtain ⟨W, _, hW⟩ := spectral_model_of_basis hT hv ho hd
  obtain ⟨h, hh, hm⟩ := hW g
  have hh' : h = koopman hT g := by
    apply Subtype.ext
    exact Lp.ext (Filter.EventuallyEq.trans hh (Filter.EventuallyEq.symm (koopman_ae hT g)))
  have hm' : circleMulLI 1 (W g) = W g := by
    rw [hh', hg] at hm
    apply Lp.ext
    exact Filter.EventuallyEq.trans (circleMul_ae 1 (W g)) (Filter.EventuallyEq.symm hm)
  apply W.injective
  rw [map_zero]
  exact circleMul_one_fixed hm'

/-- Invariant measurable sets give centered L² fixed vectors. This establishes
ergodicity from the *full* mean-zero space, not from a proper cyclic subspace. -/
lemma ergodic_of_no_meanZero_fixed {T : Torus → Torus} (hT : MeasurePreserving T μ μ)
    (hfixed : ∀ g : H₀, koopman hT g = g → g = 0) : Ergodic T μ := by
  refine { hT with aeconst_set := ?_ }
  intro s hs hTs
  classical
  let q : Torus → ℂ := s.indicator (fun _ => 1)
  have hq : MemLp q 2 μ := (memLp_const (1 : ℂ)).indicator hs
  let c : ℂ := ∫ x, q x ∂μ
  let g₀ : H := hq.toLp q - Lp.const 2 μ c
  have hge : g₀ =ᵐ[μ] fun x => q x - c := by
    filter_upwards [Lp.coeFn_sub (hq.toLp q) (Lp.const 2 μ c),
      hq.coeFn_toLp, Lp.coeFn_const 2 μ c] with x hx hy hz
    simpa only [g₀, Pi.sub_apply, hy, hz, Function.const_apply] using hx
  have hgc : g₀ ∈ meanZero := by
    change ∫ x, g₀ x ∂μ = 0
    rw [integral_congr_ae hge, integral_sub (hq.integrable (by norm_num)) (integrable_const c)]
    simp [c]
  let g : H₀ := ⟨g₀, hgc⟩
  have hqinvar (x : Torus) : q (T x) = q x := by
    have hx : T x ∈ s ↔ x ∈ s := by
      change x ∈ T ⁻¹' s ↔ x ∈ s
      rw [hTs]
    simp only [q, indicator_apply, hx]
  have hgfix : koopman hT g = g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [koopman_ae hT g, hge, hT.quasiMeasurePreserving.ae hge]
      with x hx hy hz
    change (koopman hT g).1 x = g₀ x
    change (koopman hT g).1 x = g₀ (T x) at hx
    rw [hx, hz, hy, hqinvar]
  have hgzero : g₀ = 0 := congrArg Subtype.val (hfixed g hgfix)
  have hqc : q =ᵐ[μ] fun _ => c := by
    filter_upwards [hge, Lp.coeFn_zero ℂ 2 μ] with x hx hz
    rw [hgzero, hz] at hx
    exact sub_eq_zero.mp hx.symm
  apply Filter.eventuallyEmptyOrUniv_iff.mpr
  by_cases hc : c = 0
  · right
    filter_upwards [hqc] with x hx
    intro hxs
    simp [q, hxs, hc] at hx
  · left
    filter_upwards [hqc] with x hx
    by_contra hxs
    exact hc (by simpa [q, hxs] using hx.symm)

lemma ergodic_of_basis {T : Equiv.Perm Torus} (hT : MeasurePreserving T μ μ)
    {f : H₀} {v : ℤ → H₀}
    (hv : ∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T^n) x))
    (ho : Orthonormal ℂ v) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H₀)) :
    Ergodic T μ :=
  ergodic_of_no_meanZero_fixed hT (fun _ hg => koopman_no_fixed_of_basis hT hv ho hd hg)

/-- Once the unconditional geometric construction produces its bilateral basis,
all stated spectral and ergodic consequences follow. This lemma is not the existence theorem. -/
lemma mainConclusion_of_basis (T : Equiv.Perm Torus)
    (hs : Smooth T) (hsi : Smooth T.symm) (hT : MeasurePreserving T μ μ)
    (f : H₀) (hf : IsReal f) (v : ℤ → H₀)
    (hv : ∀ n : ℤ, ∀ᵐ x ∂μ, (v n).1 x = f.1 ((T^n) x))
    (ho : Orthonormal ℂ v) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H₀)) :
    MainConclusion := by
  refine ⟨T, hs, hsi, hT, f, hf, v, hv, ho, hd, ergodic_of_basis hT hv ho hd, ?_⟩
  obtain ⟨W, _, hW⟩ := spectral_model_of_basis hT hv ho hd
  exact ⟨W, hW⟩

end ThreeTorus
end
end

end OAI
