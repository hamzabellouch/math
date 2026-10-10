import Mathlib
import OAI.Geometry.BallPacking.Surfaces.DiagonalQuadric
import OAI.Geometry.BallPacking.Moser.BackgroundDensity

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Topology
section
variable {ι : Type*} [Fintype ι]
abbrev PlanePhase (ι : Type*) := ι → Plane

def phaseArea : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  ∑ i, planarArea.bilinearComp (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

theorem phaseArea_apply (v w : PlanePhase ι) :
    phaseArea v w = ∑ i, ((v i).1*(w i).2-(v i).2*(w i).1) := by
  simp [phaseArea]

theorem phaseArea_skew (v w : PlanePhase ι) : phaseArea v w = -phaseArea w v := by
  simp only [phaseArea_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable [DecidableEq ι]

@[simp] theorem phaseArea_single_right (v : PlanePhase ι) (i : ι) (w : Plane) :
    phaseArea v (Pi.single i w) = planarArea (v i) w := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

@[simp] theorem phaseArea_single_left (i : ι) (v : Plane) (w : PlanePhase ι) :
    phaseArea (Pi.single i v) w = planarArea v (w i) := by
  classical
  rw [phaseArea_apply,Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [hbi]
  · simp

theorem phaseArea_injective : Injective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro v w h
  funext i
  have h1 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (0,1))) h
  have h2 := congrArg (fun A : PlanePhase ι →L[ℝ] ℝ => A (Pi.single i (1,0))) h
  apply Prod.ext
  · simpa using h1
  · simpa using h2

theorem phase_decomposition (w : PlanePhase ι) :
    (∑ i, ((w i).1 • (Pi.single i ((1:ℝ),0) : PlanePhase ι) + (w i).2 • (Pi.single i ((0:ℝ),1) : PlanePhase ι))) = w := by
  funext j
  simp only [Finset.sum_apply,Pi.add_apply,Pi.smul_apply]
  rw [Finset.sum_eq_single j]
  · ext <;> simp
  · intro b _ hbj
    simp [Ne.symm hbj]
  · simp

theorem phaseArea_surjective : Surjective (phaseArea : PlanePhase ι →L[ℝ] _) := by
  intro α
  let v : PlanePhase ι := fun i => (α (Pi.single i (0,1)),-α (Pi.single i (1,0)))
  refine ⟨v,?_⟩
  ext w
  rw [←phase_decomposition w]
  simp only [map_sum,map_add,map_smul,smul_eq_mul,
    phaseArea_single_right,planarArea_apply,v,mul_zero,mul_one,sub_zero,zero_sub,neg_neg]

theorem phaseArea_isInvertible : (phaseArea : PlanePhase ι →L[ℝ] _).IsInvertible :=
  ⟨(LinearEquiv.ofBijective (phaseArea : PlanePhase ι →L[ℝ] _).toLinearMap
    ⟨phaseArea_injective,phaseArea_surjective⟩).toContinuousLinearEquiv,rfl⟩

end
section

variable {ι : Type*} [Fintype ι]

def phaseDot : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i)) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i)))

@[simp] theorem phaseDot_apply (z v : PlanePhase ι) :
    phaseDot z v = ∑ i, ((z i).1*(v i).1+(z i).2*(v i).2) := by
  simp [phaseDot]

theorem phaseDot_symm (z v : PlanePhase ι) : phaseDot z v = phaseDot v z := by
  simp only [phaseDot_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

def phaseSq (z : PlanePhase ι) : ℝ := phaseDot z z

theorem phaseSq_nonneg (z : PlanePhase ι) : 0 ≤ phaseSq z := by
  rw [phaseSq,phaseDot_apply]
  apply Finset.sum_nonneg
  intro i _
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp] theorem phaseSq_smul (a : ℝ) (z : PlanePhase ι) :
    phaseSq (a • z) = a^2 * phaseSq z := by
  simp only [phaseSq,map_smul,smul_apply,smul_eq_mul]
  ring

@[fun_prop] theorem phaseSq_smooth : ContDiff ℝ ∞ (phaseSq (ι := ι)) :=
  (phaseDot (ι := ι)).contDiff.clm_apply contDiff_id

theorem phaseSq_hasFDerivAt (z : PlanePhase ι) :
    HasFDerivAt phaseSq ((2:ℝ) • phaseDot z) z := by
  have h := phaseDot.hasFDerivAt.clm_apply (hasFDerivAt_id z)
  apply h.congr_fderiv
  ext v
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.flip_apply,id_eq,
    smul_apply,smul_eq_mul]
  rw [phaseDot_symm v z]
  ring

@[simp] theorem phaseSq_fderiv (z v : PlanePhase ι) :
    fderiv ℝ phaseSq z v = 2 * phaseDot z v := by
  rw [(phaseSq_hasFDerivAt z).fderiv]
  rfl

theorem phaseArea_self (z : PlanePhase ι) : phaseArea z z = 0 := by
  have h := phaseArea_skew z z
  linarith

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in

theorem inverse_chart_isEmbedding {f g : E → E} {U W : Set E}
    (hf : ContinuousOn f U) (hg : ContinuousOn g W)
    (himage : f '' U = W) (hl : ∀ x ∈ U, g (f x) = x)
    (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y) :
    Topology.IsEmbedding (fun y : W => g y) := by
  let e : PartialHomeomorph E E := {
    toFun := f
    invFun := g
    source := U
    target := W
    map_source' := fun x hx => himage ▸ mem_image_of_mem f hx
    map_target' := fun y hy => (hr y hy).1
    left_inv' := hl
    right_inv' := fun y hy => (hr y hy).2
    continuousOn_toFun := hf
    continuousOn_invFun := hg }
  exact e.symm.isEmbedding_restrict

theorem inverse_chart_pullback {f g : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ x ∈ U, ∀ v w,
      B (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w)
    {y : E} (hy : y ∈ W) (v w : E) :
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) = B v w := by
  have hdf : DifferentiableAt ℝ f (g y) :=
    (hf.contDiffAt (hU.mem_nhds (hr y hy).1)).differentiableAt (by simp)
  have hdg : DifferentiableAt ℝ g y :=
    (hg.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp)
  have heq : (f ∘ g) =ᶠ[𝓝 y] id :=
    Filter.eventually_of_mem (hW.mem_nhds hy) (fun z hz => (hr z hz).2)
  have hd : (fderiv ℝ f (g y)).comp (fderiv ℝ g y) = ContinuousLinearMap.id ℝ E := by
    rw [←fderiv_comp y hdf hdg,heq.fderiv_eq]
    exact fderiv_id
  calc
    A (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) =
      B (fderiv ℝ f (g y) (fderiv ℝ g y v))
        (fderiv ℝ f (g y) (fderiv ℝ g y w)) := (hform _ (hr y hy).1 _ _).symm
    _ = B v w := by
      change B ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) v)
        ((fderiv ℝ f (g y)).comp (fderiv ℝ g y) w) = _
      rw [hd]
      rfl

theorem inverse_chart_composition_pullback {f g q : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g W) (hr : ∀ y ∈ W, g y ∈ U ∧ f (g y) = y)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hform : ∀ x ∈ U, ∀ v w,
      B (fderiv ℝ f x v) (fderiv ℝ f x w) = A x v w)
    (hq : ContDiff ℝ ∞ q)
    (hqform : ∀ x v w, B (fderiv ℝ q x v) (fderiv ℝ q x w) = B v w)
    {z : E} (hz : q z ∈ W) (v w : E) :
    A ((g ∘ q) z) (fderiv ℝ (g ∘ q) z v) (fderiv ℝ (g ∘ q) z w) = B v w := by
  have hdg : DifferentiableAt ℝ g (q z) :=
    (hg.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have hdq : DifferentiableAt ℝ q z := hq.differentiable (by simp) z
  rw [fderiv_comp z hdg hdq]
  simp only [ContinuousLinearMap.comp_apply,Function.comp_apply]
  rw [inverse_chart_pullback hU hW hf hg hr A B hform hz]
  exact hqform z v w

end
section

variable {ι : Type*} [Fintype ι]

def fsBallMap (a : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  (Real.sqrt a / Real.sqrt (1+phaseSq z)) • z

def fsAffineMap (a : ℝ) (z : PlanePhase ι) : PlanePhase ι :=
  (Real.sqrt (a-phaseSq z))⁻¹ • z

def phaseOpenBall (a : ℝ) : Set (PlanePhase ι) := {z | phaseSq z < a}

theorem phaseOpenBall_open (a : ℝ) : IsOpen (phaseOpenBall (ι := ι) a) :=
  isOpen_lt phaseSq_smooth.continuous continuous_const

theorem fs_den_pos (z : PlanePhase ι) : 0 < 1+phaseSq z := by
  linarith [phaseSq_nonneg z]

@[fun_prop] theorem fsBallMap_smooth (a : ℝ) : ContDiff ℝ ∞ (fsBallMap (ι := ι) a) := by
  change ContDiff ℝ ∞ ((fun z : PlanePhase ι => Real.sqrt a / Real.sqrt (1+phaseSq z)) • (id : PlanePhase ι → PlanePhase ι))
  apply ContDiff.smul
  · exact contDiff_const.div ((contDiff_const.add phaseSq_smooth).sqrt
      (fun z => (fs_den_pos z).ne')) (fun z => (Real.sqrt_pos.2 (fs_den_pos z)).ne')
  · exact contDiff_id

theorem fsAffineMap_smoothOn (a : ℝ) :
    ContDiffOn ℝ ∞ (fsAffineMap (ι := ι) a) (phaseOpenBall a) := by
  change ContDiffOn ℝ ∞ ((fun z : PlanePhase ι => (Real.sqrt (a-phaseSq z))⁻¹) • (id : PlanePhase ι → PlanePhase ι)) (phaseOpenBall a)
  apply ContDiffOn.smul
  · apply ContDiffOn.inv
    · exact (contDiffOn_const.sub phaseSq_smooth.contDiffOn).sqrt
        (fun z hz => (sub_pos.2 hz).ne')
    · intro z hz
      exact (Real.sqrt_pos.2 (sub_pos.2 hz)).ne'
  · exact contDiffOn_id

theorem fsBallMap_sq {a : ℝ} (ha : 0 ≤ a) (z : PlanePhase ι) :
    phaseSq (fsBallMap a z) = a*phaseSq z/(1+phaseSq z) := by
  simp only [fsBallMap,phaseSq_smul,div_pow,Real.sq_sqrt ha,
    Real.sq_sqrt (fs_den_pos z).le]
  ring

theorem fsBallMap_gap {a : ℝ} (ha : 0 ≤ a) (z : PlanePhase ι) :
    a-phaseSq (fsBallMap a z) = a/(1+phaseSq z) := by
  rw [fsBallMap_sq ha]
  field_simp [(fs_den_pos z).ne']
  ring

theorem fsBallMap_mem {a : ℝ} (ha : 0 < a) (z : PlanePhase ι) :
    fsBallMap a z ∈ phaseOpenBall a := by
  change phaseSq (fsBallMap a z) < a
  have h := div_pos ha (fs_den_pos z)
  rw [←fsBallMap_gap ha.le] at h
  exact sub_pos.1 h

@[simp] theorem fsAffineMap_fsBallMap {a : ℝ} (ha : 0 < a) (z : PlanePhase ι) :
    fsAffineMap a (fsBallMap a z) = z := by
  change (Real.sqrt (a-phaseSq (fsBallMap a z)))⁻¹ • fsBallMap a z = z
  rw [fsBallMap_gap ha.le,Real.sqrt_div ha.le]
  simp only [fsBallMap,smul_smul]
  rw [inv_mul_cancel₀ (div_pos (Real.sqrt_pos.2 ha)
    (Real.sqrt_pos.2 (fs_den_pos z))).ne',one_smul]

theorem fsAffineMap_sq {a : ℝ} {z : PlanePhase ι} (hz : z ∈ phaseOpenBall a) :
    phaseSq (fsAffineMap a z) = phaseSq z/(a-phaseSq z) := by
  simp only [fsAffineMap,phaseSq_smul,inv_pow,Real.sq_sqrt (sub_pos.2 hz).le]
  ring

@[simp] theorem fsBallMap_fsAffineMap {a : ℝ} (ha : 0 < a)
    {z : PlanePhase ι} (hz : z ∈ phaseOpenBall a) : fsBallMap a (fsAffineMap a z) = z := by
  have hgap : 0 < a-phaseSq z := sub_pos.2 hz
  have heq : 1+phaseSq (fsAffineMap a z) = a/(a-phaseSq z) := by
    rw [fsAffineMap_sq hz]
    field_simp [hgap.ne']
    ring
  change (Real.sqrt a/Real.sqrt (1+phaseSq (fsAffineMap a z))) • fsAffineMap a z = z
  rw [heq,Real.sqrt_div ha.le]
  simp only [fsAffineMap,smul_smul]
  have hscalar : Real.sqrt a / (Real.sqrt a / Real.sqrt (a-phaseSq z)) *
      (Real.sqrt (a-phaseSq z))⁻¹ = 1 := by
    field_simp [(Real.sqrt_pos.2 ha).ne',(Real.sqrt_pos.2 hgap).ne']
  rw [hscalar,one_smul]

theorem fsBallMap_image {a : ℝ} (ha : 0 < a) :
    fsBallMap (ι := ι) a '' univ = phaseOpenBall a := by
  apply Subset.antisymm
  · rintro _ ⟨z,_,rfl⟩
    exact fsBallMap_mem ha z
  · intro z hz
    exact ⟨fsAffineMap a z,mem_univ _,fsBallMap_fsAffineMap ha hz⟩

theorem fsBallMap_injective {a : ℝ} (ha : 0 < a) : Injective (fsBallMap (ι := ι) a) :=
  Function.LeftInverse.injective (fsAffineMap_fsBallMap ha)

theorem fsAffineMap_isEmbedding {a : ℝ} (ha : 0 < a) :
    Topology.IsEmbedding (fun z : phaseOpenBall (ι := ι) a => fsAffineMap a z.1) :=
  inverse_chart_isEmbedding (fsBallMap_smooth a).continuous.continuousOn
    (fsAffineMap_smoothOn a).continuousOn (fsBallMap_image ha)
    (fun z _ => fsAffineMap_fsBallMap ha z)
    (fun _ hz => ⟨mem_univ _,fsBallMap_fsAffineMap ha hz⟩)

def fsBallDifferential (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] PlanePhase ι :=
  (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
    (ContinuousLinearMap.id ℝ _ - ((1+phaseSq z)⁻¹ • phaseDot z).smulRight z)

theorem fsBallDifferential_apply (a : ℝ) (z v : PlanePhase ι) :
    fsBallDifferential a z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  simp only [fsBallDifferential,smul_apply,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  simp only [div_eq_mul_inv]
  rw [mul_comm ((1+phaseSq z)⁻¹) (phaseDot z v)]

theorem fsBallMap_hasFDerivAt (a : ℝ) (z : PlanePhase ι) :
    HasFDerivAt (fsBallMap a) (fsBallDifferential a z) z := by
  have hs : HasFDerivAt (fun y : PlanePhase ι => 1+phaseSq y)
      ((2:ℝ) • phaseDot z) z := by
    exact (phaseSq_hasFDerivAt z).const_add 1
  have ht := hs.sqrt (fs_den_pos z).ne'
  have hc := ((hasDerivAt_inv (Real.sqrt_pos.2 (fs_den_pos z)).ne').comp_hasFDerivAt z ht).const_mul (Real.sqrt a)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a/Real.sqrt (1+phaseSq y))
      ((-(Real.sqrt a / Real.sqrt (1+phaseSq z))/(1+phaseSq z)) • phaseDot z) z := by
    change HasFDerivAt (fun y : PlanePhase ι => Real.sqrt a*(Real.sqrt (1+phaseSq y))⁻¹) _ z
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    have hq := Real.sq_sqrt (fs_den_pos z).le
    field_simp [(Real.sqrt_pos.2 (fs_den_pos z)).ne',(fs_den_pos z).ne']
    rw [hq]
  apply (hc'.smul (hasFDerivAt_id z)).congr_fderiv
  ext v i <;>
    simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,id_eq,fsBallDifferential_apply,
      Pi.add_apply,Pi.smul_apply,Pi.sub_apply,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

@[simp] theorem fsBallMap_fderiv (a : ℝ) (z v : PlanePhase ι) :
    fderiv ℝ (fsBallMap a) z v = (Real.sqrt a / Real.sqrt (1+phaseSq z)) •
      (v-(phaseDot z v/(1+phaseSq z)) • z) := by
  rw [(fsBallMap_hasFDerivAt a z).fderiv,fsBallDifferential_apply]

def affineFSForm (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ :=
  (a/(1+phaseSq z)) • phaseArea - (a/(1+phaseSq z)^2) •
    ((phaseDot z).smulRight (phaseArea z) - (phaseArea z).smulRight (phaseDot z))

theorem affineFSForm_apply (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z v w = a/(1+phaseSq z)*phaseArea v w - a/(1+phaseSq z)^2*
      (phaseDot z v*phaseArea z w-phaseArea z v*phaseDot z w) := by
  simp only [affineFSForm,sub_apply,smul_apply,ContinuousLinearMap.smulRight_apply,smul_eq_mul]

theorem fsBallMap_pullback {a : ℝ} (ha : 0 ≤ a) (z v w : PlanePhase ι) :
    phaseArea (fderiv ℝ (fsBallMap a) z v) (fderiv ℝ (fsBallMap a) z w) =
      affineFSForm a z v w := by
  rw [fsBallMap_fderiv,fsBallMap_fderiv,affineFSForm_apply]
  simp only [map_smul,map_sub,smul_apply,sub_apply,smul_eq_mul,phaseArea_self,mul_zero,sub_zero]
  rw [phaseArea_skew v z]
  have hs : (Real.sqrt a/Real.sqrt (1+phaseSq z))^2 = a/(1+phaseSq z) := by
    rw [div_pow,Real.sq_sqrt ha,Real.sq_sqrt (fs_den_pos z).le]
  calc
    _ = (Real.sqrt a/Real.sqrt (1+phaseSq z))^2 *
        (phaseArea v w - (phaseDot z v*phaseArea z w-phaseArea z v*phaseDot z w)/(1+phaseSq z)) := by ring
    _ = _ := by rw [hs]; field_simp [(fs_den_pos z).ne']

theorem fsAffineMap_pullback {a : ℝ} (ha : 0 < a) {z : PlanePhase ι}
    (hz : z ∈ phaseOpenBall a) (v w : PlanePhase ι) :
    affineFSForm a (fsAffineMap a z)
      (fderiv ℝ (fsAffineMap a) z v) (fderiv ℝ (fsAffineMap a) z w) = phaseArea v w := by
  apply inverse_chart_pullback isOpen_univ (phaseOpenBall_open a)
    (fsBallMap_smooth a).contDiffOn (fsAffineMap_smoothOn a)
    (fun y hy => ⟨Set.mem_univ _,fsBallMap_fsAffineMap ha hy⟩)
    (affineFSForm a) phaseArea (fun y _ => fsBallMap_pullback ha.le y) hz

def affineFSPrimitive (a : ℝ) (z : PlanePhase ι) : PlanePhase ι →L[ℝ] ℝ :=
  (a/(2*(1+phaseSq z))) • phaseArea z

theorem affineFSPrimitive_smooth (a : ℝ) :
    ContDiff ℝ ∞ (affineFSPrimitive a : PlanePhase ι → _) := by
  have hc : ContDiff ℝ ∞ (fun z : PlanePhase ι => a/(2*(1+phaseSq z))) :=
    contDiff_const.div (contDiff_const.mul (contDiff_const.add phaseSq_smooth))
      (fun z => mul_ne_zero (by norm_num) (fs_den_pos z).ne')
  exact hc.smul (phaseArea (ι := ι)).contDiff

theorem affineFSPrimitive_fderiv (a : ℝ) (z v w : PlanePhase ι) :
    fderiv ℝ (affineFSPrimitive a) z v w =
      a/(2*(1+phaseSq z))*phaseArea v w -
        a/(1+phaseSq z)^2*phaseDot z v*phaseArea z w := by
  have hs : HasFDerivAt (fun y : PlanePhase ι => 1+phaseSq y)
      ((2:ℝ) • phaseDot z) z := (phaseSq_hasFDerivAt z).const_add 1
  have hc := ((hasDerivAt_inv (fs_den_pos z).ne').comp_hasFDerivAt z hs).const_mul (a/2)
  have hc' : HasFDerivAt (fun y : PlanePhase ι => a/(2*(1+phaseSq y)))
      ((-a/(1+phaseSq z)^2) • phaseDot z) z := by
    have he : (fun y : PlanePhase ι => a/(2*(1+phaseSq y))) =
        (fun y => a/2 * ((1+phaseSq y))⁻¹) := by funext y; field_simp [(fs_den_pos y).ne']
    rw [he]
    apply hc.congr_fderiv
    ext v
    simp only [smul_apply,smul_eq_mul,smul_smul]
    ring
  have hd := hc'.smul (phaseArea (ι := ι)).hasFDerivAt
  rw [show fderiv ℝ (affineFSPrimitive a) z = _ from hd.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem affineFSPrimitive_exterior (a : ℝ) (z v w : PlanePhase ι) :
    fderiv ℝ (affineFSPrimitive a) z v w -
      fderiv ℝ (affineFSPrimitive a) z w v = affineFSForm a z v w := by
  rw [affineFSPrimitive_fderiv,affineFSPrimitive_fderiv,affineFSForm_apply,
    phaseArea_skew w v]
  field_simp [(fs_den_pos z).ne']
  ring

def phaseJ : PlanePhase ι →L[ℝ] PlanePhase ι :=
  ContinuousLinearMap.pi fun i =>
    (-((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))).prod
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.proj i))

omit [Fintype ι] in
@[simp] theorem phaseJ_apply (z : PlanePhase ι) (i : ι) :
    phaseJ z i = (-(z i).2,(z i).1) := rfl

omit [Fintype ι] in
@[simp] theorem phaseJ_sq (z : PlanePhase ι) : phaseJ (phaseJ z) = -z := by
  ext i <;> simp

@[simp] theorem phaseDot_J_right (z v : PlanePhase ι) :
    phaseDot z (phaseJ v) = -phaseArea z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseDot_J_left (z v : PlanePhase ι) :
    phaseDot (phaseJ z) v = phaseArea z v := by
  rw [phaseDot_symm,phaseDot_J_right,phaseArea_skew v z,neg_neg]

@[simp] theorem phaseArea_J_right (z v : PlanePhase ι) :
    phaseArea z (phaseJ v) = phaseDot z v := by
  simp only [phaseDot_apply,phaseArea_apply,phaseJ_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem phaseArea_J_left (z v : PlanePhase ι) :
    phaseArea (phaseJ z) v = -phaseDot z v := by
  rw [phaseArea_skew,phaseArea_J_right,phaseDot_symm]

@[simp] theorem phaseDot_J_J (z v : PlanePhase ι) :
    phaseDot (phaseJ z) (phaseJ v) = phaseDot z v := by
  rw [phaseDot_J_left,phaseArea_J_right]

theorem phaseSq_eq_zero_iff (z : PlanePhase ι) : phaseSq z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    funext i
    have hi : (z i).1*(z i).1+(z i).2*(z i).2 ≤ phaseSq z := by
      rw [phaseSq,phaseDot_apply]
      exact Finset.single_le_sum (f := fun j => (z j).1*(z j).1+(z j).2*(z j).2) (fun j _ =>
        add_nonneg (mul_self_nonneg (z j).1) (mul_self_nonneg (z j).2)) (Finset.mem_univ i)
    rw [hz] at hi
    apply Prod.ext <;> dsimp
    · nlinarith [sq_nonneg (z i).2]
    · nlinarith [sq_nonneg (z i).1]
  · rintro rfl
    simp [phaseSq]

theorem phaseSq_pos {z : PlanePhase ι} (hz : z ≠ 0) : 0 < phaseSq z :=
  lt_of_le_of_ne (phaseSq_nonneg z) (fun h => hz ((phaseSq_eq_zero_iff z).mp h.symm))

theorem phase_complex_cauchy (z v : PlanePhase ι) :
    (phaseDot z v)^2+(phaseArea z v)^2 ≤ phaseSq z*phaseSq v := by
  by_cases hz : z=0
  · subst z
    simp [phaseSq]
  have hq := phaseSq_pos hz
  have h := phaseSq_nonneg (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z)
  have he : phaseSq (phaseSq z • v - phaseDot z v • z - phaseArea z v • phaseJ z) =
      (phaseSq z)^2*phaseSq v-phaseSq z*((phaseDot z v)^2+(phaseArea z v)^2) := by
    simp only [phaseSq,map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,
      phaseDot_J_left,phaseDot_J_right,phaseArea_J_left,phaseArea_self]
    rw [phaseDot_symm v z,phaseArea_skew v z]
    ring
  rw [he] at h
  have hm : 0 ≤ phaseSq z*(phaseSq z*phaseSq v-((phaseDot z v)^2+(phaseArea z v)^2)) := by
    nlinarith only [h]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hq).mp hm)

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def horizontalSystem (Ω : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] F) :
    (E × (F →L[ℝ] ℝ)) →L[ℝ] ((E →L[ℝ] ℝ) × F) :=
  ((Ω.comp (ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ))) -
    (((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp (ContinuousLinearMap.snd ℝ E (F →L[ℝ] ℝ)))).prod
    (A.comp (ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ)))

@[simp] theorem horizontalSystem_apply (Ω : E →L[ℝ] E →L[ℝ] ℝ)
    (A : E →L[ℝ] F) (v : E) (l : F →L[ℝ] ℝ) :
    horizontalSystem Ω A (v,l) = (Ω v - l.comp A, A v) := rfl

theorem horizontalSystem_injective {Ω : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] F}
    (hA : Surjective A)
    (hV : ∀ v, A v = 0 → (∀ w, A w = 0 → Ω v w = 0) → v = 0) :
    Injective (horizontalSystem Ω A) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  rintro ⟨v,l⟩ h
  have h2 : A v = 0 := congrArg Prod.snd h
  have h1 : Ω v = l.comp A := sub_eq_zero.mp (congrArg Prod.fst h)
  have hv : v = 0 := hV v h2 (fun w hw => by rw [h1]; simp [hw])
  subst v
  have hl : l = 0 := by
    ext z
    obtain ⟨w,rfl⟩ := hA z
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) h1
    simpa using hh.symm
  simp [hl]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem finrank_continuous_dual : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

theorem horizontalSystem_isInvertible {Ω : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] F}
    (hA : Surjective A)
    (hV : ∀ v, A v = 0 → (∀ w, A w = 0 → Ω v w = 0) → v = 0) :
    (horizontalSystem Ω A).IsInvertible := by
  have he : Module.finrank ℝ (E × (F →L[ℝ] ℝ)) =
      Module.finrank ℝ ((E →L[ℝ] ℝ) × F) := by
    simp only [Module.finrank_prod,finrank_continuous_dual]
  have hI := horizontalSystem_injective hA hV
  have hS : Surjective (horizontalSystem Ω A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he).mp hI
  exact ⟨(LinearEquiv.ofBijective (horizontalSystem Ω A).toLinearMap ⟨hI,hS⟩).toContinuousLinearEquiv,rfl⟩

def symplecticHorizontalLift (Ω : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] F) : F →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E (F →L[ℝ] ℝ)).comp
    ((horizontalSystem Ω A).inverse.comp (ContinuousLinearMap.inr ℝ (E →L[ℝ] ℝ) F))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem symplecticHorizontalLift_projects {Ω : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] F}
    (h : (horizontalSystem Ω A).IsInvertible) (b : F) :
    A (symplecticHorizontalLift Ω A b) = b := by
  exact congrArg Prod.snd (h.self_apply_inverse (0,b))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem symplecticHorizontalLift_orthogonal {Ω : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] F}
    (h : (horizontalSystem Ω A).IsInvertible) (b : F) {w : E} (hw : A w = 0) :
    Ω (symplecticHorizontalLift Ω A b) w = 0 := by
  have he := congrArg (fun p : (E →L[ℝ] ℝ) × F => p.1 w) (h.self_apply_inverse (0,b))
  change Ω (symplecticHorizontalLift Ω A b) w -
    ((horizontalSystem Ω A).inverse (0,b)).2 (A w) = 0 at he
  simpa only [hw,map_zero,sub_zero] using he

end
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem bilinear_injective_of_taming {Ω : E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (h : ∀ v, v ≠ 0 → 0 < Ω v (J v)) : Injective Ω := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  change Ω v = 0 at hv
  by_contra hn
  have hp := h v hn
  rw [hv] at hp
  simp at hp

variable [FiniteDimensional ℝ E]

theorem bilinear_isInvertible_of_taming {Ω : E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (h : ∀ v, v ≠ 0 → 0 < Ω v (J v)) : Ω.IsInvertible := by
  have hI := bilinear_injective_of_taming h
  have hS : Surjective Ω :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := E)).symm).mp hI
  exact ⟨(LinearEquiv.ofBijective Ω.toLinearMap ⟨hI,hS⟩).toContinuousLinearEquiv,rfl⟩

omit [FiniteDimensional ℝ E] in

theorem convex_form_taming {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {J : E → E}
    (h₀ : ∀ v, v ≠ 0 → 0 < Ω₀ v (J v))
    (h₁ : ∀ v, v ≠ 0 → 0 < Ω₁ v (J v)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (v : E) (hv : v ≠ 0) :
    0 < ((1-t) • Ω₀ + t • Ω₁) v (J v) := by
  simp only [add_apply,smul_apply,smul_eq_mul]
  have h0 := h₀ v hv
  have h1 := h₁ v hv
  nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (le_of_lt h0),
    mul_nonneg ht.1 (le_of_lt h1)]

variable [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in

theorem complex_pullback_isInvertible {Ω : E →L[ℝ] E →L[ℝ] ℝ}
    {i : F →L[ℝ] E} {J : E → E} {j : F → F}
    (hΩ : ∀ v, v ≠ 0 → 0 < Ω v (J v)) (hi : Injective i)
    (hj : ∀ v, i (j v) = J (i v)) : (Ω.bilinearComp i i).IsInvertible := by
  apply bilinear_isInvertible_of_taming (J := j)
  intro v hv
  change 0 < Ω (i v) (i (j v))
  rw [hj]
  exact hΩ (i v) (fun he => hv (hi (he.trans (map_zero i).symm)))

end

variable {ι : Type*} [Fintype ι]

theorem affineFSForm_eq_exterior (a : ℝ) :
    (affineFSForm a : PlanePhase ι → _) = euclideanExteriorOneForm (affineFSPrimitive a) := by
  funext z
  ext v w
  exact (affineFSPrimitive_exterior a z v w).symm

theorem affineFSForm_smooth (a : ℝ) : ContDiff ℝ ∞ (affineFSForm a : PlanePhase ι → _) := by
  rw [affineFSForm_eq_exterior]
  exact euclideanExteriorOneForm_smooth (affineFSPrimitive_smooth a)

theorem affineFSForm_closed (a : ℝ) (z u v w : PlanePhase ι) :
    fderiv ℝ (affineFSForm a) z u v w - fderiv ℝ (affineFSForm a) z v u w +
      fderiv ℝ (affineFSForm a) z w u v = 0 := by
  rw [affineFSForm_eq_exterior]
  exact euclideanExteriorOneForm_closed (affineFSPrimitive_smooth a) z u v w

theorem affineFSForm_skew (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z v w = -affineFSForm a z w v := by
  rw [affineFSForm_apply,affineFSForm_apply,phaseArea_skew v w]
  ring

theorem affineFSForm_J (a : ℝ) (z v w : PlanePhase ι) :
    affineFSForm a z (phaseJ v) (phaseJ w) = affineFSForm a z v w := by
  simp only [affineFSForm_apply,phaseArea_J_right,phaseDot_J_left,phaseDot_J_right]
  ring

theorem affineFSForm_positive {a : ℝ} (ha : 0<a) (z v : PlanePhase ι) (hv : v≠0) :
    0 < affineFSForm a z v (phaseJ v) := by
  rw [affineFSForm_apply,phaseArea_J_right,phaseArea_J_right,phaseDot_J_right]
  change 0 < a/(1+phaseSq z)*phaseSq v - a/(1+phaseSq z)^2 *
    (phaseDot z v*phaseDot z v-phaseArea z v*(-phaseArea z v))
  have he : a/(1+phaseSq z)*phaseSq v - a/(1+phaseSq z)^2 *
      (phaseDot z v*phaseDot z v-phaseArea z v*(-phaseArea z v)) =
      a/(1+phaseSq z)^2 * ((1+phaseSq z)*phaseSq v-
        ((phaseDot z v)^2+(phaseArea z v)^2)) := by
    field_simp [(fs_den_pos z).ne']
    ring
  rw [he]
  apply mul_pos (div_pos ha (sq_pos_of_pos (fs_den_pos z)))
  have hc := phase_complex_cauchy z v
  have hp := phaseSq_pos hv
  nlinarith

theorem affineFSForm_isInvertible {a : ℝ} (ha : 0<a) (z : PlanePhase ι) :
    (affineFSForm a z).IsInvertible :=
  bilinear_isInvertible_of_taming (J := phaseJ) (affineFSForm_positive ha z)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function
open Hamiltonian

 def affinePhase (m : ℕ) : Affine m →L[ℝ] PlanePhase (Option (Fin m)) :=
  ContinuousLinearMap.pi fun j => match j with
    | none => Complex.equivRealProdCLM.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ ℂ (Fin m → ℂ))
    | some j => Complex.equivRealProdCLM.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℝ ℂ (Fin m → ℂ)))

@[simp] theorem affinePhase_none (m : ℕ) (z : Affine m) :
    affinePhase m z none=(z.1.re,z.1.im) := rfl
@[simp] theorem affinePhase_some (m : ℕ) (z : Affine m) (j : Fin m) :
    affinePhase m z (some j)=((z.2 j).re,(z.2 j).im) := rfl

theorem affinePhase_injective (m : ℕ) : Injective (affinePhase m) := by
  intro z w h
  apply Prod.ext
  · apply Complex.ext
    · exact congrArg Prod.fst (congrFun h none)
    · exact congrArg Prod.snd (congrFun h none)
  · funext j
    apply Complex.ext
    · exact congrArg Prod.fst (congrFun h (some j))
    · exact congrArg Prod.snd (congrFun h (some j))

theorem affinePhase_I (m : ℕ) (z : Affine m) :
    affinePhase m (Complex.I • z)=phaseJ (affinePhase m z) := by
  funext j
  cases j <;> simp [Pi.smul_apply,Complex.mul_re,Complex.mul_im]

 def realPhaseDerivative {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    (ℝ × ℝ) →L[ℝ] PlanePhase (Option (Fin m)) :=
  (affinePhase m).comp ((L.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)

@[simp] theorem realPhaseDerivative_one {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    realPhaseDerivative L (1,0)=affinePhase m (L 1) := rfl

 theorem realPhaseDerivative_I {m : ℕ} (L : ℂ →L[ℂ] Affine m) :
    realPhaseDerivative L (0,1)=phaseJ (realPhaseDerivative L (1,0)) := by
  change affinePhase m (L Complex.I)=phaseJ (affinePhase m (L 1))
  have hL := L.map_smul Complex.I (1 : ℂ)
  rw [smul_eq_mul,mul_one] at hL
  rw [hL]
  exact affinePhase_I m (L 1)

 theorem affineFSForm_holomorphic_positive {m : ℕ} {c : ℝ} (hc : 0<c)
    (z : Affine m) (L : ℂ →L[ℂ] Affine m) (hL : L 1≠0) :
    0<affineFSForm c (affinePhase m z) (realPhaseDerivative L (1,0))
      (realPhaseDerivative L (0,1)) := by
  rw [realPhaseDerivative_I]
  apply affineFSForm_positive hc
  rw [realPhaseDerivative_one]
  intro hz
  apply hL
  exact affinePhase_injective m (by simpa using hz)

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
