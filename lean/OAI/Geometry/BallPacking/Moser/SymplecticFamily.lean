import Mathlib
import OAI.Geometry.BallPacking.Moser.DiskMoser

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def familyGenerator (φ : P → Plane ≃ₜ Plane) (v : P) (p : P × Plane) : Plane :=
  fderiv ℝ (fun q : P × Plane => φ q.1 q.2) (p.1,(φ p.1).symm p.2) (v,0)

theorem familyGenerator_smooth (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2)) (v : P) :
    ContDiff ℝ ∞ (familyGenerator φ v) :=
  ((hφ.fderiv_right (by simp)).comp (contDiff_fst.prodMk hφi)).clm_apply contDiff_const

theorem fderiv_apply_const {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {F : E → G}
    (hF : ContDiff ℝ ∞ F) (p v w : E) :
    fderiv ℝ (fun p => fderiv ℝ F p v) p w = fderiv ℝ (fderiv ℝ F) p w v := by
  have hFd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hh := (hFd.differentiable (by simp) p).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem family_symplectic_variation {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F)
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (fun x => F (y,x)) x u)
      (fderiv ℝ (fun x => F (y,x)) x w) = planarArea u w)
    (y v : P) (x u w : Plane) :
    planarArea (fderiv ℝ (fderiv ℝ F) (y,x) (0,u) (v,0))
        (fderiv ℝ F (y,x) (0,w)) +
      planarArea (fderiv ℝ F (y,x) (0,u))
        (fderiv ℝ (fderiv ℝ F) (y,x) (0,w) (v,0)) = 0 := by
  have hFdd : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hFd := hFdd.differentiable (by simp)
  have hf (d : Plane) : Differentiable ℝ (fun p : P × Plane => fderiv ℝ F p (0,d)) :=
    hFd.clm_apply (differentiable_const _)
  have he : (fun p : P × Plane => planarArea (fderiv ℝ F p (0,u))
      (fderiv ℝ F p (0,w))) = fun _ => planarArea u w := by
    funext p
    have hh := hsp p.1 p.2 u w
    simpa only [family_spatial_fderiv hF,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hh
  have hd := planarArea.hasFDerivAt_of_bilinear ((hf u (y,x)).hasFDerivAt)
    ((hf w (y,x)).hasFDerivAt)
  have hz := hd.fderiv
  rw [he,fderiv_const_apply] at hz
  have hh := congrArg (fun A : P × Plane →L[ℝ] ℝ => A (v,0)) hz
  simp only [zero_apply,add_apply,ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply,fderiv_apply_const hF] at hh
  have hs : IsSymmSndFDerivAt ℝ F (y,x) := hF.contDiffAt.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq (v,0) (0,u),hs.eq (v,0) (0,w)] at hh
  linarith

theorem familyGenerator_fderiv_image (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (y v : P) (x u : Plane) :
    fderiv ℝ (fun z => familyGenerator φ v (y,z)) (φ y x) (fderiv ℝ (φ y) x u) =
      fderiv ℝ (fderiv ℝ (fun p : P × Plane => φ p.1 p.2)) (y,x) (0,u) (v,0) := by
  let F : P × Plane → Plane := fun p => φ p.1 p.2
  let V : P × Plane → Plane := fun p => fderiv ℝ F p (v,0)
  have hFD : ContDiff ℝ ∞ (fderiv ℝ F) := hφ.fderiv_right (by simp)
  have hV : ContDiff ℝ ∞ V := hFD.clm_apply contDiff_const
  have hG := familyGenerator_smooth φ hφ hφi v
  have hGy : Differentiable ℝ (fun z => familyGenerator φ v (y,z)) :=
    (hG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hφy : Differentiable ℝ (φ y) :=
    (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
  have he : (fun z => familyGenerator φ v (y,φ y z)) = fun z => V (y,z) := by
    funext z
    simp [familyGenerator,V,F]
  have hc := fderiv_comp x (hGy (φ y x)) (hφy x)
  have hec : ((fun z => familyGenerator φ v (y,z)) ∘ φ y) = fun z => V (y,z) := he
  rw [hec,family_spatial_fderiv hV] at hc
  have hh := congrArg (fun A : Plane →L[ℝ] Plane => A u) hc.symm
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    V,fderiv_apply_const (F := F) hφ,F] using hh

theorem family_fderiv_right_inverse (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (y : P) (z u : Plane) :
    fderiv ℝ (φ y) ((φ y).symm z) (fderiv ℝ (φ y).symm z u) = u := by
  have hφy : Differentiable ℝ (φ y) :=
    (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
  have hφyi : Differentiable ℝ (φ y).symm :=
    (hφi.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
  have he := fderiv_comp z (hφy ((φ y).symm z)) (hφyi z)
  have hid : ((φ y) ∘ (φ y).symm) = id := funext (fun z => (φ y).apply_symm_apply z)
  rw [hid,fderiv_id] at he
  have hh := congrArg (fun A : Plane →L[ℝ] Plane => A u) he.symm
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh

theorem familyGenerator_infinitesimal (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (φ y) x u)
      (fderiv ℝ (φ y) x w) = planarArea u w)
    (y v : P) (z u w : Plane) :
    planarArea (fderiv ℝ (fun z => familyGenerator φ v (y,z)) z u) w +
      planarArea u (fderiv ℝ (fun z => familyGenerator φ v (y,z)) z w) = 0 := by
  let x := (φ y).symm z
  let a := fderiv ℝ (φ y).symm z u
  let b := fderiv ℝ (φ y).symm z w
  have hu : fderiv ℝ (φ y) x a = u := family_fderiv_right_inverse φ hφ hφi y z u
  have hw : fderiv ℝ (φ y) x b = w := family_fderiv_right_inverse φ hφ hφi y z w
  have hvu := familyGenerator_fderiv_image φ hφ hφi y v x a
  have hvw := familyGenerator_fderiv_image φ hφ hφi y v x b
  have he : φ y x = z := (φ y).apply_symm_apply z
  rw [he,hu] at hvu
  rw [he,hw] at hvw
  have hh := family_symplectic_variation hφ hsp y v x a b
  have hfu : fderiv ℝ (fun p : P × Plane => φ p.1 p.2) (y,x) (0,a) = u := by
    simpa only [family_spatial_fderiv hφ,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hu
  have hfw : fderiv ℝ (fun p : P × Plane => φ p.1 p.2) (y,x) (0,b) = w := by
    simpa only [family_spatial_fderiv hφ,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using hw
  rw [hfu,hfw,← hvu,← hvw] at hh
  exact hh

theorem familyGenerator_support (φ : P → Plane ≃ₜ Plane) (v : P) :
    tsupport (familyGenerator φ v) ⊆ tsupport (fun p : P × Plane => φ p.1 p.2-p.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have hfix : φ p.1 p.2 = p.2 := sub_eq_zero.mp
    (image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => φ p.1 p.2-p.2) hn)
  have hinv : (φ p.1).symm p.2 = p.2 := by
    apply (φ p.1).injective
    rw [(φ p.1).apply_symm_apply,hfix]
  have he : (fun q : P × Plane => φ q.1 q.2) =ᶠ[𝓝 p] Prod.snd := by
    filter_upwards [(isClosed_tsupport (fun p : P × Plane => φ p.1 p.2-p.2)).isOpen_compl.mem_nhds hn] with q hq
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => φ p.1 p.2-p.2) hq)
  apply hp
  dsimp [familyGenerator]
  rw [hinv,show (p.1,p.2) = p from Prod.eta p,he.fderiv_eq]
  rw [fderiv_snd]
  rfl

variable [FiniteDimensional ℝ P]

theorem exists_hamiltonian_of_symplectic_family (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hφc : HasCompactSupport (fun p : P × Plane => φ p.1 p.2-p.2))
    {R : ℝ} (hR : 0 < R)
    (hφs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hsp : ∀ y x u w, planarArea (fderiv ℝ (φ y) x u)
      (fderiv ℝ (φ y) x w) = planarArea u w) (v : P) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (-planarArea (familyGenerator φ v (y,x))) x) ∧
      ∀ y, (∀ x, familyGenerator φ v (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  let α : P × Plane → Plane →L[ℝ] ℝ := fun p => -planarArea (familyGenerator φ v p)
  have hG := familyGenerator_smooth φ hφ hφi v
  have hα : ContDiff ℝ ∞ α := (planarArea.contDiff.comp hG).neg
  have hsα : tsupport α ⊆ tsupport (fun p : P × Plane => φ p.1 p.2-p.2) := by
    apply Subset.trans _ (familyGenerator_support φ v)
    apply closure_minimal _ (isClosed_tsupport _)
    intro p hp
    by_contra hn
    apply hp
    simp [α,image_eq_zero_of_notMem_tsupport (f := familyGenerator φ v) hn]
  have hαc : HasCompactSupport α := hφc.of_isClosed_subset (isClosed_tsupport _) hsα
  have hαs : tsupport α ⊆ univ ×ˢ roundDisk R := hsα.trans hφs
  have hd (y : P) (x : Plane) : fderiv ℝ (fun x => α (y,x)) x =
      -(planarArea.comp (fderiv ℝ (fun x => familyGenerator φ v (y,x)) x)) := by
    have hGy := (hG.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
    exact ((planarArea.hasFDerivAt.comp x (hGy x).hasFDerivAt).neg).fderiv
  have hclosed (y : P) (x u w : Plane) :
      fderiv ℝ (fun x => α (y,x)) x u w = fderiv ℝ (fun x => α (y,x)) x w u := by
    rw [hd]
    simp only [neg_apply,ContinuousLinearMap.comp_apply]
    have hh := familyGenerator_infinitesimal φ hφ hφi hsp y v x u w
    have hskew (a b : Plane) : planarArea a b = -planarArea b a := by
      simp only [planarArea_apply]
      ring
    rw [hskew u] at hh
    linarith
  obtain ⟨H,hH,hHc,hHs,hHd,hH0⟩ := exists_parametric_disk_closed_primitive hα hαc hR hαs hclosed
  refine ⟨H,hH,hHc,hHs,hHd,?_⟩
  intro y hy
  apply hH0
  intro x
  simp [α,hy]


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem timeStep_preserves_form {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (x v w : E) :
    Ω (t+h,timeStep X hX h t x)
      (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) =
      Ω (t,x) v w := by
  let Y := clockField X
  let hY := clockField_lipschitz X hX
  let u := fixedStep Y hY h (t,x)
  let A := fderiv ℝ (fixedStep Y hY h) (t,x)
  let D : C(Time,(ℝ × E) →L[ℝ] (ℝ × E)) :=
    ⟨fun s => fderiv ℝ Y (u s),
      ((clockField_smooth X hXs).continuous_fderiv (by simp)).comp u.continuous⟩
  have hA (z : ℝ × E) : A z = constantPath z + h • pathIntegral (pathLinear D (A z)) :=
    congrArg (fun T : (ℝ × E) →L[ℝ] C(Time,ℝ × E) => T z)
      (fixedStep_variation Y hY (clockField_smooth X hXs) hh (t,x))
  have hA0 (z : ℝ × E) : extendPath (A z) 0 = z := by
    have he := congrArg (fun V : C(Time,ℝ × E) => V ⟨0,by simp⟩) (hA z)
    exact (extendPath_coe (A z) ⟨0,by simp⟩).trans (by simpa using he)
  let V : E → ℝ → E := fun z s => (extendPath (A (0,z)) s).2
  have hhor (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      extendPath (A (0,z)) s = (0,V z s) := by
    apply Prod.ext
    · rw [show extendPath (A (0,z)) s = A (0,z) ⟨s,hs⟩ from extendPath_coe _ ⟨s,hs⟩]
      exact fixedStep_variation_clock X hX hXs hh (t,x) z ⟨s,hs⟩
    · rfl
  have hVd (z : E) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivWithinAt (V z) (h • fderiv ℝ X (extendPath u s) (0,V z s)) (Icc (0:ℝ) 1) s := by
    have hd := (path_equation_derivative _ _ (0,z) h (hA (0,z)) hs).snd
    change HasDerivWithinAt (V z)
      (h • (fderiv ℝ Y (extendPath u s) (extendPath (A (0,z)) s)).2) _ s at hd
    rw [hhor z s hs,clockField_fderiv hXs] at hd
    exact hd
  let F : ℝ → ℝ := fun s => Ω (extendPath u s) (V v s) (V w s)
  have hFc : Continuous F := ((hΩ.continuous.comp (extendPath u).continuous).clm_apply
    (extendPath (A (0,v))).continuous.snd).clm_apply (extendPath (A (0,w))).continuous.snd
  have hFd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le,hs.2.le⟩
    have hUd := fixedStep_derivative Y hY hh (t,x) hs'
    have hΩd := ((hΩ.differentiable (by simp) (extendPath u s)).hasFDerivAt).comp_hasDerivWithinAt s hUd
    have hd := (hΩd.clm_apply (hVd v s hs')).clm_apply (hVd w s hs')
    have hz : (fderiv ℝ Ω (extendPath u s) (h • Y (extendPath u s)) (V v s) +
        Ω (extendPath u s) (h • fderiv ℝ X (extendPath u s) (0,V v s))) (V w s) +
        Ω (extendPath u s) (V v s) (h • fderiv ℝ X (extendPath u s) (0,V w s)) = 0 := by
      simp only [map_smul,smul_apply,smul_eq_mul,add_apply]
      have he := hPDE (extendPath u s) (V v s) (V w s)
      change fderiv ℝ Ω (extendPath u s) (Y (extendPath u s)) (V v s) (V w s) +
        Ω (extendPath u s) (fderiv ℝ X (extendPath u s) (0,V v s)) (V w s) +
        Ω (extendPath u s) (V v s) (fderiv ℝ X (extendPath u s) (0,V w s)) = 0 at he
      linear_combination h * he
    have hd0 : HasDerivWithinAt F 0 (Icc (0:ℝ) 1) s := hd.congr_deriv hz
    exact hd0.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ) ≤ 1)
    hFc.continuousOn hFd (intervalIntegrable_const (c := (0:ℝ)))
  have hend : F 1 = F 0 := sub_eq_zero.mp (by simpa using hi.symm)
  have hzero : F 0 = Ω (t,x) v w := by
    change Ω (extendPath u 0) (extendPath (A (0,v)) 0).2 (extendPath (A (0,w)) 0).2 = _
    rw [hA0,hA0,show extendPath u 0 = (t,x) from
      (extendPath_coe u ⟨0,by simp⟩).trans (fixedStep_initial Y hY hh (t,x))]
  have hfinal : extendPath u 1 = (t+h,timeStep X hX h t x) := by
    rw [show extendPath u 1 = u ⟨1,by simp⟩ from extendPath_coe u ⟨1,by simp⟩]
    exact Prod.ext (stepEndpoint_clock X hX hh (t,x)) rfl
  have hfinalV (z : E) : V z 1 = fderiv ℝ (timeStep X hX h t) x z := by
    rw [timeStep_fderiv X hX hXs hh, stepEndpoint_fderiv Y hY (clockField_smooth X hXs) hh]
    exact congrArg Prod.snd (extendPath_coe (A (0,z)) ⟨1,by simp⟩)
  have hone : F 1 = Ω (t+h,timeStep X hX h t x) (fderiv ℝ (timeStep X hX h t) x v) (fderiv ℝ (timeStep X hX h t) x w) := by
    change Ω (extendPath u 1) (V v 1) (V w 1) = _
    rw [hfinal,hfinalV,hfinalV]
  exact hone.symm.trans (hend.trans hzero)

theorem timeSteps_preserves_form {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0)
    {h : ℝ} (hh : ‖h‖ * L < 1) (t : ℝ) (N : ℕ) (x v w : E) :
    Ω (t+N*h,timeSteps X hX hXs hh t N x)
      (fderiv ℝ (timeSteps X hX hXs hh t N) x v)
      (fderiv ℝ (timeSteps X hX hXs hh t N) x w) = Ω (t,x) v w := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    let F := timeSteps X hX hXs hh t N
    let G := timeStep X hX h (t+N*h)
    have hF : Differentiable ℝ F := (timeSteps_smooth X hX hXs hh t N).1.differentiable (by simp)
    have hG : Differentiable ℝ G := (timeStep_smooth X hX hXs hh (t+N*h)).differentiable (by simp)
    change Ω (t+(N+1:ℕ)*h,G (F x))
      (fderiv ℝ (G ∘ F) x v) (fderiv ℝ (G ∘ F) x w) = _
    rw [fderiv_comp x (hG (F x)) (hF x)]
    have ht : t + (N+1:ℕ)*h = (t+N*h)+h := by push_cast; ring
    rw [ht]
    exact (timeStep_preserves_form X hX hXs Ω hΩ hPDE hh (t+N*h) (F x)
      (fderiv ℝ F x v) (fderiv ℝ F x w)).trans ih

theorem exists_form_transport {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (hΩ : ContDiff ℝ ∞ Ω)
    (hPDE : ∀ p v w, fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0)
    (K : Set E) (hK : IsCompact K) (hXspt : ∀ s x, x ∉ K → X (s,x) = 0)
    (t T : ℝ) : ∃ Φ : E ≃ₜ E, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ K → Φ x = x) ∧ HasCompactSupport (fun x => Φ x - x) ∧
      (∀ x v w, Ω (t+T,Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = Ω (t,x) v w) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ := timeSteps X hX hXs hh t N
  have hfix (x : E) (hx : x ∉ K) : Φ x = x :=
    timeSteps_of_stationary X hX hXs hh t N (fun s => hXspt s x hx)
  refine ⟨Φ,(timeSteps_smooth X hX hXs hh t N).1,
    (timeSteps_smooth X hX hXs hh t N).2,hfix,?_,?_⟩
  · exact HasCompactSupport.intro hK (fun x hx => sub_eq_zero.mpr (hfix x hx))
  · intro x v w
    simpa only [he] using timeSteps_preserves_form X hX hXs Ω hΩ hPDE hh t N x v w


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def formMoserField (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ × E → E →L[ℝ] ℝ) (p : ℝ × E) : E := -(Ω p).inverse (α p)

theorem formMoserField_smooth {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible) : ContDiff ℝ ∞ (formMoserField Ω α) := by
  have hi : ContDiff ℝ ∞ (fun p => (Ω p).inverse) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hΩinv p).contDiffAt_map_inverse.comp p hΩ.contDiffAt
  exact (hi.clm_apply hα).neg

omit [CompleteSpace E] in
theorem formMoserField_solve {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩinv : ∀ p, (Ω p).IsInvertible) (p : ℝ × E) :
    Ω p (formMoserField Ω α p) = -α p := by
  simp only [formMoserField,map_neg,(hΩinv p).self_apply_inverse]

omit [CompleteSpace E] in
theorem formMoserField_support (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ × E → E →L[ℝ] ℝ) : tsupport (formMoserField Ω α) ⊆ tsupport α := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  apply hp
  simp [formMoserField,image_eq_zero_of_notMem_tsupport (f := α) hn]

theorem formMoserField_contraction_derivative {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible) (p q : ℝ × E) (w : E) :
    fderiv ℝ Ω p q (formMoserField Ω α p) w +
      Ω p (fderiv ℝ (formMoserField Ω α) p q) w = -(fderiv ℝ α p q w) := by
  have hX := formMoserField_smooth hΩ hα hΩinv
  have hleft := ((hΩ.differentiable (by simp) p).hasFDerivAt).clm_apply
    ((hX.differentiable (by simp) p).hasFDerivAt)
  have hright := ((hα.differentiable (by simp) p).hasFDerivAt).neg
  have heq : (fun p => Ω p (formMoserField Ω α p)) = fun p => -α p :=
    funext (formMoserField_solve hΩinv)
  change HasFDerivAt (fun p => -α p) (-fderiv ℝ α p) p at hright
  rw [← heq] at hright
  have hh := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) (hleft.unique hright)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    neg_apply,add_comm] using hh

theorem formMoserField_transport_equation {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hΩinv : ∀ p, (Ω p).IsInvertible)
    (hskew : ∀ p u v, Ω p u v = -Ω p v u)
    (hclosed : ∀ p u v w, fderiv ℝ Ω p (0,u) v w - fderiv ℝ Ω p (0,v) u w +
      fderiv ℝ Ω p (0,w) u v = 0)
    (htime : ∀ p v w, fderiv ℝ Ω p (1,0) v w =
      fderiv ℝ α p (0,v) w - fderiv ℝ α p (0,w) v) (p : ℝ × E) (v w : E) :
    fderiv ℝ Ω p (1,formMoserField Ω α p) v w +
      Ω p (fderiv ℝ (formMoserField Ω α) p (0,v)) w +
      Ω p v (fderiv ℝ (formMoserField Ω α) p (0,w)) = 0 := by
  have h1 := formMoserField_contraction_derivative hΩ hα hΩinv p (0,v) w
  have h2 := formMoserField_contraction_derivative hΩ hα hΩinv p (0,w) v
  have hc := hclosed p (formMoserField Ω α p) v w
  have ht := htime p v w
  rw [show (1,formMoserField Ω α p) = ((1,0) : ℝ × E)+(0,formMoserField Ω α p) by ext <;> simp,
    map_add,add_apply,add_apply,hskew p v]
  linarith

omit [CompleteSpace E] in

theorem formMoserField_tangent {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩinv : ∀ p, (Ω p).IsInvertible)
    (hskew : ∀ p u v, Ω p u v = -Ω p v u) (p : ℝ × E)
    (μ : E → ℝ) (Z : E) (hface : Ω p Z = -(fderiv ℝ μ p.2))
    (hhor : α p Z = 0) : fderiv ℝ μ p.2 (formMoserField Ω α p) = 0 := by
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A Z) (formMoserField_solve (α := α) hΩinv p)
  have hh' := congrArg (fun A : E →L[ℝ] ℝ => A (formMoserField Ω α p)) hface
  simp only [neg_apply,hhor,neg_zero] at hh
  simp only [neg_apply] at hh'
  rw [hskew] at hh
  linarith

variable [FiniteDimensional ℝ E]

theorem exists_compact_form_moser {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} (hΩ : ContDiff ℝ ∞ Ω) (hα : ContDiff ℝ ∞ α)
    (hαc : HasCompactSupport α) (hΩinv : ∀ p, (Ω p).IsInvertible)
    (hskew : ∀ p u v, Ω p u v = -Ω p v u)
    (hclosed : ∀ p u v w, fderiv ℝ Ω p (0,u) v w - fderiv ℝ Ω p (0,v) u w +
      fderiv ℝ Ω p (0,w) u v = 0)
    (htime : ∀ p v w, fderiv ℝ Ω p (1,0) v w =
      fderiv ℝ α p (0,v) w - fderiv ℝ α p (0,w) v) (t T : ℝ) :
    ∃ Φ : E ≃ₜ E, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ Prod.snd '' tsupport α → Φ x = x) ∧
      HasCompactSupport (fun x => Φ x-x) ∧
      ∀ x v w, Ω (t+T,Φ x) (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = Ω (t,x) v w := by
  have hXs := formMoserField_smooth hΩ hα hΩinv
  let X : C(ℝ × E,E) := ⟨formMoserField Ω α,hXs.continuous⟩
  have hXc : HasCompactSupport X := hαc.of_isClosed_subset (isClosed_tsupport _)
    (formMoserField_support Ω α)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  apply exists_form_transport X hL hXs Ω hΩ
    (formMoserField_transport_equation hΩ hα hΩinv hskew hclosed htime)
    (Prod.snd '' tsupport α) (hαc.image continuous_snd) _ t T
  intro s x hx
  have hn : (s,x) ∉ tsupport α := fun hp => hx ⟨(s,x),hp,rfl⟩
  change formMoserField Ω α (s,x) = 0
  simp [formMoserField,image_eq_zero_of_notMem_tsupport (f := α) hn]


end

section
open scoped ContDiff Topology NNReal
open Set Function

variable {E Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem timeStep_comp_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} {x : Q → E} (hhs : ContDiff ℝ ∞ h)
    (hts : ContDiff ℝ ∞ t) (hxs : ContDiff ℝ ∞ x)
    (hh : ∀ q, ‖h q‖ * L < 1) :
    ContDiff ℝ ∞ (fun q => timeStep X hX (h q) (t q) (x q)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hloc := (localPath_smooth (clockField X) (clockField_lipschitz X hX)
    (clockField_smooth X hXs)).contDiffAt ((picardDomain_open L).mem_nhds
      (show ((t q,x q),h q) ∈ picardDomain L from hh q))
  have hc := hloc.comp q ((hts.prodMk hxs).prodMk hhs).contDiffAt
  exact ((ContinuousMap.evalCLM (M := ℝ × E) ℝ (⟨1,by simp⟩ : Time)).contDiff.contDiffAt.comp q hc).snd

theorem timeSteps_variable_smooth {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h t : Q → ℝ} (hhs : ContDiff ℝ ∞ h) (hts : ContDiff ℝ ∞ t)
    (hh : ∀ q, ‖h q‖ * L < 1) (N : ℕ) :
    ContDiff ℝ ∞ (fun p : Q × E => timeSteps X hX hXs (hh p.1) (t p.1) N p.2) ∧
    ContDiff ℝ ∞ (fun p : Q × E => (timeSteps X hX hXs (hh p.1) (t p.1) N).symm p.2) := by
  induction N with
  | zero => exact ⟨contDiff_snd,contDiff_snd⟩
  | succ N ih =>
    constructor
    · exact timeStep_comp_smooth X hX hXs (hhs.comp contDiff_fst)
        ((hts.add (contDiff_const.mul hhs)).comp contDiff_fst) ih.1 (fun p => hh p.1)
    · have hg : ContDiff ℝ ∞ (fun p : Q × E =>
          timeStep X hX (-h p.1) ((t p.1+N*h p.1)+h p.1) p.2) :=
        timeStep_comp_smooth X hX hXs (hhs.neg.comp contDiff_fst)
          (((hts.add (contDiff_const.mul hhs)).add hhs).comp contDiff_fst)
          contDiff_snd (fun p => by simpa only [norm_neg] using hh p.1)
      exact ih.2.comp (contDiff_fst.prodMk hg)

omit [FiniteDimensional ℝ E] in
@[simp] theorem timeStep_zero {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (t : ℝ) (x : E) : timeStep X hX 0 t x = x := by
  have he := fixedStep_equation (clockField X) (clockField_lipschitz X hX)
    (h := 0) (by simp) (t,x)
  simp only [zero_smul,add_zero] at he
  change (fixedStep (clockField X) (clockField_lipschitz X hX) 0 (t,x) ⟨1,by simp⟩).2 = x
  rw [he]
  rfl

@[simp] theorem timeSteps_zero {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    (t : ℝ) (N : ℕ) (x : E) :
    timeSteps X hX hXs (h := 0) (by simp) t N x = x := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change timeStep X hX 0 (t+N*0) (timeSteps X hX hXs (h := 0) (by simp) t N x) = x
    rw [timeStep_zero,ih]

omit [FiniteDimensional ℝ E] in

theorem fixedStep_eq_solution {L : ℝ≥0} (X : C(E,E))
    (hX : LipschitzWith L X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (u : C(Time,E)) (x : E) (hu0 : u ⟨0,by simp⟩ = x)
    (hud : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (extendPath u) (h • X (extendPath u s)) s) :
    fixedStep X hX h x = u := by
  apply (picard_contracts X hX (p := (x,h)) hh).fixedPoint_unique'
    (localPath_fixed X hX (p := (x,h)) hh)
  ext s
  change x + h • (∫ t in 0..(s : ℝ), extendPath (X.comp u) t) = u s
  have hd (t : ℝ) (ht : t ∈ Ioo 0 (s : ℝ)) :
      HasDerivAt (extendPath u) (h • extendPath (X.comp u) t) t := by
    exact hud t ⟨ht.1,ht.2.trans_le s.property.2⟩
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le s.property.1
    (extendPath u).continuous.continuousOn hd
    ((continuous_const.smul (extendPath (X.comp u)).continuous).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_smul,extendPath_coe u s,
    extendPath_coe u ⟨0,by simp⟩,hu0] at hi
  rw [hi]
  abel

omit [FiniteDimensional ℝ E] in

theorem timeStep_eq_solution {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) {h : ℝ} (hh : ‖h‖ * L < 1)
    (u : ℝ → E) (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (X (s,u s)) s) (t : ℝ) :
    timeStep X hX h t (u t) = u (t+h) := by
  let v : C(Time,ℝ × E) := ⟨fun s => (t+h*(s:ℝ),u (t+h*(s:ℝ))),
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).prodMk
      (hu.comp (continuous_const.add (continuous_const.mul continuous_subtype_val)))⟩
  have hv0 : v ⟨0,by simp⟩ = (t,u t) := by simp [v]
  have hvd (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (extendPath v)
        (h • clockField X (extendPath v s)) s := by
    have he : extendPath v =ᶠ[𝓝 s] (fun r => (t+h*r,u (t+h*r))) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
      exact extendPath_coe v ⟨r,hr⟩
    have ha : HasDerivAt (fun r : ℝ => t+h*r) h s := by
      exact (hasDerivAt_const_mul h).const_add t
    have huc := (hud (t+h*s)).scomp s ha
    have hv := ha.prodMk huc
    have hp : extendPath v s = (t+h*s,u (t+h*s)) := he.eq_of_nhds
    rw [hp,clockField_apply]
    simpa only [Prod.smul_mk,smul_eq_mul,mul_one] using hv.congr_of_eventuallyEq he
  have he := fixedStep_eq_solution (clockField X) (clockField_lipschitz X hX)
    hh v (t,u t) hv0 hvd
  change (fixedStep (clockField X) (clockField_lipschitz X hX) h (t,u t) ⟨1,by simp⟩).2 = _
  rw [he]
  simp [v]

theorem timeSteps_eq_solution {L : ℝ≥0} (X : C(ℝ × E,E))
    (hX : LipschitzWith L X) (hXs : ContDiff ℝ ∞ X)
    {h : ℝ} (hh : ‖h‖ * L < 1) (u : ℝ → E) (hu : Continuous u)
    (hud : ∀ s, HasDerivAt u (X (s,u s)) s) (t : ℝ) (N : ℕ) :
    timeSteps X hX hXs hh t N (u t) = u (t+N*h) := by
  induction N with
  | zero => simp [timeSteps]
  | succ N ih =>
    change timeStep X hX h (t+N*h) (timeSteps X hX hXs hh t N (u t)) = _
    rw [ih,timeStep_eq_solution X hX hh u hu hud]
    congr 1
    push_cast
    ring


end

open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def spatialDifferential (H : ℝ × E → ℝ) (p : ℝ × E) : E →L[ℝ] ℝ :=
  (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ E)

@[simp] theorem spatialDifferential_apply (H : ℝ × E → ℝ) (p : ℝ × E) (v : E) :
    spatialDifferential H p v = fderiv ℝ H p (0,v) := rfl

theorem spatialDifferential_smooth {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (spatialDifferential H) :=
  (hH.fderiv_right (by simp)).clm_comp contDiff_const

theorem spatialDifferential_support (H : ℝ × E → ℝ) :
    tsupport (spatialDifferential H) ⊆ tsupport H := by
  apply (tsupport_comp_subset (f := fderiv ℝ H)
    (g := fun A : (ℝ × E) →L[ℝ] ℝ => A.comp (ContinuousLinearMap.inr ℝ ℝ E))
    (by ext; rfl)).trans (tsupport_fderiv_subset ℝ)

theorem spatialDifferential_fderiv {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    (p q : ℝ × E) (w : E) :
    fderiv ℝ (spatialDifferential H) p q w = fderiv ℝ (fderiv ℝ H) p q (0,w) := by
  have hHd : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hd := ((hHd.differentiable (by simp) p).hasFDerivAt).clm_comp
    (hasFDerivAt_const (c := ContinuousLinearMap.inr ℝ ℝ E) p)
  have he := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) hd.fderiv
  change fderiv ℝ (fun p => (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ E)) p q w = _
  simpa only [add_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,
    map_zero,zero_apply,zero_add] using he

theorem spatialDifferential_closed {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H)
    (p : ℝ × E) (v w : E) :
    fderiv ℝ (spatialDifferential H) p (0,v) w =
      fderiv ℝ (spatialDifferential H) p (0,w) v := by
  rw [spatialDifferential_fderiv hH,spatialDifferential_fderiv hH]
  have hs := (hH.contDiffAt (x := p)).isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact hs.eq (0,v) (0,w)

def hamiltonianField (A : E →L[ℝ] E →L[ℝ] ℝ) (H : ℝ × E → ℝ) : ℝ × E → E :=
  formMoserField (fun _ => A) (spatialDifferential H)

variable [CompleteSpace E]

theorem hamiltonianField_smooth {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamiltonianField A H) :=
  formMoserField_smooth contDiff_const (spatialDifferential_smooth hH) (fun _ => hA)

omit [CompleteSpace E] in
theorem hamiltonianField_contraction {A : E →L[ℝ] E →L[ℝ] ℝ} (hA : A.IsInvertible)
    (H : ℝ × E → ℝ) (p : ℝ × E) (w : E) :
    A (hamiltonianField A H p) w = -fderiv ℝ H p (0,w) := by
  exact congrArg (fun α : E →L[ℝ] ℝ => α w) (formMoserField_solve (fun _ => hA) p)

omit [CompleteSpace E] in
theorem hamiltonianField_support (A : E →L[ℝ] E →L[ℝ] ℝ) (H : ℝ × E → ℝ) :
    tsupport (hamiltonianField A H) ⊆ tsupport H :=
  (formMoserField_support _ _).trans (spatialDifferential_support H)

theorem hamiltonianField_transport_equation {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (p : ℝ × E) (v w : E) :
    A (fderiv ℝ (hamiltonianField A H) p (0,v)) w +
      A v (fderiv ℝ (hamiltonianField A H) p (0,w)) = 0 := by
  have he := formMoserField_transport_equation (Ω := fun _ => A)
    contDiff_const (spatialDifferential_smooth hH) (fun _ => hA) (fun _ => hskew)
    (by intro p u v w; simp) (by
      intro p v w
      simp only [fderiv_const_apply,zero_apply]
      exact (sub_eq_zero.mpr (spatialDifferential_closed hH p v w)).symm) p v w
  simpa only [hamiltonianField,fderiv_const_apply,zero_apply,zero_add] using he

variable [FiniteDimensional ℝ E]

theorem exists_hamiltonian_endpoint {A : E →L[ℝ] E →L[ℝ] ℝ}
    (hA : A.IsInvertible) (hskew : ∀ v w, A v w = -A w v)
    {H : ℝ × E → ℝ} (hH : ContDiff ℝ ∞ H) (hHc : HasCompactSupport H)
    (t T : ℝ) : ∃ Φ : E ≃ₜ E, ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      (∀ x, x ∉ Prod.snd '' tsupport H → Φ x = x) ∧
      HasCompactSupport (fun x => Φ x-x) ∧
      (∀ x v w, A (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = A v w) ∧
      (∀ (u : ℝ → E), Continuous u →
        (∀ s, HasDerivAt u (hamiltonianField A H (s,u s)) s) → Φ (u t) = u (t+T)) := by
  have hXs := hamiltonianField_smooth hA hH
  let X : C(ℝ × E,E) := ⟨hamiltonianField A H,hXs.continuous⟩
  have hXc : HasCompactSupport X := hHc.of_isClosed_subset (isClosed_tsupport _)
    (hamiltonianField_support A H)
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T / (N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le, div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ := timeSteps X hL hXs hh t N
  have hfix (x : E) (hx : x ∉ Prod.snd '' tsupport H) : Φ x = x := by
    apply timeSteps_of_stationary X hL hXs hh t N
    intro s
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact hx ⟨(s,x),hamiltonianField_support A H hp,rfl⟩
  refine ⟨Φ,(timeSteps_smooth X hL hXs hh t N).1,
    (timeSteps_smooth X hL hXs hh t N).2,hfix,?_,?_,?_⟩
  · exact HasCompactSupport.intro (hHc.image continuous_snd)
      (fun x hx => sub_eq_zero.mpr (hfix x hx))
  · intro x v w
    apply timeSteps_preserves_form X hL hXs (fun _ => A) contDiff_const _ hh t N x v w
    intro p v w
    simpa only [X,ContinuousMap.coe_mk,fderiv_const_apply,zero_apply,zero_add] using
      hamiltonianField_transport_equation hA hskew hH p v w
  · intro u hu hud
    simpa only [he] using timeSteps_eq_solution X hL hXs hh u hu hud t N



end PackingSufficiencySupport.Hamiltonian
end

end OAI
