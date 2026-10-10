import Mathlib
import OAI.Geometry.BallPacking.Moser.ParametricMoser

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

section
variable [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in

theorem radialDisk_pullback_compact {R : ℝ} (hR : 0 < R) {f : P × Plane → ℝ}
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ univ ×ˢ roundDisk R) :
    HasCompactSupport (fun p : P × Plane =>
      radialDiskDensity R p.2 * f (p.1,radialDiskChart R p.2)) := by
  let c := radialDiskChart R
  have ht : tsupport f ⊆ univ ×ˢ c.target := by simpa only [c, radialDiskChart_target hR] using hfs
  have hc : ContinuousOn (fun p : P × Plane => (p.1,c.symm p.2)) (tsupport f) :=
    continuousOn_fst.prodMk (c.continuousOn_symm.comp continuousOn_snd (fun p hp => (ht hp).2))
  apply HasCompactSupport.intro (hfc.image_of_continuousOn hc)
  intro p hp
  have hz : f (p.1,c p.2) = 0 := by
    by_contra hn
    apply hp
    refine ⟨(p.1,c p.2),subset_closure hn,?_⟩
    have hs : p.2 ∈ c.source := by rw [radialDiskChart_source]; trivial
    simp only [c.left_inv hs]
  exact mul_eq_zero_of_right _ hz

theorem exists_parametric_disk_moser {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 < R) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ univ ×ˢ roundDisk R)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0) (hpos : ∀ p, 0 < 1+f p)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, (∫ p in roundDisk (r i), f (y,p)) = 0) :
    ∃ Ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, (1+f (y,Ψ y x)) *
        planarArea (fderiv ℝ (Ψ y) x v) (fderiv ℝ (Ψ y) x w) = planarArea v w) ∧
      (∀ i y, Ψ y '' closedRoundDisk (r i) = closedRoundDisk (r i)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, Ψ y x = x := by
  let c := radialDiskChart R
  have hcs : c.source = univ := radialDiskChart_source R
  have hct : c.target = roundDisk R := radialDiskChart_target hR
  have hc : ContDiff ℝ ∞ c := radialDiskChart_smooth R
  have hci : ContDiffOn ℝ ∞ c.symm c.target := by
    rw [hct]
    exact radialDiskChart_symm_smooth hR
  let g : P × Plane → ℝ := fun p => radialDiskDensity R p.2
  let F : P × Plane → ℝ := fun p => g p*f (p.1,c p.2)
  have hg : ContDiff ℝ ∞ g := (radialDiskDensity_smooth R).comp contDiff_snd
  have hF : ContDiff ℝ ∞ F := hg.mul (hf.comp (contDiff_fst.prodMk (hc.comp contDiff_snd)))
  have hFc : HasCompactSupport F := radialDisk_pullback_compact hR hfc hfs
  have hF0 (y : P) : (∫ p, F (y,p)) = 0 := by
    change (∫ p, radialDiskDensity R p * (fun x => f (y,x)) (radialDiskChart R p)) = 0
    rw [← radialDiskChart_integral hR (fun x => f (y,x))]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, hf0 y]
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (f := f) (fun h => hx (hfs h).2)
  have hgpos (p : P × Plane) : 0 < g p := radialDiskDensity_pos hR p.2
  have hGFpos (p : P × Plane) : 0 < g p+F p := by
    change 0 < g p+g p*f (p.1,c p.2)
    nlinarith only [mul_pos (hgpos p) (hpos (p.1,c p.2))]
  let r' := fun i => diskChartRadius R (r i)
  have hr' (i : ι) : 0 < r' i := diskChartRadius_pos (hr i) (hrR i)
  have hri' : Injective r' := by
    intro i j hij
    apply hri
    exact (diskChartRadius_strictMonoOn hR).injOn ⟨(hr i).le,hrR i⟩ ⟨(hr j).le,hrR j⟩ hij
  have hz' (i : ι) (y : P) : (∫ p in roundDisk (r' i), F (y,p)) = 0 := by
    change (∫ p in roundDisk (diskChartRadius R (r i)),
      radialDiskDensity R p * (fun x => f (y,x)) (radialDiskChart R p)) = 0
    rw [← radialDiskChart_integral_inner hR (hr i).le (hrR i) (fun x => f (y,x))]
    exact hz i y
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦzero⟩ :=
    exists_parametric_relative_background_moser hg hF hFc hF0 hgpos hGFpos r' hr' hri' hz'
  obtain ⟨Ψ,hΨeq,hΨ,hΨi,hΨc,hΨsupp⟩ :=
    Chart.exists_conjugate_family c hcs hc hci Φ hΦ hΦi hΦc
  have hΨfun (y : P) : (Ψ y : Plane → Plane) = Chart.conjugate c (Φ y) := funext (hΨeq y)
  have hΦy (y : P) : ContDiff ℝ ∞ (Φ y) := hΦ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨Ψ,hΨ,hΨi,hΨc,by simpa only [hct] using hΨsupp,?_,?_,?_⟩
  · intro y x v w
    by_cases hx : x ∈ c.target
    · let q := c.symm x
      let v' := fderiv ℝ c.symm x v
      let w' := fderiv ℝ c.symm x w
      have hcq : c q = x := c.right_inv hx
      have hv : fderiv ℝ c q v' = v := Chart.chart_fderiv_right_inverse c hc hci hx v
      have hw : fderiv ℝ c q w' = w := Chart.chart_fderiv_right_inverse c hc hci hx w
      have hΨx : Ψ y x = c (Φ y q) := by
        rw [hΨeq y x,Chart.conjugate_of_mem c _ hx]
      have hdv : fderiv ℝ (Ψ y) x v = fderiv ℝ c (Φ y q) (fderiv ℝ (Φ y) q v') := by
        calc
          _ = fderiv ℝ (Ψ y) (c q) (fderiv ℝ c q v') := by rw [hcq,hv]
          _ = _ := by rw [hΨfun]; exact Chart.conjugate_fderiv_chart c hcs hc hci (Φ y) (hΦy y) q v'
      have hdw : fderiv ℝ (Ψ y) x w = fderiv ℝ c (Φ y q) (fderiv ℝ (Φ y) q w') := by
        calc
          _ = fderiv ℝ (Ψ y) (c q) (fderiv ℝ c q w') := by rw [hcq,hw]
          _ = _ := by rw [hΨfun]; exact Chart.conjugate_fderiv_chart c hcs hc hci (Φ y) (hΦy y) q w'
      rw [hΨx,hdv,hdw,radialDiskChart_area hR]
      have hA := hΦarea y q v' w'
      have hB := radialDiskChart_area hR q v' w'
      change planarArea (fderiv ℝ c q v') (fderiv ℝ c q w') = g (y,q)*planarArea v' w' at hB
      rw [hv,hw] at hB
      rw [hB]
      convert hA using 1
      dsimp [F,g]
      ring
    · have hn : (y,x) ∉ tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2) :=
        fun h => hx (hΨsupp h).2
      have he : Ψ y =ᶠ[𝓝 x] id := by
        have hnhood := (isClosed_tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2)).isOpen_compl.mem_nhds hn
        have hh := (continuous_const.prodMk continuous_id).tendsto x hnhood
        filter_upwards [hh] with z hz
        exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
          (f := fun p : P × Plane => Ψ p.1 p.2-p.2) hz)
      have hfx : f (y,x) = 0 := image_eq_zero_of_notMem_tsupport
        (f := f) (fun h => hx (by rw [hct]; exact (hfs h).2))
      rw [he.eq_of_nhds,he.fderiv_eq,fderiv_id,ContinuousLinearMap.id_apply,
        ContinuousLinearMap.id_apply, id_eq,hfx,add_zero,one_mul]
  · intro i y
    rw [hΨfun,← radialDiskChart_image_closed hR (hr i).le (hrR i),
      Chart.conjugate_image c hcs,hΦdisk]
  · intro y hy x
    have hFzero (p : Plane) : F (y,p) = 0 := by simp only [F,hy,mul_zero]
    have hid : (Φ y : Plane → Plane) = id := funext (hΦzero y hFzero)
    rw [hΨeq,hid,Chart.conjugate_id]

end

 theorem planarArea_map (A : Plane →L[ℝ] Plane) (v w : Plane) :
    planarArea (A v) (A w) = A.det * planarArea v w := by
  have hd (u : Plane) : A u = u.1 • A (1,0) + u.2 • A (0,1) := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp
  rw [planar_det,hd v,hd w]
  simp only [planarArea_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

 theorem family_spatial_fderiv {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F)
    (y : P) (x : Plane) :
    fderiv ℝ (fun x => F (y,x)) x =
      (fderiv ℝ F (y,x)).comp (ContinuousLinearMap.inr ℝ P Plane) := by
  have hi : HasFDerivAt (fun x : Plane => (y,x)) (ContinuousLinearMap.inr ℝ P Plane) x :=
    (hasFDerivAt_const y x).prodMk (hasFDerivAt_id x)
  exact (((hF.differentiable (by simp)) (y,x)).hasFDerivAt.comp x hi).fderiv

 theorem family_spatial_fderiv_smooth {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he : (fun p : P × Plane => fderiv ℝ (fun x => F (p.1,x)) p.2) =
      fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ P Plane) :=
    funext (fun p => family_spatial_fderiv hF p.1 p.2)
  rw [he]
  exact (hF.fderiv_right (by simp)).clm_comp contDiff_const

def spatialJacobian (F : P × Plane → Plane) (p : P × Plane) : ℝ :=
  (fderiv ℝ (fun x => F (p.1,x)) p.2).det

 theorem spatialJacobian_smooth {F : P × Plane → Plane} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialJacobian F) := by
  have hd := family_spatial_fderiv_smooth hF
  have ha := hd.clm_apply (contDiff_const (c := ((1,0) : Plane)))
  have hb := hd.clm_apply (contDiff_const (c := ((0,1) : Plane)))
  have he : spatialJacobian F = fun p => planarArea
      (fderiv ℝ (fun x => F (p.1,x)) p.2 (1,0))
      (fderiv ℝ (fun x => F (p.1,x)) p.2 (0,1)) :=
    funext (fun p => planar_det _)
  rw [he]
  exact (planarArea.contDiff.comp ha).clm_apply hb

omit [NormedSpace ℝ P] in
 theorem spatialJacobian_support (F : P × Plane → Plane) :
    tsupport (fun p => spatialJacobian F p-1) ⊆ tsupport (fun p => F p-p.2) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  have he : (fun x => F (p.1,x)) =ᶠ[𝓝 p.2] id := by
    have hh := (continuous_const.prodMk continuous_id).tendsto p.2
      ((isClosed_tsupport (fun p : P × Plane => F p-p.2)).isOpen_compl.mem_nhds hn)
    filter_upwards [hh] with x hx
    exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => F p-p.2) hx)
  apply hp
  simp [spatialJacobian,he.fderiv_eq,fderiv_id,planar_det,planarArea_apply]

omit [NormedSpace ℝ P] in
 theorem homeomorph_image_of_fixed_compl (φ : Plane ≃ₜ Plane) (S : Set Plane)
    (h : ∀ x ∉ S, φ x = x) : φ '' S = S := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    by_contra hn
    have hh : φ (φ y) = φ y := h (φ y) hn
    apply hn
    rw [φ.injective hh]
    exact hy
  · intro x hx
    refine ⟨φ.symm x,?_,φ.apply_symm_apply x⟩
    by_contra hn
    have hh := h (φ.symm x) hn
    rw [φ.apply_symm_apply] at hh
    exact hn (hh ▸ hx)

theorem spatialJacobian_integral {R : ℝ} (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hfs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hpos : ∀ p : P × Plane, 0 < spatialJacobian (fun p => φ p.1 p.2) p) (y : P) :
    (∫ x, spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x)-1) = 0 := by
  let J := spatialJacobian (fun p : P × Plane => φ p.1 p.2)
  have hJ : ContDiff ℝ ∞ J := spatialJacobian_smooth hφ
  have hd : ContDiff ℝ ∞ (φ y) := hφ.comp (contDiff_const.prodMk contDiff_id)
  have hfix (x : Plane) (hx : x ∉ closedRoundDisk R) : φ y x = x := by
    apply sub_eq_zero.mp
    apply image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => φ p.1 p.2-p.2) (x := (y,x))
    intro hh
    apply hx
    change radiusSq x ≤ R^2
    exact le_of_lt (hfs hh).2
  have himg := homeomorph_image_of_fixed_compl (φ y) (closedRoundDisk R) hfix
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (closedRoundDisk_isCompact R).measurableSet
    (f' := fderiv ℝ (φ y))
    (fun x _ => ((hd.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    (φ y).injective.injOn (fun _ : Plane => (1 : ℝ))
  have hJpos (x : Plane) : 0 < (fderiv ℝ (φ y) x).det := hpos (y,x)
  simp only [himg,smul_eq_mul,mul_one,abs_of_pos (hJpos _)] at hi
  have he : (∫ x in closedRoundDisk R, J (y,x)-1) = 0 := by
    rw [integral_sub]
    · exact sub_eq_zero.mpr hi.symm
    · exact ContinuousOn.integrableOn_compact (closedRoundDisk_isCompact R)
        (hJ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
    · exact integrableOn_const (closedRoundDisk_isCompact R).measure_lt_top.ne
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at he
  · exact he
  · intro x hx
    apply image_eq_zero_of_notMem_tsupport (f := fun p : P × Plane => J p-1) (x := (y,x))
    intro hh
    have hs := hfs (spatialJacobian_support (fun p : P × Plane => φ p.1 p.2) hh)
    exact hx (show radiusSq x ≤ R^2 from le_of_lt hs.2)

theorem exists_corrected_disk_diffeomorphisms [FiniteDimensional ℝ P]
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hφc : HasCompactSupport (fun p : P × Plane => φ p.1 p.2-p.2))
    (hφs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hpos : ∀ p : P × Plane, 0 < spatialJacobian (fun p => φ p.1 p.2) p)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, (∫ x in roundDisk (r i),
      spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x)-1) = 0) :
    ∃ ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, planarArea (fderiv ℝ (ψ y) x v) (fderiv ℝ (ψ y) x w) = planarArea v w) ∧
      (∀ i y, ψ y '' closedRoundDisk (r i) = φ y '' closedRoundDisk (r i)) ∧
      ∀ y, (∀ x, spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x) = 1) →
        ∀ x, ψ y x = φ y x := by
  let f : P × Plane → ℝ := fun p => spatialJacobian (fun p : P × Plane => φ p.1 p.2) p-1
  have hf : ContDiff ℝ ∞ f := (spatialJacobian_smooth hφ).sub contDiff_const
  have hfc : HasCompactSupport f :=
    hφc.of_isClosed_subset (isClosed_tsupport f) (spatialJacobian_support _)
  have hfs : tsupport f ⊆ univ ×ˢ roundDisk R := (spatialJacobian_support _).trans hφs
  have hf0 (y : P) : (∫ x, f (y,x)) = 0 := spatialJacobian_integral φ hφ hφs hpos y
  have hfpos (p : P × Plane) : 0 < 1+f p := by dsimp [f]; linarith [hpos p]
  obtain ⟨χ,hχ,hχi,hχc,hχs,hχarea,hχdisk,hχzero⟩ :=
    exists_parametric_disk_moser hR hf hfc hfs hf0 hfpos r hr hrR hri hz
  let ψ : P → Plane ≃ₜ Plane := fun y => (χ y).trans (φ y)
  have hψ : ContDiff ℝ ∞ (fun p : P × Plane => ψ p.1 p.2) :=
    hφ.comp (contDiff_fst.prodMk hχ)
  have hψi : ContDiff ℝ ∞ (fun p : P × Plane => (ψ p.1).symm p.2) :=
    hχi.comp (contDiff_fst.prodMk hφi)
  have hs : tsupport (fun p : P × Plane => ψ p.1 p.2-p.2) ⊆
      tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ∪
      tsupport (fun p : P × Plane => χ p.1 p.2-p.2) := by
    apply closure_minimal _ ((isClosed_tsupport _).union (isClosed_tsupport _))
    intro p hp
    by_contra hn
    have ha := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => φ p.1 p.2-p.2) (fun h => hn (Or.inl h)))
    have hb := sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
      (f := fun p : P × Plane => χ p.1 p.2-p.2) (fun h => hn (Or.inr h)))
    apply hp
    change φ p.1 (χ p.1 p.2)-p.2 = 0
    rw [hb,ha,sub_self]
  refine ⟨ψ,hψ,hψi,(hφc.union hχc).of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans (union_subset hφs hχs),?_,?_,?_⟩
  · intro y x v w
    have hdφ : Differentiable ℝ (φ y) := (hφ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
    have hdχ : Differentiable ℝ (χ y) := (hχ.comp ((contDiff_const (c := y)).prodMk contDiff_id)).differentiable (by simp)
    have he : fderiv ℝ (ψ y) x = (fderiv ℝ (φ y) (χ y x)).comp (fderiv ℝ (χ y) x) :=
      fderiv_comp x (hdφ (χ y x)) (hdχ x)
    rw [he,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,planarArea_map]
    have hh := hχarea y x v w
    have hnum : 1+f (y,χ y x) = (fderiv ℝ (φ y) (χ y x)).det := by
      dsimp only [f,spatialJacobian]
      ring
    rw [hnum] at hh
    exact hh
  · intro i y
    change (φ y ∘ χ y) '' closedRoundDisk (r i) = _
    rw [image_comp,hχdisk]
  · intro y hy x
    have hh := hχzero y (fun x => sub_eq_zero.mpr (hy x)) x
    change φ y (χ y x) = φ y x
    rw [hh]

variable [FiniteDimensional ℝ P]

def rectangularPotential (B : ℝ) (α : P × Plane → Plane →L[ℝ] ℝ) (p : P × Plane) : ℝ :=
  (∫ t in B..p.2.1, α (p.1,(t,B)) (1,0)) +
    ∫ t in B..p.2.2, α (p.1,(p.2.1,t)) (0,1)

 theorem rectangularPotential_smooth {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (B : ℝ) : ContDiff ℝ ∞ (rectangularPotential B α) := by
  have h1 : ContDiff ℝ ∞ (fun p : P × ℝ => α (p.1,(p.2,B)) (1,0)) :=
    (hα.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).clm_apply contDiff_const
  have h2 : ContDiff ℝ ∞ (fun p : (P × ℝ) × ℝ => α (p.1.1,(p.1.2,p.2)) (0,1)) :=
    (hα.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))).clm_apply contDiff_const
  exact ((contDiff_parameter_segment_integral h1 B).comp
    (contDiff_fst.prodMk contDiff_snd.fst)).add
    ((contDiff_parameter_segment_integral h2 B).comp
      ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd))

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
 theorem rectangularPotential_eq_of_hasFDerivAt {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : Continuous α) (B : ℝ) (y : P) {H : Plane → ℝ}
    (hH : ∀ x, HasFDerivAt H (α (y,x)) x) (x : Plane) :
    rectangularPotential B α (y,x) = H x-H (B,B) := by
  have h1 (t : ℝ) : HasDerivAt (fun t => H (t,B)) (α (y,(t,B)) (1,0)) t :=
    (hH (t,B)).comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t B))
  have h2 (t : ℝ) : HasDerivAt (fun t => H (x.1,t)) (α (y,(x.1,t)) (0,1)) t :=
    (hH (x.1,t)).comp_hasDerivAt t ((hasDerivAt_const t x.1).prodMk (hasDerivAt_id t))
  have hi1 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h1 t)
    (((hα.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))).clm_apply
      continuous_const).intervalIntegrable B x.1)
  have hi2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h2 t)
    (((hα.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).clm_apply
      continuous_const).intervalIntegrable B x.2)
  change (∫ t in B..x.1, α (y,(t,B)) (1,0)) +
    (∫ t in B..x.2, α (y,(x.1,t)) (0,1)) = _
  rw [hi1,hi2]
  simp only [Prod.eta]
  ring

omit [FiniteDimensional ℝ P] in
 theorem rectangularPotential_hasFDerivAt {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α)
    (hc : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) (B : ℝ) (y : P) (x : Plane) :
    HasFDerivAt (fun x => rectangularPotential B α (y,x)) (α (y,x)) x := by
  have hαy : ContDiff ℝ ∞ (fun x => α (y,x)) := hα.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨H,hH⟩ := (convex_univ : Convex ℝ (univ : Set Plane)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hαy.differentiable (by simp)).differentiableOn (fun x _ v w => hc y x v w)
  have he : (fun x => rectangularPotential B α (y,x)) = fun x => H x-H (B,B) :=
    funext (rectangularPotential_eq_of_hasFDerivAt hα.continuous B y (fun x => hH x trivial))
  rw [he]
  exact (hH x trivial).sub_const _

theorem exists_parametric_closed_primitive {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    (hclosed : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (α (y,x)) x) ∧
      ∀ y, (∀ x, α (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  obtain ⟨A,hA,hB⟩ := hαc.isBounded.subset_ball_lt 1 (0 : P × Plane)
  let B := A+1
  let H := rectangularPotential B α
  have hHd (y : P) (x : Plane) : HasFDerivAt (fun x => H (y,x)) (α (y,x)) x :=
    rectangularPotential_hasFDerivAt hα hclosed B y x
  have hzero (y : P) (hy : ∀ x, α (y,x) = 0) (x : Plane) : H (y,x) = 0 := by
    simp [H,rectangularPotential,hy]
  have ha0 (y : P) (x : Plane) (hx : A ≤ |x.1| ∨ A ≤ |x.2|) : α (y,x) = 0 := by
    by_contra hn
    have hb := hB (subset_tsupport α (show (y,x) ∈ support α from hn))
    simp only [Metric.mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] at hb
    rcases hx with hx | hx
    · exact (not_lt_of_ge hx) hb.2.1
    · exact (not_lt_of_ge hx) hb.2.2
  have hvert (y : P) (u : ℝ) (hu : A ≤ |u|) (v w : ℝ) : H (y,(u,v)) = H (y,(u,w)) := by
    have hd (t : ℝ) : HasDerivAt (fun t => H (y,(u,t))) 0 t := by
      have hh := (hHd y (u,t)).comp_hasDerivAt t
        ((hasDerivAt_const t u).prodMk (hasDerivAt_id t))
      exact hh.congr_deriv (by rw [ha0 y (u,t) (Or.inl hu)]; rfl)
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) v w
  have hhor (y : P) (v : ℝ) (hv : A ≤ |v|) (u w : ℝ) : H (y,(u,v)) = H (y,(w,v)) := by
    have hd (t : ℝ) : HasDerivAt (fun t => H (y,(t,v))) 0 t := by
      have hh := (hHd y (t,v)).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t v))
      exact hh.congr_deriv (by rw [ha0 y (t,v) (Or.inr hv)]; rfl)
    exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv) u w
  have hAB : A ≤ |B| := le_trans (by dsimp [B]; linarith) (le_abs_self B)
  have hout (y : P) (x : Plane) (hx : A ≤ |x.1| ∨ A ≤ |x.2|) : H (y,x) = 0 := by
    have he : H (y,x) = H (y,(B,B)) := by
      rcases hx with hx | hx
      · exact (hvert y x.1 hx x.2 B).trans (hhor y B hAB x.1 B)
      · exact (hhor y x.2 hx x.1 B).trans (hvert y B hAB x.2 B)
    rw [he]
    simp only [H,rectangularPotential,intervalIntegral.integral_same,zero_add]
  refine ⟨H,rectangularPotential_smooth hα B,?_,hHd,hzero⟩
  apply HasCompactSupport.intro ((hαc.image continuous_fst).prod
    (isCompact_Icc : IsCompact (Icc (-A,-A) (A,A) : Set Plane)))
  intro p hp
  by_cases hy : p.1 ∈ Prod.fst '' tsupport α
  · apply hout
    have hx : p.2 ∉ Icc (-A,-A) (A,A) := fun h => hp ⟨hy,h⟩
    by_contra! ht
    apply hx
    exact ⟨⟨(abs_lt.mp ht.1).1.le,(abs_lt.mp ht.2).1.le⟩,
      ⟨(abs_lt.mp ht.1).2.le,(abs_lt.mp ht.2).2.le⟩⟩
  · apply hzero
    intro x
    exact image_eq_zero_of_notMem_tsupport (f := α) (x := (p.1,x))
      (fun h => hy ⟨(p.1,x),h,rfl⟩)

theorem compact_potential_zero_outside {H : Plane → ℝ} {α : Plane → Plane →L[ℝ] ℝ}
    (hHc : HasCompactSupport H) (hd : ∀ x, HasFDerivAt H (α x) x)
    {T : ℝ} (hT : 0 < T) (ha : ∀ x, T ≤ radiusSq x → α x = 0)
    (x : Plane) (hx : T ≤ radiusSq x) : H x = 0 := by
  have hx0 : x ≠ 0 := by
    intro he
    subst x
    simp [radiusSq] at hx
    linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let γ : ℝ → Plane := fun t => (1+t^2) • x
  have hγ (t : ℝ) : T ≤ radiusSq (γ t) := by
    dsimp [γ]
    rw [radiusSq_smul]
    have ht := sq_nonneg t
    have hxz := radiusSq_nonneg x
    nlinarith [sq_nonneg (t^2)]
  have hg (t : ℝ) : HasDerivAt (fun t => H (γ t)) 0 t := by
    have hgd : HasDerivAt γ ((2*t) • x) t := by
      simpa [γ] using (((hasDerivAt_id t).pow 2).const_add 1).smul_const x
    have hh := (hd (γ t)).comp_hasDerivAt t hgd
    rw [ha (γ t) (hγ t)] at hh
    exact hh.congr_deriv (by simp)
  have he (t : ℝ) : H x = H (γ t) := by
    have hh := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) 0 t
    simpa [γ] using hh
  obtain ⟨A,hA,hB⟩ := hHc.isBounded.subset_ball_lt 1 (0 : Plane)
  let t := Real.sqrt (A/‖x‖)
  have ht : t^2 = A/‖x‖ := Real.sq_sqrt (by positivity)
  rw [he t]
  apply image_eq_zero_of_notMem_tsupport
  intro hs
  have hb := hB hs
  simp only [Metric.mem_ball, dist_zero_right] at hb
  have hn : ‖γ t‖ = A+‖x‖ := by
    dsimp [γ]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),ht]
    field_simp
    ring
  rw [hn] at hb
  linarith

theorem exists_parametric_disk_closed_primitive {α : P × Plane → Plane →L[ℝ] ℝ}
    (hα : ContDiff ℝ ∞ α) (hαc : HasCompactSupport α)
    {R : ℝ} (_hR : 0 < R) (hαs : tsupport α ⊆ univ ×ˢ roundDisk R)
    (hclosed : ∀ y x v w, fderiv ℝ (fun x => α (y,x)) x v w =
      fderiv ℝ (fun x => α (y,x)) x w v) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      tsupport H ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x, HasFDerivAt (fun x => H (y,x)) (α (y,x)) x) ∧
      ∀ y, (∀ x, α (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  obtain ⟨H,hH,hHc,hd,hzero⟩ := exists_parametric_closed_primitive hα hαc hclosed
  refine ⟨H,hH,hHc,?_,hd,hzero⟩
  by_cases hs : (tsupport α).Nonempty
  · obtain ⟨p,hp,hmax⟩ := hαc.exists_isMaxOn hs
      (radiusSq_smooth.continuous.comp continuous_snd).continuousOn
    have hpr : radiusSq p.2 < R^2 := (hαs hp).2
    let T := (radiusSq p.2+R^2)/2
    have hT : 0 < T := by dsimp [T]; nlinarith [radiusSq_nonneg p.2]
    have hpT : radiusSq p.2 < T := by dsimp [T]; linarith
    have hTR : T < R^2 := by dsimp [T]; linarith
    have ha (y : P) (x : Plane) (hx : T ≤ radiusSq x) : α (y,x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      have hh := hmax hm
      change radiusSq x ≤ radiusSq p.2 at hh
      linarith
    have hsupport : tsupport H ⊆ {p : P × Plane | radiusSq p.2 ≤ T} := by
      apply closure_minimal _ (isClosed_le (radiusSq_smooth.continuous.comp continuous_snd) continuous_const)
      intro q hq
      by_contra hn
      have hn' : T ≤ radiusSq q.2 := le_of_not_ge hn
      exact hq (compact_potential_zero_outside (compactSupport_fiber hHc q.1)
        (hd q.1) hT (ha q.1) q.2 hn')
    intro q hq
    exact ⟨trivial,lt_of_le_of_lt (hsupport hq) hTR⟩
  · have hα0 (y : P) (x : Plane) : α (y,x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hs ⟨(y,x),h⟩)
    have hHz : H = 0 := funext (fun p => hzero p.1 (hα0 p.1) p.2)
    simp [hHz]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
