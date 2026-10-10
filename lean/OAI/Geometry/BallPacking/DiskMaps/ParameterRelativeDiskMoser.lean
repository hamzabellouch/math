import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.NormalizedRoundedBoxes

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_disk_moser {ι : Type*} [Fintype ι]
    {R : ℝ} (hR : 0 < R) {f : P × Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ univ ×ˢ roundDisk R)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0) (hpos : ∀ p, 0 < 1+f p)
    (Y : Set P) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (r i), f (y,p)) = 0) :
    ∃ Ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => Ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, (1+f (y,Ψ y x)) *
        planarArea (fderiv ℝ (Ψ y) x v) (fderiv ℝ (Ψ y) x w) = planarArea v w) ∧
      (∀ i y, y ∈ Y → Ψ y '' closedRoundDisk (r i) = closedRoundDisk (r i)) ∧
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
  have hz' (i : ι) (y : P) (hy : y ∈ Y) : (∫ p in roundDisk (r' i), F (y,p)) = 0 := by
    change (∫ p in roundDisk (diskChartRadius R (r i)),
      radialDiskDensity R p * (fun x => f (y,x)) (radialDiskChart R p)) = 0
    rw [← radialDiskChart_integral_inner hR (hr i).le (hrR i) (fun x => f (y,x))]
    exact hz i y hy
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦzero⟩ :=
    exists_parameter_relative_background_moser hg hF hFc hF0 hgpos hGFpos Y r' hr' hri' hz'
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
  · intro i y hy
    rw [hΨfun,← radialDiskChart_image_closed hR (hr i).le (hrR i),
      Chart.conjugate_image c hcs,hΦdisk i y hy]
  · intro y hy x
    have hFzero (p : Plane) : F (y,p) = 0 := by simp only [F,hy,mul_zero]
    have hid : (Φ y : Plane → Plane) = id := funext (hΦzero y hFzero)
    rw [hΨeq,hid,Chart.conjugate_id]



theorem exists_parameter_relative_corrected_disk_diffeomorphisms
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (φ : P → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : P × Plane => φ p.1 p.2))
    (hφi : ContDiff ℝ ∞ (fun p : P × Plane => (φ p.1).symm p.2))
    (hφc : HasCompactSupport (fun p : P × Plane => φ p.1 p.2-p.2))
    (hφs : tsupport (fun p : P × Plane => φ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R)
    (hpos : ∀ p : P × Plane, 0 < spatialJacobian (fun p => φ p.1 p.2) p)
    (Y : Set P) (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (hz : ∀ i y, y ∈ Y → (∫ x in roundDisk (r i),
      spatialJacobian (fun p : P × Plane => φ p.1 p.2) (y,x)-1) = 0) :
    ∃ ψ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (ψ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => ψ p.1 p.2-p.2) ∧
      tsupport (fun p : P × Plane => ψ p.1 p.2-p.2) ⊆ univ ×ˢ roundDisk R ∧
      (∀ y x v w, planarArea (fderiv ℝ (ψ y) x v) (fderiv ℝ (ψ y) x w) = planarArea v w) ∧
      (∀ i y, y ∈ Y → ψ y '' closedRoundDisk (r i) = φ y '' closedRoundDisk (r i)) ∧
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
    exists_parameter_relative_disk_moser hR hf hfc hfs hf0 hfpos Y r hr hrR hri hz
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
  · intro i y hy
    change (φ y ∘ χ y) '' closedRoundDisk (r i) = _
    rw [image_comp,hχdisk i y hy]
  · intro y hy x
    have hh := hχzero y (fun x => sub_eq_zero.mpr (hy x)) x
    change φ y (χ y x) = φ y x
    rw [hh]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

theorem circle_volume_zero (R : ℝ) :
    volume {x : Plane | radiusSq x = R^2} = 0 := by
  change (volume.prod volume) {x : Plane | radiusSq x = R^2} = 0
  apply Measure.measure_prod_null_of_ae_null
    (isClosed_eq ((continuous_fst.pow 2).add (continuous_snd.pow 2)) continuous_const).measurableSet
  apply Filter.Eventually.of_forall
  intro x
  apply measure_mono_null (t := {Real.sqrt (R^2-x^2),-Real.sqrt (R^2-x^2)})
  · intro y hy
    change x^2+y^2 = R^2 at hy
    have hn : 0 ≤ R^2-x^2 := by nlinarith [sq_nonneg y]
    have he : y^2 = (Real.sqrt (R^2-x^2))^2 := by rw [Real.sq_sqrt hn]; linarith
    simpa only [mem_insert_iff,mem_singleton_iff] using sq_eq_sq_iff_eq_or_eq_neg.mp he
  · exact Set.Finite.measure_zero ((Set.finite_singleton _).insert _) volume

theorem roundDisk_ae_closedRoundDisk (R : ℝ) :
    roundDisk R =ᵐ[volume] closedRoundDisk R := by
  have hh : ∀ᵐ x : Plane ∂volume, x ∉ {x : Plane | radiusSq x = R^2} := by
    apply ae_iff.mpr
    simpa only [not_not,mem_ofPred_eq] using circle_volume_zero R
  filter_upwards [hh] with x hx
  change (radiusSq x < R^2) = (radiusSq x ≤ R^2)
  exact propext (lt_iff_le_and_ne.trans (and_iff_left hx))

theorem integral_roundDisk_eq_closedRoundDisk (f : Plane → ℝ) (R : ℝ) :
    (∫ x in roundDisk R, f x) = ∫ x in closedRoundDisk R, f x :=
  setIntegral_congr_set (roundDisk_ae_closedRoundDisk R)

theorem jacobian_defect_roundDisk_of_area (φ : Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ φ) (hpos : ∀ x, 0 < (fderiv ℝ φ x).det) (r : ℝ)
    (harea : volume (φ '' closedRoundDisk r) = volume (closedRoundDisk r)) :
    (∫ x in roundDisk r, (fderiv ℝ φ x).det-1) = 0 := by
  rw [integral_roundDisk_eq_closedRoundDisk]
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume
    (closedRoundDisk_isCompact r).measurableSet
    (f' := fderiv ℝ φ)
    (fun x _ => ((hφ.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt)
    φ.injective.injOn (fun _ : Plane => (1 : ℝ))
  simp only [smul_eq_mul,mul_one,abs_of_pos (hpos _)] at hi
  have ha : (∫ _ in φ '' closedRoundDisk r, (1:ℝ)) = ∫ _ in closedRoundDisk r, (1:ℝ) := by
    simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,mul_one,Measure.real,harea]
  rw [ha] at hi
  rw [integral_sub]
  · exact sub_eq_zero.mpr hi.symm
  · have hd : Continuous (fun x => (fderiv ℝ φ x).det) :=
      ContinuousLinearMap.continuous_det.comp (hφ.fderiv_right (m := ∞) (by simp)).continuous
    exact hd.continuousOn.integrableOn_compact (closedRoundDisk_isCompact r)
  · exact integrableOn_const (closedRoundDisk_isCompact r).measure_lt_top.ne


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def planarHamiltonianField (α : Plane →L[ℝ] ℝ) : Plane := (-α (0,1),α (1,0))

@[simp] theorem planarHamiltonianField_neg_area (v : Plane) :
    planarHamiltonianField (-planarArea v) = v := by
  ext <;> simp [planarHamiltonianField,planarArea_apply]

theorem familyGenerator_hasDerivAt
    (φ : P × ℝ → Plane ≃ₜ Plane)
    (hφ : ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => φ p.1 p.2))
    (y : P) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => φ (y,s) x)
      (familyGenerator φ (0,1) ((y,t),φ (y,t) x)) t := by
  have hg : HasDerivAt (fun s : ℝ => ((y,s),x)) ((0,1),0) t :=
    ((hasDerivAt_const t y).prodMk (hasDerivAt_id t)).prodMk (hasDerivAt_const t x)
  have hh := (hφ.differentiable (by simp) ((y,t),x)).hasFDerivAt.comp_hasDerivAt t hg
  simpa only [familyGenerator,Homeomorph.symm_apply_apply,Function.comp_def] using hh

structure HamiltonianDiskIsotopyFamily (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (R : ℝ) where
  isotopy : SupportedSmoothIsotopyFamily P Plane (roundDisk R)
  symplectic : ∀ y t x v w, planarArea (fderiv ℝ (isotopy.map y t) x v)
    (fderiv ℝ (isotopy.map y t) x w) = planarArea v w
  hamiltonian : (P × ℝ) × Plane → ℝ
  smooth : ContDiff ℝ ∞ hamiltonian
  compact : HasCompactSupport hamiltonian
  support : tsupport hamiltonian ⊆ univ ×ˢ roundDisk R
  flow : ∀ y t x, HasDerivAt (fun s => isotopy.map y s x)
    (planarHamiltonianField (fderiv ℝ (fun z => hamiltonian ((y,t),z))
      (isotopy.map y t x))) t

variable [FiniteDimensional ℝ P]

theorem exists_hamiltonian_disk_isotopy
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    (Φ : SupportedSmoothIsotopyFamily P Plane (roundDisk R))
    (Y : Set P) (hY : IsCompact Y)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (hrR : ∀ i, r i < R) (hri : Injective r)
    (harea : ∀ i y, y ∈ Y → volume (Φ.map y 1 '' closedRoundDisk (r i)) =
      volume (closedRoundDisk (r i))) :
    ∃ Ψ : HamiltonianDiskIsotopyFamily P R, ∀ i y, y ∈ Y →
      Ψ.isotopy.map y 1 '' closedRoundDisk (r i) = Φ.map y 1 '' closedRoundDisk (r i) := by
  obtain ⟨Φ₀,hΦc,hΦeq⟩ := Φ.exists_joint_compact Y hY
  let φ : P × ℝ → Plane ≃ₜ Plane := fun q => Φ₀.map q.1 q.2
  have hφs : tsupport (fun p : (P × ℝ) × Plane => φ p.1 p.2-p.2) ⊆
      univ ×ˢ roundDisk R := Φ₀.joint_support.trans (prod_mono Subset.rfl Φ₀.support_subset)
  have hpos (p : (P × ℝ) × Plane) :
      0 < spatialJacobian (fun p => φ p.1 p.2) p :=
    (Φ₀.eval p.1.1).det_fderiv_pos p.1.2 p.2
  have hz (i : ι) (q : P × ℝ) (hq : q ∈ Y ×ˢ ({1} : Set ℝ)) :
      (∫ x in roundDisk (r i), spatialJacobian (fun p => φ p.1 p.2) (q,x)-1) = 0 := by
    have ht : q.2 = 1 := hq.2
    have he : φ q = Φ.map q.1 1 := by
      change Φ₀.map q.1 q.2 = _
      rw [ht,hΦeq q.1 hq.1 1 ⟨zero_le_one,le_rfl⟩]
    apply jacobian_defect_roundDisk_of_area (φ q) ((Φ₀.eval q.1).map_smooth q.2)
      (fun x => hpos (q,x)) (r i)
    rw [he]
    exact harea i q.1 hq.1
  obtain ⟨ψ,hψ,hψi,hψc,hψs,hψsp,hψdisk,hψzero⟩ :=
    exists_parameter_relative_corrected_disk_diffeomorphisms hR φ Φ₀.smooth
      Φ₀.inverse_smooth hΦc hφs hpos (Y ×ˢ ({1} : Set ℝ)) r hr hrR hri hz
  have hzero (y : P) : ψ (y,0) = Homeomorph.refl Plane := by
    apply Homeomorph.ext
    intro x
    have hJ (z : Plane) : spatialJacobian (fun p => φ p.1 p.2) ((y,0),z) = 1 := by
      dsimp only [spatialJacobian,φ]
      rw [Φ₀.zero y]
      simp [ContinuousLinearMap.det]
    rw [hψzero (y,0) hJ x]
    change Φ₀.map y 0 x = x
    rw [Φ₀.zero y]
    rfl
  let Ψ : SupportedSmoothIsotopyFamily P Plane (roundDisk R) := {
    map := fun y t => ψ (y,t)
    smooth := hψ
    inverse_smooth := hψi
    zero := hzero
    support := Prod.snd '' tsupport (fun p : (P × ℝ) × Plane => ψ p.1 p.2-p.2)
    compact_support := hψc.image continuous_snd
    support_subset := by rintro x ⟨p,hp,rfl⟩; exact (hψs hp).2
    fixed := by
      intro y t x hx
      exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport
        (f := fun p : (P × ℝ) × Plane => ψ p.1 p.2-p.2)
        (fun hp => hx ⟨((y,t),x),hp,rfl⟩)) }
  obtain ⟨H,hH,hHc,hHs,hHd,_⟩ := exists_hamiltonian_of_symplectic_family ψ hψ hψi
    hψc hR hψs hψsp (0,1)
  refine ⟨{ isotopy := Ψ
            symplectic := fun y t => hψsp (y,t)
            hamiltonian := H
            smooth := hH
            compact := hHc
            support := hHs
            flow := ?_ },?_⟩
  · intro y t x
    have hd := hHd (y,t) (ψ (y,t) x)
    rw [hd.fderiv,planarHamiltonianField_neg_area]
    exact familyGenerator_hasDerivAt ψ hψ y t x
  · intro i y hy
    change ψ (y,1) '' closedRoundDisk (r i) = _
    rw [hψdisk i (y,1) ⟨hy,rfl⟩]
    change Φ₀.map y 1 '' closedRoundDisk (r i) = _
    rw [hΦeq y hy 1 ⟨zero_le_one,le_rfl⟩]


end

open scoped ContDiff Topology
open Set Function

structure PlanarDiskEmbedding where
  radius : ℝ
  radius_pos : 0 < radius
  map : ℂ → ℂ
  smooth : ContDiff ℝ ∞ map
  domain : Set ℂ
  open_domain : IsOpen domain
  convex_domain : Convex ℝ domain
  subset_domain : Metric.closedBall 0 radius ⊆ domain
  injective : InjOn map domain
  nonsingular : ∀ x ∈ domain, (fderiv ℝ map x).IsInvertible
  orientation : 0 < (fderiv ℝ map 0).det

namespace PlanarDiskEmbedding

def carrier (D : PlanarDiskEmbedding) : Set ℂ := D.map '' Metric.closedBall 0 D.radius

theorem compact_carrier (D : PlanarDiskEmbedding) : IsCompact D.carrier :=
  (isCompact_closedBall (0:ℂ) D.radius).image D.smooth.continuous

def Nested (D E : PlanarDiskEmbedding) : Prop :=
  E.radius < D.radius ∧ E.carrier ⊆ interior D.carrier

def pull {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    PlanarDiskEmbedding where
  radius := D.radius
  radius_pos := D.radius_pos
  map := (Φ.map 1).symm ∘ D.map
  smooth := (Φ.symm_smooth 1).comp D.smooth
  domain := D.domain
  open_domain := D.open_domain
  convex_domain := D.convex_domain
  subset_domain := D.subset_domain
  injective := (Φ.map 1).symm.injective.injOn.comp D.injective (mapsTo_univ _ _)
  nonsingular := by
    intro x hx
    rw [fderiv_comp x ((Φ.symm_smooth 1).differentiable (by simp) _) (D.smooth.differentiable (by simp) x)]
    exact (Φ.symm.fderiv_isInvertible 1 (D.map x)).comp (D.nonsingular x hx)
  orientation := by
    rw [fderiv_comp 0 ((Φ.symm_smooth 1).differentiable (by simp) _) (D.smooth.differentiable (by simp) 0)]
    rw [ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
    exact mul_pos (Φ.symm.det_fderiv_pos 1 (D.map 0)) D.orientation

@[simp] theorem pull_radius {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    (D.pull Φ).radius = D.radius := rfl

@[simp] theorem pull_carrier {W : Set ℂ} (D : PlanarDiskEmbedding) (Φ : SupportedSmoothIsotopy W) :
    (D.pull Φ).carrier = (Φ.map 1).symm '' D.carrier := by
  change ((Φ.map 1).symm ∘ D.map) '' Metric.closedBall 0 D.radius =
    (Φ.map 1).symm '' (D.map '' Metric.closedBall 0 D.radius)
  exact image_comp _ _ _

theorem nested_pull {W : Set ℂ} {D E : PlanarDiskEmbedding} (h : D.Nested E)
    (Φ : SupportedSmoothIsotopy W) : (D.pull Φ).Nested (E.pull Φ) := by
  refine ⟨h.1,?_⟩
  simp only [pull_carrier]
  rw [← (Φ.map 1).symm.image_interior]
  exact image_mono h.2

theorem exists_isotopy (D : PlanarDiskEmbedding) {R : ℝ}
    (hDR : D.radius < R) (hD : D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  have h0 : (0:ℂ) ∈ Metric.closedBall 0 D.radius := Metric.mem_closedBall_self D.radius_pos.le
  have HH := exists_compact_planar_embedding_isotopy D.map D.smooth D.domain
    (Metric.ball 0 R) D.open_domain Metric.isOpen_ball D.convex_domain (convex_ball (0:ℂ) R)
    D.injective D.nonsingular (Metric.closedBall 0 D.radius) (isCompact_closedBall _ _) h0
    D.subset_domain (Metric.closedBall_subset_ball hDR) (fun x hx => hD ⟨x,hx,rfl⟩)
    (by rw [← complex_det]; exact D.orientation)
  obtain ⟨Φ,hΦ⟩ := HH
  refine ⟨Φ,?_⟩
  apply image_congr
  intro x hx
  exact hΦ x hx

end PlanarDiskEmbedding

namespace SupportedSmoothIsotopy

def mono {U W : Set ℂ} (Φ : SupportedSmoothIsotopy U) (hUW : U ⊆ W) :
    SupportedSmoothIsotopy W where
  map := Φ.map
  smooth := Φ.smooth
  inverse_smooth := Φ.inverse_smooth
  zero := Φ.zero
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset.trans hUW
  fixed := Φ.fixed

theorem image_closedBall {R : ℝ} (Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R))
    (t : ℝ) : Φ.map t '' Metric.closedBall 0 R = Metric.closedBall 0 R := by
  have hh (Ψ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R)) :
      MapsTo (Ψ.map t) (Metric.closedBall 0 R) (Metric.closedBall 0 R) := by
    intro x hx
    by_cases hx' : x ∈ Metric.ball 0 R
    · exact Metric.ball_subset_closedBall (Ψ.mapsTo t hx')
    · rwa [Ψ.fixed t x (fun h => hx' (Ψ.support_subset h))]
  apply Subset.antisymm (image_subset_iff.mpr (hh Φ))
  intro x hx
  exact ⟨(Φ.map t).symm x,hh Φ.symm hx,(Φ.map t).apply_symm_apply x⟩

end SupportedSmoothIsotopy

theorem exists_nested_disk_isotopy (L : List PlanarDiskEmbedding)
    (hL : L.Pairwise PlanarDiskEmbedding.Nested) (R : ℝ)
    (hR : ∀ D ∈ L, D.radius < R)
    (hW : ∀ D ∈ L, D.carrier ⊆ Metric.ball 0 R) :
    ∃ Φ : SupportedSmoothIsotopy (Metric.ball (0:ℂ) R),
      ∀ D ∈ L, Φ.map 1 '' Metric.closedBall 0 D.radius = D.carrier := by
  induction hn : L.length using Nat.strong_induction_on generalizing L R with
  | h n ih =>
    cases L with
    | nil => exact ⟨SupportedSmoothIsotopy.refl _,by simp⟩
    | cons D L =>
      obtain ⟨Φ,hΦ⟩ := D.exists_isotopy (hR D (by simp)) (hW D (by simp))
      let L' := L.map (fun E => E.pull Φ)
      have hLL : L.Pairwise PlanarDiskEmbedding.Nested := hL.of_cons
      have hDL : ∀ E ∈ L, D.Nested E := fun _ h => List.rel_of_pairwise_cons hL h
      have hL' : L'.Pairwise PlanarDiskEmbedding.Nested := by
        exact List.Pairwise.map (fun E => E.pull Φ)
          (fun _ _ h => PlanarDiskEmbedding.nested_pull h Φ) hLL
      have hR' : ∀ E ∈ L', E.radius < D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        exact (hDL E0 hE0).1
      have hW' : ∀ E ∈ L', E.carrier ⊆ Metric.ball 0 D.radius := by
        intro E hE
        change E ∈ L.map (fun E => E.pull Φ) at hE
        obtain ⟨E0,hE0,he⟩ := List.mem_map.mp hE
        subst E
        rw [PlanarDiskEmbedding.pull_carrier]
        have hsub := image_mono (f := (Φ.map 1).symm) (hDL E0 hE0).2
        rw [(Φ.map 1).symm.image_interior,← hΦ] at hsub
        simpa only [Set.image_image,(Φ.map 1).symm_apply_apply,Set.image_id',
          interior_closedBall'] using hsub
      have hlen : L'.length < n := by
        simp only [L',List.length_map]
        simp only [List.length_cons] at hn
        omega
      obtain ⟨Ψ,hΨ⟩ := ih L'.length hlen L' hL' D.radius hR' hW' rfl
      let Ψ' := Ψ.mono (Metric.ball_subset_ball (hR D (by simp)).le)
      refine ⟨Ψ'.trans Φ,?_⟩
      intro E hE
      rcases List.mem_cons.mp hE with hE | hE
      · subst E
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 D.radius = D.carrier
        rw [← Set.image_image,Ψ.image_closedBall 1,hΦ]
      · have he := hΨ (E.pull Φ) (List.mem_map.mpr ⟨E,hE,rfl⟩)
        simp only [PlanarDiskEmbedding.pull_radius] at he
        change (fun x => Φ.map 1 (Ψ.map 1 x)) '' Metric.closedBall 0 E.radius = E.carrier
        rw [← Set.image_image,he,PlanarDiskEmbedding.pull_carrier]
        simp only [Set.image_image,(Φ.map 1).apply_symm_apply,Set.image_id']



end PackingSufficiencySupport.Hamiltonian
end

end OAI
