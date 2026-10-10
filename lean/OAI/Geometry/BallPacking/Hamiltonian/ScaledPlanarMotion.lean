import Mathlib
import OAI.Geometry.BallPacking.Hamiltonian.AnnularDensityMass

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem planarHamiltonianField_smul (c : ℝ) (α : Plane →L[ℝ] ℝ) :
    planarHamiltonianField (c • α) = c • planarHamiltonianField α := by
  ext <;> simp [planarHamiltonianField]

theorem scaled_planar_fderiv {H : Plane → ℝ} (hH : Differentiable ℝ H)
    {a : ℝ} (ha : a ≠ 0) (c : ℝ) (x : Plane) :
    fderiv ℝ (fun z => (c*a^2)*H (a⁻¹ • z)) x =
      (c*a) • fderiv ℝ H (a⁻¹ • x) := by
  have hd := ((hH (a⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul a⁻¹)).const_mul (c*a^2)
  change fderiv ℝ (fun z => (c*a^2)*(H ∘ HSMul.hSMul a⁻¹) z) x = _
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  field_simp [ha]

def scaledPlanarHamiltonian (Ψ : PlanarHamiltonianMotion P) (a χ : P → ℝ)
    (p : (P × ℝ) × Plane) : ℝ :=
  ((χ p.1.1 * deriv Real.smoothTransition p.1.2)*(a p.1.1)^2) *
    Ψ.hamiltonian ((p.1.1,χ p.1.1 * Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2)

def scaledPlanarTrace (Ψ : PlanarHamiltonianMotion P) (a χ : P → ℝ)
    (y : P) (t : ℝ) (x : Plane) : Plane :=
  a y • Ψ.trace y (χ y * Real.smoothTransition t) ((a y)⁻¹ • x)

theorem scaledPlanarHamiltonian_smooth (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (scaledPlanarHamiltonian Ψ a χ) := by
  have hai : ContDiff ℝ ∞ (fun y => (a y)⁻¹) := ha.inv hn
  have hβ : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
  unfold scaledPlanarHamiltonian
  exact (((hχ.comp contDiff_fst.fst).mul (hβ.comp contDiff_fst.snd)).mul
    ((ha.comp contDiff_fst.fst).pow 2)).mul (Ψ.smooth.comp
      ((contDiff_fst.fst.prodMk ((hχ.comp contDiff_fst.fst).mul
        (Real.smoothTransition.contDiff.comp contDiff_fst.snd))).prodMk
          ((hai.comp contDiff_fst.fst).smul contDiff_snd)))

theorem scaledPlanarHamiltonian_compact (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) (hχ : HasCompactSupport χ) :
    HasCompactSupport (scaledPlanarHamiltonian Ψ a χ) := by
  let K := (tsupport χ ×ˢ tsupport (deriv Real.smoothTransition)) ×ˢ (Prod.snd '' tsupport Ψ.hamiltonian)
  let f : (P × ℝ) × Plane → (P × ℝ) × Plane := fun p => (p.1,a p.1.1 • p.2)
  have hK : IsCompact K := (hχ.prod smoothTransition_deriv_compact).prod
    (Ψ.compact.image continuous_snd)
  have hf : Continuous f := continuous_fst.prodMk ((ha.comp continuous_fst.fst).smul continuous_snd)
  apply HasCompactSupport.intro (hK.image hf)
  intro p hp
  by_contra hne
  have hc : χ p.1.1 ≠ 0 := by intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  have ht : deriv Real.smoothTransition p.1.2 ≠ 0 := by
    intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  have hb : Ψ.hamiltonian ((p.1.1,χ p.1.1*Real.smoothTransition p.1.2),(a p.1.1)⁻¹ • p.2) ≠ 0 := by
    intro hz; apply hne; simp [scaledPlanarHamiltonian,hz]
  apply hp
  refine ⟨(p.1,(a p.1.1)⁻¹ • p.2),⟨⟨subset_closure hc,subset_closure ht⟩,?_⟩,?_⟩
  · exact ⟨_,subset_closure hb,rfl⟩
  · dsimp [f]
    rw [smul_inv_smul₀ (hn p.1.1)]

theorem scaledPlanarTrace_continuous (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (ha : Continuous a) (hn : ∀ y, a y ≠ 0) (hχ : Continuous χ) :
    Continuous (fun p : (P × ℝ) × Plane => scaledPlanarTrace Ψ a χ p.1.1 p.1.2 p.2) := by
  unfold scaledPlanarTrace
  exact (ha.comp continuous_fst.fst).smul (Ψ.continuous.comp
    ((continuous_fst.fst.prodMk ((hχ.comp continuous_fst.fst).mul
      (Real.smoothTransition.continuous.comp continuous_fst.snd))).prodMk
        (((ha.inv₀ hn).comp continuous_fst.fst).smul continuous_snd)))

theorem scaledPlanarTrace_zero (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (hn : ∀ y, a y ≠ 0) (y : P) (x : Plane) :
    scaledPlanarTrace Ψ a χ y 0 x = x := by
  simp only [scaledPlanarTrace,Real.smoothTransition.zero_of_nonpos le_rfl,mul_zero,Ψ.zero]
  exact smul_inv_smul₀ (hn y) x

theorem scaledPlanarTrace_flow (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (hn : ∀ y, a y ≠ 0) (y : P) (t : ℝ) (x : Plane) :
    HasDerivAt (fun s => scaledPlanarTrace Ψ a χ y s x)
      (planarHamiltonianField (fderiv ℝ (fun z => scaledPlanarHamiltonian Ψ a χ ((y,t),z))
        (scaledPlanarTrace Ψ a χ y t x))) t := by
  have hβ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp) t).hasDerivAt
  have hd := ((Ψ.flow y (χ y*Real.smoothTransition t) ((a y)⁻¹ • x)).scomp t
    (hβ.const_mul (χ y))).const_smul (a y)
  have hs : Differentiable ℝ (fun z => Ψ.hamiltonian ((y,χ y*Real.smoothTransition t),z)) :=
    (Ψ.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  dsimp only [scaledPlanarHamiltonian]
  rw [scaled_planar_fderiv hs (hn y),planarHamiltonianField_smul]
  simp only [scaledPlanarTrace,inv_smul_smul₀ (hn y)]
  convert! hd using 1
  simp only [smul_smul]
  congr 1
  ring

def PlanarHamiltonianMotion.scaled (Ψ : PlanarHamiltonianMotion P)
    (a χ : P → ℝ) (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) : PlanarHamiltonianMotion P where
  hamiltonian := scaledPlanarHamiltonian Ψ a χ
  smooth := scaledPlanarHamiltonian_smooth Ψ ha hn hχ
  compact := scaledPlanarHamiltonian_compact Ψ ha.continuous hn hχc
  trace := scaledPlanarTrace Ψ a χ
  continuous := scaledPlanarTrace_continuous Ψ ha.continuous hn hχ.continuous
  zero := scaledPlanarTrace_zero Ψ hn
  flow := scaledPlanarTrace_flow Ψ hn

end

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

@[simp] theorem radialArea_smul (a : ℝ) (x : Plane) :
    radialArea (a • x) = a^2*radialArea x := by
  simp only [radialArea,radiusSq_smul]
  ring

theorem scaledPlanarTrace_smooth (Ψ : PlanarHamiltonianMotion P)
    (hΨ : ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => Ψ.trace p.1.1 p.1.2 p.2))
    {a χ : P → ℝ} (ha : ContDiff ℝ ∞ a) (hn : ∀ y, a y ≠ 0) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (fun p : (P × ℝ) × Plane => scaledPlanarTrace Ψ a χ p.1.1 p.1.2 p.2) := by
  unfold scaledPlanarTrace
  exact (ha.comp contDiff_fst.fst).smul (hΨ.comp
    ((contDiff_fst.fst.prodMk ((hχ.comp contDiff_fst.fst).mul
      (Real.smoothTransition.contDiff.comp contDiff_fst.snd))).prodMk
        (((ha.inv hn).comp contDiff_fst.fst).smul contDiff_snd)))

theorem scaledPlanarTrace_cutoff_zero (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (hχ : χ y = 0) (t : ℝ) (x : Plane) :
    scaledPlanarTrace Ψ a χ y t x = x := by
  simp only [scaledPlanarTrace,hχ,zero_mul,Ψ.zero]
  exact smul_inv_smul₀ ha x

theorem scaledPlanarTrace_time_one (Ψ : PlanarHamiltonianMotion P)
    {a χ : P → ℝ} (y : P) (hχ : χ y = 1) (x : Plane) :
    scaledPlanarTrace Ψ a χ y 1 x = a y • Ψ.trace y 1 ((a y)⁻¹ • x) := by
  simp [scaledPlanarTrace,hχ,Real.smoothTransition.one_of_one_le le_rfl]

theorem scaled_disk_fixed (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : (a y)^2 ≤ radialArea x) : scaledPlanarTrace Ψ.motion a χ y t x = x := by
  have hs : (a y)⁻¹ • x ∉ roundDisk (areaRadius 1) := by
    rw [mem_roundDisk_areaRadius (by norm_num),radialArea_smul,not_lt]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [Ψ.isotopy.fixed y _ _ (fun h => hs (Ψ.isotopy.support_subset h))]
  exact smul_inv_smul₀ ha x

theorem scaled_disk_mapsTo (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane)
    (hx : radialArea x ≤ (a y)^2) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ (a y)^2 := by
  have hs : (a y)⁻¹ • x ∈ closedRoundDisk (areaRadius 1) := by
    rw [mem_closedRoundDisk_areaRadius (by norm_num),radialArea_smul]
    have hh := mul_le_mul_of_nonneg_left hx (sq_nonneg (a y)⁻¹)
    have he : (a y)⁻¹^2*(a y)^2 = 1 := by field_simp
    linarith
  have hm := Ψ.mapsTo_closed y (χ y*Real.smoothTransition t) hs
  rw [mem_closedRoundDisk_areaRadius (by norm_num)] at hm
  dsimp only [scaledPlanarTrace,HamiltonianDiskIsotopyFamily.motion]
  rw [radialArea_smul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (sq_nonneg (a y))

theorem scaled_disk_preserves_slice (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1))
    {a χ : P → ℝ} (y : P) (ha : a y ≠ 0) (t : ℝ) (x : Plane) {L : ℝ}
    (hx : radialArea x ≤ L) (hfit : χ y ≠ 0 → (a y)^2 ≤ L) :
    radialArea (scaledPlanarTrace Ψ.motion a χ y t x) ≤ L := by
  by_cases hc : χ y = 0
  · rw [scaledPlanarTrace_cutoff_zero Ψ.motion y ha hc]; exact hx
  · rcases le_total (radialArea x) ((a y)^2) with hl | hl
    · exact (scaled_disk_mapsTo Ψ y ha t x hl).trans (hfit hc)
    · rw [scaled_disk_fixed Ψ y ha t x hl]; exact hx

theorem HamiltonianDiskIsotopyFamily.exists_support_margin
    (Ψ : HamiltonianDiskIsotopyFamily P (areaRadius 1)) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∀ p ∈ tsupport Ψ.hamiltonian, radialArea p.2 ≤ σ := by
  rcases (tsupport Ψ.hamiltonian).eq_empty_or_nonempty with he | hn
  · exact ⟨1/2,by norm_num,by norm_num,by simp [he]⟩
  obtain ⟨p,hp,hm⟩ := Ψ.compact.exists_isMaxOn hn
    (radialArea_smooth.continuous.comp continuous_snd).continuousOn
  have hp1 : radialArea p.2 < 1 :=
    (mem_roundDisk_areaRadius (by norm_num) _).mp (Ψ.support hp).2
  refine ⟨(radialArea p.2+1)/2,by linarith [radialArea_nonneg p.2],by linarith,?_⟩
  intro q hq
  have hh : radialArea q.2 ≤ radialArea p.2 := hm hq
  linarith

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Comparison
open scoped Topology
open Set Function Filter
section

theorem exists_longer_strict_interval {f : ℝ → ℝ} (hf : Continuous f)
    {a h c : ℝ} (ha : 0 ≤ a) (hah : a+h ≤ 1) (_hh : 0 ≤ h) (hh1 : h < 1)
    (hla : f a < c) (hlb : f (a+h) < c) :
    ∃ u v : ℝ, 0 < u ∧ v < 1 ∧ h < v-u ∧ f u < c ∧ f v < c := by
  let u₀ : ℝ := (1-h)/4
  let v₀ : ℝ := (3+h)/4
  have hu₀ : 0 < u₀ := by dsimp [u₀]; linarith
  have hv₀ : v₀ < 1 := by dsimp [v₀]; linarith
  have huv₀ : h < v₀-u₀ := by dsimp [u₀,v₀]; linarith
  let u (t : ℝ) := (1-t)*a+t*u₀
  let v (t : ℝ) := (1-t)*(a+h)+t*v₀
  have huc : Continuous u := by dsimp [u]; fun_prop
  have hvc : Continuous v := by dsimp [v]; fun_prop
  have heu : ∀ᶠ t : ℝ in 𝓝 0, f (u t) < c :=
    (hf.comp huc).continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa [u] using hla))
  have hev : ∀ᶠ t : ℝ in 𝓝 0, f (v t) < c :=
    (hf.comp hvc).continuousAt.tendsto.eventually (isOpen_Iio.mem_nhds (by simpa [v] using hlb))
  have he : ∀ᶠ t : ℝ in 𝓝 0, t < 1 ∧ f (u t) < c ∧ f (v t) < c := by
    filter_upwards [(isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) ∈ Iio 1) : Iio (1:ℝ) ∈ 𝓝 (0:ℝ)),heu,hev] with t ht hu hv
    exact ⟨ht,hu,hv⟩
  obtain ⟨t,ht,htpos⟩ := ((he.filter_mono
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  refine ⟨u t,v t,?_,?_,?_,ht.2.1,ht.2.2⟩
  · dsimp [u]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [ht.1]) ha) (mul_pos htpos hu₀)
  · dsimp [v]
    nlinarith only [mul_nonneg (by linarith [ht.1] : 0 ≤ 1-t) (sub_nonneg.mpr hah),
      mul_pos htpos (sub_pos.mpr hv₀)]
  · dsimp [u,v]
    nlinarith only [mul_pos htpos (sub_pos.mpr huv₀)]

variable {P : Type*} [TopologicalSpace P] {m : ℕ}

def IntervalRoom (V : P → Fin m → Set ℝ) (L : Fin m → ℝ) (y : P) : Prop :=
  ∀ i, ∃ a b : ℝ, a ∈ V y i ∧ b ∈ V y i ∧ L i < b-a

theorem intervalRoom_open (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i}) :
    IsOpen {p : (Fin m → ℝ) × P | IntervalRoom V p.1 p.2} := by
  have hmem (i : Fin m) (a : ℝ) : IsOpen {p : (Fin m → ℝ) × P | a ∈ V p.2 i} :=
    (hV i).preimage (continuous_snd.prodMk continuous_const)
  change IsOpen {p : (Fin m → ℝ) × P | ∀ i, ∃ a b : ℝ,
    a ∈ V p.2 i ∧ b ∈ V p.2 i ∧ p.1 i < b-a}
  simp only [ofPred_forall,ofPred_exists,ofPred_and]
  exact isOpen_iInter_of_finite (fun i => isOpen_iUnion (fun a => isOpen_iUnion (fun b =>
    (hmem i a).inter ((hmem i b).inter (isOpen_lt ((continuous_apply i).comp continuous_fst) continuous_const)))))

theorem strictMono_open : IsOpen {L : Fin m → ℝ | StrictMono L} := by
  change IsOpen {L : Fin m → ℝ | ∀ i j, i < j → L i < L j}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i < j
  · simpa [hij] using isOpen_lt (f := fun u : Fin m → ℝ => u i) (g := fun u => u j)
      (continuous_apply i) (continuous_apply j)
  · simp [hij]

theorem exists_uniform_interval_widths {Y : Set P} (hY : IsCompact Y)
    (h : Fin m → ℝ) (hh : StrictMono h) (V : P → Fin m → Set ℝ)
    (hV : ∀ i, IsOpen {p : P × ℝ | p.2 ∈ V p.1 i})
    (hroom : ∀ y ∈ Y, IntervalRoom V h y) :
    ∃ L w : Fin m → ℝ, StrictMono L ∧ StrictMono w ∧
      (∀ i, 0 < w i ∧ w i < 1 ∧ L i*w i = h i) ∧
      ∀ y ∈ Y, IntervalRoom V L y := by
  have hsub : ({h} : Set (Fin m → ℝ)) ×ˢ Y ⊆ {p | IntervalRoom V p.1 p.2} := by
    rintro ⟨L,y⟩ ⟨hL,hy⟩
    have he : L = h := hL
    subst L
    exact hroom y hy
  obtain ⟨U,W,hU,_,hhU,hYW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hY (intervalRoom_open V hV) hsub
  let d (i : Fin m) : ℝ := (m:ℝ)-(i:ℕ)
  have hd (i : Fin m) : 0 < d i := by
    dsimp [d]
    exact sub_pos.mpr (by exact_mod_cast i.isLt)
  let w (t : ℝ) (i : Fin m) := 1-t*d i
  let L (t : ℝ) (i : Fin m) := h i/w t i
  have hwc (i : Fin m) : Continuous (fun t => w t i) := by dsimp [w]; fun_prop
  have hLc : ContinuousAt L 0 := by
    apply continuousAt_pi.mpr
    intro i
    exact continuousAt_const.div (hwc i).continuousAt (by simp [w])
  have hL0 : L 0 = h := by ext i; simp [L,w]
  have heU : ∀ᶠ t in 𝓝 (0:ℝ), L t ∈ U := by
    apply hLc.tendsto.eventually
    rw [hL0]
    exact hU.mem_nhds (hhU rfl)
  have hemono : ∀ᶠ t in 𝓝 (0:ℝ), StrictMono (L t) := by
    apply hLc.tendsto.eventually
    rw [hL0]
    exact strictMono_open.mem_nhds hh
  have hepos : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, 0 < w t i := by
    rw [eventually_all]
    intro i
    exact (hwc i).continuousAt.tendsto.eventually (isOpen_Ioi.mem_nhds (by simp [w]))
  obtain ⟨t,ht,htpos⟩ := (((heU.and (hemono.and hepos)).filter_mono
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).and self_mem_nhdsWithin).exists
  refine ⟨L t,w t,ht.2.1,?_,?_,?_⟩
  · intro i j hij
    have hij' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
    dsimp [w,d]
    nlinarith only [mul_pos htpos (sub_pos.mpr hij')]
  · intro i
    refine ⟨ht.2.2 i,?_,?_⟩
    · dsimp [w]
      linarith only [mul_pos htpos (hd i)]
    · exact div_mul_cancel₀ _ (ht.2.2 i).ne'
  · intro y hy
    exact hUW (show (L t,y) ∈ U ×ˢ W from ⟨ht.1,hYW hy⟩)

def clampUnit (h : ℝ) : ℝ := max 0 (min 1 h)

theorem continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clampUnit_eq {h : ℝ} (hh : h ∈ Icc (0:ℝ) 1) : clampUnit h = h := by
  simp [clampUnit,min_eq_right hh.2,max_eq_right hh.1]

def unitIntervalValue (F : C(P × ℝ,ℝ)) : C((P × ℝ) × UnitInterval,ℝ) where
  toFun p := max (F (p.1.1,p.2.val*(1-clampUnit p.1.2)))
    (F (p.1.1,p.2.val*(1-clampUnit p.1.2)+clampUnit p.1.2))
  continuous_toFun := by
    have hc : Continuous (fun p : (P × ℝ) × UnitInterval => clampUnit p.1.2) :=
      continuous_clampUnit.comp (continuous_snd.comp continuous_fst)
    have ht : Continuous (fun p : (P × ℝ) × UnitInterval => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hy : Continuous (fun p : (P × ℝ) × UnitInterval => p.1.1) :=
      continuous_fst.comp continuous_fst
    exact (F.continuous.comp (hy.prodMk (ht.mul (continuous_const.sub hc)))).max
      (F.continuous.comp (hy.prodMk ((ht.mul (continuous_const.sub hc)).add hc)))

def unitRearrange (F : C(P × ℝ,ℝ)) : C(P × ℝ,ℝ) where
  toFun p := minimum ((unitIntervalValue F).curry p)
  continuous_toFun := minimum_lipschitz.continuous.comp (unitIntervalValue F).curry.continuous

theorem unitRearrange_attained (F : C(P × ℝ,ℝ)) (y : P) {h : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a+h ≤ 1 ∧ unitRearrange F (y,h) = max (F (y,a)) (F (y,a+h)) := by
  obtain ⟨t,ht⟩ := minimum_attained ((unitIntervalValue F).curry (y,h))
  refine ⟨t.val*(1-h),mul_nonneg t.property.1 (sub_nonneg.mpr hh.2),?_,?_⟩
  · nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hh.2)]
  · change minimum ((unitIntervalValue F).curry (y,h)) = _
    rw [←ht]
    simp [unitIntervalValue,clampUnit_eq hh]

theorem unitRearrange_le_candidate (F : C(P × ℝ,ℝ)) (y : P) {h a : ℝ}
    (hh : h ∈ Icc (0:ℝ) 1) (ha : 0 ≤ a) (hah : a+h ≤ 1) :
    unitRearrange F (y,h) ≤ max (F (y,a)) (F (y,a+h)) := by
  obtain ⟨t,ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr hh.2) ha (by linarith)
  calc
    _ ≤ (unitIntervalValue F).curry (y,h) t := minimum_le _ t
    _ = _ := by simp [unitIntervalValue,clampUnit_eq hh,ht]

theorem unitRearrange_one (F : C(P × ℝ,ℝ)) (y : P) :
    unitRearrange F (y,1) = max (F (y,0)) (F (y,1)) := by
  obtain ⟨a,ha,hah,he⟩ := unitRearrange_attained F y (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  have ha0 : a = 0 := by linarith
  simpa [ha0] using he

theorem unitRearrange_mono (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) :
    MonotoneOn (fun h => unitRearrange F (y,h)) (Icc 0 1) := by
  intro h hh H hH hle
  obtain ⟨a,ha,haH,he⟩ := unitRearrange_attained F y hH
  have hah : a+h ≤ 1 := by linarith
  apply (unitRearrange_le_candidate F y hh ha hah).trans
  change max (F (y,a)) (F (y,a+h)) ≤ unitRearrange F (y,H)
  rw [he]
  apply max_le
  · exact le_max_left _ _
  · exact hconv.le_max_of_mem_Icc ⟨ha,by linarith [hH.1]⟩
      ⟨by linarith [hH.1],haH⟩ ⟨by linarith [hh.1],by linarith⟩

def unitSublevel (F : C(P × ℝ,ℝ)) (h ε : ℝ) (y : P) : Set ℝ :=
  {v | v ∈ Ioo 0 1 ∧ F (y,v) < unitRearrange F (y,h)+ε}

theorem unitSublevel_open (F : C(P × ℝ,ℝ)) (h ε : ℝ) :
    IsOpen {p : P × ℝ | p.2 ∈ unitSublevel F h ε p.1} :=
  (isOpen_Ioo.preimage continuous_snd).inter
    (isOpen_lt F.continuous (((unitRearrange F).continuous.comp
      (continuous_fst.prodMk continuous_const)).add continuous_const))

theorem unitSublevel_room (F : C(P × ℝ,ℝ)) (y : P) {h ε : ℝ}
    (hh : 0 ≤ h) (hh1 : h < 1) (he : 0 < ε) :
    ∃ u v : ℝ, u ∈ unitSublevel F h ε y ∧ v ∈ unitSublevel F h ε y ∧ h < v-u := by
  obtain ⟨a,ha,hah,hg⟩ := unitRearrange_attained F y ⟨hh,hh1.le⟩
  obtain ⟨u,v,hu,hv,huv,hfu,hfv⟩ := exists_longer_strict_interval
    (F.continuous.comp (continuous_const.prodMk continuous_id)) ha hah hh hh1
    (show F (y,a) < unitRearrange F (y,h)+ε by rw [hg]; linarith only [le_max_left (F (y,a)) (F (y,a+h)),he])
    (show F (y,a+h) < unitRearrange F (y,h)+ε by rw [hg]; linarith only [le_max_right (F (y,a)) (F (y,a+h)),he])
  exact ⟨u,v,⟨⟨hu,by linarith⟩,hfu⟩,⟨⟨by linarith,hv⟩,hfv⟩,huv⟩

theorem unitSublevel_convex (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) (h ε : ℝ) :
    Convex ℝ (unitSublevel F h ε y) := by
  have he : unitSublevel F h ε y = Ioo 0 1 ∩
      {v ∈ Icc 0 1 | F (y,v) < unitRearrange F (y,h)+ε} := by
    ext v
    exact ⟨fun hv => ⟨hv.1,⟨hv.1.1.le,hv.1.2.le⟩,hv.2⟩,
      fun hv => ⟨hv.1,hv.2.2⟩⟩
  rw [he]
  exact (convex_Ioo (𝕜 := ℝ) 0 1).inter (hconv.convex_lt _)

theorem unitSublevel_mono (F : C(P × ℝ,ℝ)) (y : P)
    (hconv : ConvexOn ℝ (Icc 0 1) (fun v => F (y,v))) (ε : ℝ) :
    MonotoneOn (fun h => unitSublevel F h ε y) (Icc 0 1) := by
  intro h hh H hH hle v hv
  refine ⟨hv.1,?_⟩
  have hg := unitRearrange_mono F y hconv hh hH hle
  change unitRearrange F (y,h) ≤ unitRearrange F (y,H) at hg
  linarith only [hv.2,hg]

end

def fixedIntervalValue (f : C(ℝ,ℝ)) (L h : ℝ) : C(UnitInterval,ℝ) where
  toFun t := max (f (t.val*(L-h))) (f (t.val*(L-h)+h))
  continuous_toFun := (f.continuous.comp (continuous_subtype_val.mul continuous_const)).max
    (f.continuous.comp ((continuous_subtype_val.mul continuous_const).add continuous_const))

def intervalMinimum (f : C(ℝ,ℝ)) (L h : ℝ) : ℝ := minimum (fixedIntervalValue f L h)

theorem intervalMinimum_attained (f : C(ℝ,ℝ)) {L h : ℝ} (hh : h ∈ Icc 0 L) :
    ∃ a : ℝ, 0 ≤ a ∧ a+h ≤ L ∧ intervalMinimum f L h = max (f a) (f (a+h)) := by
  obtain ⟨t,ht⟩ := minimum_attained (fixedIntervalValue f L h)
  refine ⟨t.val*(L-h),mul_nonneg t.property.1 (sub_nonneg.mpr hh.2),?_,ht.symm⟩
  nlinarith only [mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hh.2)]

theorem intervalMinimum_le_candidate (f : C(ℝ,ℝ)) {L h a : ℝ}
    (hh : h ∈ Icc 0 L) (ha : 0 ≤ a) (hah : a+h ≤ L) :
    intervalMinimum f L h ≤ max (f a) (f (a+h)) := by
  obtain ⟨t,ht⟩ := exists_unitInterval_mul (sub_nonneg.mpr hh.2) ha (by linarith)
  simpa only [intervalMinimum,fixedIntervalValue,ContinuousMap.coe_mk,ht] using minimum_le (fixedIntervalValue f L h) t

theorem intervalMinimum_shortening (f : C(ℝ,ℝ)) {L l h ε : ℝ}
    (_hl : 0 ≤ l) (hlL : l ≤ L) (hh : h ∈ Icc 0 l)
    (hm : ∀ s ∈ Icc (0:ℝ) L, ∀ t ∈ Icc (0:ℝ) L,
      |s-t| ≤ L-l → f s ≤ f t+ε) :
    intervalMinimum f l h ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f ⟨hh.1,hh.2.trans hlL⟩
  let b := min a (l-h)
  have hb : 0 ≤ b := le_min ha (sub_nonneg.mpr hh.2)
  have hbh : b+h ≤ l := by dsimp [b]; linarith [min_le_right a (l-h)]
  have hba : b ≤ a := min_le_left _ _
  have hab : a-b ≤ L-l := by
    dsimp [b]
    rcases le_total a (l-h) with hx | hx
    · rw [min_eq_left hx]; linarith
    · rw [min_eq_right hx]; linarith
  have h1 := hm b ⟨hb,by linarith [hh.1]⟩ a ⟨ha,by linarith [hh.1]⟩
    (by rw [abs_of_nonpos (sub_nonpos.mpr hba)]; linarith)
  have h2 := hm (b+h) ⟨by linarith [hh.1],hbh.trans hlL⟩ (a+h) ⟨by linarith [hh.1],hah⟩
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  apply (intervalMinimum_le_candidate f hh hb hbh).trans
  rw [he]
  exact max_le ((h1.trans (add_le_add (le_max_left _ _) le_rfl)))
    (h2.trans (add_le_add (le_max_right _ _) le_rfl))

theorem intervalMinimum_outer_strip (f : C(ℝ,ℝ)) {L l h ε : ℝ}
    (hh : h ∈ Icc 0 L) (hlh : l ≤ h)
    (hm : ∀ s ∈ Icc (0:ℝ) L, ∀ t ∈ Icc (0:ℝ) L,
      |s-t| ≤ L-l → f s ≤ f t+ε) :
    f h ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f hh
  have h1 := hm h hh (a+h) ⟨by linarith [hh.1],hah⟩
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  rw [he]
  exact h1.trans (add_le_add (le_max_right _ _) le_rfl)

theorem intervalMinimum_small (f : C(ℝ,ℝ)) {L h s ε : ℝ}
    (hh : h ∈ Icc 0 L) (hs : s ∈ Icc 0 L)
    (hm : ∀ u ∈ Icc (0:ℝ) L, ∀ v ∈ Icc (0:ℝ) L, f u ≤ f v+ε) :
    f s ≤ intervalMinimum f L h+ε := by
  obtain ⟨a,ha,hah,he⟩ := intervalMinimum_attained f hh
  rw [he]
  exact (hm s hs a ⟨ha,by linarith [hh.1]⟩).trans
    (add_le_add (le_max_left _ _) le_rfl)

variable {P : Type*} [TopologicalSpace P]

def scaledUnitFamily (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) : C(P × ℝ,ℝ) :=
  F.comp ⟨fun p => (p.1,l p.1*p.2), continuous_fst.prodMk
    ((l.continuous.comp continuous_fst).mul continuous_snd)⟩

def fiberFunction (F : C(P × ℝ,ℝ)) (y : P) : C(ℝ,ℝ) :=
  F.comp ⟨fun t => (y,t),continuous_const.prodMk continuous_id⟩

theorem unitRearrange_scaled (F : C(P × ℝ,ℝ)) (l : C(P,ℝ)) (y : P)
    (hl : 0 < l y) {h : ℝ} (hh : h ∈ Icc 0 (l y)) :
    unitRearrange (scaledUnitFamily F l) (y,h/l y) = intervalMinimum (fiberFunction F y) (l y) h := by
  have hq : h/l y ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg hh.1 hl.le,(div_le_one hl).mpr hh.2⟩
  change minimum ((unitIntervalValue (scaledUnitFamily F l)).curry (y,h/l y)) =
    minimum (fixedIntervalValue (fiberFunction F y) (l y) h)
  apply congrArg minimum
  apply ContinuousMap.ext
  intro t
  simp only [unitIntervalValue,ContinuousMap.coe_mk,ContinuousMap.curry_apply,
    clampUnit_eq hq,scaledUnitFamily,ContinuousMap.comp_apply,fiberFunction,fixedIntervalValue]
  congr 2 <;> field_simp

end PackingSufficiencySupport.Comparison
end

end OAI
