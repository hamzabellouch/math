import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialAreaDensity

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_complement_both_extents {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hout : quotientMap (axialSectionCorner b i t (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∈openRepresentative E)
    (hn : volume (axialSlice (frontier (openRepresentative E)) i (t : AxisCircle))=0)
    (j : Fin 2) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (t : AxisCircle),‖y j‖<L) ∧
      (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →
        y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (t : AxisCircle)) ∧
      ENNReal.ofReal ((1-volume.real (axialSlice (openRepresentative E) i (t : AxisCircle)))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmin
  have hRc (i : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' Eᶜ) := (hR i).compl
  have hdc := isMinimizerAt_complement_octant_downset hV hmin hR hd
  have hswap0 : (fun j : Fin 2 ↦ !(j==0))=(fun j ↦ j==1) := by funext j; fin_cases j <;> decide
  have hswap1 : (fun j : Fin 2 ↦ !(j==1))=(fun j ↦ j==0) := by funext j; fin_cases j <;> decide
  have hin : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun _ ↦ false))∈openRepresentative Eᶜ := by
    rw [openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse]
    exact hout
  have hv0 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==0))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap0]
    simpa using hin1
  have hv1 : quotientMap (axialSectionCorner (fun k ↦ !b k) i t (fun j ↦ j==1))∉closure (openRepresentative Eᶜ) := by
    rw [closure_openRepresentative_compl_eq hV hmin,axialSectionCorner_reverse,hswap1]
    simpa using hin0
  obtain ⟨L,hL,hband,hfill,hp⟩ := isMinimizerAt_section_both_extents hVc hmc hRc hdc i t hin hv0 hv1 j
  rw [axialSlice_complement_volume hV hmin i _ hn,axialSlice_complement_perimeter hV hmin i _ hn] at hp
  exact ⟨L,hL,hband,hfill,hp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_bottom_both_extents {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    0<H*s ∧ Real.pi*(1-s)≤((H/2)*s)^2 ∧
      ∀ j : Fin 2,∃ L : ℝ,L∈Ioo 0 1 ∧
        (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle),2*‖y j‖<L) ∧
        (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →2*‖y j‖<L →
          y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle)) ∧
        (1-s)/L+Real.pi*L/4≤(H/2)*s := by
  dsimp only
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  obtain ⟨hHs,hdisc,_⟩ := isMinimizerAt_bottom_extent_calibration hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  refine ⟨hHs,hdisc,fun j ↦ ?_⟩
  have hn := isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha (octantHeight b i 0 : AxisCircle)
  obtain ⟨L,hL,hband,hfill,hcal⟩ := isMinimizerAt_section_complement_both_extents hV hmin hR hd i (octantHeight b i 0) hout hin0 hin1 hn j
  have hp := isMinimizerAt_missing_neighbor_seam_bound hV hE hmin hR b hd hμ hCMC i ha hv
  have hcal' : (1-s)/L+Real.pi*L≤H*s :=
    (ENNReal.ofReal_le_ofReal_iff hHs.le).mp (hcal.trans hp)
  refine ⟨2*L,⟨mul_pos (by norm_num) hL.1,by linarith [hL.2]⟩,?_,?_,?_⟩
  · intro y hy
    linarith [hband y hy]
  · intro y hy hyL
    exact hfill y hy (by linarith)
  · have he : (1-s)/(2*L)+Real.pi*(2*L)/4=((1-s)/L+Real.pi*L)/2 := by field_simp; ring
    rw [he]
    nlinarith [hcal']

end CubicTorus

end
end

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

def lambda : ℝ := 49 / 50
def ell : ℝ := 7 / 25
def cutoff : ℝ := Real.sqrt 48 / 7
def rawWeight (X : ℝ) : ℝ := (1 - lambda * X ^ 2) / Real.sqrt (1 - X ^ 2)
def weight (X : ℝ) : ℝ := rawWeight (min X cutoff)

def fluxAux (J X : ℝ) : ℝ :=
  1 / X - lambda * X - J * (Real.sqrt (1 - X ^ 2) / X)

def fluxAuxDeriv (J X : ℝ) : ℝ :=
  -1 / X ^ 2 - lambda + J / (X ^ 2 * Real.sqrt (1 - X ^ 2))

def fluxAuxSecond (J X : ℝ) : ℝ :=
  2 / X ^ 3 + J * (3 * X ^ 2 - 2) /
    (X ^ 3 * (Real.sqrt (1 - X ^ 2)) ^ 3)

lemma sqrt_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    0 < Real.sqrt (1 - x ^ 2) := by
  apply Real.sqrt_pos.2
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma sqrt_square_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [hx.1, hx.2, sq_nonneg x]

lemma hasDerivAt_sqrt_one_sub_sq {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
      (-x / Real.sqrt (1 - x ^ 2)) x := by
  have hp : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  convert ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2)).sqrt
    (ne_of_gt hp) using 1
  · rfl
  · dsimp
    ring

lemma hasDerivAt_fluxAux {J x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fluxAux J) (fluxAuxDeriv J x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hh := (((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx0).sub
    ((hasDerivAt_id x).const_mul lambda)).sub
    ((hs.div (hasDerivAt_id x) hx0).const_mul J)
  convert hh using 1 <;> try rfl
  dsimp [fluxAuxDeriv]
  field_simp [hx0, hs0]
  linear_combination -J * hs2

lemma hasDerivAt_fluxAuxDeriv {J x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fluxAuxDeriv J) (fluxAuxSecond J x) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hsq := (hasDerivAt_id x).pow 2
  have hh := (((hasDerivAt_const x (-1 : ℝ)).div hsq (pow_ne_zero 2 hx0)).sub
    (hasDerivAt_const x lambda)).add
    ((hasDerivAt_const x J).div (hsq.mul hs) (mul_ne_zero (pow_ne_zero 2 hx0) hs0))
  convert hh using 1 <;> try rfl
  dsimp [fluxAuxSecond]
  field_simp [hx0, hs0]
  linear_combination 2 * J * hs2

lemma fluxAuxSecond_nonneg {J x : ℝ} (hJ : J ∈ Icc 0 1) (hx : x ∈ Ioo 0 1) :
    0 ≤ fluxAuxSecond J x := by
  have hs : 0 < Real.sqrt (1 - x ^ 2) := sqrt_pos_of_mem_Ioo hx
  have hs2 := sqrt_square_of_mem_Ioo hx
  unfold fluxAuxSecond
  have hx0 := ne_of_gt hx.1
  have hs0 := ne_of_gt hs
  rw [show 2 / x ^ 3 + J * (3 * x ^ 2 - 2) /
      (x ^ 3 * Real.sqrt (1 - x ^ 2) ^ 3) =
      (2 * Real.sqrt (1 - x ^ 2) ^ 3 + J * (3 * x ^ 2 - 2)) /
      (x ^ 3 * Real.sqrt (1 - x ^ 2) ^ 3) by field_simp]
  apply div_nonneg _ (le_of_lt (mul_pos (pow_pos hx.1 _) (pow_pos hs _)))
  have hid : 2 * Real.sqrt (1 - x ^ 2) ^ 3 + J * (3 * x ^ 2 - 2) =
      (1 - J) * (2 * Real.sqrt (1 - x ^ 2) ^ 3) +
      J * ((Real.sqrt (1 - x ^ 2) - 1) ^ 2 * (2 * Real.sqrt (1 - x ^ 2) + 1)) := by
    linear_combination 3 * J * hs2
  rw [hid]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hJ.2) (by positivity))
    (mul_nonneg hJ.1 (mul_nonneg (sq_nonneg _) (by positivity)))

lemma continuousOn_fluxAux {ε : ℝ} (hε : 0 < ε) (J : ℝ) :
    ContinuousOn (fluxAux J) (Icc ε 1) := by
  have hn : ∀ x ∈ Icc ε (1 : ℝ), x ≠ 0 := fun _ hx => ne_of_gt (lt_of_lt_of_le hε hx.1)
  have hc : Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))
  exact ((continuousOn_const.div continuousOn_id hn).sub
    (continuousOn_const.mul continuousOn_id)).sub
    (continuousOn_const.mul (hc.continuousOn.div continuousOn_id hn))

lemma convexOn_fluxAux {ε J : ℝ} (hε : 0 < ε) (hJ : J ∈ Icc 0 1) :
    ConvexOn ℝ (Icc ε 1) (fluxAux J) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := fluxAuxDeriv J)
    (f'' := fluxAuxSecond J) (convex_Icc ε 1) (continuousOn_fluxAux hε J) ?_ ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_fluxAux ⟨lt_trans hε hx.1, hx.2⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_fluxAuxDeriv ⟨lt_trans hε hx.1, hx.2⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact fluxAuxSecond_nonneg hJ ⟨lt_trans hε hx.1, hx.2⟩

lemma cutoff_pos : 0 < cutoff := by
  unfold cutoff
  positivity

lemma cutoff_sq : cutoff ^ 2 = 48 / 49 := by
  norm_num [cutoff, div_pow]

lemma cutoff_lt_one : cutoff < 1 := by
  nlinarith [cutoff_sq, cutoff_pos]

lemma sqrt_cutoff : Real.sqrt (1 - cutoff ^ 2) = 1 / 7 := by
  rw [cutoff_sq]
  norm_num

lemma rawWeight_cutoff : rawWeight cutoff = ell := by
  rw [rawWeight, sqrt_cutoff, cutoff_sq]
  norm_num [lambda, ell]

lemma rawWeight_lower {x : ℝ} (hx : x ∈ Ico 0 1) : ell ≤ rawWeight x := by
  have hrad : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hs2 := Real.sq_sqrt (le_of_lt hrad)
  unfold rawWeight ell lambda
  apply (le_div_iff₀ hs).2
  nlinarith [sq_nonneg (7 * Real.sqrt (1 - x ^ 2) - 1)]

lemma hasDerivAt_rawWeight {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt rawWeight
      (x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3)) x := by
  have hs := hasDerivAt_sqrt_one_sub_sq hx
  have hs0 := ne_of_gt (sqrt_pos_of_mem_Ioo hx)
  have hs2 := sqrt_square_of_mem_Ioo hx
  have hh := ((hasDerivAt_const x (1 : ℝ)).sub
    (((hasDerivAt_id x).pow 2).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 98 * x * hs2

lemma continuousOn_rawWeight : ContinuousOn rawWeight (Icc 0 cutoff) := by
  have hs : ∀ x ∈ Icc 0 cutoff, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    apply ne_of_gt (Real.sqrt_pos.2 _)
    have hxl : x < 1 := lt_of_le_of_lt hx.2 cutoff_lt_one
    nlinarith [hx.1, sq_nonneg x]
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn) hs

lemma antitoneOn_rawWeight : AntitoneOn rawWeight (Icc 0 cutoff) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun x =>
    x * (49 * x ^ 2 - 48) / (50 * Real.sqrt (1 - x ^ 2) ^ 3))
    (convex_Icc 0 cutoff) continuousOn_rawWeight ?_ ?_
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_rawWeight ⟨hx.1, lt_trans hx.2 cutoff_lt_one⟩).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hx.1)
    have hsq : x ^ 2 ≤ cutoff ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hx.1) (le_of_lt hx.2) 2
    nlinarith [cutoff_sq]

lemma weight_mem {x : ℝ} (hx : 0 ≤ x) : weight x ∈ Icc ell 1 := by
  have hm : min x cutoff ∈ Icc 0 cutoff :=
    ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩
  constructor
  · exact rawWeight_lower ⟨hm.1, lt_of_le_of_lt hm.2 cutoff_lt_one⟩
  · have hh := antitoneOn_rawWeight ⟨le_rfl, le_of_lt cutoff_pos⟩ hm hm.1
    simpa [weight, rawWeight] using hh

lemma antitoneOn_weight : AntitoneOn weight (Ici 0) := by
  intro x hx y hy hxy
  exact antitoneOn_rawWeight
    ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩
    ⟨le_min hy (le_of_lt cutoff_pos), min_le_right _ _⟩ (min_le_min hxy le_rfl)

lemma weight_le_rawWeight {x : ℝ} (hx : x ∈ Ico 0 1) : weight x ≤ rawWeight x := by
  by_cases hxc : x ≤ cutoff
  · simp [weight, min_eq_left hxc]
  · rw [weight, min_eq_right (le_of_not_ge hxc), rawWeight_cutoff]
    exact rawWeight_lower hx

lemma fluxAux_weight_nonneg {m : ℝ} (hm : m ∈ Ioc 0 1) :
    0 ≤ fluxAux (weight m) m := by
  rcases lt_or_eq_of_le hm.2 with hm1 | rfl
  · have hs : 0 < Real.sqrt (1 - m ^ 2) := sqrt_pos_of_mem_Ioo ⟨hm.1, hm1⟩
    have hw := weight_le_rawWeight ⟨le_of_lt hm.1, hm1⟩
    have hh : weight m * Real.sqrt (1 - m ^ 2) ≤ 1 - lambda * m ^ 2 :=
      (le_div_iff₀ hs).mp hw
    rw [fluxAux, show 1 / m - lambda * m - weight m * (Real.sqrt (1 - m ^ 2) / m) =
      (1 - lambda * m ^ 2 - weight m * Real.sqrt (1 - m ^ 2)) / m by
        field_simp]
    exact div_nonneg (sub_nonneg.mpr hh) (le_of_lt hm.1)
  · norm_num [fluxAux, lambda]

theorem integrated_flux_probability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {α : Ω → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hα : ∀ᵐ x ∂μ, α x ∈ Icc ε 1)
    (hαi : Integrable α μ) (hii : Integrable (fun x => 1 / α x) μ)
    (hqi : Integrable (fun x => Real.sqrt (1 - α x ^ 2) / α x) μ) :
    weight (∫ x, α x ∂μ) * (∫ x, Real.sqrt (1 - α x ^ 2) / α x ∂μ) ≤
      (∫ x, 1 / α x ∂μ) - lambda * (∫ x, α x ∂μ) := by
  let m : ℝ := ∫ x, α x ∂μ
  have hm : m ∈ Icc ε 1 := by
    constructor
    · have hh := integral_mono_ae (integrable_const ε) hαi (hα.mono fun _ hx => hx.1)
      simpa [m] using hh
    · have hh := integral_mono_ae hαi (integrable_const (1 : ℝ)) (hα.mono fun _ hx => hx.2)
      simpa [m] using hh
  have hm0 : 0 < m := lt_of_lt_of_le hε hm.1
  have hw := weight_mem (le_of_lt hm0)
  have hJ : weight m ∈ Icc 0 1 := ⟨le_trans (by norm_num [ell]) hw.1, hw.2⟩
  have hfi : Integrable ((fluxAux (weight m)) ∘ α) μ :=
    (hii.sub (hαi.const_mul lambda)).sub (hqi.const_mul (weight m))
  have hj := (convexOn_fluxAux hε hJ).map_integral_le
    (continuousOn_fluxAux hε (weight m)) isClosed_Icc hα hαi hfi
  have hh : 0 ≤ ∫ x, fluxAux (weight m) (α x) ∂μ :=
    (fluxAux_weight_nonneg ⟨hm0, hm.2⟩).trans hj
  change 0 ≤ ∫ x, ((1 / α x - lambda * α x) -
    weight m * (Real.sqrt (1 - α x ^ 2) / α x)) ∂μ at hh
  have hli : Integrable (fun x => 1 / α x - lambda * α x) μ :=
    hii.sub (hαi.const_mul lambda)
  rw [integral_sub hli (hqi.const_mul (weight m)),
    integral_sub hii (hαi.const_mul lambda), integral_const_mul, integral_const_mul] at hh
  exact sub_nonneg.mp hh

lemma product_sqrt_le_half {x : ℝ} (hx : x ∈ Icc 0 1) :
    x * Real.sqrt (1 - x ^ 2) ≤ 1 / 2 := by
  have hr : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  nlinarith [Real.sq_sqrt hr, sq_nonneg (x - Real.sqrt (1 - x ^ 2))]

lemma product_sqrt_le_of_lower {a x d : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hx1 : x ≤ 1) (ha2 : 1 / 2 ≤ a ^ 2) (hd : 0 ≤ d)
    (had : a ^ 2 * (1 - a ^ 2) ≤ d ^ 2) :
    x * Real.sqrt (1 - x ^ 2) ≤ d := by
  have hx0 := le_trans ha hax
  have hxa := pow_le_pow_left₀ ha hax 2
  have hr : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hr
  have hxs := congrArg (fun t : ℝ => x ^ 2 * t) hs
  have hp : (x ^ 2 - a ^ 2) * (1 - a ^ 2 - x ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  apply (sq_le_sq₀ (mul_nonneg hx0 (Real.sqrt_nonneg _)) hd).1
  nlinarith

lemma weight_derivative_bound_of_row {x n d : ℝ} (hx : x ∈ Ico 0 1)
    (hn : n * (1 - x ^ 2) ≤ 48 / 100 - (49 / 100 : ℝ) * x ^ 2)
    (hd : x * Real.sqrt (1 - x ^ 2) ≤ d) (hnd : (91 / 100 : ℝ) * d ≤ n) :
    (91 / 100 : ℝ) * x ≤
      (48 / 100 - (49 / 100 : ℝ) * x ^ 2) / Real.sqrt (1 - x ^ 2) ^ 3 := by
  have hr : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hr
  apply (le_div_iff₀ (pow_pos hs 3)).2
  calc
    (91 / 100 : ℝ) * x * Real.sqrt (1 - x ^ 2) ^ 3 =
        ((91 / 100 : ℝ) * (x * Real.sqrt (1 - x ^ 2))) * Real.sqrt (1 - x ^ 2) ^ 2 := by ring
    _ ≤ ((91 / 100 : ℝ) * d) * Real.sqrt (1 - x ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _)
    _ ≤ n * Real.sqrt (1 - x ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hnd (sq_nonneg _)
    _ = n * (1 - x ^ 2) := by rw [Real.sq_sqrt (le_of_lt hr)]
    _ ≤ 48 / 100 - (49 / 100 : ℝ) * x ^ 2 := hn

theorem weight_derivative_bound {x : ℝ} (hx : x ∈ Icc 0 (24 / 25 : ℝ)) :
    (91 / 100 : ℝ) * x ≤
      (48 / 100 - (49 / 100 : ℝ) * x ^ 2) / Real.sqrt (1 - x ^ 2) ^ 3 := by
  have hx1 : x ∈ Ico 0 1 := ⟨hx.1, by linarith [hx.2]⟩
  by_cases h84 : x ≤ 84 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h84 2
    apply weight_derivative_bound_of_row (n := 456 / 1000) (d := 1 / 2) hx1
    · nlinarith
    · exact product_sqrt_le_half ⟨hx.1, le_of_lt hx1.2⟩
    · norm_num
  by_cases h89 : x ≤ 89 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h89 2
    apply weight_derivative_bound_of_row (n := 44 / 100) (d := 46 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 84 / 100) (by norm_num) (le_of_not_ge h84)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num
  by_cases h94 : x ≤ 94 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h94 2
    apply weight_derivative_bound_of_row (n := 40 / 100) (d := 41 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 89 / 100) (by norm_num) (le_of_not_ge h89)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num
  · have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    apply weight_derivative_bound_of_row (n := 36 / 100) (d := 33 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 94 / 100) (by norm_num) (le_of_not_ge h94)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num

def squaredWeight (r : ℝ) : ℝ := (1 - lambda * r) / Real.sqrt (1 - r)

lemma hasDerivAt_squaredWeight {r : ℝ} (hr : r < 1) :
    HasDerivAt squaredWeight
      (-((48 / 100 - (49 / 100 : ℝ) * r) / Real.sqrt (1 - r) ^ 3)) r := by
  have hrad : 0 < 1 - r := sub_pos.2 hr
  have hs := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).sqrt (ne_of_gt hrad)
  have hs2 := Real.sq_sqrt (le_of_lt hrad)
  have hs0 := ne_of_gt (Real.sqrt_pos.2 hrad)
  have hh := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_id r).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 9800 * hs2

lemma squaredWeight_eq_rawWeight {r : ℝ} (hr : 0 ≤ r) :
    squaredWeight r = rawWeight (Real.sqrt r) := by
  simp only [squaredWeight, rawWeight, Real.sq_sqrt hr]

lemma squaredWeight_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ (24 / 25 : ℝ) ^ 2) :
    (91 / 100 : ℝ) * Real.sqrt a * (b - a) ≤ squaredWeight a - squaredWeight b := by
  have hi : ∀ r ∈ Icc a b, 0 ≤ r ∧ r < 1 := fun r hr => ⟨le_trans ha hr.1, by linarith [hr.2]⟩
  have hc : ContinuousOn squaredWeight (Icc a b) := by
    intro r hr
    exact (hasDerivAt_squaredWeight (hi r hr).2).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun r => squaredWeight r + (91 / 100 : ℝ) * Real.sqrt a * r) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun r =>
      -((48 / 100 - (49 / 100 : ℝ) * r) / Real.sqrt (1 - r) ^ 3) +
        (91 / 100 : ℝ) * Real.sqrt a) (convex_Icc a b)
    · exact hc.add (continuousOn_const.mul continuousOn_id)
    · intro r hr
      rw [interior_Icc] at hr
      convert ((hasDerivAt_squaredWeight (hi r ⟨le_of_lt hr.1, le_of_lt hr.2⟩).2).add
        ((hasDerivAt_id r).const_mul ((91 / 100 : ℝ) * Real.sqrt a))).hasDerivWithinAt using 1 <;> try rfl
      simp only [mul_one]
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 := le_trans ha (le_of_lt hr.1)
      have hs : Real.sqrt r ∈ Icc 0 (24 / 25 : ℝ) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.2 ⟨by norm_num, le_trans (le_of_lt hr.2) hb⟩⟩
      have hbound := weight_derivative_bound hs
      rw [Real.sq_sqrt hr0] at hbound
      have hmon := Real.sqrt_le_sqrt (le_of_lt hr.1)
      linarith
  have hh := hm ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  linarith

theorem pointwise_weight_gain {x K : ℝ} (hx : x ∈ Icc 0 (24 / 25 : ℝ)) (hK : 0 ≤ K) :
    (91 / 100 : ℝ) * x ^ 3 * K / Real.sqrt (1 + K) ^ 3 ≤
      weight (x / Real.sqrt (1 + K)) - weight x := by
  have hp : 0 < 1 + K := by linarith
  have hs0 : 0 < Real.sqrt (1 + K) := Real.sqrt_pos.2 hp
  have hs1 : 1 ≤ Real.sqrt (1 + K) := by
    nlinarith [Real.sq_sqrt (le_of_lt hp), Real.sqrt_nonneg (1 + K)]
  have hy0 : 0 ≤ x / Real.sqrt (1 + K) := div_nonneg hx.1 (le_of_lt hs0)
  have hyx : x / Real.sqrt (1 + K) ≤ x := (div_le_iff₀ hs0).2 (by nlinarith [hx.1])
  have hd : (24 / 25 : ℝ) < cutoff := by nlinarith [cutoff_sq, cutoff_pos]
  have hc1 : x ≤ cutoff := le_trans hx.2 (le_of_lt hd)
  have hc2 : x / Real.sqrt (1 + K) ≤ cutoff := le_trans hyx hc1
  rw [weight, min_eq_left hc2, weight, min_eq_left hc1]
  have ha : 0 ≤ x ^ 2 / (1 + K) := div_nonneg (sq_nonneg x) (le_of_lt hp)
  have hab : x ^ 2 / (1 + K) ≤ x ^ 2 := (div_le_iff₀ hp).2 (by nlinarith [sq_nonneg x])
  have hb := pow_le_pow_left₀ hx.1 hx.2 2
  have hg := squaredWeight_difference ha hab hb
  have heqa : Real.sqrt (x ^ 2 / (1 + K)) = x / Real.sqrt (1 + K) := by
    rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx.1]
  rw [squaredWeight_eq_rawWeight ha, squaredWeight_eq_rawWeight (sq_nonneg x),
    heqa, Real.sqrt_sq hx.1] at hg
  convert hg using 1
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  field_simp
  linear_combination -x ^ 3 * K * hs2

end CubicTorus.Nesting

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

def t (h : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 + 4 * h ^ 2 / Real.pi))
def c : ℝ := 27 / 10
def dm : ℝ := 21 / 100
def u (h : ℝ) : ℝ := min (1 - 1 / Real.pi) ((24 / 25 : ℝ) / h)
def theta : ℝ := 2 / (1 + Real.sqrt (1 + 4 * c * dm / Real.pi))
def shape (q : ℝ) : ℝ := min (q ^ 2) (Real.pi * (1 - q) / (c * dm))
def moment : ℝ := ∫ q in (0 : ℝ)..1, shape q
def firstMoment : ℝ := ∫ q in (0 : ℝ)..1, q * shape q
def meanQ : ℝ := firstMoment / moment
def p₂ : ℝ := 1 + c * dm ^ 2 * theta ^ 2

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

lemma extent_lower_bound {h s L : ℝ} (hL : 0 < L)
    (hcal : (1 - s) / L + Real.pi * L / 4 ≤ h * s) :
    2 / Real.pi * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) ≤ L := by
  have hp := Real.pi_pos
  have hh := (mul_le_mul_of_nonneg_right hcal (le_of_lt hL))
  have hsq : (h * s - Real.pi * L / 2) ^ 2 ≤ h ^ 2 * s ^ 2 - Real.pi * (1 - s) := by
    have heq : ((1 - s) / L + Real.pi * L / 4) * L = 1 - s + Real.pi * L ^ 2 / 4 := by
      field_simp
    rw [heq] at hh
    have hm := mul_le_mul_of_nonneg_left hh (le_of_lt hp)
    nlinarith
  have hs := Real.le_sqrt_of_sq_le hsq
  convert (show 2 * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) / Real.pi ≤ L from
    (div_le_iff₀ hp).2 (by nlinarith)) using 1
  ring

lemma endpoint_slack_bound {h s t₀ : ℝ} (hh : 0 ≤ h) (ht : 0 ≤ t₀) (hst : t₀ ≤ s)
    (hroot : h ^ 2 * t₀ ^ 2 = Real.pi * (1 - t₀)) :
    1 - 2 / Real.pi * (h * s - Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s))) ≤
      1 - 2 * h * t₀ / Real.pi +
        (2 / Real.pi * Real.sqrt (Real.pi + 2 * h ^ 2 * t₀)) * Real.sqrt (s - t₀) := by
  let Y := Real.sqrt (s - t₀)
  let R := Real.sqrt (Real.pi + 2 * h ^ 2 * t₀)
  have hY : 0 ≤ Y := Real.sqrt_nonneg _
  have hY2 : Y ^ 2 = s - t₀ := Real.sq_sqrt (sub_nonneg.2 hst)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = Real.pi + 2 * h ^ 2 * t₀ := Real.sq_sqrt (by positivity)
  have hupper : Real.sqrt (h ^ 2 * s ^ 2 - Real.pi * (1 - s)) ≤ R * Y + h * Y ^ 2 := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    have hm : 0 ≤ 2 * (R * Y) * (h * Y ^ 2) := by positivity
    have heq : h ^ 2 * s ^ 2 - Real.pi * (1 - s) = R ^ 2 * Y ^ 2 + h ^ 2 * Y ^ 4 := by
      rw [hR2]
      have hs : s = t₀ + Y ^ 2 := by linarith
      rw [hs]
      nlinarith [hroot]
    rw [heq]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hupper (le_of_lt (div_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
  dsimp [R, Y] at hm hY2
  rw [hY2] at hm
  ring_nf at hm ⊢
  linarith only [hm]

theorem interval_placement {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (1033 / 2700 : ℝ) ≤ u h - dm ∧ (38 / 100 : ℝ) < u h - dm ∧
    1 / Real.pi < (38 / 100 : ℝ) ∧ u h ≤ 1 - 1 / Real.pi ∧
    u h < t h ∧ h * u h ≤ 24 / 25 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hh0 : 0 < h := by linarith [hh.1]
  have hu1 : u h ≤ 1 - 1 / Real.pi := min_le_left _ _
  have huv : u h ≤ (24 / 25 : ℝ) / h := min_le_right _ _
  have hu : (16 / 27 : ℝ) ≤ u h := by
    apply le_min
    · apply (le_sub_iff_add_le).2
      have hip : 1 / Real.pi ≤ (1 / 3 : ℝ) := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hp3))
      linarith
    · apply (le_div_iff₀ hh0).2
      linarith [hh.2]
  have hhU : h * u h ≤ 24 / 25 := by
    have := (le_div_iff₀ hh0).1 huv
    nlinarith
  have htr := t_spec hh0
  have hlt : u h < t h := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt htr.1) hn 2) (sq_nonneg h)
    have hsq := pow_le_pow_left₀ (mul_nonneg (le_of_lt hh0) (by linarith : 0 ≤ u h)) hhU 2
    have hip : 1 ≤ Real.pi * (1 - u h) := by
      have hh := mul_le_mul_of_nonneg_left hu1 (le_of_lt hp)
      field_simp at hh
      nlinarith
    nlinarith [htr.2.2]
  refine ⟨?_, ?_, ?_, hu1, hlt, hhU⟩
  · dsimp [dm]; linarith
  · dsimp [dm]; linarith
  · apply (div_lt_iff₀ hp).2
    nlinarith

lemma theta_spec : 0 < theta ∧ theta < 1 ∧ c * dm * theta ^ 2 = Real.pi * (1 - theta) := by
  simpa only [theta, mul_assoc] using positive_quadratic_root (a := c * dm) (by norm_num [c, dm])

lemma theta_bounds : (32 / 37 : ℝ) < theta ∧ theta < 13 / 15 := by
  have ht := theta_spec
  have hp := Real.pi_gt_d2
  have hpU : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hr := ht.2.2
  norm_num [c, dm] at hr
  constructor
  · by_contra! hn
    have hs := pow_le_pow_left₀ (le_of_lt ht.1) hn 2
    have hh := mul_lt_mul_of_pos_right hp (by linarith : 0 < 1 - theta)
    nlinarith
  · by_contra! hn
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13 / 15) hn 2
    have hh := mul_lt_mul_of_pos_right hpU (by linarith : 0 < 1 - theta)
    nlinarith

lemma shape_on_left {q : ℝ} (hq : q ∈ Icc 0 theta) : shape q = q ^ 2 := by
  apply min_eq_left
  apply (le_div_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.1 hq.2 2)
    (by norm_num [c, dm] : 0 ≤ c * dm)
  have ht := theta_spec.2.2
  have hp := mul_le_mul_of_nonneg_left hq.2 (le_of_lt Real.pi_pos)
  nlinarith

lemma shape_on_right {q : ℝ} (hq : q ∈ Icc theta 1) :
    shape q = Real.pi * (1 - q) / (c * dm) := by
  apply min_eq_right
  apply (div_le_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt theta_spec.1) hq.1 2)
    (by norm_num [c, dm] : 0 ≤ c * dm)
  have ht := theta_spec.2.2
  have hp := mul_le_mul_of_nonneg_left hq.1 (le_of_lt Real.pi_pos)
  nlinarith

lemma shape_nonneg {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ shape q := by
  exact le_min (sq_nonneg q) (div_nonneg
    (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.2 hq.2)) (by norm_num [c, dm]))

lemma shape_le_one {q : ℝ} (hq : q ∈ Icc 0 1) : shape q ≤ 1 := by
  have hq2 := pow_le_pow_left₀ hq.1 hq.2 2
  exact le_trans (min_le_left _ _) (by simpa using hq2)

lemma shape_max {q : ℝ} (hq : q ∈ Icc 0 1) : shape q ≤ theta ^ 2 := by
  by_cases hh : q ≤ theta
  · rw [shape_on_left ⟨hq.1, hh⟩]
    exact pow_le_pow_left₀ hq.1 hh 2
  · rw [shape_on_right ⟨le_of_not_ge hh, hq.2⟩]
    apply (div_le_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
    have ht := theta_spec.2.2
    have hp := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (le_of_lt Real.pi_pos)
    nlinarith

lemma continuous_shape : Continuous shape := by
  unfold shape
  fun_prop

lemma integral_eq_split : moment = theta ^ 3 / 3 +
    Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
  have hfi : IntervalIntegrable shape volume 0 theta := continuous_shape.intervalIntegrable 0 theta
  have hfi2 : IntervalIntegrable shape volume theta 1 := continuous_shape.intervalIntegrable theta 1
  have h0 := theta_spec
  unfold moment
  rw [← intervalIntegral.integral_add_adjacent_intervals hfi hfi2]
  have hleft : (∫ q in (0 : ℝ)..theta, shape q) = theta ^ 3 / 3 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 2) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      exact shape_on_left hq
  have hright : (∫ q in theta..(1 : ℝ), shape q) =
      Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (1 - q)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume theta 1 from continuous_const.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)]
      norm_num
      ring
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hleft, hright]

lemma moment_eq : moment = theta ^ 2 * (3 - theta) / 6 := by
  rw [integral_eq_split]
  have ht := theta_spec.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 567 : ℝ) * (1 - theta) * ht

lemma firstMoment_eq : firstMoment = theta ^ 2 * (2 + 2 * theta - theta ^ 2) / 12 := by
  have hc : Continuous (fun q : ℝ => q * shape q) := continuous_id.mul continuous_shape
  have h0 := theta_spec
  unfold firstMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (0 : ℝ) theta) (hc.intervalIntegrable theta (1 : ℝ))]
  have hl : (∫ q in (0 : ℝ)..theta, q * shape q) = theta ^ 4 / 4 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 3) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      dsimp only
      rw [shape_on_left hq]
      ring
  have hr : (∫ q in theta..(1 : ℝ), q * shape q) =
      Real.pi / (c * dm) * ((1 - theta ^ 2) / 2 - (1 - theta ^ 3) / 3) := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (q - q ^ 2)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q ^ 2) volume theta 1 from (continuous_id.pow 2).intervalIntegrable _ _)]
      norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hl, hr]
  have ht := h0.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 1701 : ℝ) * (1 - theta) * (1 + 2 * theta) * ht

lemma moment_pos : 0 < moment := by
  rw [moment_eq]
  have ht := theta_spec
  have h3 : 0 < 3 - theta := by linarith [ht.2.1]
  have htpos := ht.1
  positivity

lemma meanQ_eq : meanQ = (2 + 2 * theta - theta ^ 2) / (2 * (3 - theta)) := by
  unfold meanQ
  rw [moment_eq, firstMoment_eq]
  have ht := theta_spec
  have ht0 := ne_of_gt ht.1
  have h30 : 3 - theta ≠ 0 := by linarith [ht.2.1]
  field_simp [ht0, h30]
  ring

lemma meanQ_mem : meanQ ∈ Ioo 0 1 := by
  rw [meanQ_eq]
  have ht := theta_spec
  have hs : theta ^ 2 < 1 := by nlinarith [ht.1, ht.2.1]
  constructor
  · apply div_pos
    · nlinarith
    · linarith
  · apply (div_lt_one (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 2)]

theorem moment_bounds : (2659 / 10000 : ℝ) < moment ∧
    (697 / 1000 : ℝ) < meanQ ∧ p₂ < (109 / 100 : ℝ) := by
  have ht := theta_spec
  have hb := theta_bounds
  have hθ2 := pow_lt_pow_left₀ hb.1 (by norm_num : (0 : ℝ) ≤ 32 / 37) (by norm_num : (2 : ℕ) ≠ 0)
  have hθU := pow_lt_pow_left₀ hb.2 (le_of_lt ht.1) (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [moment_eq]
    have hm : 0 ≤ (theta ^ 2 - (32 / 37) ^ 2) * (3 - theta) :=
      mul_nonneg (by linarith) (by linarith [ht.2.1])
    nlinarith [hb.2]
  · rw [meanQ_eq]
    apply (lt_div_iff₀ (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 1)]
  · dsimp [p₂, c, dm]
    nlinarith

lemma affine_shape_integral (a b : ℝ) :
    (∫ q in (0 : ℝ)..1, (a + b * q) * shape q) = moment * (a + b * meanQ) := by
  have hc : IntervalIntegrable shape volume 0 1 := continuous_shape.intervalIntegrable 0 1
  have hq : IntervalIntegrable (fun q : ℝ => q * shape q) volume 0 1 :=
    (continuous_id.mul continuous_shape).intervalIntegrable 0 1
  have heq : (fun q : ℝ => (a + b * q) * shape q) =
      fun q => a * shape q + b * (q * shape q) := by funext q; ring
  rw [heq, intervalIntegral.integral_add (hc.const_mul a) (hq.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change a * moment + b * firstMoment = moment * (a + b * meanQ)
  unfold meanQ
  field_simp [ne_of_gt moment_pos]

lemma cubic_shape_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment * (a + b * meanQ) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (a + b * q) ^ 3 * shape q := by
  let m := a + b * meanQ
  have hm : 0 ≤ m := add_nonneg ha (mul_nonneg hb (le_of_lt meanQ_mem.1))
  have hc : IntervalIntegrable (fun q : ℝ => (a + b * q) ^ 3 * shape q) volume 0 1 :=
    (((continuous_const.add (continuous_const.mul continuous_id)).pow 3).mul continuous_shape).intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun q : ℝ => m ^ 3 * shape q) volume 0 1 :=
    (continuous_const.mul continuous_shape).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun q : ℝ => (a + b * q - m) * shape q) volume 0 1 :=
    (( (continuous_const.add (continuous_const.mul continuous_id)).sub continuous_const).mul continuous_shape).intervalIntegrable 0 1
  have hbound := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (h1.add (h2.const_mul (3 * m ^ 2))) hc (fun q hq => by
      have hs := shape_nonneg hq
      have hf : 0 ≤ a + b * q := add_nonneg ha (mul_nonneg hb hq.1)
      have hh := mul_nonneg (mul_nonneg (sq_nonneg (a + b * q - m))
        (show 0 ≤ a + b * q + 2 * m by linarith)) hs
      nlinarith)
  rw [intervalIntegral.integral_add h1 (h2.const_mul (3 * m ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  have hz : (∫ q in (0 : ℝ)..1, (a + b * q - m) * shape q) = 0 := by
    have heq : (fun q : ℝ => (a + b * q - m) * shape q) =
        fun q => (a - m + b * q) * shape q := by funext q; ring
    rw [heq, affine_shape_integral]
    dsimp [m]
    ring
  rw [hz, mul_zero, add_zero] at hbound
  change moment * m ^ 3 ≤ _
  change m ^ 3 * moment ≤ _ at hbound
  linarith only [hbound]

lemma cubic_shape_lower_dm {u₀ δ : ℝ} (hδ : δ ∈ Icc 0 dm) (hu : dm ≤ u₀) :
    moment * (u₀ - (1 - meanQ) * dm) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (u₀ - δ + δ * q) ^ 3 * shape q := by
  have hm := meanQ_mem
  have h1 := cubic_shape_lower (a := u₀ - δ) (b := δ) (by linarith [hδ.2]) hδ.1
  apply le_trans _ h1
  apply mul_le_mul_of_nonneg_left _ (le_of_lt moment_pos)
  have hb : u₀ - (1 - meanQ) * dm ≤ u₀ - δ + δ * meanQ := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 (show 0 ≤ 1 - meanQ by linarith [hm.2])
    nlinarith
  apply pow_le_pow_left₀ _ hb 3
  have hh : 0 ≤ dm * meanQ := mul_nonneg (by norm_num [dm]) (le_of_lt hm.1)
  nlinarith

lemma p₂_pos : 0 < p₂ := by
  unfold p₂ c dm
  positivity

lemma coefficient_lower : (574 / 1000 : ℝ) <
    ((91 / 100 : ℝ) * c * moment) / Real.sqrt p₂ ^ 3 := by
  have hM := moment_bounds.1
  have hp := moment_bounds.2.2
  have hs : 0 < Real.sqrt p₂ := Real.sqrt_pos.2 p₂_pos
  have hs2 := Real.sq_sqrt (le_of_lt p₂_pos)
  have hd : (Real.sqrt p₂ ^ 3) ^ 2 = p₂ ^ 3 := by
    rw [show (Real.sqrt p₂ ^ 3) ^ 2 = (Real.sqrt p₂ ^ 2) ^ 3 by ring, hs2]
  have hp3 := pow_lt_pow_left₀ hp (le_of_lt p₂_pos) (by norm_num : (3 : ℕ) ≠ 0)
  have hc : (574 / 1000 : ℝ) * Real.sqrt p₂ ^ 3 <
      (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ) := by
    apply (sq_lt_sq₀ (by positivity)
      (by norm_num [c] : (0 : ℝ) ≤ (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ))).1
    rw [mul_pow, hd]
    norm_num [c]
    nlinarith only [hp3]
  apply (lt_div_iff₀ (pow_pos hs 3)).2
  have hmc := mul_lt_mul_of_pos_left hM (by norm_num [c] : (0 : ℝ) < (91 / 100 : ℝ) * c)
  exact lt_trans hc hmc

end CubicTorus.Shape
end
end
end
end

end OAI
