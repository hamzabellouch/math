import OAI.Analysis.Steinitz.Rearrangement

namespace OAI

/-! Heat and energy inequalities for affine sections. -/

section

open MeasureTheory Set Filter
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section RealFunctions
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

noncomputable def complexLp (f : X → ℝ) (hf : MemLp f 2 μ) : Lp ℂ 2 μ :=
  hf.ofReal.toLp (fun x => (f x:ℂ))

lemma complexLp_coe (f : X → ℝ) (hf : MemLp f 2 μ) :
    (complexLp f hf : X → ℂ) =ᵐ[μ] fun x => (f x:ℂ) := MemLp.coeFn_toLp _

lemma complexLp_norm_sq (f : X → ℝ) (hf : MemLp f 2 μ) :
    ‖complexLp f hf‖^2 = ∫ x,f x^2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [complexLp_coe f hf] with x hx
  simp only [hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]

noncomputable def nonnegRepresentative (D : Set X) (_hD : MeasurableSet D) (f : Lp ℂ 2 μ) : X → ℝ :=
  D.indicator (fun x => ‖(Lp.aestronglyMeasurable f).mk f x‖)

lemma nonnegRepresentative_measurable (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) :
    Measurable (nonnegRepresentative D hD f) :=
  (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.norm.measurable.indicator hD

lemma nonnegRepresentative_nonneg (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ) (x : X) :
    0 ≤ nonnegRepresentative D hD f x := by
  exact indicator_nonneg (fun _ _ => norm_nonneg _) x

lemma nonnegRepresentative_zero (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    {x : X} (hx : x ∉ D) : nonnegRepresentative D hD f x=0 := indicator_of_notMem hx _

lemma nonnegRepresentative_ae (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : nonnegRepresentative D hD f =ᵐ[μ] fun x => ‖f x‖ := by
  filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk,hf] with x hx hfx
  by_cases hxd : x ∈ D
  · simp only [nonnegRepresentative,indicator_of_mem hxd,hx]
  · simp only [nonnegRepresentative,indicator_of_notMem hxd,hfx hxd,norm_zero]

lemma nonnegRepresentative_memLp (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : MemLp (nonnegRepresentative D hD f) 2 μ :=
  (Lp.memLp f).norm.ae_eq (nonnegRepresentative_ae D hD f hf).symm

lemma nonnegRepresentative_square (D : Set X) (hD : MeasurableSet D) (f : Lp ℂ 2 μ)
    (hf : f ∈ supported D) : (∫ x,nonnegRepresentative D hD f x^2 ∂μ)=‖f‖^2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [nonnegRepresentative_ae D hD f hf] with x hx
  rw [hx]

end RealFunctions

section Spatial
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

noncomputable def realDistance (f : E → ℝ) (a : E) : ℝ := ∫ x,(f (x+a)-f x)^2

lemma realDistance_eq (f : E → ℝ) (hf : MemLp f 2 volume) (a : E) :
    realDistance f a = ‖translate a (complexLp f hf)-complexLp f hf‖^2 := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (translate a (complexLp f hf)) (complexLp f hf),
    translate_coe a (complexLp f hf),complexLp_coe f hf,
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp (complexLp_coe f hf)]
    with x hsub htr hx hxa
  simp only [Function.comp_apply] at hxa
  simp only [hsub,Pi.sub_apply,htr,hx,hxa,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]

omit [FiniteDimensional ℝ F] in
lemma realDistance_integrable (f : E → ℝ) (hf : MemLp f 2 volume) (A : F →L[ℝ] E)
    (ν : Measure F) [IsFiniteMeasure ν] : Integrable (fun z => realDistance f (A z)) ν := by
  simp_rw [realDistance_eq f hf]
  exact integrable_difference_sq A ν _

lemma realEnergy_eq (f : E → ℝ) (hf : MemLp f 2 volume) (A : F →L[ℝ] E) :
    (1/2:ℝ)*(∫ z,realDistance f (A z) ∂ProbabilityTheory.stdGaussian F) =
      energy (gaussianSymbol A) (complexLp f hf) := by
  rw [gaussian_energy_difference]
  simp_rw [realDistance_eq f hf]

lemma norm_representative_distance_le (f : Lp ℂ 2 (volume : Measure E))
    (g : E → ℝ) (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖) (a : E) :
    realDistance g a ≤ ‖translate a f-f‖^2 := by
  have hgi := ((hg.comp_measurePreserving (measurePreserving_add_right volume a)).sub hg)
  have hgsq := (memLp_two_iff_integrable_sq hgi.aestronglyMeasurable).mp hgi
  have hfm := (Lp.memLp (translate a f-f)).norm
  have hfint := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mp hfm
  simp only [Pi.sub_apply,Function.comp_apply] at hgsq
  rw [realDistance,norm_sq_integral]
  apply integral_mono_ae hgsq hfint
  filter_upwards [he,(measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp he,
    Lp.coeFn_sub (translate a f) f,translate_coe a f] with x hx hxa hsub htr
  simp only [Function.comp_apply] at hxa
  simp only [hx,hxa,hsub,Pi.sub_apply,htr]
  apply sq_le_sq.mpr
  simpa only [abs_norm] using abs_norm_sub_norm_le (f (x+a)) (f x)

end Spatial
end HeatL2

end

section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace HeatL2
section Slice
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma horizontal_translate_preserving (a : E) :
    MeasurePreserving (fun p : E × ℝ => (p.1+a,p.2))
      ((volume : Measure E).prod volume) (volume.prod volume) := by
  exact (measurePreserving_add_right volume a).prod (MeasurePreserving.id volume)

lemma horizontal_difference_integrable (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    Integrable (fun q : F × (E × ℝ) => (G (q.2.1+A q.1,q.2.2)-G q.2)^2)
      (ν.prod ((volume : Measure E).prod volume)) := by
  have hp : MeasurePreserving (fun q : F × (E × ℝ) => (q.1,(q.2.1+A q.1,q.2.2)))
      (ν.prod (volume.prod volume)) (ν.prod (volume.prod volume)) :=
    (MeasurePreserving.id ν).skew_product (by fun_prop)
      (ae_of_all _ fun z => (horizontal_translate_preserving (A z)).map_eq)
  have h₀ : MemLp (fun q : F × (E × ℝ) => G q.2) 2 (ν.prod (volume.prod volume)) :=
    hG.comp_measurePreserving measurePreserving_snd
  have h₁ := h₀.comp_measurePreserving hp
  have hd := h₁.sub h₀
  exact (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd

lemma slice_memLp (G : E × ℝ → ℝ) (hm : Measurable G)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) :
    ∀ᵐ s ∂(volume : Measure ℝ), MemLp (fun x => G (x,s)) 2 volume := by
  have hi := (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG
  filter_upwards [hi.prod_left_ae] with s hs
  exact (memLp_two_iff_integrable_sq (hm.comp (by fun_prop)).aestronglyMeasurable).mpr hs

noncomputable def sliceEnergy (ν : Measure F) (A : F →L[ℝ] E) (G : E × ℝ → ℝ) (s : ℝ) : ℝ :=
  (1/2:ℝ) * ∫ z, realDistance (fun x => G (x,s)) (A z) ∂ν

lemma sliceEnergy_integrable (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] : Integrable (sliceEnergy ν A G) volume := by
  have hi := horizontal_difference_integrable G hG A ν
  have ha := (measurePreserving_prodAssoc ν (volume : Measure E)
    (volume : Measure ℝ)).integrable_comp_of_integrable hi
  have hk := ha.integral_prod_right
  apply (hk.const_mul (1/2:ℝ)).congr
  filter_upwards [ha.prod_left_ae] with s hs
  dsimp [sliceEnergy,realDistance]
  congr 1
  exact integral_prod _ hs

lemma integral_sliceEnergy (G : E × ℝ → ℝ)
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) (A : F →L[ℝ] E)
    (ν : Measure F) [IsProbabilityMeasure ν] :
    (∫ s,sliceEnergy ν A G s) = (1/2:ℝ) * ∫ z,
      ∫ p,(G (p.1+A z,p.2)-G p)^2 ∂((volume : Measure E).prod volume) ∂ν := by
  have hi := horizontal_difference_integrable G hG A ν
  have hp := measurePreserving_prodAssoc ν (volume : Measure E) (volume : Measure ℝ)
  have ha := hp.integrable_comp_of_integrable hi
  unfold sliceEnergy
  rw [integral_const_mul]
  congr 1
  calc
    (∫ s,∫ z,realDistance (fun x => G (x,s)) (A z) ∂ν) =
        ∫ s,∫ q : F × E,(G (q.2+A q.1,s)-G (q.2,s))^2 ∂ν.prod volume := by
      apply integral_congr_ae
      filter_upwards [ha.prod_left_ae] with s hs
      exact (integral_prod _ hs).symm
    _ = ∫ q : (F × E) × ℝ,(G (q.1.2+A q.1.1,q.2)-G (q.1.2,q.2))^2
        ∂(ν.prod volume).prod volume := (integral_prod_symm _ ha).symm
    _ = ∫ q : F × (E × ℝ),(G (q.2.1+A q.1,q.2.2)-G q.2)^2
        ∂ν.prod (volume.prod volume) := hp.integral_comp MeasurableEquiv.prodAssoc.measurableEmbedding
          (fun q : F × (E × ℝ) => (G (q.2.1+A q.1,q.2.2)-G q.2)^2)
    _ = _ := integral_prod _ hi

lemma integral_sliceEnergy_le {G : E × ℝ → ℝ}
    (hG : MemLp G 2 ((volume : Measure E).prod volume)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (A : F →L[ℝ] E)
    (hc : ∀ a : E,(∫ p,(G (p.1+a,p.2)-G p)^2 ∂(volume : Measure E).prod volume) ≤ realDistance f a) :
    (∫ s,sliceEnergy (ProbabilityTheory.stdGaussian F) A G s) ≤
      energy (gaussianSymbol A) (complexLp f hf) := by
  rw [integral_sliceEnergy G hG,← realEnergy_eq]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact integral_mono (horizontal_difference_integrable G hG A _).integral_prod_left
    (realDistance_integrable f hf A _) (fun z => hc (A z))

end Slice
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
variable {ι : Type*} [Fintype ι]

noncomputable def sliceMass (G : EuclideanSpace ℝ ι × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ x,G (x,s)^2

lemma sliceMass_nonneg (G : EuclideanSpace ℝ ι × ℝ → ℝ) (s : ℝ) : 0 ≤ sliceMass G s :=
  integral_nonneg fun _ => sq_nonneg _

lemma sliceMass_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume)) : Integrable (sliceMass G) volume :=
  ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG).integral_prod_right

lemma integral_sliceMass {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume)) :
    (∫ s,sliceMass G s) = ∫ p,G p^2 ∂(volume : Measure (EuclideanSpace ℝ ι)).prod volume :=
  (integral_prod_symm _ ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG)).symm

lemma sliceMass_height_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) :
    Integrable (fun s => |s| *sliceMass G s) volume := by
  have hi := hH.integral_prod_right
  simpa only [sliceMass,integral_const_mul] using hi

lemma integral_sliceMass_height {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) :
    (∫ s,|s| *sliceMass G s) = ∫ p,|p.2| *G p^2 ∂(volume : Measure (EuclideanSpace ℝ ι)).prod volume := by
  rw [integral_prod_symm _ hH]
  simp only [sliceMass,integral_const_mul]

lemma height_above_one {K : Set (EuclideanSpace ℝ ι)} (e : EuclideanSpace ℝ ι) (ell : ℝ)
    {G : EuclideanSpace ℝ ι × ℝ → ℝ} (hG : MemLp G 2 (volume.prod volume))
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1)
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hh : 1 < ∫ p,|p.2| *G p^2 ∂volume.prod volume)
    (hs : ∀ p,p.1 ∉ sectionDomain K e ell |p.2| → G p=0) :
    ∃ r ∈ activeHeights K e ell,1 < r := by
  have hp : ∃ p : EuclideanSpace ℝ ι × ℝ, 1 < |p.2| ∧ G p ≠ 0 := by
    by_contra! he
    have hle : ∀ p : EuclideanSpace ℝ ι × ℝ, |p.2| *G p^2 ≤ G p^2 := by
      intro p
      by_cases hp : 1 < |p.2|
      · simp only [he p hp,zero_pow (by norm_num : 2 ≠ 0),mul_zero,le_refl]
      · exact mul_le_of_le_one_left (sq_nonneg _) (le_of_not_gt hp)
    have hi := integral_mono hH ((memLp_two_iff_integrable_sq hG.aestronglyMeasurable).mp hG) hle
    rw [hn] at hi
    linarith
  obtain ⟨p,hp,hpn⟩ := hp
  refine ⟨|p.2|,⟨abs_nonneg _,⟨p.1,?_⟩⟩,hp⟩
  by_contra hx
  exact hpn (hs p hx)

lemma activeHeights_contains_one {K : Set (EuclideanSpace ℝ ι)} (hK : Convex ℝ K)
    (e : EuclideanSpace ℝ ι) (ell : ℝ) (hr : ∃ r ∈ activeHeights K e ell,1 < r) :
    (0:ℝ) ∈ activeHeights K e ell ∧ (1:ℝ) ∈ activeHeights K e ell := by
  obtain ⟨r,hr,hr1⟩ := hr
  obtain ⟨y,hy⟩ := hr.2
  exact ⟨⟨le_refl 0,⟨y,section_mono hK e ell (le_refl 0) hr.1 hy⟩⟩,
    ⟨by norm_num,⟨y,section_mono hK e ell (by norm_num) hr1.le hy⟩⟩⟩

lemma activeHeights_lt {K : Set (EuclideanSpace ℝ ι)} (e : EuclideanSpace ℝ ι) (ell : ℝ)
    {s : ℝ} (hs : s ∈ activeHeights K e ell) : s < ell := by
  obtain ⟨y,c,hc,_,_⟩ := hs.2
  linarith [abs_nonneg c]

end ShiftedSections

end

section

open MeasureTheory Set
open scoped ComplexInnerProductSpace
namespace HeatL2

lemma loss_bounded_lower {t R L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) (hRL : R ≤ L) :
    t/(1+t*L)*R ≤ max 0 (loss (t*R)) := by
  have hd : 0 < 1+t*L := by positivity
  by_cases hR : 0 ≤ R
  · apply le_trans _ (le_max_right _ _)
    apply le_trans _ (loss_lower (mul_nonneg ht.le hR))
    calc
      t/(1+t*L)*R = (t*R)/(1+t*L) := by ring
      _ ≤ (t*R)/(1+t*R) := div_le_div_of_nonneg_left (mul_nonneg ht.le hR)
        (by positivity) (by nlinarith)
  · apply le_trans _ (le_max_left _ _)
    exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht.le hd.le) (le_of_not_ge hR)

section Affine
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma compressed_norm_smalltime (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖compressedHeat D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg ht.le (hn ξ))‖ ≤
      ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖^t := by
  have hh := compressed_norm_rpow D hD w hw hn ht ht1
  simp only [one_mul] at hh
  simpa only [one_div,inv_inv] using
    (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (norm_nonneg _) (one_div_pos.mpr ht)).mpr hh

lemma energy_lower_rate (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    (hnorm : 0 < ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hR : R ≤ -Real.log ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    loss (t*R)*‖f‖^2 ≤ energy (fun ξ => t*w ξ) f := by
  have hs := compressed_norm_smalltime D hD w hw hn ht ht1
  have he : ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖^t ≤ Real.exp (-(t*R)) := by
    rw [Real.rpow_def_of_pos hnorm]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hh := form_le_norm D hD (fun ξ => t*w ξ) (hw.const_mul t).aestronglyMeasurable
      (fun ξ => mul_nonneg ht.le (hn ξ)) hf
  have hb := mul_le_mul_of_nonneg_right (hs.trans he) (sq_nonneg ‖f‖)
  dsimp [loss]
  nlinarith

lemma energy_lower_affine (D : Set E) (hD : MeasurableSet D)
    (w : E → ℝ) (hw : Measurable w) (hn : ∀ x,0 ≤ w x)
    (hnorm : 0 < ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {t R L : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hL : 0 ≤ L) (hRL : R ≤ L)
    (hR : R ≤ -Real.log ‖compressedHeat D hD w hw.aestronglyMeasurable hn‖)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : f ∈ supported D) :
    (t/(1+t*L)*R)*‖f‖^2 ≤ energy (fun ξ => t*w ξ) f := by
  have hh := loss_bounded_lower ht hL hRL
  apply (mul_le_mul_of_nonneg_right hh (sq_nonneg ‖f‖)).trans
  rw [max_mul_of_nonneg _ _ (sq_nonneg ‖f‖),zero_mul]
  exact max_le (energy_nonneg _ (fun ξ => mul_nonneg ht.le (hn ξ)) f)
    (energy_lower_rate D hD w hw hn hnorm ht ht1 hR hf)

end Affine
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace ShiftedSections
open HeatL2
variable {ι : Type*} [Fintype ι]

lemma sliceMass_affine_integrable {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume))
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume)) (h a : ℝ) :
    Integrable (fun s => (h+a*(|s|-1))*sliceMass G s) volume := by
  have he : (fun s => (h+a*(|s|-1))*sliceMass G s) =
      (fun s => (h-a)*sliceMass G s+a*(|s| *sliceMass G s)) := by ext s; ring
  rw [he]
  exact ((sliceMass_integrable hG).const_mul (h-a)).add
    ((sliceMass_height_integrable hH).const_mul a)

lemma integral_sliceMass_affine {G : EuclideanSpace ℝ ι × ℝ → ℝ}
    (hG : MemLp G 2 (volume.prod volume))
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1) (h a : ℝ) :
    (∫ s,(h+a*(|s|-1))*sliceMass G s) = h+a*((∫ p,|p.2| *G p^2 ∂volume.prod volume)-1) := by
  have he : (fun s => (h+a*(|s|-1))*sliceMass G s) =
      (fun s => (h-a)*sliceMass G s+a*(|s| *sliceMass G s)) := by ext s; ring
  rw [he,integral_add ((sliceMass_integrable hG).const_mul _) ((sliceMass_height_integrable hH).const_mul _),
    integral_const_mul,integral_const_mul,integral_sliceMass hG,hn,integral_sliceMass_height hH]
  ring

lemma integrated_section_rate {K : Set (EuclideanSpace ℝ ι)} (hKo : IsOpen K)
    (hKb : Bornology.IsBounded K) (e : EuclideanSpace ℝ ι) {ell : ℝ} (hell : 0 ≤ ell)
    (v : ι → ℝ≥0) {h a : ℝ} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (hline : ∀ r ∈ activeHeights K e ell,h+a*(r-1) ≤ sectionRate K hKo e ell v r)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hA : gaussianSymbol A = fun ξ => t*GaussianKernel.symbol v ξ)
    {G : EuclideanSpace ℝ ι × ℝ → ℝ} (hGm : Measurable G)
    (hG : MemLp G 2 (volume.prod volume))
    (hGs : ∀ p,p.1 ∉ sectionDomain K e ell |p.2| → G p=0)
    (hn : (∫ p,G p^2 ∂volume.prod volume)=1)
    (hH : Integrable (fun p => |p.2| *G p^2) (volume.prod volume))
    (hheight : 1 ≤ ∫ p,|p.2| *G p^2 ∂volume.prod volume) :
    t/(1+t*(h+a*ell))*h ≤ ∫ s,sliceEnergy (ProbabilityTheory.stdGaussian _) A G s := by
  let L := h+a*ell
  have hL : 0 ≤ L := add_nonneg hh (mul_nonneg ha hell)
  have hC : 0 ≤ t/(1+t*L) := by positivity
  have hint := (sliceMass_affine_integrable hG hH h a).const_mul (t/(1+t*L))
  have hbound : ∀ᵐ s ∂(volume : Measure ℝ),
      (t/(1+t*L))*((h+a*(|s|-1))*sliceMass G s) ≤
        sliceEnergy (ProbabilityTheory.stdGaussian _) A G s := by
    filter_upwards [slice_memLp G hGm hG] with s hs
    by_cases hact : |s| ∈ activeHeights K e ell
    · let D := sectionDomain K e ell |s|
      have hD : MeasurableSet D := (section_open hKo e ell |s|).measurableSet
      have hsupp : complexLp (fun x => G (x,s)) hs ∈ supported D := by
        filter_upwards [complexLp_coe (fun x => G (x,s)) hs] with x hx hn
        rw [hx,hGs (x,s) hn,Complex.ofReal_zero]
      have hb := energy_lower_affine D hD (GaussianKernel.symbol v)
        (GaussianKernel.symbol_continuous v).measurable (GaussianKernel.symbol_nonneg v)
        (sectionNorm_pos hKo hKb e ell v hact) ht ht1 hL
        (show h+a*(|s|-1) ≤ L by
          have := activeHeights_lt e ell hact
          dsimp [L]
          nlinarith)
        (hline |s| hact) hsupp
      rw [complexLp_norm_sq,← hA,← realEnergy_eq] at hb
      simpa only [sliceMass,sliceEnergy,mul_assoc] using hb
    · have hz : ∀ x,G (x,s)=0 := by
        intro x
        apply hGs (x,s)
        intro hx
        exact hact ⟨abs_nonneg _,⟨x,hx⟩⟩
      simp only [sliceMass,sliceEnergy,realDistance,hz,sub_self,zero_pow (by norm_num : 2 ≠ 0),
        integral_zero,mul_zero,le_refl]
  have hInt := integral_mono_ae hint (sliceEnergy_integrable G hG A _) hbound
  rw [integral_const_mul,integral_sliceMass_affine hG hH hn h a] at hInt
  apply le_trans _ hInt
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith

end ShiftedSections

end

section

open MeasureTheory Set FourierTransform
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
section Energy
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

lemma energy_sum_dilate_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (w : ι → E → ℝ)
    (hc : ∀ i ∈ s,1 ≤ c i) (hw : ∀ i ∈ s,AEStronglyMeasurable (w i) volume)
    (hn : ∀ i ∈ s,∀ ξ,0 ≤ w i ξ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy (fun ξ => ∑ i ∈ s,c i*w i ξ) f ≤ ∑ i ∈ s,c i*energy (w i) f := by
  have hi i (h : i ∈ s) := (integrable_energy (w i) (hw i h) (hn i h) f).const_mul (c i)
  have hw' : AEStronglyMeasurable (fun ξ => ∑ i ∈ s,c i*w i ξ) volume :=
    s.aestronglyMeasurable_fun_sum fun i hi => (hw i hi).const_mul (c i)
  have hn' ξ : 0 ≤ ∑ i ∈ s,c i*w i ξ := Finset.sum_nonneg fun i hi =>
    mul_nonneg (le_trans zero_le_one (hc i hi)) (hn i hi ξ)
  have he : (∑ i ∈ s,c i*energy (w i) f) =
      ∫ ξ,∑ i ∈ s,c i*(loss (w i ξ)*‖(𝓕 f) ξ‖^2) := by
    rw [integral_finsetSum s hi]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_const_mul _ _).symm
  rw [he]
  apply integral_mono (integrable_energy _ hw' hn' f) (integrable_finsetSum s hi)
  intro ξ
  simpa only [← mul_assoc,← Finset.sum_mul] using
    mul_le_mul_of_nonneg_right (loss_sum_dilate_le s c (fun i => w i ξ) hc
      (fun i hi => hn i hi ξ)) (sq_nonneg ‖(𝓕 f) ξ‖)

lemma norm_representative_energy_le (f : Lp ℂ 2 (volume : Measure E))
    (g : E → ℝ) (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖)
    (A : F →L[ℝ] E) : energy (gaussianSymbol A) (complexLp g hg) ≤ energy (gaussianSymbol A) f := by
  rw [← realEnergy_eq,gaussian_energy_difference]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact integral_mono (realDistance_integrable g hg A _) (integrable_difference_sq A _ f)
    (fun z => norm_representative_distance_le f g hg he _)

end Energy
namespace Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma directionalSymbol_single (i : ι) : directionalSymbol (EuclideanSpace.single i (1:ℝ))=coordSymbol i := by
  ext ξ
  simp only [directionalSymbol,coordSymbol,EuclideanSpace.inner_single_left,map_one,one_mul]

omit [DecidableEq ι] in
lemma symbol_scaled_sum (v : ι → ℝ≥0) (t : ℝ) :
    (fun ξ => t*GaussianKernel.symbol v ξ) = fun ξ => ∑ i,(t*(v i:ℝ)/2)*coordSymbol i ξ := by
  ext ξ
  unfold GaussianKernel.symbol coordSymbol
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [DecidableEq ι] in
lemma energy_weighted_le (v : ι → ℝ≥0) {η t : ℝ} (hη : 0 < η)
    (hηt : ∀ i,η ≤ t*(v i:ℝ)/2) (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :
    energy (fun ξ => t*GaussianKernel.symbol v ξ) f ≤
      ∑ i,(t*(v i:ℝ)/(2*η))*energy (fun ξ => η*coordSymbol i ξ) f := by
  have he : (fun ξ => t*GaussianKernel.symbol v ξ) =
      fun ξ => ∑ i,(t*(v i:ℝ)/(2*η))*(η*coordSymbol i ξ) := by
    rw [symbol_scaled_sum]
    ext ξ
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [he]
  apply energy_sum_dilate_le
  · intro i _
    rw [le_div_iff₀ (by positivity : 0 < 2*η)]
    linarith [hηt i]
  · intro i _
    exact ((coordSymbol_continuous i).const_mul η).aestronglyMeasurable
  · intro i _ ξ
    exact mul_nonneg hη.le (coordSymbol_nonneg i ξ)

lemma norm_representative_diagonal_energy_le (v : ι → ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (g : EuclideanSpace ℝ ι → ℝ)
    (hg : MemLp g 2 volume) (he : g =ᵐ[volume] fun x => ‖f x‖) :
    energy (GaussianKernel.symbol v) (complexLp g hg) ≤ energy (GaussianKernel.symbol v) f := by
  rw [← GaussianKernel.symbol_eq]
  exact norm_representative_energy_le f g hg he _

end Diagonal
end HeatL2

end

section

open MeasureTheory Set
open scoped ENNReal NNReal
namespace HeatL2.Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma simultaneous_real_density {D : Set (EuclideanSpace ℝ ι)} {hD : MeasurableSet D}
    {c η ε : ℝ} (hB : Bound D hD c) (hη : 0 < η) (hε : 0 < ε) :
    ∃ f : EuclideanSpace ℝ ι → ℝ, Measurable f ∧ (∀ x,0 ≤ f x) ∧
      (∀ x,x ∉ D → f x=0) ∧ ∃ hf : MemLp f 2 volume,
      (∫ x,f x^2)=1 ∧ ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) < η*(c+ε) := by
  obtain ⟨F,hF,hFn,hFe⟩ := simultaneous_coordinate_energy hB hη hε
  let f := nonnegRepresentative D hD F
  have hf := nonnegRepresentative_memLp D hD F hF
  refine ⟨f,nonnegRepresentative_measurable D hD F,nonnegRepresentative_nonneg D hD F,
    fun x hx => nonnegRepresentative_zero D hD F hx,hf,?_,?_⟩
  · rw [nonnegRepresentative_square D hD F hF,hFn,one_pow]
  · intro i
    let ηn : ℝ≥0 := ⟨η,hη.le⟩
    have hh := norm_representative_diagonal_energy_le (Pi.single i (2*ηn)) F f hf
      (nonnegRepresentative_ae D hD F hF)
    rw [symbol_single i ηn] at hh
    exact hh.trans_lt (hFe i)

lemma real_coordinate_distance {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 volume)
    {η ε : ℝ} (hη : 0 < η) (hη1 : η ≤ 1/4) (hε : ε ≤ 1/10000)
    (hEn : ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) ≤ η*((1/10000)+ε))
    (j : ι) {r t : ℝ} (hr : r ∈ Ioo (-(5/2:ℝ)) (5/2)) (ht : t ∈ Ioo (-(5/2:ℝ)) (5/2)) :
    realDistance f ((r-t) • EuclideanSpace.single j 1) ≤ 3/500 := by
  rw [realDistance_eq f hf]
  have hh := directional_translate_bound (EuclideanSpace.single j (1:ℝ)) (r-t) η hη (complexLp f hf)
  rw [directionalSymbol_single] at hh
  have hnn : 0 ≤ ((r-t)^2+4*η)/η := div_nonneg (by positivity) hη.le
  have he := mul_le_mul_of_nonneg_left (hEn j) hnn
  have heq : (((r-t)^2+4*η)/η)*(η*((1/10000)+ε)) = ((r-t)^2+4*η)*((1/10000)+ε) := by
    field_simp
  rw [heq] at he
  apply hh.trans (he.trans ?_)
  have hd : (r-t)^2 ≤ 25 := by
    have hx : -(5:ℝ) ≤ r-t ∧ r-t ≤ 5 := by constructor <;> linarith [hr.1,hr.2,ht.1,ht.2]
    nlinarith [sq_nonneg (r-t+5),sq_nonneg (r-t-5)]
  have hA : (r-t)^2+4*η ≤ 26 := by linarith
  have hB : (1/10000:ℝ)+ε ≤ 1/5000 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (r-t)^2+4*η)
  nlinarith

omit [DecidableEq ι] in
lemma energy_weighted_density {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 volume)
    {η c t : ℝ} (hη : 0 < η) (v : ι → ℝ≥0) (ht : 0 ≤ t)
    (hηt : ∀ i,η ≤ t*(v i:ℝ)/2)
    (hE : ∀ i,energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf) ≤ η*c) :
    energy (fun ξ => t*GaussianKernel.symbol v ξ) (complexLp f hf) ≤ (t*c/2)*∑ i,(v i:ℝ) := by
  classical
  apply (energy_weighted_le v hη hηt _).trans
  calc
    (∑ i,t*(v i:ℝ)/(2*η)*energy (fun ξ => η*coordSymbol i ξ) (complexLp f hf)) ≤
        ∑ i,t*(v i:ℝ)/(2*η)*(η*c) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hE i) (by positivity)
    _ = (t*c/2)*∑ i,(v i:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp

omit [DecidableEq ι] in
lemma exists_coordinate_time (v : ι → ℝ≥0) (hv : ∀ i,0 < v i) {t : ℝ} (ht : 0 < t) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1/4 ∧ ∀ i,η ≤ t*(v i:ℝ)/2 := by
  have hh : ∀ s : Finset ι,∃ η : ℝ,0 < η ∧ η ≤ 1/4 ∧ ∀ i ∈ s,η ≤ t*(v i:ℝ)/2 := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨1/4,by norm_num,le_rfl,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨η,hη,hη1,hηs⟩ := ih
      have hvi : (0:ℝ) < v i := hv i
      refine ⟨min η (t*(v i:ℝ)/2),lt_min hη (by positivity),
        (min_le_left _ _).trans hη1,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hηs j hj)
  obtain ⟨η,hη,hη1,hηs⟩ := hh Finset.univ
  exact ⟨η,hη,hη1,fun i => hηs i (Finset.mem_univ i)⟩

end HeatL2.Diagonal

end

end OAI
