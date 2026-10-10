import OAI.Geometry.LatticeCovering.Covering

namespace OAI

section
section
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
noncomputable section

namespace SingleLatticeCovering.Sections
open Set Module MeasureTheory
open scoped BigOperators Pointwise

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma affine_section_of_ball_projection {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    {K : Set (E × F)} (hconv : Convex ℝ K) {R : ℝ} (hR : 0 < R)
    (hproj : ∀ v : F, ‖v‖ ≤ 6*(D : ℝ)*R → ∃ x : E, (x,v) ∈ K) :
    ∃ T : F →ᵃ[ℝ] E, ∀ y : F, ‖y‖ ≤ 2*R → (T y,y) ∈ K := by
  classical
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  let c : ℝ := 4*R*D
  have hc : 0 < c := by dsimp [c]; positivity
  let v₀ : F := ∑ i : Fin D, (-2*R) • b i
  let v : Fin D → F := fun i => v₀+c • b i
  have hv₀ : ‖v₀‖ ≤ 2*R*D := by
    calc
      _ ≤ ∑ i : Fin D, ‖(-2*R) • b i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin D, 2*R := by
        apply Finset.sum_le_sum; intro i hi
        rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hR.le]
        norm_num
        nlinarith [hunit i]
      _ = _ := by simp; ring
  have hvi : ∀ i, ‖v i‖ ≤ 6*(D : ℝ)*R := by
    intro i
    calc
      _ ≤ ‖v₀‖+‖c • b i‖ := norm_add_le _ _
      _ ≤ 2*R*D+c := add_le_add hv₀ (by rw [norm_smul,Real.norm_of_nonneg hc.le]; nlinarith [hunit i])
      _ = _ := by dsimp [c]; ring
  obtain ⟨x₀,hx₀⟩ := hproj v₀ (by nlinarith)
  choose x hx using fun i => hproj (v i) (hvi i)
  let lam : F → Fin D → ℝ := fun y i => (b.repr y i+2*R)/c
  let L : F →ₗ[ℝ] E := ∑ i : Fin D, (b.coord i).smulRight (c⁻¹ • (x i-x₀))
  let t₀ : E := x₀+∑ i : Fin D, (2*R/c) • (x i-x₀)
  let T : F →ᵃ[ℝ] E := L.toAffineMap+AffineMap.const ℝ F t₀
  have hT : ∀ y, T y=x₀+∑ i : Fin D, lam y i • (x i-x₀) := by
    intro y
    dsimp [T,L,t₀,lam]
    simp only [      LinearMap.sum_apply,LinearMap.smulRight_apply,Basis.coord_apply,smul_smul]
    rw [add_comm _ (x₀+_),add_assoc]; congr 1
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rw [←add_smul]
    congr 1; field_simp; ring
  refine ⟨T,fun y hy => ?_⟩
  have hlam0 : ∀ i, 0 ≤ lam y i := by
    intro i
    have hh := (abs_le.mp ((hcoord y i).trans hy)).1
    exact div_nonneg (by linarith) hc.le
  have hlamsum : ∑ i : Fin D, lam y i ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin D, 4*R/c := by
        apply Finset.sum_le_sum; intro i hi
        apply div_le_div_of_nonneg_right _ hc.le
        have hh := (abs_le.mp ((hcoord y i).trans hy)).2
        linarith
      _ = 1 := by simp [c]; field_simp
  let w : Option (Fin D) → ℝ := fun o => o.elim (1-∑ i,lam y i) (lam y)
  let z : Option (Fin D) → E × F := fun o => o.elim (x₀,v₀) (fun i => (x i,v i))
  have hw0 : ∀ o ∈ (Finset.univ : Finset (Option (Fin D))), 0 ≤ w o := by
    intro o ho; cases o with
    | none => exact sub_nonneg.mpr hlamsum
    | some i => exact hlam0 i
  have hw1 : ∑ o : Option (Fin D), w o=1 := by simp [w,Fintype.sum_option]
  have hz : ∀ o ∈ (Finset.univ : Finset (Option (Fin D))), z o ∈ K := by
    intro o ho; cases o with
    | none => exact hx₀
    | some i => exact hx i
  have hmem := hconv.sum_mem hw0 hw1 hz
  have he : ∑ o : Option (Fin D), w o • z o=(T y,y) := by
    rw [Fintype.sum_option]
    dsimp only [w,z,Option.elim]
    apply Prod.ext
    · simp only [Prod.fst_add,Prod.fst_sum,Prod.smul_fst]
      change (1-∑ i,lam y i) • x₀+∑ i,lam y i • x i=T y
      rw [hT]
      simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul]
      module
    · simp only [Prod.snd_add,Prod.snd_sum,Prod.smul_snd]
      change (1-∑ i,lam y i) • v₀+∑ i,lam y i • v i=y
      dsimp only [v]
      simp only [smul_add,smul_smul,Finset.sum_add_distrib,←Finset.sum_smul]
      have hh : ∀ i, lam y i*c=b.repr y i+2*R := by intro i; dsimp [lam]; field_simp
      simp_rw [hh,add_smul]
      rw [Finset.sum_add_distrib,b.sum_repr]
      have hsum : v₀+(∑ i : Fin D, (2*R) • b i)=0 := by
        dsimp only [v₀]
        rw [←Finset.sum_add_distrib]
        simp only [←add_smul,neg_mul,neg_add_cancel,zero_smul,Finset.sum_const_zero]
      calc
        _ = y+(v₀+∑ i : Fin D, (2*R) • b i) := by module
        _ = y := by rw [hsum,add_zero]
  rwa [he] at hmem


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



def gaussian (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (y : F) : ℝ := (Real.sqrt (2*Real.pi))^(-(finrank ℝ F : ℤ))*Real.exp (-‖y‖^2/2)

lemma gaussian_pos {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (y : F) : 0 < gaussian F y := by
  dsimp [gaussian]
  exact mul_pos (zpow_pos (Real.sqrt_pos.mpr (by positivity)) _) (Real.exp_pos _)



lemma gaussian_near {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 0 < m)
    {a y : F} (ha : ‖a‖ ≤ R) (hy : ‖y‖ ≤ R)
    (hya : dist y a ≤ R/(m : ℝ)^2) (hsmall : R^2/(m : ℝ)^2 ≤ 1) :
    Real.exp (-1)*gaussian F y ≤ gaussian F a ∧
      gaussian F a ≤ Real.exp 1*gaussian F y := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hdist : |‖a‖-‖y‖| ≤ R/(m : ℝ)^2 :=
    (abs_norm_sub_norm_le a y).trans (by simpa only [dist_comm,dist_eq_norm] using hya)
  have hsq : |‖a‖^2-‖y‖^2| ≤ 2 := by
    have he : ‖a‖^2-‖y‖^2=(‖a‖-‖y‖)*(‖a‖+‖y‖) := by ring
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    calc
      _ ≤ (R/(m : ℝ)^2)*(2*R) := mul_le_mul hdist (by linarith) (by positivity) (by positivity)
      _ = 2*(R^2/(m : ℝ)^2) := by ring
      _ ≤ 2 := by linarith
  have hp := abs_le.mp hsq
  have hlow : -1+-‖y‖^2/2 ≤ -‖a‖^2/2 := by linarith
  have hupp : -‖a‖^2/2 ≤ 1+-‖y‖^2/2 := by linarith
  have hb : 0 ≤ (Real.sqrt (2*Real.pi))^(-(finrank ℝ F : ℤ)) := by positivity
  constructor
  · have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlow) hb
    simpa only [Real.exp_add,gaussian,mul_left_comm] using hh
  · have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hupp) hb
    simpa only [Real.exp_add,gaussian,mul_left_comm] using hh




theorem finite_section_labels
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R V : ℝ} (hR : 0 < R) (hV : 0 < V) (hm : 2 ≤ finrank ℝ E)
    (hcenter : ∀ z : F, ‖z‖ ≤ 2*R → (0,z) ∈ K)
    (hlower : ∀ y : F, ‖y‖ ≤ R → V*gaussian F y/2 ≤ (μ (fiber K y)).toReal)
    (hsmall : R^2/(finrank ℝ E : ℝ)^2 ≤ 1) :
    ∃ S : Finset F, (S.card : ℝ) ≤ (3*(finrank ℝ E : ℝ)^2)^(finrank ℝ F) ∧
      ∃ J : F → Set E, (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (0 : E) ∈ J a ∧
        (μ (J a)).toReal=V*gaussian F a/8) ∧
      ∀ y : F, ‖y‖ ≤ R → ∃ a ∈ S, J a ⊆ fiber K y ∧
        (Real.exp (-1)/8)*V*gaussian F y ≤ (μ (J a)).toReal ∧
          (μ (J a)).toReal ≤ (Real.exp 1/8)*V*gaussian F y := by
  classical
  obtain ⟨S,hSc,hSn,hnet⟩ := ball_finite_net ν hR (show 1 ≤ finrank ℝ E by omega)
  let d : ℝ := 1-(finrank ℝ E : ℝ)^(-2 : ℤ)
  have hn2 : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hm
  have hd : 0 ≤ d := by
    dsimp [d]; norm_num only [zpow_neg, zpow_ofNat]
    have hh : 1 ≤ (finrank ℝ E : ℝ)^2 := by nlinarith
    exact sub_nonneg.mpr ((inv_le_one₀ (by positivity)).mpr hh)
  have hdata : ∀ a ∈ S, ∃ Ja : Set E, IsCompact Ja ∧ Convex ℝ Ja ∧ (0 : E) ∈ Ja ∧
      Ja ⊆ d • fiber K a ∧ (μ Ja).toReal=V*gaussian F a/8 := by
    intro a ha
    have haR := hSn a ha
    have hzero : (0 : E) ∈ fiber K a := hcenter a (by linarith)
    have hzero' : (0 : E) ∈ d • fiber K a := ⟨0,hzero,smul_zero _⟩
    apply prescribed_volume μ (by omega) ((fiber_compact hK a).smul d) ((fiber_convex hconv a).smul d) hzero'
      (by positivity [gaussian_pos a])
    rw [μ.addHaar_smul_of_nonneg hd,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg hd _)]
    have hh := shrink_power_half hm
    have hv := hlower a haR
    have hgp := gaussian_pos a
    have hhalf : (1/2 : ℝ)*(V*gaussian F a/2) ≤ d^finrank ℝ E*(μ (fiber K a)).toReal :=
      mul_le_mul hh hv (by positivity) (pow_nonneg hd _)
    nlinarith
  have hex : ∀ a : F, ∃ Ja : Set E, a ∈ S → IsCompact Ja ∧ Convex ℝ Ja ∧ (0 : E) ∈ Ja ∧
      Ja ⊆ d • fiber K a ∧ (μ Ja).toReal=V*gaussian F a/8 := by
    intro a
    by_cases ha : a ∈ S
    · exact ⟨(hdata a ha).choose,fun _ => (hdata a ha).choose_spec⟩
    · exact ⟨∅,fun hh => (ha hh).elim⟩
  choose J hJ using hex
  refine ⟨S,hSc,J,?_,?_⟩
  · intro a ha; exact ⟨(hJ a ha).1,(hJ a ha).2.1,(hJ a ha).2.2.1,(hJ a ha).2.2.2.2⟩
  · intro y hy
    obtain ⟨a,ha,hya⟩ := hnet y hy
    have hsub := nearby_fiber_inclusion hconv hR.le (show 1 ≤ finrank ℝ E by omega) hcenter (hSn a ha) hya
    have hg := gaussian_near hR.le (show 0 < finrank ℝ E by omega) (hSn a ha) hy hya hsmall
    refine ⟨a,ha,(hJ a ha).2.2.2.1.trans hsub,?_,?_⟩ <;>
      rw [(hJ a ha).2.2.2.2]
    · nlinarith [mul_le_mul_of_nonneg_left hg.1 hV.le]
    · nlinarith [mul_le_mul_of_nonneg_left hg.2 hV.le]


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



def sectionShear (T : F →ᵃ[ℝ] E) : (E × F) ≃ᵃ[ℝ] (E × F) :=
  AffineEquiv.ofBijective (φ := ((AffineMap.fst : (E × F) →ᵃ[ℝ] E)-T.comp AffineMap.snd).prod
    AffineMap.snd) (by
      constructor
      · rintro ⟨x,y⟩ ⟨x',y'⟩ h
        have hy : y=y' := congrArg Prod.snd h
        subst y'
        have hx : x-T y=x'-T y := congrArg Prod.fst h
        exact Prod.ext (by simpa using congrArg (fun z => z+T y) hx) rfl
      · rintro ⟨x,y⟩
        refine ⟨(x+T y,y),?_⟩
        change (x+T y-T y,y)=(x,y)
        simp)

@[simp] lemma sectionShear_apply (T : F →ᵃ[ℝ] E) (x : E) (y : F) :
    sectionShear T (x,y)=(x-T y,y) := rfl

lemma fiber_sectionShear (T : F →ᵃ[ℝ] E) (K : Set (E × F)) (y : F) :
    fiber (sectionShear T '' K) y=(fun x => x-T y) '' fiber K y := by
  ext x; constructor
  · rintro ⟨⟨u,v⟩,hK,he⟩
    have hv : v=y := congrArg Prod.snd he
    subst v
    exact ⟨u,hK,congrArg Prod.fst he⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨(u,y),hu,rfl⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

lemma fiber_sectionShear_measure {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [IsAddHaarMeasure μ]
    (T : F →ᵃ[ℝ] E) (K : Set (E × F)) (y : F) :
    μ (fiber (sectionShear T '' K) y)=μ (fiber K y) := by
  rw [fiber_sectionShear]
  simp only [sub_eq_add_neg,Set.image_add_right,measure_preimage_add_right]

lemma sectionShear_measure (μ : Measure E) [IsAddHaarMeasure μ]
    (ν : Measure F) [IsAddHaarMeasure ν]
    (T : F →ᵃ[ℝ] E) {K : Set (E × F)} (hK : IsCompact K) :
    (μ.prod ν) (sectionShear T '' K)=(μ.prod ν) K := by
  have hc := (sectionShear T).toAffineMap.continuous_of_finiteDimensional
  have hK' : IsCompact (sectionShear T '' K) := hK.image hc
  rw [Measure.prod_apply_symm hK'.measurableSet,Measure.prod_apply_symm hK.measurableSet]
  apply lintegral_congr
  intro y
  exact fiber_sectionShear_measure μ T K y



lemma convex_interior_of_measure_pos (μ : Measure E) [IsAddHaarMeasure μ]
    {J : Set E} (hconv : Convex ℝ J) (hpos : 0 < (μ J).toReal) :
    (interior J).Nonempty := by
  apply hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
  by_contra h
  have hn : μ J=0 := measure_mono_null (subset_affineSpan ℝ J) (μ.addHaar_affineSubspace _ h)
  rw [hn,ENNReal.toReal_zero] at hpos
  exact (lt_irrefl 0) hpos



theorem centered_affine_image {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R)
    (hproj : ∀ v : F, ‖v‖ ≤ 6*(D : ℝ)*R → ∃ x : E, (x,v) ∈ K) :
    ∃ e : (E × F) ≃ᵃ[ℝ] (E × F), IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧
      (μ.prod ν) (e '' K)=(μ.prod ν) K ∧
      (∀ y, μ (fiber (e '' K) y)=μ (fiber K y)) ∧
      (∀ y : F, ‖y‖ ≤ 2*R → (0,y) ∈ e '' K) := by
  obtain ⟨T,hT⟩ := affine_section_of_ball_projection hD b hunit hcoord hconv hR hproj
  refine ⟨sectionShear T,hK.image (sectionShear T).toAffineMap.continuous_of_finiteDimensional,
    hconv.affine_image (sectionShear T).toAffineMap,
    sectionShear_measure μ ν T hK,fun y => fiber_sectionShear_measure μ T K y,?_⟩
  intro y hy
  refine ⟨(T y,y),hT y hy,?_⟩
  simp


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma eventually_fiber_subset {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K)
    {y : F} {U : Set E} (hU : IsOpen U) (hyU : fiber K y ⊆ U) :
    ∀ᶠ z in 𝓝 y, fiber K z ⊆ U := by
  let A : Set F := Prod.snd '' (K ∩ Prod.fst ⁻¹' Uᶜ)
  have hA : IsClosed A := ((hK.inter_right (hU.isClosed_compl.preimage continuous_fst)).image continuous_snd).isClosed
  have hy : y ∈ Aᶜ := by
    rintro ⟨⟨x,z⟩,⟨hx,hxU⟩,he⟩
    change z=y at he
    subst z
    exact hxU (hyU hx)
  filter_upwards [hA.isOpen_compl.mem_nhds hy] with z hz
  intro x hx
  by_contra hxU
  exact hz ⟨(x,z),⟨hx,hxU⟩,rfl⟩

lemma upperSemicontinuous_fiber_measure [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [OuterRegular μ] {K : Set (E × F)} (hK : IsCompact K) :
    UpperSemicontinuous (fun y : F => μ (fiber K y)) := by
  intro y r hyr
  obtain ⟨U,hfU,hU,hμU⟩ := (fiber K y).exists_isOpen_lt_of_lt r hyr
  filter_upwards [eventually_fiber_subset hK hU hfU] with z hz
  exact (measure_mono hz).trans_lt hμU



lemma lower_bound_everywhere_of_ae {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : Measure F) [IsOpenPosMeasure ν]
    {f g : F → ℝ≥0∞} (hf : UpperSemicontinuous f) (hg : Continuous g)
    {U : Set F} (hU : IsOpen U) (hae : ∀ᵐ y ∂ν, y ∈ U → g y ≤ f y) :
    ∀ y ∈ U, g y ≤ f y := by
  intro y hy
  by_contra h
  have hfg : f y < g y := lt_of_not_ge h
  obtain ⟨q,hfq,hqg⟩ := exists_between hfg
  let V := U ∩ (f ⁻¹' Iio q) ∩ (g ⁻¹' Ioi q)
  have hV : IsOpen V := (hU.inter (hf.isOpen_preimage q)).inter (isOpen_Ioi.preimage hg)
  have hyV : y ∈ V := ⟨⟨hy,hfq⟩,hqg⟩
  obtain ⟨z,hz,hzV⟩ := (ν.dense_of_ae hae).exists_mem_open hV ⟨y,hyV⟩
  exact (not_lt_of_ge (hz hzV.1.1)) (hzV.1.2.trans hzV.2)




theorem canonical_marginal_lower [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [OuterRegular μ] (ν : Measure F) [IsOpenPosMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) {g : F → ℝ≥0∞} (hg : Continuous g)
    {S : ℝ} (hae : ∀ᵐ y ∂ν, ‖y‖ < S → g y ≤ μ (fiber K y)) :
    ∀ y : F, ‖y‖ < S → g y ≤ μ (fiber K y) := by
  exact lower_bound_everywhere_of_ae ν (upperSemicontinuous_fiber_measure μ hK) hg
    (isOpen_lt continuous_norm continuous_const) hae


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]





theorem gaussian_marginal_to_sections {D : ℕ} (hD : 0 < D)
    (b : Basis (Fin D) ℝ F) (hunit : ∀ i, ‖b i‖ ≤ 1)
    (hcoord : ∀ y : F, ∀ i, |b.repr y i| ≤ ‖y‖)
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    {K : Set (E × F)} (hK : IsCompact K) (hconv : Convex ℝ K)
    {R : ℝ} (hR : 0 < R) (hV : 0 < ((μ.prod ν) K).toReal)
    (hm : 2 ≤ finrank ℝ E)
    (hlower : ∀ y : F, ‖y‖ ≤ 6*(D : ℝ)*R →
      ((μ.prod ν) K).toReal*gaussian F y/2 ≤ (μ (fiber K y)).toReal)
    (hsmall : R^2/(finrank ℝ E : ℝ)^2 ≤ 1) :
    ∃ e : (E × F) ≃ᵃ[ℝ] (E × F), IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧
      (μ.prod ν) (e '' K)=(μ.prod ν) K ∧
      ∃ S : Finset F, (S.card : ℝ) ≤ (3*(finrank ℝ E : ℝ)^2)^D ∧
        ∃ J : F → Set E,
          (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (interior (J a)).Nonempty) ∧
          ∀ y : F, ‖y‖ ≤ R → ∃ a ∈ S, J a ⊆ fiber (e '' K) y ∧
            (Real.exp (-1)/8)*((μ.prod ν) (e '' K)).toReal*gaussian F y ≤ (μ (J a)).toReal ∧
            (μ (J a)).toReal ≤ (Real.exp 1/8)*((μ.prod ν) (e '' K)).toReal*gaussian F y := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  obtain ⟨e,heK,heconv,heμ,hef,hezero⟩ := centered_affine_image hD b hunit hcoord μ ν hK hconv hR (by
    intro y hy
    have hp : 0 < (μ (fiber K y)).toReal := (by positivity [gaussian_pos y] :
      0 < ((μ.prod ν) K).toReal*gaussian F y/2).trans_le (hlower y hy)
    by_contra hn
    push Not at hn
    have hempty : fiber K y=∅ := Set.eq_empty_iff_forall_notMem.mpr hn
    rw [hempty,measure_empty,ENNReal.toReal_zero] at hp
    exact (lt_irrefl 0) hp)
  obtain ⟨S,hSc,J,hJ,hlabels⟩ := finite_section_labels μ ν heK heconv hR hV hm hezero (by
    intro y hy
    rw [hef]
    exact hlower y (hy.trans (by nlinarith))) hsmall
  have hdim : finrank ℝ F=D := by simpa using Module.finrank_eq_card_basis b
  refine ⟨e,heK,heconv,heμ,S,by simpa only [hdim] using hSc,J,?_,?_⟩
  · intro a ha
    refine ⟨(hJ a ha).1,(hJ a ha).2.1,convex_interior_of_measure_pos μ (hJ a ha).2.1 ?_⟩
    rw [(hJ a ha).2.2.2]
    positivity [gaussian_pos a]
  · intro y hy
    simpa only [heμ] using hlabels y hy


end SingleLatticeCovering.Sections

end
end
end
end
end
end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory
open scoped BigOperators

lemma gaussian_toLp {D : ℕ} (y : Fin D → ℝ) :
    gaussian (EuclideanSpace ℝ (Fin D)) (WithLp.toLp 2 y)=Folded.gamma y := by
  classical
  unfold gaussian Folded.gamma Folded.gamma1
  rw [finrank_euclideanSpace_fin,EuclideanSpace.real_norm_sq_eq]
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← Real.exp_sum,zpow_neg,zpow_natCast]
  rw [div_eq_mul_inv,mul_comm]
  congr 2
  simp only [div_eq_mul_inv,Finset.sum_mul,Finset.sum_neg_distrib,neg_mul]

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory LatticeGeometry
open scoped BigOperators

lemma appendEquiv_measurePreserving (m D : ℕ) :
    MeasurePreserving (appendEquiv m D)
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin D → ℝ))) volume := by
  have h := (volume_preserving_arrowCongr' (finSumFinEquiv (m := m) (n := D))
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id volume)).comp
      (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin D => ℝ))
  have he : (fun t : (Fin m → ℝ) × (Fin D → ℝ) =>
      (MeasurableEquiv.arrowCongr' finSumFinEquiv (MeasurableEquiv.refl ℝ))
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin D => ℝ)).symm t))=
      appendEquiv m D := by
    funext t i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [MeasurableEquiv.arrowCongr',MeasurableEquiv.sumPiEquivProdPi,
        Equiv.arrowCongr',appendEquiv,Fin.appendEquiv]
  exact he ▸ h

def flatten (m D : ℕ) : ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)) ≃ₗ[ℝ] (Fin (m+D) → ℝ) :=
  ((LinearEquiv.refl ℝ (Fin m → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (Fin D → ℝ))).trans
    (appendEquiv m D)

@[simp] lemma flatten_apply (m D : ℕ) (x : Fin m → ℝ) (y : EuclideanSpace ℝ (Fin D)) :
    flatten m D (x,y)=Fin.append x (WithLp.ofLp y) := rfl

lemma flatten_measurePreserving (m D : ℕ) :
    MeasurePreserving (flatten m D) volume volume :=
  (appendEquiv_measurePreserving m D).comp
    ((MeasurePreserving.id (volume : Measure (Fin m → ℝ))).prod
      (PiLp.volume_preserving_ofLp (Fin D)))

lemma flatten_volume (m D : ℕ) {K : Set ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D))}
    (hK : IsCompact K) : volume (flatten m D '' K)=volume K := by
  have h := (flatten_measurePreserving m D).measure_preimage
    ((hK.image (flatten m D).toContinuousLinearEquiv.continuous).measurableSet.nullMeasurableSet)
  change volume ((flatten m D) ⁻¹' ((flatten m D) '' K))=volume ((flatten m D) '' K) at h
  rw [(flatten m D).injective.preimage_image] at h
  exact h.symm

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory Set
open scoped BigOperators



def coordinateFiber {m D : ℕ} (K : Set (Fin (m+D) → ℝ)) (y : Fin D → ℝ) :
    Set (Fin m → ℝ) := {x | Fin.append x y ∈ K}

lemma flatten_fiber {m D : ℕ} (K : Set (Fin (m+D) → ℝ)) (y : EuclideanSpace ℝ (Fin D)) :
    fiber ((flatten m D).symm '' K) y=coordinateFiber K (WithLp.ofLp y) := by
  ext x
  change (x,y) ∈ (flatten m D).symm '' K ↔ _
  constructor
  · rintro ⟨z,hz,hzxy⟩
    change flatten m D (x,y) ∈ K
    rw [←hzxy,(flatten m D).apply_symm_apply]
    exact hz
  · intro hx
    exact ⟨flatten m D (x,y),hx,(flatten m D).symm_apply_apply _⟩



theorem coordinate_marginal_to_labels {m D : ℕ} (hm : 2 ≤ m) (hD : 0 < D)
    {K : Set (Fin (m+D) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) {R : ℝ} (hR : 0 < R)
    (hsmall : R^2/(m : ℝ)^2 ≤ 1)
    (hlower : ∀ y : Fin D → ℝ, ‖WithLp.toLp 2 y‖ ≤ 6*(D : ℝ)*R →
      (volume K).toReal*Folded.gamma y/2 ≤ (volume (coordinateFiber K y)).toReal) :
    ∃ e : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ),
      IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ volume (e '' K)=volume K ∧
      ∃ S : Finset (EuclideanSpace ℝ (Fin D)), (S.card : ℝ) ≤ (3*(m : ℝ)^2)^D ∧
        ∃ J : EuclideanSpace ℝ (Fin D) → Set (Fin m → ℝ),
          (∀ a ∈ S, IsCompact (J a) ∧ Convex ℝ (J a) ∧ (interior (J a)).Nonempty) ∧
          ∀ y : Fin D → ℝ, (∑ j, (y j)^2) ≤ R^2 → ∃ a ∈ S,
            (∀ x ∈ J a, Fin.append x y ∈ e '' K) ∧
            (Real.exp (-1)/8)*(volume (e '' K)).toReal*Folded.gamma y ≤ (volume (J a)).toReal ∧
            (volume (J a)).toReal ≤ (Real.exp 1/8)*(volume (e '' K)).toReal*Folded.gamma y := by
  let f := flatten m D
  let Kp : Set ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)) := f.symm '' K
  have hKp : IsCompact Kp := hK.image f.symm.toContinuousLinearEquiv.continuous
  have hconvp : Convex ℝ Kp := hconv.linear_image f.symm.toLinearMap
  have hflat : f '' Kp=K := by dsimp [Kp]; exact f.image_symm_image K
  have hvolp : volume Kp=volume K := by rw [←flatten_volume m D hKp]; exact congrArg volume hflat
  let b := EuclideanSpace.basisFun (Fin D) ℝ
  have hunit : ∀ i, ‖b.toBasis i‖ ≤ 1 := by intro i; exact (b.orthonormal.1 i).le
  have hcoord : ∀ y : EuclideanSpace ℝ (Fin D), ∀ i, |b.toBasis.repr y i| ≤ ‖y‖ := by
    intro y i
    rw [OrthonormalBasis.coe_toBasis_repr_apply]
    simpa only [Real.norm_eq_abs,b,EuclideanSpace.basisFun_repr] using PiLp.norm_apply_le y i
  obtain ⟨e,heK,heconv,hevol,S,hSc,J,hJ,hlabels⟩ := gaussian_marginal_to_sections hD b.toBasis hunit hcoord
    (volume : Measure (Fin m → ℝ)) (volume : Measure (EuclideanSpace ℝ (Fin D))) hKp hconvp hR
    (by simpa only [←Measure.volume_eq_prod,hvolp] using hV)
    (by simpa using hm) (by
      intro y hy
      have hh := hlower y.ofLp (by simpa using hy)
      simpa only [←Measure.volume_eq_prod,hvolp,Kp,f,flatten_fiber,←gaussian_toLp,WithLp.toLp_ofLp] using hh)
    (by simpa using hsmall)
  let e' : (Fin (m+D) → ℝ) ≃ᵃ[ℝ] (Fin (m+D) → ℝ) :=
    (f.symm.toAffineEquiv.trans e).trans f.toAffineEquiv
  have he'image : e' '' K=f '' (e '' Kp) := by
    change (fun x => f (e (f.symm x))) '' K = _
    simp only [Kp,Set.image_image]
  have hevol' : volume (e '' Kp)=volume Kp := by simpa only [←Measure.volume_eq_prod] using hevol
  have he'vol : volume (e' '' K)=volume K := by
    rw [he'image,flatten_volume m D heK]
    exact hevol'.trans hvolp
  refine ⟨e',?_,?_,he'vol,S,?_,J,hJ,?_⟩
  · rw [he'image]; exact heK.image f.toContinuousLinearEquiv.continuous
  · rw [he'image]; exact heconv.linear_image f.toLinearMap
  · simpa using hSc
  · intro y hy
    have hynorm : ‖WithLp.toLp 2 y‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR.le).mp
      simpa only [EuclideanSpace.real_norm_sq_eq] using hy
    obtain ⟨a,ha,hsub,hl,hu⟩ := hlabels (WithLp.toLp 2 y) hynorm
    refine ⟨a,ha,?_,?_,?_⟩
    · intro x hx
      rw [he'image]
      exact ⟨(x,WithLp.toLp 2 y),hsub hx,rfl⟩
    · rw [←gaussian_toLp,he'vol,←hvolp]
      simpa only [←Measure.volume_eq_prod,hevol'] using hl
    · rw [←gaussian_toLp,he'vol,←hvolp]
      simpa only [←Measure.volume_eq_prod,hevol'] using hu


end SingleLatticeCovering.Sections

end
end

section



noncomputable section
open Real Filter Topology Asymptotics

end
end
end

end OAI
