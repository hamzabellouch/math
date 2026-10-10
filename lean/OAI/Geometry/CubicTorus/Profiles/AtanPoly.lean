import Mathlib
import OAI.Geometry.CubicTorus.Profiles.NestingBaseline

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_sharp_flux {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (b : Fin 3 →Bool),
      IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,
        quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E →
        0≤H ∧ Nesting.lambda*H*V+2*(∫ s in (0 : ℝ)..
          (axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal,
            sharpSectionWeight H s)≤(perimeter E).toReal := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV' hmin).resolve_right (fun h ↦ hstd h.2.2)
  obtain ⟨b,hd⟩ := isMinimizerAt_octant_downset hV' hmin hc hR
  obtain ⟨μ,H,hμ,hCMC,ha,_⟩ := isMinimizerAt_nonstandard_integrated_flux hV hmin hstd hR
  refine ⟨μ,H,b,hμ,hCMC,hd,ha,fun i hv ↦ ?_⟩
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hvF : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [ho]
  have hμF := hμ.congr_ae hFE.symm
  have hHF := Periodic.coordinateCMC_of_global hμF hCMC
  have hf := isMinimizerAt_missing_neighbor_flux_unrestricted hV' hF hmF hRF b hdF hμF hHF i hvF
  have hH0 : 0≤H := by
    have hh := axialTransverseMass_nonneg μ i
    rw [hf] at hh
    exact nonneg_of_mul_nonneg_left hh hV.1
  refine ⟨hH0,?_⟩
  have hh := isMinimizerAt_missing_neighbor_sharp_area_flux hV' hF hmF hRF b hdF hμF hH0 hHF i (ha i) hvF
  rwa [ho,perimeter_congr_ae hFE] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_three_vertex_nesting {E : Set Torus}
    (hmin : IsMinimizerAt (1/Real.pi) E) (hstd : ¬StandardRegionAt (1/Real.pi) E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (b : Fin 3 →Bool),
      IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,
        quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E →
        (∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) →
        let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
        (perimeter E).toReal/2 ≤ 1 ∧
        Real.sqrt (Real.pi*(1-s))/s ≤ H/2 ∧ H/2 ≤ Real.pi*(1-s^2) ∧
        s∈Ioo (107/200 : ℝ) (89/100 : ℝ) ∧ H/2∈Icc (16/25 : ℝ) (9/4 : ℝ) ∧ Shape.t (H/2) ≤ s ∧
        nestingBaseline (H/2) ≤ (perimeter E).toReal/2-1 ∧
        (H/2∈Icc (51/50 : ℝ) (81/50 : ℝ) →
          nestingBaseline (H/2)+nestingGainInfimum (H/2) ≤ (perimeter E).toReal/2-1) := by
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) 1 := ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hVh : (1/Real.pi)∈Ioc (0 : ℝ) (1/2) := ⟨hV.1,by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]⟩
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV hmin).resolve_right (fun h ↦ hstd h.2.2)
  obtain ⟨μ,H,b,hμ,hCMC,hd,ha,hf⟩ := isMinimizerAt_nonstandard_sharp_flux hVh hmin hstd hR
  refine ⟨μ,H,b,hμ,hCMC,hd,ha,fun i hv haxes ↦ ?_⟩
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [ho]
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hvF : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [ho]
  have haxesF : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative F := by rwa [ho]
  have hμF := hμ.congr_ae hFE.symm
  obtain ⟨hA,hlo,hhi,hs,hcurv,ht⟩ := isMinimizerAt_three_vertex_parameters hF hmF hcF hRF b hdF hμF hCMC i (ha i) hvF haxesF
  simp only [ho,perimeter_congr_ae hFE] at hA hlo hhi hs hcurv ht
  refine ⟨hA,hlo,hhi,hs,hcurv,ht,?_,fun hH ↦ ?_⟩
  · have hh0 : 0 ≤ H/2 := by linarith [hcurv.1]
    have hb := nestingBaseline_slack hh0 ht
    rw [show 2*(H/2)=H by ring] at hb
    have hflux := (hf i hv).2
    change Nesting.lambda*H*(1/Real.pi)+2*(∫ v in (0 : ℝ)..
      volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle)),sharpSectionWeight H v)≤(perimeter E).toReal at hflux
    have he : Nesting.lambda*H*(1/Real.pi)=2*(Nesting.lambda*(H/2)/Real.pi) := by ring
    rw [he] at hflux
    have hnon := mul_nonneg (show 0 ≤ Nesting.ell by norm_num [Nesting.ell]) (sub_nonneg.mpr ht)
    linarith
  ·
    obtain ⟨hout,hin⟩ := isMinimizerAt_three_vertex_bottom hV hmF hcF hRF b hdF i hvF haxesF
    have hh := isMinimizerAt_nesting_area_bound hF hmF hRF b hdF hμF hCMC i (ha i) hvF hout (hin 0) (hin 1) hH
    rwa [perimeter_congr_ae hFE] at hh

end CubicTorus

end
end

section

namespace ReusedScalar205

noncomputable section

namespace CubicTorus.Arithmetic
open Set Filter
open scoped Topology

def atanPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ↑(2 * i + 1)

lemma atan_terms_antitone {x : ℝ} (hx : x ∈ Icc 0 1) :
    Antitone (fun n : ℕ ↦ x ^ (2 * n + 1) / ↑(2 * n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  calc
    _ ≤ x ^ (2 * n + 1) / ↑(2 * (n + 1) + 1) :=
      div_le_div_of_nonneg_right (pow_le_pow_of_le_one hx.1 hx.2 (by omega)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg hx.1 _) (by positivity) (by norm_cast; omega)

lemma atanPoly_bounds {x : ℝ} (hx : x ∈ Ico 0 1) (n : ℕ) :
    atanPoly (2 * n) x ≤ Real.arctan x ∧ Real.arctan x ≤ atanPoly (2 * n + 1) x := by
  have hs := (Real.hasSum_arctan (show ‖x‖ < 1 by simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2)).tendsto_sum_nat
  have ha := atan_terms_antitone ⟨hx.1, hx.2.le⟩
  have heq : (fun k : ℕ ↦ ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / ↑(2 * i + 1))) =
      (fun k : ℕ ↦ ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ↑(2 * i + 1)) := by
    funext k
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← heq] at hs
  exact ⟨by simpa only [atanPoly, mul_div_assoc] using ha.alternating_series_le_tendsto hs n,
    by simpa only [atanPoly, mul_div_assoc] using ha.tendsto_le_alternating_series hs n⟩

def atanHalf (x : ℝ) : ℝ := x / (1 + Real.sqrt (1 + x ^ 2))

lemma atanHalf_spec {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ atanHalf x ∧ atanHalf x < 1 ∧ 2 * Real.arctan (atanHalf x) = Real.arctan x := by
  have hs0 := Real.sqrt_nonneg (1 + x ^ 2)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + x ^ 2)
  have hsx : x < Real.sqrt (1 + x ^ 2) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + x ^ 2) := by positivity
  have hz0 : 0 ≤ atanHalf x := div_nonneg hx hd.le
  have hz1 : atanHalf x < 1 := (div_lt_one hd).2 (by linarith)
  refine ⟨hz0, hz1, ?_⟩
  rw [Real.two_mul_arctan (by linarith) hz1]
  congr 1
  have hzden : 1 - atanHalf x ^ 2 ≠ 0 := by
    have := (sq_lt_sq₀ hz0 (by norm_num : (0 : ℝ) ≤ 1)).2 hz1
    nlinarith
  apply (div_eq_iff hzden).2
  unfold atanHalf
  field_simp
  nlinarith

def asinQuarterArg (z : ℝ) : ℝ :=
  atanHalf (z / (1 + Real.sqrt (1 - z ^ 2)))

lemma arcsin_quarter {z : ℝ} (hz : z ∈ Ico 0 1) :
    0 ≤ asinQuarterArg z ∧ asinQuarterArg z < 1 ∧
      Real.arcsin z = 4 * Real.arctan (asinQuarterArg z) := by
  let b := Real.sqrt (1 - z ^ 2)
  have hsq : z ^ 2 < 1 := by simpa only [one_pow] using (sq_lt_sq₀ hz.1 (by norm_num : (0 : ℝ) ≤ 1)).2 hz.2
  have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
  have hb : b ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
  let k := z / (1 + b)
  have hk0 : 0 ≤ k := div_nonneg hz.1 (by positivity)
  have hk1 : k < 1 := (div_lt_one (by positivity)).2 (by linarith [hz.2])
  obtain ⟨hv0, hv1, hv⟩ := atanHalf_spec hk0
  refine ⟨hv0, hv1, ?_⟩
  change Real.arcsin z = 4 * Real.arctan (atanHalf k)
  have hk : 2 * Real.arctan k = Real.arcsin z := by
    rw [Real.two_mul_arctan (by linarith) hk1, Real.arcsin_eq_arctan ⟨by linarith [hz.1], hz.2⟩]
    congr 1
    change 2 * k / (1 - k ^ 2) = z / b
    have hd : 1 - k ^ 2 ≠ 0 := by nlinarith
    apply (div_eq_div_iff hd hb0.ne').2
    dsimp [k]
    field_simp
    have hbz := congrArg (fun t : ℝ ↦ z * t) hb
    nlinarith only [hbz]
  linarith

lemma arcsin_enclosure {z l u : ℝ} (hz : z ∈ Ico 0 1)
    (hl : l ∈ Ico 0 1) (hu : u ∈ Ico 0 1)
    (hlo : l ≤ asinQuarterArg z) (hhi : asinQuarterArg z ≤ u) (n : ℕ) :
    4 * atanPoly (2 * n) l ≤ Real.arcsin z ∧
      Real.arcsin z ≤ 4 * atanPoly (2 * n + 1) u := by
  rw [(arcsin_quarter hz).2.2]
  exact ⟨mul_le_mul_of_nonneg_left ((atanPoly_bounds hl n).1.trans (Real.arctan_mono hlo)) (by norm_num),
    mul_le_mul_of_nonneg_left ((Real.arctan_mono hhi).trans (atanPoly_bounds hu n).2) (by norm_num)⟩

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic

def Encl (x l u : ℝ) : Prop := l ≤ x ∧ x ≤ u

lemma Encl.exact (x : ℝ) : Encl x x x := ⟨le_rfl, le_rfl⟩

lemma Encl.widen {x l u L U : ℝ} (hx : Encl x l u) (hL : L ≤ l) (hU : u ≤ U) : Encl x L U :=
  ⟨hL.trans hx.1, hx.2.trans hU⟩

lemma Encl.neg {x l u L U : ℝ} (hx : Encl x l u) (hL : L ≤ -u) (hU : -l ≤ U) : Encl (-x) L U :=
  ⟨hL.trans (neg_le_neg hx.2), (neg_le_neg hx.1).trans hU⟩

lemma Encl.add {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ l + p) (hU : u + q ≤ U) : Encl (x + y) L U :=
  ⟨hL.trans (add_le_add hx.1 hy.1), (add_le_add hx.2 hy.2).trans hU⟩

lemma Encl.sub {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ l - q) (hU : u - p ≤ U) : Encl (x - y) L U :=
  ⟨hL.trans (sub_le_sub hx.1 hy.2), (sub_le_sub hx.2 hy.1).trans hU⟩

lemma Encl.mul_nonneg {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hl : 0 ≤ l) (hp : 0 ≤ p) (hL : L ≤ l * p) (hU : u * q ≤ U) : Encl (x * y) L U := by
  refine ⟨hL.trans (mul_le_mul hx.1 hy.1 hp (hl.trans hx.1)), ?_⟩
  exact (mul_le_mul hx.2 hy.2 (hp.trans hy.1) (hl.trans (hx.1.trans hx.2))).trans hU

lemma Encl.square {x l u L U : ℝ} (hx : Encl x l u) (hl : 0 ≤ l)
    (hL : L ≤ l ^ 2) (hU : u ^ 2 ≤ U) : Encl (x ^ 2) L U := by
  exact ⟨hL.trans (pow_le_pow_left₀ hl hx.1 2), (pow_le_pow_left₀ (hl.trans hx.1) hx.2 2).trans hU⟩

lemma Encl.div_nonneg {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hl : 0 ≤ l) (hp : 0 < p) (hL : L * q ≤ l) (hU : u ≤ U * p) : Encl (x / y) L U := by
  have hy0 := hp.trans_le hy.1
  have hq0 := hy0.trans_le hy.2
  have hu0 := hl.trans (hx.1.trans hx.2)
  have hU0 : 0 ≤ U := by nlinarith
  constructor
  · calc
      L ≤ l / q := (le_div_iff₀ hq0).2 hL
      _ ≤ x / y := div_le_div₀ (hl.trans hx.1) hx.1 hy0 hy.2
  · exact (div_le_iff₀ hy0).2 (hx.2.trans (hU.trans (mul_le_mul_of_nonneg_left hy.1 hU0)))

lemma Encl.sqrt {x l u L U : ℝ} (hx : Encl x l u)
    (hL0 : 0 ≤ L) (hU0 : 0 ≤ U) (hL : L ^ 2 ≤ l) (hU : u ≤ U ^ 2) : Encl (Real.sqrt x) L U := by
  have hx0 : 0 ≤ x := (sq_nonneg L).trans (hL.trans hx.1)
  exact ⟨(Real.le_sqrt hL0 hx0).2 (hL.trans hx.1), (Real.sqrt_le_iff).2 ⟨hU0, hx.2.trans hU⟩⟩

lemma Encl.min {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hL : L ≤ min l p) (hU : min u q ≤ U) : Encl (min x y) L U :=
  ⟨hL.trans (min_le_min hx.1 hy.1), (min_le_min hx.2 hy.2).trans hU⟩

lemma Encl.arcsin {z a b L U : ℝ} (hz : z ∈ Set.Ico 0 1)
    (ha : a ∈ Set.Ico 0 1) (hb : b ∈ Set.Ico 0 1)
    (harg : Encl (asinQuarterArg z) a b) (n : ℕ)
    (hL : L ≤ 4 * atanPoly (2 * n) a) (hU : 4 * atanPoly (2 * n + 1) b ≤ U) :
    Encl (Real.arcsin z) L U :=
  (arcsin_enclosure hz ha hb harg.1 harg.2 n).imp (hL.trans ·) (·.trans hU)

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic

lemma Encl.mul_nonpos_nonneg {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hu : u ≤ 0) (hp : 0 ≤ p) (hL : L ≤ l * q) (hU : u * p ≤ U) : Encl (x * y) L U := by
  have hn : Encl (-x) (-u) (-l) := hx.neg le_rfl le_rfl
  have hm := hn.mul_nonneg hy (neg_nonneg.2 hu) hp (L := -U) (U := -L)
    (by nlinarith only [hU]) (by nlinarith only [hL])
  simpa only [neg_mul, neg_neg] using hm.neg le_rfl le_rfl

lemma Encl.mul_nonneg_nonpos {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hl : 0 ≤ l) (hq : q ≤ 0) (hL : L ≤ u * p) (hU : l * q ≤ U) : Encl (x * y) L U := by
  simpa only [mul_comm] using hy.mul_nonpos_nonneg hx hq hl (by simpa only [mul_comm] using hL)
    (by simpa only [mul_comm] using hU)

lemma Encl.mul_nonpos {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hu : u ≤ 0) (hq : q ≤ 0) (hL : L ≤ u * q) (hU : l * p ≤ U) : Encl (x * y) L U := by
  have hn : Encl (-x) (-u) (-l) := hx.neg le_rfl le_rfl
  have hn' : Encl (-y) (-q) (-p) := hy.neg le_rfl le_rfl
  simpa only [neg_mul_neg] using hn.mul_nonneg hn' (neg_nonneg.2 hu) (neg_nonneg.2 hq)
    (by simpa only [neg_mul_neg] using hL) (by simpa only [neg_mul_neg] using hU)

lemma Encl.div_nonpos {x y l u p q L U : ℝ} (hx : Encl x l u) (hy : Encl y p q)
    (hu : u ≤ 0) (hp : 0 < p) (hL : L * p ≤ l) (hU : u ≤ U * q) : Encl (x / y) L U := by
  have hn : Encl (-x) (-u) (-l) := hx.neg le_rfl le_rfl
  have hm := hn.div_nonneg hy (neg_nonneg.2 hu) hp (L := -U) (U := -L)
    (by nlinarith only [hU]) (by nlinarith only [hL])
  simpa only [neg_div, neg_neg] using hm.neg le_rfl le_rfl

end CubicTorus.Arithmetic

namespace CubicTorus.Arithmetic
lemma Encl.pow {x l u L U : ℝ} (hx : Encl x l u) (hl : 0 ≤ l) (n : ℕ)
    (hL : L ≤ l ^ n) (hU : u ^ n ≤ U) : Encl (x ^ n) L U :=
  ⟨hL.trans (pow_le_pow_left₀ hl hx.1 n), (pow_le_pow_left₀ (hl.trans hx.1) hx.2 n).trans hU⟩
end CubicTorus.Arithmetic

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

end CubicTorus.Shape
end
end
end
end ReusedScalar205
end
end

end OAI
