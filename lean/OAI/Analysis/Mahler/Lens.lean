import OAI.Analysis.Mahler.Medians
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.PSeries

namespace OAI

noncomputable section

namespace SymmetricMahler

section
open Set Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SignedUnitRepresentation

def ofFintype {ι : Type*} [Fintype ι] {q : E} {a T : ℝ}
    (b : ι → E) (s w : ι → ℝ) (hb : ∀ i, ‖b i‖ ≤ 1)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hw : ∀ i, 0 ≤ w i)
    (hq : ∑ i, w i • b i = q) (ha : ∑ i, w i*s i = a) (hT : ∑ i, w i = T) :
    SignedUnitRepresentation q a T where
  size := Fintype.card ι
  point := b ∘ (Fintype.equivFin ι).symm
  sign := s ∘ (Fintype.equivFin ι).symm
  weight := w ∘ (Fintype.equivFin ι).symm
  point_norm i := hb _
  sign_eq i := hs _
  weight_nonneg i := hw _
  sum_point := by
    exact ((Fintype.equivFin ι).symm.sum_comp (fun i => w i • b i)).trans hq
  sum_sign := by
    exact ((Fintype.equivFin ι).symm.sum_comp (fun i => w i*s i)).trans ha
  sum_weight := by simpa only [Function.comp_apply, Equiv.sum_comp] using hT

lemma ofFintype_cost {ι : Type*} [Fintype ι] {q : E} {a T : ℝ}
    (b : ι → E) (s w : ι → ℝ) (hb : ∀ i, ‖b i‖ ≤ 1)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (hw : ∀ i, 0 ≤ w i)
    (hq : ∑ i, w i • b i = q) (ha : ∑ i, w i*s i = a) (hT : ∑ i, w i = T)
    (ell : ℝ → ℝ) (u : E →L[ℝ] ℝ) (δ : ℝ) :
    (ofFintype b s w hb hs hw hq ha hT).cost ell u δ =
      ∑ i, w i * liftedLensCost ell u δ (b i) (s i) := by
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => w i * liftedLensCost ell u δ (b i) (s i))
end SignedUnitRepresentation

lemma lifted_cost_eq {ell : ℝ → ℝ} (heven : ∀ t, ell (-t) = ell t)
    (u : E →L[ℝ] ℝ) (δ : ℝ) (b : E) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    liftedLensCost ell u δ b s = ell (δ*u b+(1-δ)*s) := by
  rcases hs with rfl | rfl
  · dsimp [liftedLensCost]
    congr 1
    ring
  · rw [liftedLensCost, ← heven (δ*u b+(1-δ)*(-1))]
    congr 1; ring

lemma lens_face_interval (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) {b : E} (hb : ‖b‖ ≤ 1)
    {s : ℝ} (hs : |s| ≤ 1) : δ*u b+(1-δ)*s ∈ Icc (-1:ℝ) 1 := by
  have hub : |u b| ≤ 1 := (u.le_opNorm b).trans
    ((mul_le_mul hu hb (norm_nonneg b) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _))
  have hbound : |δ*u b+(1-δ)*s| ≤ 1 := by
    calc
      _ ≤ |δ*u b|+|(1-δ)*s| := abs_add_le _ _
      _ = δ*|u b|+(1-δ)*|s| := by rw [abs_mul,abs_mul,abs_of_nonneg hδ,abs_of_nonneg (sub_nonneg.mpr hδ1)]
      _ ≤ δ*1+(1-δ)*1 := add_le_add (mul_le_mul_of_nonneg_left hub hδ)
        (mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hδ1))
      _ = 1 := by ring
  exact abs_le.mp hbound

theorem optimal_signed_of_common_lens
    {ell : ℝ → ℝ} (heven : ∀ t, ell (-t) = ell t)
    (hconcave : ConcaveOn ℝ (Icc (-1:ℝ) 1) ell)
    (u : E →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {q : E} {a T : ℝ} (hT : 0 < T) (L : (E × ℝ) →ₗ[ℝ] ℝ)
    (hbound : ∀ b : E, ‖b‖ ≤ 1 → ∀ s : ℝ, |s| ≤ 1 →
      L (b,s) ≤ ell (δ*u b+(1-δ)*s))
    (hcontact : (T⁻¹ • q, T⁻¹*a) ∈ convexHull ℝ
      {z : E × ℝ | ‖z.1‖ ≤ 1 ∧ |z.2| ≤ 1 ∧ L z = ell (δ*u z.1+(1-δ)*z.2)}) :
    ∃ R : SignedUnitRepresentation q a T,
      ∀ U : ℝ, ∀ S : SignedUnitRepresentation q a U, R.cost ell u δ ≤ S.cost ell u δ := by
  classical
  obtain ⟨ι,_,z,w,hz,_,hw,hw1,heq⟩ := eq_pos_convex_span_of_mem_convexHull hcontact
  have hz' (i : ι) := hz (mem_range_self i)
  let b : ι × Fin 2 → E := fun i => (z i.1).1
  let s : ι × Fin 2 → ℝ := fun i => if i.2 = 0 then 1 else -1
  let v : ι × Fin 2 → ℝ := fun i => T*w i.1 * ((1+s i*(z i.1).2)/2)
  have hb (i : ι × Fin 2) : ‖b i‖ ≤ 1 := (hz' i.1).1
  have hs (i : ι × Fin 2) : s i = 1 ∨ s i = -1 := by
    dsimp [s]; split <;> simp
  have hv (i : ι × Fin 2) : 0 ≤ v i := by
    have hzi := abs_le.mp (hz' i.1).2.1
    rcases hs i with hh | hh <;> dsimp only [v] <;> rw [hh] <;>
      exact mul_nonneg (mul_nonneg hT.le (hw _).le) (by linarith)
  have heq1 : ∑ i, w i • (z i).1 = T⁻¹ • q := by
    simpa only [Prod.fst_sum,Prod.smul_fst] using congrArg Prod.fst heq
  have heq2 : ∑ i, w i*(z i).2 = T⁻¹*a := by
    simpa only [Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd heq
  have hvq : ∑ i, v i • b i = q := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,b,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul]
    simp_rw [← add_smul, show ∀ i, T*w i*((1+(z i).2)/2)+T*w i*((1+ -(z i).2)/2) = T*w i by intro i; ring]
    simp_rw [mul_smul]
    rw [← smul_sum, heq1, smul_smul, mul_inv_cancel₀ hT.ne',one_smul]
  have hva : ∑ i, v i*s i = a := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul,mul_one,mul_neg_one]
    simp_rw [show ∀ i, T*w i*((1+(z i).2)/2)+ -(T*w i*((1+ -(z i).2)/2)) = T*(w i*(z i).2) by intro i; ring]
    rw [← mul_sum,heq2,← mul_assoc,mul_inv_cancel₀ hT.ne',one_mul]
  have hvT : ∑ i, v i = T := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,v,s,ite_true,one_ne_zero,ite_false,one_mul,neg_one_mul]
    simp_rw [show ∀ i, T*w i*((1+(z i).2)/2)+T*w i*((1+ -(z i).2)/2) = T*w i by intro i; ring]
    rw [← mul_sum,hw1,mul_one]
  let R := SignedUnitRepresentation.ofFintype b s v hb hs hv hvq hva hvT
  have hR : R.cost ell u δ ≤ L (q,a) := by
    rw [SignedUnitRepresentation.ofFintype_cost]
    have hli (i : ι) :
        ((1+(z i).2)/2)*ell (δ*u (z i).1+(1-δ)) +
        ((1-(z i).2)/2)*ell (δ*u (z i).1-(1-δ)) ≤ L (z i) := by
      have hzi := abs_le.mp (hz' i).2.1
      have hh := hconcave.2
        (lens_face_interval u hu hδ hδ1 (hz' i).1 (by norm_num : |(1:ℝ)| ≤ 1))
        (lens_face_interval u hu hδ hδ1 (hz' i).1 (by norm_num : |(-1:ℝ)| ≤ 1))
        (show 0 ≤ (1+(z i).2)/2 by linarith) (show 0 ≤ (1-(z i).2)/2 by linarith)
        (show (1+(z i).2)/2+(1-(z i).2)/2 = 1 by ring)
      rw [(hz' i).2.2]
      simp only [smul_eq_mul, mul_one, mul_neg_one, ← sub_eq_add_neg] at hh
      convert hh using 1
      congr 1
      ring
    calc
      _ = ∑ i, T*w i*(((1+(z i).2)/2)*ell (δ*u (z i).1+(1-δ)) +
          ((1-(z i).2)/2)*ell (δ*u (z i).1-(1-δ))) := by
        simp_rw [lifted_cost_eq heven u δ _ (hs _)]
        rw [Fintype.sum_prod_type]
        apply sum_congr rfl
        intro i hi
        simp only [Fin.sum_univ_two,b,v,s,ite_true,one_ne_zero,ite_false,one_mul,mul_one,neg_one_mul,mul_neg_one,← sub_eq_add_neg]
        ring
      _ ≤ ∑ i, T*w i * L (z i) := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hli i) (mul_nonneg hT.le (hw i).le))
      _ = L (q,a) := by
        have hh : ∑ i, (T*w i) • z i = (q,a) := by
          simp_rw [mul_smul]
          rw [← smul_sum,heq]
          ext <;> simp [smul_smul,hT.ne']
        simpa only [map_sum,map_smul,smul_eq_mul] using congrArg L hh
  refine ⟨R,?_⟩
  intro U S
  apply hR.trans
  have hsum : ∑ i, S.weight i • (S.point i,S.sign i) = (q,a) := by
    ext
    · simpa only [Prod.fst_sum,Prod.smul_fst] using S.sum_point
    · simpa only [Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using S.sum_sign
  calc
    L (q,a) = ∑ i, S.weight i * L (S.point i,S.sign i) := by rw [← hsum,map_sum]; simp only [map_smul,smul_eq_mul]
    _ ≤ S.cost ell u δ := by
      apply sum_le_sum
      intro i hi
      rw [lifted_cost_eq heven u δ _ (S.sign_eq i)]
      apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
      apply hbound _ (S.point_norm i)
      rcases S.sign_eq i with hh | hh <;> rw [hh] <;> norm_num

end

open Set Filter MeasureTheory
open scoped Topology ENNReal Pointwise

lemma unconditional_stripMassBound {n N : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 2 ≤ m) : StripMassBound A m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply stripMassBound_of_special_gram_mass A hm
  have hspecial := euclideanSpecial_massHypotheses A (by omega) hA hm
  have hvalue := hspecial.homogeneousSphereFlux_value
  have hregular (j : ℕ) : SpecialRegularMassBound A m j := by
    apply special_regular_mass_of_source_flux_limit A hA hm j
    simpa only [hvalue] using hspecial.sourceCoordinateFlux_limit
  have h := Mahler.massIntegral_lower_of_sublevels (euclideanStripDomain A)
    (euclideanSpecialMap A m) m tendsto_stripRegularLevel
    (fun j => (stripRegularLevel_mem j).2.le) hregular
  rwa [euclideanSpecial_massIntegral (volume_preserving_complex_ofLp (k+1)) A m] at h

lemma stripMap_volume_lower {n N : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    {m : ℕ} (hm : 2 ≤ m) :
    ENNReal.ofReal ((4:ℝ)^n / (Nat.factorial n : ℝ)) ≤
      volume (stripMap A m '' stripSublevel A m) := by
  have hmass := unconditional_stripMassBound hn A hA hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpm : 0 < Real.pi*(m:ℝ) := mul_pos Real.pi_pos hm0
  have hc : 0 ≤ (4/(Real.pi*(m:ℝ)))^n := by positivity
  have he : (4/(Real.pi*(m:ℝ)))^n * ((Real.pi*(m:ℝ))^n/(Nat.factorial n:ℝ)) =
      (4:ℝ)^n/(Nat.factorial n:ℝ) := by
    rw [← mul_div_assoc, ← mul_pow, div_mul_cancel₀ _ hpm.ne']
  rw [stripMap_volume_eq A hA hm]
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ = ENNReal.ofReal ((4/(Real.pi*(m:ℝ)))^n) *
        ENNReal.ofReal ((Real.pi*(m:ℝ))^n/(Nat.factorial n:ℝ)) := by
          rw [← ENNReal.ofReal_mul hc, he]
    _ ≤ _ := mul_le_mul le_rfl hmass (by positivity) (by positivity)

end SymmetricMahler

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

lemma nonempty_inter_of_small_deficit {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {A S U : Set α} (hS : S ⊆ A) (hU : U ⊆ A)
    (hUm : MeasurableSet U) {M : ℝ≥0∞}
    (hM : M ≤ μ S) (hgap : μ A < M + μ U) : (S ∩ U).Nonempty := by
  by_contra hn
  have hdis : Disjoint S U := Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)
  have hunion : μ S + μ U = μ (S ∪ U) := (measure_union hdis hUm).symm
  have hle : M + μ U ≤ μ A := by
    calc
      M + μ U ≤ μ S + μ U := add_le_add hM le_rfl
      _ = μ (S ∪ U) := hunion
      _ ≤ μ A := measure_mono (union_subset hS hU)
  exact (not_lt_of_ge hle) hgap

lemma eventually_nonempty_inter_of_saturation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {U : Set α} (hU : MeasurableSet U) (hUpos : 0 < μ U)
    (hUA : ∀ᶠ j in atTop, U ⊆ A j) :
    ∀ᶠ j in atTop, (S j ∩ U).Nonempty := by
  have hlt : M < M + μ U := ENNReal.lt_add_right hM hUpos.ne'
  have he := hlim.eventually (Iio_mem_nhds hlt)
  filter_upwards [he,hUA] with j hj hUj
  exact nonempty_inter_of_small_deficit μ (hSA j) hUj hU (hvol j) hj

lemma exists_nearby_image_of_saturation {α : Type*} [MetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {x : α} (hpersist : ∀ ε > 0, ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ j ≥ k, ∃ z ∈ S j, dist z x < ε := by
  obtain ⟨U,hU,hUn,hUB,hUA⟩ := hpersist ε hε
  have he := eventually_nonempty_inter_of_saturation μ A S hM hSA hvol hlim
    hU.measurableSet (hU.measure_pos μ hUn) hUA
  obtain ⟨j,hjk,hj⟩ := (he.and (eventually_ge_atTop k)).exists
  obtain ⟨z,hzS,hzU⟩ := hjk
  exact ⟨j,hj,z,hzS,hUB hzU⟩

lemma exists_sequence_of_saturation {α : Type*} [MetricSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]
    (A S : ℕ → Set α) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hSA : ∀ j, S j ⊆ A j) (hvol : ∀ j, M ≤ μ (S j))
    (hlim : Tendsto (fun j => μ (A j)) atTop (𝓝 M))
    {x : α} (hpersist : ∀ ε > 0, ∃ U : Set α, IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j) :
    ∃ (j : ℕ → ℕ) (z : ℕ → α), Tendsto j atTop atTop ∧
      (∀ k, z k ∈ S (j k)) ∧ Tendsto z atTop (𝓝 x) := by
  have hex (k : ℕ) := exists_nearby_image_of_saturation μ A S hM hSA hvol hlim
    hpersist k (show 0 < 1 / ((k:ℝ)+1) by positivity)
  choose j hj z hz hdist using hex
  refine ⟨j,z,tendsto_atTop_mono hj tendsto_id,hz,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun k => dist_nonneg) (fun k => (hdist k).le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Pointwise

lemma subset_dilate_of_one_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {C : Set E} (hC : Convex ℝ C) (h0 : (0:E) ∈ C) {c : ℝ} (hc : 1 ≤ c) :
    C ⊆ c • C := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  intro x hx
  refine ⟨c⁻¹ • x,hC.smul_mem_of_zero_mem h0 hx
    ⟨inv_nonneg.mpr hc0.le, inv_le_one_of_one_le₀ hc⟩,?_⟩
  simp only [smul_smul,mul_inv_cancel₀ hc0.ne',one_smul]

lemma persistent_open_test_of_body_product {n : ℕ}
    {B C : Set (Fin n → ℝ)} (hB : Convex ℝ B) (hC : Convex ℝ C)
    (hiB : (interior B).Nonempty) (hiC : (interior C).Nonempty)
    (A : ℕ → Set ((Fin n → ℝ) × (Fin n → ℝ))) (hA : ∀ j, B ×ˢ C ⊆ A j)
    {x : (Fin n → ℝ) × (Fin n → ℝ)} (hx : x ∈ B ×ˢ C) :
    ∀ ε > 0, ∃ U : Set ((Fin n → ℝ) × (Fin n → ℝ)), IsOpen U ∧ U.Nonempty ∧
      U ⊆ ball x ε ∧ ∀ᶠ j in atTop, U ⊆ A j := by
  have hcl : x ∈ closure ((interior B) ×ˢ (interior C)) := by
    rw [closure_prod_eq,hB.closure_interior_eq_closure_of_nonempty_interior hiB,
      hC.closure_interior_eq_closure_of_nonempty_interior hiC]
    exact ⟨subset_closure hx.1,subset_closure hx.2⟩
  intro ε hε
  refine ⟨ball x ε ∩ (interior B ×ˢ interior C),
    isOpen_ball.inter (isOpen_interior.prod isOpen_interior),?_,inter_subset_left,?_⟩
  · exact mem_closure_iff.mp hcl _ isOpen_ball (mem_ball_self hε)
  · exact Eventually.of_forall (fun j =>
      inter_subset_right.trans ((Set.prod_mono interior_subset interior_subset).trans (hA j)))

lemma volume_body_product_dilate {n : ℕ} (B C : Set (Fin n → ℝ)) {c : ℝ} (hc : 0 ≤ c) :
    volume (B ×ˢ (c • C)) = volume B * (ENNReal.ofReal (c^n) * volume C) := by
  rw [Measure.volume_eq_prod,Measure.prod_prod,Measure.addHaar_smul_of_nonneg volume hc]
  simp only [Module.finrank_pi,Fintype.card_fin,
    ]

lemma tendsto_volume_body_product_dilate {n : ℕ}
    {B C : Set (Fin n → ℝ)} (hB : IsCompact B) (hC : IsCompact C)
    (A : ℕ → Set (Fin n → ℝ)) (hA : ∀ j, IsCompact (A j))
    (c : ℕ → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hvol : Tendsto (fun j => (volume (A j)).toReal) atTop (𝓝 (volume B).toReal))
    (hc1 : Tendsto c atTop (𝓝 1)) :
    Tendsto (fun j => volume (A j ×ˢ (c j • C))) atTop (𝓝 (volume B*volume C)) := by
  have hfin (j : ℕ) : volume (A j ×ˢ (c j • C)) ≠ ∞ := by
    rw [volume_body_product_dilate _ _ (hc j)]
    exact ENNReal.mul_ne_top (hA j).measure_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC.measure_ne_top)
  apply (ENNReal.tendsto_toReal_iff hfin (ENNReal.mul_ne_top hB.measure_ne_top hC.measure_ne_top)).mp
  simp only [volume_body_product_dilate _ _ (hc _),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg (hc _) _)]
  convert hvol.mul ((hc1.pow n).mul_const (volume C).toReal) using 1
  simp only [one_pow,one_mul]

theorem equality_strip_images_dense {n : ℕ} (hn : 1 ≤ n)
    {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hconv : Convex ℝ B)
    (hsym : ∀ x ∈ B, -x ∈ B) (hint : (interior B).Nonempty)
    (heq : (volume B).toReal * (volume (coordinatePolar B)).toReal =
      (4:ℝ)^n/(Nat.factorial n:ℝ))
    (a : ℕ → coordinatePolar B)
    (ha : ∀ j, Function.Injective (measurement (fun i : Fin (n+j) => (a i).val)))
    (hcompact : ∀ j, IsCompact (stripBody (fun i : Fin (n+j) => (a i).val)))
    (hsub : ∀ j, B ⊆ stripBody (fun i : Fin (n+j) => (a i).val))
    (hvol : Tendsto (fun j => (volume (stripBody (fun i : Fin (n+j) => (a i).val))).toReal)
      atTop (𝓝 (volume B).toReal))
    (m : ℕ → ℕ) (hm : ∀ j, 2 ≤ m j)
    (herr : Tendsto (fun j => ((n+j:ℕ):ℝ)*planarError (m j)) atTop (𝓝 0))
    {x e : Fin n → ℝ} (hx : x ∈ B) (he : e ∈ coordinatePolar B) :
    ∃ j : ℕ → ℕ, ∃ z : ℕ → ((Fin n → ℝ) × (Fin n → ℝ)),
      Tendsto j atTop atTop ∧
      (∀ k, z k ∈ stripSublevel (fun i : Fin (n+j k) => (a i).val) (m (j k))) ∧
      Tendsto (fun k => stripMap (fun i : Fin (n+j k) => (a i).val) (m (j k)) (z k))
        atTop (𝓝 (x,e)) := by
  let C := coordinatePolar B
  obtain ⟨hC,hCc,hCs,hCi⟩ := coordinatePolar_is_symmetric_convex_body hB hconv hsym hint
  let A (j : ℕ) : Matrix (Fin (n+j)) (Fin n) ℝ := fun i => (a i).val
  let c (j : ℕ) : ℝ := 1+((n+j:ℕ):ℝ)*planarError (m j)
  have hc (j : ℕ) : 1 ≤ c j := by
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (planarError_nonneg _))
  have hc1 : Tendsto c atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add herr
  let O (j : ℕ) := stripBody (A j) ×ˢ (c j • C)
  let S (j : ℕ) := stripMap (A j) (m j) '' stripSublevel (A j) (m j)
  have hSO (j : ℕ) : S j ⊆ O j := by
    apply (stripMap_image_subset_product (A j) (hm j)).trans
    exact Set.prod_mono Subset.rfl (smul_set_mono (coordinatePolar_antitone (hsub j)))
  have hlim : Tendsto (fun j => volume (O j)) atTop (𝓝 (volume B*volume C)) :=
    tendsto_volume_body_product_dilate hB hC _ hcompact c (fun j => zero_le_one.trans (hc j)) hvol hc1
  have hconst : volume B * volume C = ENNReal.ofReal ((4:ℝ)^n/(Nat.factorial n:ℝ)) := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hB.measure_ne_top hC.measure_ne_top),ENNReal.toReal_mul]
    exact congrArg ENNReal.ofReal heq
  rw [hconst] at hlim
  have hpersist := persistent_open_test_of_body_product hconv hCc hint hCi O
    (fun j => Set.prod_mono (hsub j) (subset_dilate_of_one_le hCc (zero_mem_coordinatePolar B) (hc j)))
    (show (x,e) ∈ B ×ˢ C from ⟨hx,he⟩)
  obtain ⟨j,v,hj,hv,hvlim⟩ := exists_sequence_of_saturation volume O S ENNReal.ofReal_ne_top
    hSO (fun j => stripMap_volume_lower hn (A j) (ha j) (hm j)) hlim hpersist
  choose z hz hzv using hv
  refine ⟨j,z,hj,hz,?_⟩
  have heqv : (fun k => stripMap (A (j k)) (m (j k)) (z k)) = v := funext hzv
  rw [heqv]
  exact hvlim

end SymmetricMahler

open Set Filter Metric MeasureTheory Complex
open scoped Topology
namespace MahlerConformal

lemma summable_odd_square_inv : Summable (fun k : ℕ => 1 / ((2*k+1:ℕ):ℝ)^2) := by
  exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2:ℕ))).comp_injective
    (by intro a b h; change 2*a+1 = 2*b+1 at h; omega)

lemma term_two_bound_closed (k : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖term 2 k w‖ ≤ 1 / ((2*k+1:ℕ):ℝ)^2 := by
  rw [term, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hw) (by positivity)

lemma summable_series_two_closed {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k => term 2 k w) :=
  Summable.of_norm_bounded summable_odd_square_inv (fun k => term_two_bound_closed k hw)

lemma continuousOn_F_closed : ContinuousOn F (closedBall (0:ℂ) 1) := by
  apply continuousOn_const.mul
  apply continuousOn_tsum (fun k => ?_) summable_odd_square_inv
  · intro k w hw
    exact term_two_bound_closed k (mem_closedBall_zero_iff.mp hw)
  · unfold term
    fun_prop

lemma closure_Omega_eq : closure Omega = F '' closedBall (0:ℂ) 1 := by
  apply subset_antisymm
  · apply closure_minimal (image_mono ball_subset_closedBall)
    exact (isCompact_closedBall (0:ℂ) 1).image_of_continuousOn continuousOn_F_closed |>.isClosed
  · have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball _ (by norm_num)
    rw [← hcl]
    exact (hcl ▸ continuousOn_F_closed).image_closure

lemma continuous_boundary_F : Continuous (fun θ : ℝ => F (polar 1 θ)) := by
  apply continuousOn_F_closed.comp_continuous
  · unfold polar
    fun_prop
  · intro θ
    simp only [mem_closedBall_zero_iff, norm_polar (by norm_num : (0:ℝ) ≤ 1), le_refl]

lemma tendsto_F_polar_boundary (θ : ℝ) :
    Tendsto (fun r : ℝ => F (polar r θ)) (𝓝[<] 1) (𝓝 (F (polar 1 θ))) := by
  apply (continuousOn_F_closed _ (by simp [norm_polar])).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have : Continuous (fun r : ℝ => polar r θ) := by unfold polar; fun_prop
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_radius] with r hr
    simpa only [mem_closedBall_zero_iff, norm_polar hr.1.le] using hr.2.le

lemma boundary_F_one : F 1 = 1 := by
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_F_polar_boundary 0)
  simp only [polar_zero, Complex.ofReal_one, Function.comp_def] at hlim
  have hreal : (F 1).re = 1 := tendsto_nhds_unique hlim F_real_tendsto_one
  apply Complex.ext
  · exact hreal
  · simpa using F_real_im 1

lemma integral_B_boundary {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Tendsto (fun r => ∫ t in (0:ℝ)..θ, B r t) (𝓝[<] 1) (𝓝 (2*θ/Real.pi)) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := θ) (F := B) (f := fun _ => 2/Real.pi)
    (fun _ => 2/Real.pi)
    (Filter.Eventually.of_forall fun r => (continuous_B r).aestronglyMeasurable)
    (by
      filter_upwards [eventually_radius] with r hr
      exact Filter.Eventually.of_forall fun t ht => by
        rw [uIoc_of_le hθ] at ht
        rw [Real.norm_eq_abs, abs_of_nonneg (B_nonneg hr.1 hr.2 ⟨ht.1.le,ht.2.trans hθπ⟩)]
        exact (B_lt_two_div_pi r t).le)
    intervalIntegrable_const
    (by
      filter_upwards [volume.ae_ne Real.pi] with t htπ
      intro ht
      rw [uIoc_of_le hθ] at ht
      exact B_tendsto_one ht.1 (lt_of_le_of_ne (ht.2.trans hθπ) htπ))
  convert ht using 1 ; simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] ; congr 1 ; ring

lemma Q_boundary {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    Q 1 θ = 1 - 2*θ/Real.pi := by
  have hlim := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_F_polar_boundary θ)
  have hlim' := F_real_tendsto_one.sub (integral_B_boundary hθ hθπ)
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (F (r:ℂ)).re - (∫ t in (0:ℝ)..θ, B r t) = Q r θ := by
    filter_upwards [eventually_radius] with r hr
    rw [integral_B hr.1 hr.2, Q_zero]
    ring
  exact tendsto_nhds_unique hlim (hlim'.congr' he)

def lensWidth (t : ℝ) : ℝ := (F (polar 1 (Real.pi/2*(1-t)))).im

lemma continuous_lensWidth : Continuous lensWidth := by
  exact Complex.continuous_im.comp (continuous_boundary_F.comp (by fun_prop))

lemma lensWidth_one : lensWidth 1 = 0 := by simp [lensWidth, polar_zero, boundary_F_one]

lemma lensWidth_neg_one : lensWidth (-1) = 0 := by
  unfold lensWidth
  rw [show Real.pi/2*(1-(-1:ℝ)) = Real.pi by ring, polar_pi, F_odd]
  simp [boundary_F_one]

lemma lensWidth_even (t : ℝ) : lensWidth (-t) = lensWidth t := by
  have he : Real.pi/2*(1-(-t)) = Real.pi - Real.pi/2*(1-t) := by ring
  simp only [lensWidth, he, polar_pi_sub, F_odd, F_conj, Complex.neg_im, Complex.conj_im, neg_neg]

lemma boundary_upper_real {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    (F (polar 1 (Real.pi/2*(1-t)))).re = t := by
  have hθ₀ : 0 ≤ Real.pi/2*(1-t) := mul_nonneg (by positivity) (sub_nonneg.mpr ht.2)
  have hθπ : Real.pi/2*(1-t) ≤ Real.pi := by nlinarith [mul_nonneg Real.pi_pos.le (show 0 ≤ t+1 by linarith [ht.1])]
  rw [← Q, Q_boundary hθ₀ hθπ]
  field_simp
  ring

def boundaryDerivative (w : ℂ) : ℂ →L[ℝ] ℂ :=
  (4 / ((Real.pi : ℂ)^2 * w) * Complex.log (cayley w)) •
    ContinuousLinearMap.id ℝ ℂ

lemma cayley_im_of_ne {w : ℂ} (_ : w ≠ 1) :
    (cayley w).im = 2*w.im / Complex.normSq (1-w) := by
  simp only [cayley, Complex.div_im, Complex.add_re, Complex.sub_re,
    Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im]

  ring

lemma continuousAt_boundaryDerivative {w : ℂ} (hw₀ : w ≠ 0)
    (hw₁ : w ≠ 1) (hwi : (cayley w).im ≠ 0) :
    ContinuousAt boundaryDerivative w := by
  have hden : (1:ℂ)-w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw₁)
  have hc : ContinuousAt cayley w := by
    exact (continuousAt_const.add continuousAt_id).div
      (continuousAt_const.sub continuousAt_id) hden
  have hl := (continuousAt_clog (Or.inr hwi)).comp hc
  unfold boundaryDerivative
  exact ((continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_ne_zero (pow_ne_zero _ pi_cast_ne) hw₀)).mul hl).smul continuousAt_const

lemma hasFDerivWithinAt_F_closed {w : ℂ} (hw₀ : w ≠ 0)
    (hw₁ : w ≠ 1) (hwi : (cayley w).im ≠ 0) :
    HasFDerivWithinAt F (boundaryDerivative w) (closedBall (0:ℂ) 1) w := by
  have hcl : closure (ball (0:ℂ) 1) = closedBall 0 1 := closure_ball _ (by norm_num)
  rw [← hcl]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (differentiableOn_F.restrictScalars ℝ) (convex_ball (0:ℂ) 1) isOpen_ball
  · intro z hz
    exact (continuousOn_F_closed z (hcl ▸ hz)).mono ball_subset_closedBall
  · apply ((continuousAt_boundaryDerivative hw₀ hw₁ hwi).tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin, (eventually_ne_nhds hw₀).filter_mono nhdsWithin_le_nhds] with z hz hz₀
    have hd := (hasDerivAt_F_log (mem_ball_zero_iff.mp hz) hz₀).hasFDerivAt.restrictScalars ℝ
    rw [hd.fderiv]
    ext v
    simp [boundaryDerivative, ContinuousLinearMap.toSpanSingleton_apply, mul_comm, cayley]

lemma hasDerivAt_boundary_F {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    HasDerivAt (fun t : ℝ => F (polar 1 t))
      ((4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ))) θ := by
  have hwim : 0 < (polar 1 θ).im := by
    rw [polar_im, one_mul]
    exact Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hw₁ : polar 1 θ ≠ 1 := by intro h; simp [h] at hwim
  have hwi : (cayley (polar 1 θ)).im ≠ 0 := by
    rw [cayley_im_of_ne hw₁]
    exact ne_of_gt (div_pos (by positivity) (Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hw₁))))
  have hd := (hasFDerivWithinAt_F_closed (polar_ne_zero zero_lt_one θ) hw₁ hwi).comp_hasDerivAt θ
    (hasDerivAt_polar_complex 1 (θ:ℂ)).comp_ofReal
    (Filter.Eventually.of_forall fun t => by simp [norm_polar])
  change HasDerivAt (fun t : ℝ => F (polar 1 t))
    (boundaryDerivative (polar 1 θ) (I*polar 1 θ)) θ at hd
  have he : boundaryDerivative (polar 1 θ) (I*polar 1 θ) =
      (4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ)) := by
    simp only [boundaryDerivative, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    field_simp [polar_ne_zero zero_lt_one θ]
  rwa [he] at hd

lemma hasDerivAt_boundary_S {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    HasDerivAt (S 1) (4/Real.pi^2 * Real.log ‖cayley (polar 1 θ)‖) θ := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_boundary_F hθ hθπ)
  change HasDerivAt (S 1)
    (((4/(Real.pi:ℂ)^2)*I*Complex.log (cayley (polar 1 θ))).im) θ at hd
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.mul_im, Complex.log_re] using hd

lemma cayley_polar_boundary {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    cayley (polar 1 θ) = ((Real.cos (θ/2) / Real.sin (θ/2) : ℝ) : ℂ) * I := by
  have hs : Real.sin (θ/2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have hw : (1:ℂ)-polar 1 θ ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [polar_im] at hi
    exact (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne' hi
  unfold cayley
  apply (div_eq_iff hw).mpr
  have hsin : Real.sin θ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using Real.sin_two_mul (θ/2)
  have hcos : Real.cos θ = Real.cos (θ/2)^2 - Real.sin (θ/2)^2 := by
    have h := Real.cos_two_mul (θ/2)
    rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] at h
    nlinarith [Real.sin_sq_add_cos_sq (θ/2)]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.one_re, polar_re, polar_im, one_mul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_im,
      zero_mul, mul_zero, zero_sub, sub_zero, add_zero, mul_one]
    rw [hsin, hcos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (θ/2), congrArg (fun x : ℝ => x * Real.sin (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2)), congrArg (fun x : ℝ => x * Real.cos (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2))]
  · simp only [Complex.add_im, Complex.one_im, polar_im, one_mul,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      polar_re, zero_mul, mul_zero, zero_sub, sub_zero, add_zero, zero_add, mul_one]
    rw [hsin, hcos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (θ/2), congrArg (fun x : ℝ => x * Real.sin (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2)), congrArg (fun x : ℝ => x * Real.cos (θ/2))
      (Real.sin_sq_add_cos_sq (θ/2))]

lemma norm_cayley_polar_boundary {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    ‖cayley (polar 1 θ)‖ = Real.cos (θ/2) / Real.sin (θ/2) := by
  rw [cayley_polar_boundary hθ hθπ, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos]
  exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith⟩)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

lemma concaveOn_boundary_S : ConcaveOn ℝ (Icc 0 Real.pi) (S 1) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    (Complex.continuous_im.comp continuous_boundary_F).continuousOn
  · rw [interior_Icc]
    intro θ hθ
    exact (hasDerivAt_boundary_S hθ.1 hθ.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    change deriv (S 1) y ≤ deriv (S 1) x
    rw [(hasDerivAt_boundary_S hx.1 hx.2).deriv, (hasDerivAt_boundary_S hy.1 hy.2).deriv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [norm_cayley_polar_boundary hx.1 hx.2, norm_cayley_polar_boundary hy.1 hy.2]
    apply Real.log_le_log
    · exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos,hy.1],by linarith [hy.2]⟩)
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hy.1]) (by linarith [hy.2,Real.pi_pos]))
    · apply div_le_div₀
      · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2]⟩
      · exact Real.antitoneOn_cos ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2,Real.pi_pos]⟩
          ⟨by linarith [hy.1],by linarith [hy.2,Real.pi_pos]⟩ (by linarith)
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])
      · exact Real.monotoneOn_sin ⟨by linarith [hx.1,Real.pi_pos],by linarith [hx.2]⟩
          ⟨by linarith [hy.1,Real.pi_pos],by linarith [hy.2]⟩ (by linarith)

lemma width_angle_mem {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) :
    Real.pi/2*(1-t) ∈ Icc 0 Real.pi := by
  constructor
  · exact mul_nonneg (by positivity) (sub_nonneg.mpr ht.2)
  · nlinarith [mul_nonneg Real.pi_pos.le (show 0 ≤ t+1 by linarith [ht.1])]

lemma concaveOn_lensWidth : ConcaveOn ℝ (Icc (-1:ℝ) 1) lensWidth := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := concaveOn_boundary_S.2 (width_angle_mem hx) (width_angle_mem hy) ha hb hab
  change a*S 1 (Real.pi/2*(1-x)) + b*S 1 (Real.pi/2*(1-y)) ≤
    S 1 (a*(Real.pi/2*(1-x))+b*(Real.pi/2*(1-y))) at h
  have he : a*(Real.pi/2*(1-x))+b*(Real.pi/2*(1-y)) =
      Real.pi/2*(1-(a*x+b*y)) := by
    calc
      _ = Real.pi/2*((a+b)-(a*x+b*y)) := by ring
      _ = _ := by rw [hab]
  simpa only [he, lensWidth, S, smul_eq_mul] using h

lemma lensWidth_nonneg {t : ℝ} (ht : t ∈ Icc (-1:ℝ) 1) : 0 ≤ lensWidth t := by
  have h := concaveOn_lensWidth.2
    (show (-1:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by constructor <;> norm_num)
    (show 0 ≤ (1-t)/2 by linarith [ht.2])
    (show 0 ≤ (1+t)/2 by linarith [ht.1])
    (show (1-t)/2 + (1+t)/2 = 1 by ring)
  simpa only [lensWidth_neg_one, lensWidth_one, smul_eq_mul, mul_zero, add_zero,
    show (1-t)/2*(-1)+(1+t)/2*1 = t by ring] using h

lemma boundary_width_upper {θ : ℝ} (hθ : θ ∈ Icc 0 Real.pi) :
    (F (polar 1 θ)).re ∈ Icc (-1:ℝ) 1 ∧
      (F (polar 1 θ)).im = lensWidth (F (polar 1 θ)).re := by
  have he := Q_boundary hθ.1 hθ.2
  change (F (polar 1 θ)).re = 1-2*θ/Real.pi at he
  have hq : (F (polar 1 θ)).re ∈ Icc (-1:ℝ) 1 := by
    rw [he]
    constructor
    · have := (div_le_iff₀ Real.pi_pos).mpr (show 2*θ ≤ 2*Real.pi by linarith [hθ.2])
      linarith
    · have := div_nonneg (show 0 ≤ 2*θ by linarith [hθ.1]) Real.pi_pos.le
      linarith
  refine ⟨hq, ?_⟩
  unfold lensWidth
  congr 3
  rw [he]
  field_simp
  ring

lemma boundary_width {w : ℂ} (hw : ‖w‖ = 1) :
    (F w).re ∈ Icc (-1:ℝ) 1 ∧ |(F w).im| = lensWidth (F w).re := by
  have hp : polar 1 w.arg = w := by
    have h : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    simpa only [hw] using h
  by_cases ha : 0 ≤ w.arg
  · have h := boundary_width_upper ⟨ha, Complex.arg_le_pi w⟩
    rw [hp] at h
    exact ⟨h.1, by rw [h.2, abs_of_nonneg (lensWidth_nonneg h.1)]⟩
  · have ham : -w.arg ∈ Icc 0 Real.pi :=
      ⟨by linarith, by linarith [Complex.neg_pi_lt_arg w]⟩
    have h := boundary_width_upper ham
    rw [polar_neg_angle, hp, F_conj] at h
    simp only [Complex.conj_re, Complex.conj_im] at h
    exact ⟨h.1, by rw [← abs_neg, h.2, abs_of_nonneg (lensWidth_nonneg h.1)]⟩

lemma isCompact_closure_Omega : IsCompact (closure Omega) := by
  rw [closure_Omega_eq]
  exact (isCompact_closedBall (0:ℂ) 1).image_of_continuousOn continuousOn_F_closed

lemma closure_Omega_real {u : ℂ} (hu : u ∈ closure Omega) :
    u.re ∈ Icc (-1:ℝ) 1 := by
  rw [closure_Omega_eq] at hu
  obtain ⟨w,hw,rfl⟩ := hu
  have hb := mem_closedBall_zero_iff.mp hw
  rcases hb.lt_or_eq with hlt | he
  · have h := F_re_mem_strip (w := w) hlt
    exact ⟨h.1.le,h.2.le⟩
  · exact (boundary_width he).1

lemma closure_Omega_im_le {u : ℂ} (hu : u ∈ closure Omega) :
    u.im ≤ lensWidth u.re := by
  let T : Set ℂ := closure Omega ∩ {v | v.re = u.re}
  have hT : IsCompact T := isCompact_closure_Omega.inter_right
    (isClosed_eq Complex.continuous_re continuous_const)
  have huT : u ∈ T := ⟨hu,rfl⟩
  obtain ⟨v,hv,hmax⟩ := hT.exists_isMaxOn ⟨u,huT⟩ Complex.continuous_im.continuousOn
  have hvn : v ∉ Omega := by
    intro hvO
    obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp isOpen_Omega v hvO
    let z : ℂ := v + (ε/2 : ℝ)*I
    have hz : z ∈ ball v ε := by
      rw [mem_ball, dist_eq_norm]
      simp only [z, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hzr : z.re = u.re := by simpa [z] using hv.2
    have hzi : z.im = v.im+ε/2 := by simp [z]
    have hh := hmax ⟨subset_closure (hεO hz),hzr⟩
    change z.im ≤ v.im at hh
    linarith
  obtain ⟨w,hw,hwv⟩ := closure_Omega_eq ▸ hv.1
  have hwe : ‖w‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hw) (by
    by_contra! hn
    exact hvn (hwv ▸ (show F w ∈ Omega from ⟨w,mem_ball_zero_iff.mpr hn,rfl⟩)))
  have hb := (boundary_width hwe).2
  rw [hwv] at hb
  calc
    u.im ≤ v.im := hmax huT
    _ ≤ |v.im| := le_abs_self _
    _ = lensWidth v.re := hb
    _ = lensWidth u.re := congrArg lensWidth hv.2

lemma closure_Omega_conj {u : ℂ} (hu : u ∈ closure Omega) :
    starRingEnd ℂ u ∈ closure Omega := by
  obtain ⟨w,hw,rfl⟩ := closure_Omega_eq ▸ hu
  rw [closure_Omega_eq]
  refine ⟨starRingEnd ℂ w, ?_, F_conj w⟩
  simpa only [mem_closedBall_zero_iff, norm_conj] using hw

lemma closure_Omega_width_bound {u : ℂ} (hu : u ∈ closure Omega) :
    |u.im| ≤ lensWidth u.re := by
  apply abs_le.mpr
  constructor
  · have h := closure_Omega_im_le (closure_Omega_conj hu)
    simp only [Complex.conj_re, Complex.conj_im] at h
    linarith
  · exact closure_Omega_im_le hu

end MahlerConformal

open Set Filter
open scoped Topology
namespace MahlerEndpoint

def logCot (t : ℝ) : ℝ := Real.log (Real.cos t / Real.sin t)

lemma logCot_scaled_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => logCot (a*t) / Real.log t) (𝓝[>] 0) (𝓝 (-1)) := by
  let h : ℝ → ℝ := fun t => Real.cos (a*t) / (a * Real.sinc (a*t))
  have ht : Tendsto (fun t : ℝ => a*t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0)))
  have hh : Tendsto h (𝓝[>] 0) (𝓝 (1/a)) := by
    simpa only [h, Real.cos_zero, Real.sinc_zero, mul_one, Function.comp_def, Pi.div_apply, Pi.mul_apply] using!
      (Real.continuous_cos.continuousAt.tendsto.comp ht).div
        (tendsto_const_nhds.mul (Real.continuous_sinc.continuousAt.tendsto.comp ht))
        (by simpa using ha.ne')
  have hh0 : (1/a:ℝ) ≠ 0 := one_div_ne_zero ha.ne'
  have hlim := ((hh.log hh0).div_atBot Real.tendsto_log_nhdsGT_zero).sub_const 1
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin, hh.eventually_ne hh0,
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (0:ℝ))] with t ht hh hl
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hlog : Real.log t ≠ 0 := hl.ne
  have hcot : Real.cos (a*t) / Real.sin (a*t) = h t / t := by
    dsimp [h]
    rw [Real.sinc_of_ne_zero (mul_ne_zero ha.ne' ht0)]
    field_simp
  rw [logCot, hcot, Real.log_div hh ht0, sub_div, div_self hlog]

lemma logCot_scaled_ratio {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun t : ℝ => logCot (a*(c*t)) / logCot (a*t)) (𝓝[>] 0) (𝓝 1) := by
  have h1 := logCot_scaled_div_log (mul_pos ha hc)
  have h2 := logCot_scaled_div_log ha
  have hlim := h1.div h2 (by norm_num : (-1:ℝ) ≠ 0)
  simp only [div_self (by norm_num : (-1:ℝ) ≠ 0)] at hlim
  apply hlim.congr'
  filter_upwards [Real.tendsto_log_nhdsGT_zero.eventually (eventually_lt_atBot (0:ℝ))] with t ht
  have hlog := ht.ne
  change (logCot (a*c*t)/Real.log t) / (logCot (a*t)/Real.log t) = _
  rw [mul_assoc, div_div_div_cancel_right₀ hlog]

lemma profile_ratio {f : ℝ → ℝ} {a k r : ℝ}
    (ha : 0 < a) (hk : k ≠ 0) (hr : 0 < r)
    (hf0 : Tendsto f (𝓝[>] 0) (𝓝 0))
    (hder : ∀ t ∈ Ioo 0 r, HasDerivAt f (k * logCot (a*t)) t)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => f (c*t) / f t) (𝓝[>] 0) (𝓝 c) := by
  have ht : Tendsto (fun t : ℝ => c*t) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hc ht
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  have hlog : ∀ᶠ t : ℝ in 𝓝[>] 0, logCot (a*t) ≠ 0 := by
    have hh := (logCot_scaled_div_log ha).eventually_ne (by norm_num : (-1:ℝ) ≠ 0)
    filter_upwards [hh] with t ht
    exact fun h => ht (by rw [h, zero_div])
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun t => (k * logCot (a*(c*t))) * c)
    (g' := fun t => k * logCot (a*t))
  · filter_upwards [ht.eventually hsmall] with t htt
    exact (hder (c*t) htt).comp t (by simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul c)
  · exact hsmall.mono (fun t ht => hder t ht)
  · exact hlog.mono (fun t ht => mul_ne_zero hk ht)
  · exact hf0.comp ht
  · exact hf0
  · have hh := (logCot_scaled_ratio ha hc).mul_const c
    simp only [one_mul] at hh
    convert hh using 1
    ext t
    field_simp

lemma concave_ratio_antitone {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc (0:ℝ) 2) f)
    (hf0 : f 0 = 0) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ 2) :
    f y / y ≤ f x / x := by
  have hyp : 0 < y := hx.trans_le hxy
  have h := hf.2 (show (0:ℝ) ∈ Icc (0:ℝ) 2 by norm_num)
    (show y ∈ Icc (0:ℝ) 2 from ⟨hyp.le,hy⟩)
    (show 0 ≤ 1-x/y by apply sub_nonneg.mpr; exact (div_le_one hyp).mpr hxy)
    (div_nonneg hx.le hyp.le) (by ring : 1-x/y + x/y = 1)
  simp only [smul_eq_mul, hf0, mul_zero, zero_add, div_mul_cancel₀ x hyp.ne'] at h
  apply (div_le_div_iff₀ hyp hx).mpr
  have hh := mul_le_mul_of_nonneg_left h hyp.le
  field_simp at hh
  nlinarith

lemma uniform_profile_ratio {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc (0:ℝ) 2) f) (hf0 : f 0 = 0)
    (hfpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < f t)
    (hratio : ∀ c : ℝ, 0 < c →
      Tendsto (fun t : ℝ => f (c*t) / f t) (𝓝[>] 0) (𝓝 c))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < f δ ∧
      ∀ c ∈ Icc a b, |f (δ*c) / f δ - c| ≤ ε := by
  have hb : 0 < b := ha.trans_le hab
  have ha' := (hratio a ha).div_const a
  have hb' := (hratio b hb).div_const b
  rw [div_self ha.ne'] at ha'
  rw [div_self hb.ne'] at hb'
  have hea := (Metric.tendsto_nhds.mp ha') (ε/b) (div_pos hε hb)
  have heb := (Metric.tendsto_nhds.mp hb') (ε/b) (div_pos hε hb)
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Ioo 0 (min 1 (2/b)) :=
    Ioo_mem_nhdsGT (by positivity)
  have hδ := hsmall.and (hea.and heb)
  obtain ⟨δ,hδ,hea,heb⟩ := hδ.exists
  have hδ0 := hδ.1
  have hδ1 := hδ.2.trans_le (min_le_left _ _)
  have hδb : δ*b ≤ 2 := (le_div_iff₀ hb).mp (hδ.2.le.trans (min_le_right _ _))
  have hfp := hfpos δ ⟨hδ0,hδ1⟩
  refine ⟨δ,hδ0,hδ1,hfp,?_⟩
  intro c hc
  have hc0 : 0 < c := ha.trans_le hc.1
  have hlo := concave_ratio_antitone hf hf0 (mul_pos hδ0 hc0)
    (mul_le_mul_of_nonneg_left hc.2 hδ0.le) hδb
  have hhi := concave_ratio_antitone hf hf0 (mul_pos hδ0 ha)
    (mul_le_mul_of_nonneg_left hc.1 hδ0.le)
    ((mul_le_mul_of_nonneg_left hc.2 hδ0.le).trans hδb)
  have hlo' := mul_le_mul_of_nonneg_left hlo (div_nonneg hδ0.le hfp.le)
  have hhi' := mul_le_mul_of_nonneg_left hhi (div_nonneg hδ0.le hfp.le)
  have hlo'' : (f (b*δ)/ f δ)/ b ≤ (f (δ*c)/f δ)/c := by
    convert hlo' using 1 <;> try field_simp [hδ0.ne',hc0.ne',hb.ne',hfp.ne']

  have hhi'' : (f (δ*c)/f δ)/c ≤ (f (a*δ)/ f δ)/ a := by
    convert hhi' using 1 <;> try field_simp [hδ0.ne',hc0.ne',ha.ne',hfp.ne']

  rw [Real.dist_eq] at hea heb
  have hal := (abs_lt.mp hea).2
  have hbl := (abs_lt.mp heb).1
  have hrlo : 1-ε/b ≤ (f (δ*c)/f δ)/c := by linarith
  have hrhi : (f (δ*c)/f δ)/c ≤ 1+ε/b := by linarith
  have hlow := (le_div_iff₀ hc0).mp hrlo
  have hhigh := (div_le_iff₀ hc0).mp hrhi
  have hec : ε/b*c ≤ ε := by
    calc
      ε/b*c ≤ ε/b*b := mul_le_mul_of_nonneg_left hc.2 (div_nonneg hε.le hb.le)
      _ = ε := div_mul_cancel₀ ε hb.ne'
  rw [abs_le]
  constructor <;> nlinarith

end MahlerEndpoint

namespace MahlerConformal
open Set Filter Metric Complex
open scoped Topology

lemma lensWidth_zero_pos : 0 < lensWidth 0 := by
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp isOpen_Omega 0 zero_mem_Omega
  have hr2 : 0 < r/2 := half_pos hr
  have hu : ((r/2:ℝ):ℂ)*I ∈ closure Omega := subset_closure (hrO (by
    simp only [mem_ball_zero_iff, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr2]
    linarith))
  have hb := closure_Omega_width_bound hu
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, sub_self, add_zero] at hb
  have hp : 0 < |r/2| := abs_pos.mpr (div_ne_zero hr.ne' (by norm_num))
  exact hp.trans_le hb

lemma lensWidth_endpoint_pos {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    0 < lensWidth (1-t) := by
  have hh := concaveOn_lensWidth.2
    (show (1:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
    (show (0:ℝ) ∈ Icc (-1:ℝ) 1 by norm_num)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1.le (by ring : 1-t+t=1)
  simp only [smul_eq_mul, lensWidth_one, mul_zero, zero_add, mul_one, add_zero] at hh
  exact (mul_pos ht.1 lensWidth_zero_pos).trans_le hh

lemma concaveOn_endpoint_profile :
    ConcaveOn ℝ (Icc (0:ℝ) 2) (fun t => lensWidth (1-t)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := concaveOn_lensWidth.2
    (show 1-x ∈ Icc (-1:ℝ) 1 by constructor <;> linarith [hx.1,hx.2])
    (show 1-y ∈ Icc (-1:ℝ) 1 by constructor <;> linarith [hy.1,hy.2]) ha hb hab
  have he : a*(1-x)+b*(1-y)=1-(a*x+b*y) := by nlinarith
  simpa only [smul_eq_mul, he] using hh

lemma hasDerivAt_endpoint_profile {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 2) :
    HasDerivAt (fun t => lensWidth (1-t))
      ((2/Real.pi) * MahlerEndpoint.logCot ((Real.pi/4)*t)) t := by
  have hθ0 : 0 < Real.pi/2*t := mul_pos (by positivity) ht.1
  have hθπ : Real.pi/2*t < Real.pi := by nlinarith [Real.pi_pos, ht.2]
  have hh := (hasDerivAt_boundary_S hθ0 hθπ).comp t
    (by simpa only [mul_one,id_eq] using! (hasDerivAt_id t).const_mul (Real.pi/2))
  rw [norm_cayley_polar_boundary hθ0 hθπ] at hh
  convert hh using 1 <;> try rfl
  · ext t
    unfold lensWidth S
    congr 3
    ring
  · unfold MahlerEndpoint.logCot
    rw [show Real.pi/2*t/2=Real.pi/4*t by ring]
    field_simp
    ring

lemma lensWidth_endpoint_scaling :
    ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < lensWidth (1-δ) ∧
        ∀ c ∈ Icc a b, |lensWidth (1-δ*c) / lensWidth (1-δ) - c| ≤ ε := by
  apply MahlerEndpoint.uniform_profile_ratio concaveOn_endpoint_profile
    (by simpa using lensWidth_one) (fun t ht => lensWidth_endpoint_pos ht)
  intro c hc
  apply MahlerEndpoint.profile_ratio (a := Real.pi/4) (k := 2/Real.pi)
    (r := 2) (by positivity) (by positivity) (by norm_num) _
    (fun t ht => hasDerivAt_endpoint_profile ht) hc
  have hh : Tendsto (fun t : ℝ => lensWidth (1-t)) (𝓝[>] 0) (𝓝 (lensWidth 1)) := by
    apply continuous_lensWidth.continuousAt.tendsto.comp
    simpa only [sub_zero,id_eq] using! tendsto_const_nhds.sub
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0))
  simpa only [lensWidth_one] using hh

end MahlerConformal

end

end OAI
