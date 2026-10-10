import Mathlib
import OAI.Analysis.Conductivity.Sobolev.SobolevGaugeTransform
import OAI.Analysis.Conductivity.Sources.CriticalWallGap

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma surface_cancellation_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (t f : α → ℝ) (d M ε : ℝ)
    (hM : 0≤M) (hε : 0≤ε) (ht : Integrable t μ)
    (htf : Integrable (fun x => t x*f x) μ) (hz : (∫ x,t x ∂μ)=0)
    (hb : ∀ᵐ x ∂μ,|t x|≤M) (ho : ∀ᵐ x ∂μ,|f x-d|≤ε) :
    |∫ x,t x*f x ∂μ|≤M*ε := by
  have he : (∫ x,t x*f x ∂μ)=(∫ x,t x*(f x-d) ∂μ) := by
    simp_rw [mul_sub]
    rw [integral_sub htf (ht.mul_const d),integral_mul_const,hz,zero_mul,sub_zero]
  rw [he]
  have hb' : ∀ᵐ x ∂μ,‖t x*(f x-d)‖≤|M| * |ε| := by
    filter_upwards [hb,ho] with x hx hy
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (hx.trans (le_abs_self M)) (hy.trans (le_abs_self ε))
      (abs_nonneg _) (abs_nonneg _)
  simpa [abs_of_nonneg hM,abs_of_nonneg hε] using norm_integral_le_of_norm_le_const hb'

lemma finite_surface_source_bound {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i,IsProbabilityMeasure (μ i)]
    (q : ι → ℝ) (t f : ι → α → ℝ) (d : ι → ℝ) (M ε : ℝ)
    (hM : 0≤M) (hε : 0≤ε) (hq : (∑ i,|q i|)≤2)
    (ht : ∀ i,Integrable (t i) (μ i))
    (htf : ∀ i,Integrable (fun x => t i x*f i x) (μ i))
    (hz : ∀ i,(∫ x,t i x ∂μ i)=0)
    (hb : ∀ i,∀ᵐ x ∂μ i,|t i x|≤2*M)
    (ho : ∀ i,∀ᵐ x ∂μ i,|f i x-d i|≤ε) :
    |∑ i,q i*(∫ x,t i x*f i x ∂μ i)|≤4*M*ε := by
  calc
    _ ≤ ∑ i,|q i*(∫ x,t i x*f i x ∂μ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,|q i| *(2*M*ε) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact surface_cancellation_bound (μ i) (t i) (f i) (d i) (2*M) ε
        (mul_nonneg (by norm_num) hM) hε (ht i) (htf i) (hz i) (hb i) (ho i)
    _ = (∑ i,|q i|)*(2*M*ε) := (Finset.sum_mul _ _ _).symm
    _ ≤ 2*(2*M*ε) := mul_le_mul_of_nonneg_right hq (by positivity)
    _ = _ := by ring

lemma weighted_integral_tendsto (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure,|a x|≤C) {W : ℕ → H1} {w u : H1}
    (hW : Tendsto W atTop (𝓝 w)) {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure,|weakValue u x|≤M) (c : ℝ)
    (f : R3 → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    Tendsto (fun n => ∫ x,a x*inner ℝ (weakGradient (W n) x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)
      atTop (𝓝 (∫ x,a x*inner ℝ (weakGradient w x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)) := by
  let φ := smoothH1 f hf
  obtain ⟨N,hN,hφ⟩ := smoothH1_bounded f hf
  have hs := H1_sub_constant_spec u c
  have huc : ∀ᵐ x ∂ballMeasure,|weakValue (u-constantH1 c) x|≤M+|c| := by
    filter_upwards [hu,hs.1] with x hx hy
    rw [hy]
    exact (abs_sub _ _).trans (add_le_add hx (le_refl _))
  obtain ⟨p,_,hp,_⟩ := exists_H1_product huc hφ
  have he (z : H1) : energy a z p=∫ x,a x*inner ℝ (weakGradient z x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure := by
    apply integral_congr_ae
    filter_upwards [hp,hs.1,hs.2,smoothH1_value f hf,smoothH1_gradient f hf]
      with x hx hy hz hv hg
    rw [hx,hy,hz,hv,hg]
  simpa only [he] using source_energy_limit a ha hC hb hW p

theorem weighted_annihilation_of_geometric_error (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure,|a x|≤C) {W : ℕ → H1} {w u : H1}
    (hW : Tendsto W atTop (𝓝 w)) {M : ℝ}
    (hu : ∀ᵐ x ∂ballMeasure,|weakValue u x|≤M) (c s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hfinite : ∀ (f : R3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f →
      HasCompactSupport f → tsupport f⊆ball → ∃ K : ℝ,∀ N,
        |∫ x,a x*inner ℝ (weakGradient (W N) x)
          ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure|≤K*s^N) :
    WeightedAnnihilation a w u c := by
  intro f hf hfc hfs
  obtain ⟨K,hK⟩ := hfinite f hf hfc hfs
  have ht₀ : Tendsto (fun N : ℕ => K*s^N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_mul K
  have ht := squeeze_zero (fun N => abs_nonneg _ ) hK ht₀
  have hlim := (weighted_integral_tendsto a ha C hC hb hW hu c f hf).abs
  exact abs_eq_zero.mp (tendsto_nhds_unique hlim ht)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma compact_smooth_lipschitz_bound (f : R3 → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f) :
    ∃ L : ℝ,0≤L ∧ ∀ x y,|f x-f y|≤L*dist x y := by
  obtain ⟨L,hL⟩ := (hfc.fderiv ℝ).exists_bound_of_continuous
    (hf.fderiv_right (m:=0) (by simp)).continuous
  have hL₀ : 0≤L := (norm_nonneg _).trans (hL 0)
  have hlip : LipschitzWith ⟨L,hL₀⟩ f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by simp)) (fun x => hL x)
  refine ⟨L,hL₀,?_⟩
  intro x y
  have hh := hlip.dist_le_mul x y
  change dist (f x) (f y) ≤ L*dist x y at hh
  simpa only [Real.dist_eq] using hh

theorem weighted_annihilation_of_surface_sources (a : R3 → ℝ)
    (ha : AEStronglyMeasurable a ballMeasure) (C : ℝ) (hC : 0≤C)
    (hb : ∀ᵐ x ∂ballMeasure,|a x|≤C) {W : ℕ → H1} {w u : H1}
    (hW : Tendsto W atTop (𝓝 w)) {M : ℝ} (hM : 0≤M)
    (hu : ∀ᵐ x ∂ballMeasure,|weakValue u x|≤M) (c s D : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hD : 0≤D)
    (ι : ℕ → Type*) [∀ N,Fintype (ι N)]
    (μ : ∀ N,ι N → Measure R3) [∀ N i,IsProbabilityMeasure (μ N i)]
    (q : ∀ N,ι N → ℝ) (t : ∀ N,ι N → R3 → ℝ) (x₀ : ∀ N,ι N → R3)
    (hq : ∀ N,(∑ i,|q N i|)≤2)
    (ht : ∀ N i,Integrable (t N i) (μ N i))
    (hz : ∀ N i,(∫ x,t N i x ∂μ N i)=0)
    (htb : ∀ N i,∀ᵐ x ∂μ N i,|t N i x|≤2*M)
    (hd : ∀ N i,∀ᵐ x ∂μ N i,dist x (x₀ N i)≤D*s^N)
    (hsource : ∀ (f : R3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) f →
      HasCompactSupport f → tsupport f⊆ball → ∀ N,
        (∫ x,a x*inner ℝ (weakGradient (W N) x)
          ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)=
        ∑ i,q N i*(∫ x,t N i x*f x ∂μ N i)) :
    WeightedAnnihilation a w u c := by
  apply weighted_annihilation_of_geometric_error a ha C hC hb hW hu c s hs0 hs1
  intro f hf hfc hfs
  obtain ⟨L,hL,hlip⟩ := compact_smooth_lipschitz_bound f hf hfc
  obtain ⟨A,hA⟩ := hfc.exists_bound_of_continuous hf.continuous
  refine ⟨4*M*L*D,?_⟩
  intro N
  rw [hsource f hf hfc hfs N]
  have hi (i : ι N) : Integrable (fun x => t N i x*f x) (μ N i) :=
    (ht N i).mul_bdd hf.continuous.aestronglyMeasurable (Eventually.of_forall hA)
  have hosc (i : ι N) : ∀ᵐ x ∂μ N i,|f x-f (x₀ N i)|≤L*(D*s^N) := by
    filter_upwards [hd N i] with x hx
    exact (hlip x (x₀ N i)).trans (mul_le_mul_of_nonneg_left hx hL)
  have hbound := finite_surface_source_bound (μ N) (q N) (t N) (fun _ => f)
    (fun i => f (x₀ N i)) M (L*(D*s^N)) hM (by positivity) (hq N) (ht N) hi (hz N) (htb N) hosc
  convert hbound using 1
  ring

end ScalarConductivity

end
end

end OAI
