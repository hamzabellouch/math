import OAI.Probability.GaussianReplacement.CriticalGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def criticalRefinement {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ)
    (p : Sphere d×W) : ℕ×ℤ :=
  (criticalIndex (messagePosterior P p.2) ℓ p.1, criticalLevel (messagePosterior P p.2) ℓ p.1)

lemma measurable_criticalRefinement {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [Countable W] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) :
    Measurable (criticalRefinement P ℓ) := by
  apply measurable_from_prod_countable_left
  intro w
  exact (measurable_criticalIndex (messagePosterior P w) ℓ).prodMk
    (measurable_criticalLevel (messagePosterior P w) ℓ)

lemma posterior_sphere_growth {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hd : 1 ≤ d) {w : W} (hw : P.snd {w} ≠ 0) :
    LocalGrowth (messagePosterior P w) (d-1) ((P.snd {w}).toReal⁻¹*(3*4^d)) := by
  apply dominatedSphere_growth (messagePosterior P w) (by positivity) _ hd le_rfl
  have h := messagePosterior_le P hw
  rw [hσ] at h
  convert h using 1
  rw [← ENNReal.toReal_inv,ENNReal.ofReal_toReal (by simpa using hw)]

lemma criticalRefinement_size {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) {p : Sphere d×W} (hp : P.snd {p.2} ≠ 0) :
    ((criticalRefinement P ℓ p).1:ℝ) + 2*((criticalRefinement P ℓ p).2.natAbs:ℝ) ≤
      20*((d:ℝ)+1-Real.log (P.snd {p.2}).toReal) := by
  let D := (P.snd {p.2}).toReal⁻¹*(3*4^d)
  have hd : 1 ≤ d := by omega
  have ha : 0 < (P.snd {p.2}).toReal := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have ha1 : (P.snd {p.2}).toReal ≤ 1 := by
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one : P.snd {p.2} ≤ 1))
  have hinv : 1 ≤ (P.snd {p.2}).toReal⁻¹ := (one_le_inv₀ ha).mpr ha1
  have h4 : (1:ℝ) ≤ 4^d := one_le_pow₀ (by norm_num)
  have hD : 1 ≤ D := by dsimp only [D]; nlinarith
  have hg := posterior_sphere_growth P hσ hd hp
  have hj := criticalIndex_bound (messagePosterior P p.2) D hD hg hℓ p.1
  obtain ⟨hqlo,hqhi⟩ := criticalLevel_bounds (messagePosterior P p.2) D hD hg hℓ p.1
  have hlog : Real.log D ≤ -Real.log (P.snd {p.2}).toReal + 2 + 3*d := by
    dsimp only [D]
    rw [Real.log_mul (inv_ne_zero ha.ne') (by positivity),Real.log_inv,
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),Real.log_pow]
    have h3 : Real.log 3 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)]
    have h4 : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
    nlinarith [Nat.cast_nonneg (α:=ℝ) d]
  have hn : ((d-1:ℕ):ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hl : (ℓ:ℝ) ≤ d := by exact_mod_cast (hℓ.le.trans (Nat.sub_le d 1))
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hqabs : |(criticalLevel (messagePosterior P p.2) ℓ p.1:ℝ)| ≤
      Real.log D + (d-1:ℕ) + 1 + ℓ := by
    apply abs_le.mpr
    constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) ℓ,Nat.cast_nonneg (α:=ℝ) (d-1)]
  have habs : ((criticalLevel (messagePosterior P p.2) ℓ p.1).natAbs:ℝ) =
      |(criticalLevel (messagePosterior P p.2) ℓ p.1:ℝ)| := by simp
  change (criticalIndex (messagePosterior P p.2) ℓ p.1:ℝ) +
    2*((criticalLevel (messagePosterior P p.2) ℓ p.1).natAbs:ℝ) ≤ _
  rw [habs]
  nlinarith [atom_surprisal_nonneg P.snd p.2,Nat.cast_nonneg (α:=ℝ) d]

lemma criticalRefinement_entropy {d ℓ : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [Countable W] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (hσ : P.fst = uniformSphere d)
    (hℓ : ℓ < d-1) (hH : shannonEntropy P.snd ≠ ∞) :
    shannonEntropy (P.map (criticalRefinement P ℓ)) ≠ ∞ ∧
      (shannonEntropy (P.map (criticalRefinement P ℓ))).toReal ≤
        1 + 2*Real.log (20*((d:ℝ)+1+(shannonEntropy P.snd).toReal)+1) := by
  let E := criticalRefinement P ℓ
  have hE : Measurable E := measurable_criticalRefinement P ℓ
  let c : W → ℝ := fun w => -Real.log (P.snd {w}).toReal
  have hc : Integrable c P.snd := entropy_finite_integrable P.snd hH
  have hcp : Integrable (fun p : Sphere d×W => c p.2) P :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_snd.aemeasurable).mp hc
  let b : Sphere d×W → ℝ := fun p => 20*((d:ℝ)+1+c p.2)
  have hbi : Integrable b P := ((integrable_const _).add hcp).const_mul 20
  have hle : ∀ᵐ p ∂P, ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ) ≤ b p := by
    have hp := (ae_map_iff measurable_snd.aemeasurable
      ((Set.to_countable _).measurableSet)).mp (ae_positive_atom P.snd)
    filter_upwards [hp] with p hp
    exact criticalRefinement_size P hσ hℓ hp
  have hfi : Integrable (fun p => ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ)) P := by
    apply hbi.mono' (((measurable_of_countable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ))).comp hE).aestronglyMeasurable)
    filter_upwards [hle] with p hp
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ((E p).1:ℝ)+2*((E p).2.natAbs:ℝ))] using hp
  let : IsProbabilityMeasure (P.map E) := inferInstance
  have hi : Integrable (fun x : ℕ×ℤ => (x.1:ℝ)+2*(x.2.natAbs:ℝ)) (P.map E) :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable hE.aemeasurable).mpr hfi
  have hM : 1 ≤ 20*((d:ℝ)+1+(shannonEntropy P.snd).toReal) := by
    nlinarith [ENNReal.toReal_nonneg (a:=shannonEntropy P.snd), Nat.cast_nonneg (α:=ℝ) d]
  apply natInt_entropy _ hM hi
  rw [integral_map hE.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  calc
    _ ≤ ∫ p, b p ∂P := integral_mono_ae hfi hbi hle
    _ = _ := by
      dsimp only [b]
      rw [integral_const_mul,integral_add (integrable_const _) hcp,integral_const,probReal_univ,one_smul,
        ←integral_map measurable_snd.aemeasurable (measurable_of_countable c).aestronglyMeasurable]
      rw [←Measure.snd]
      dsimp only [c]
      rw [integral_surprisal]



lemma llr_chain_ae {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [SigmaFinite P] [SigmaFinite Q] [SigmaFinite R]
    (hPQ : P ≪ Q) (hQR : Q ≪ R) :
    llr P R =ᵐ[P] fun x => llr P Q x + llr Q R x := by
  filter_upwards [hPQ.ae_le (Measure.rnDeriv_mul_rnDeriv' (μ:=P) hQR),
    Measure.rnDeriv_pos hPQ, hPQ.ae_le (Measure.rnDeriv_ne_top P Q),
    hPQ.ae_le (Measure.rnDeriv_pos hQR), (hPQ.trans hQR).ae_le (Measure.rnDeriv_ne_top Q R)]
    with x he hp hpt hq hqt
  simp only [llr_def,←he,Pi.mul_apply,ENNReal.toReal_mul]
  exact Real.log_mul (ENNReal.toReal_pos hp.ne' hpt).ne' (ENNReal.toReal_pos hq.ne' hqt).ne'



lemma density_log_integrable_and_gibbs {A : Type*} [MeasurableSpace A]
    (P Q Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (hPQ : P ≪ Q) (hQΛ : Q ≪ Λ)
    (hpos : Integrable (fun x => max (llr P Λ x) 0) P)
    (href : Integrable (llr Q Λ) P) :
    Integrable (llr P Λ) P ∧ (∫ x, llr Q Λ x ∂P) ≤ ∫ x, llr P Λ x ∂P := by
  have he := llr_chain_ae P Q Λ hPQ hQΛ
  have hb : ∀ᵐ x ∂P, llr P Q x ≤ max (llr P Λ x) 0 - llr Q Λ x := by
    filter_upwards [he] with x hx
    linarith [le_max_left (llr P Λ x) 0]
  have hk := klDiv_bound_of_llr_le P Q hPQ _ (hpos.sub href) hb
  have hi := (klDiv_ne_top_iff.mp hk.1).2
  have hpi : Integrable (llr P Λ) P := (hi.add href).congr he.symm
  refine ⟨hpi,?_⟩
  have hn : 0 ≤ ∫ x, llr P Q x ∂P := by
    simpa using integral_llr_add_sub_measure_univ_nonneg hPQ hi
  have heint : (∫ x, llr P Λ x ∂P) = (∫ x, llr P Q x ∂P) + ∫ x, llr Q Λ x ∂P := by
    rw [integral_congr_ae he,integral_add hi href]
  linarith

lemma klDiv_chain_finite {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hPQ : klDiv P Q ≠ ∞) (hQR : Q ≪ R) (hi : Integrable (llr Q R) P) :
    klDiv P R ≠ ∞ ∧ (klDiv P R).toReal = (klDiv P Q).toReal + ∫ x, llr Q R x ∂P := by
  obtain ⟨hpq,hpi⟩ := klDiv_ne_top_iff.mp hPQ
  have he := llr_chain_ae P Q R hpq hQR
  have hpr : Integrable (llr P R) P := (hpi.add hi).congr he.symm
  refine ⟨klDiv_ne_top (hpq.trans hQR) hpr,?_⟩
  rw [toReal_klDiv_of_measure_eq (hpq.trans hQR) (by simp),
    toReal_klDiv_of_measure_eq hpq (by simp),integral_congr_ae he,integral_add hpi hi]

lemma density_gibbs_integrable {A : Type*} [MeasurableSpace A]
    (P Q Λ : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (hP : Λ.withDensity p = P)
    (g : A → ℝ) (hg : Measurable g) (hgpos : ∀ x, 0 < g x)
    (hQ : Λ.withDensity (fun x => ENNReal.ofReal (g x)) = Q)
    (hpos : Integrable (fun x => max (Real.log (p x).toReal) 0) P)
    (hgi : Integrable (fun x => Real.log (g x)) P) :
    Integrable (fun x => Real.log (p x).toReal) P ∧
      (∫ x, Real.log (g x) ∂P) ≤ ∫ x, Real.log (p x).toReal ∂P := by
  have hPΛ : P ≪ Λ := by rw [←hP]; exact withDensity_absolutelyContinuous _ _
  have hQΛ : Q ≪ Λ := by rw [←hQ]; exact withDensity_absolutelyContinuous _ _
  have hΛQ : Λ ≪ Q := by
    rw [←hQ]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
  have hpd : P.rnDeriv Λ =ᵐ[P] p := by
    apply hPΛ.ae_le
    rw [←hP]
    exact Measure.rnDeriv_withDensity Λ hp
  have hgd : Q.rnDeriv Λ =ᵐ[P] fun x => ENNReal.ofReal (g x) := by
    apply hPΛ.ae_le
    rw [←hQ]
    exact Measure.rnDeriv_withDensity Λ hg.ennreal_ofReal
  have hpll : llr P Λ =ᵐ[P] fun x => Real.log (p x).toReal := by
    exact hpd.mono (fun x hx => by simp only [llr_def,hx])
  have hgll : llr Q Λ =ᵐ[P] fun x => Real.log (g x) := by
    exact hgd.mono (fun x hx => by simp only [llr_def,hx,ENNReal.toReal_ofReal (hgpos x).le])
  obtain ⟨hi,hb⟩ := density_log_integrable_and_gibbs P Q Λ (hPΛ.trans hΛQ) hQΛ
    (hpos.congr (hpll.symm.fun_comp (fun t : ℝ => max t 0))) (hgi.congr hgll.symm)
  exact ⟨hi.congr hpll,by simpa only [integral_congr_ae hpll,integral_congr_ae hgll] using hb⟩



lemma cross_llr_integrable {A : Type*} [MeasurableSpace A]
    (P Q R : Measure A) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (hPQ : klDiv P Q ≠ ∞) (hQR : Q ≪ R)
    (u : A → ℝ) (hu : Integrable u P) (hle : ∀ᵐ x ∂P, llr Q R x ≤ u x) :
    Integrable (llr Q R) P ∧ klDiv P R ≠ ∞ := by
  obtain ⟨ha,hi⟩ := klDiv_ne_top_iff.mp hPQ
  have he := llr_chain_ae P Q R ha hQR
  have hb : ∀ᵐ x ∂P, llr P R x ≤ llr P Q x + u x := by
    filter_upwards [he,hle] with x hx hy
    rw [hx]
    exact add_le_add_right hy _
  have hk := klDiv_bound_of_llr_le P R (ha.trans hQR) _ (hi.add hu) hb
  have hint := (klDiv_ne_top_iff.mp hk.1).2
  have hsub : (fun x => llr P R x - llr P Q x) =ᵐ[P] llr Q R := by
    filter_upwards [he] with x hx
    rw [hx]
    ring
  exact ⟨(hint.sub hi).congr hsub,hk.1⟩

lemma llr_of_two_densities {A : Type*} [MeasurableSpace A]
    (Q R Λ : Measure A) [IsProbabilityMeasure Q] [IsProbabilityMeasure R] [SigmaFinite Λ]
    (p : A → ℝ≥0∞) (hp : Measurable p) (hQ : Λ.withDensity p = Q)
    (g : A → ℝ) (hg : Measurable g) (hgpos : ∀ x, 0 < g x)
    (hR : Λ.withDensity (fun x => ENNReal.ofReal (g x)) = R) :
    Q ≪ R ∧ llr Q R =ᵐ[Q] fun x => Real.log (p x).toReal - Real.log (g x) := by
  have hQΛ : Q ≪ Λ := by rw [←hQ]; exact withDensity_absolutelyContinuous _ _
  have hRΛ : R ≪ Λ := by rw [←hR]; exact withDensity_absolutelyContinuous _ _
  have hΛR : Λ ≪ R := by
    rw [←hR]
    exact withDensity_absolutelyContinuous' hg.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hgpos x)).ne'))
  have hQR := hQΛ.trans hΛR
  refine ⟨hQR,?_⟩
  have hpRN : Q.rnDeriv Λ =ᵐ[Q] p := by
    apply hQΛ.ae_le
    rw [←hQ]
    exact Measure.rnDeriv_withDensity Λ hp
  have hgRN : R.rnDeriv Λ =ᵐ[Q] fun x => ENNReal.ofReal (g x) := by
    apply hQΛ.ae_le
    rw [←hR]
    exact Measure.rnDeriv_withDensity Λ hg.ennreal_ofReal
  filter_upwards [llr_chain_ae Q R Λ hQR hRΛ,hpRN,hgRN] with x hx hpq hgq
  simp only [llr_def,hpq,hgq,ENNReal.toReal_ofReal (hgpos x).le] at hx
  simp only [llr_def]
  linarith



lemma volume_ae_exactDensity_rnDeriv {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) :
    (fun y => exactDensity ρ G y) =ᵐ[volume] (labelLaw ρ G).rnDeriv volume := by
  filter_upwards [volume_ae_cube_limit ρ G,
    Besicovitch.ae_tendsto_rnDeriv (labelLaw ρ G) volume] with y he hy
  have ht := hy.comp tendsto_cube_scale
  have hratio : (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) =ᶠ[atTop]
      (fun j : ℕ => labelLaw ρ G (Metric.closedBall y (1/(j:ℝ))) /
        volume (Metric.closedBall y (1/(j:ℝ)))) := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact cubeAverage_eq_ball_ratio ρ G y (by positivity)
  exact tendsto_nhds_unique he (ht.congr' hratio.symm)

lemma labelLaw_withDensity_exact {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) (h : labelLaw ρ G ≪ volume) :
    volume.withDensity (fun y => exactDensity ρ G y) = labelLaw ρ G := by
  rw [withDensity_congr_ae (volume_ae_exactDensity_rnDeriv ρ G)]
  exact Measure.withDensity_rnDeriv_eq _ _ h

lemma map_fiber_withDensity {A S Y : Type*} [MeasurableSpace A] [MeasurableSpace S]
    [MeasurableSpace Y] (μ : Measure A) (ν : Measure S) (L : Measure Y)
    [SFinite μ] [SFinite ν] [SFinite L]
    (f : A×S → Y) (hf : Measurable f) (p : A×Y → ℝ≥0∞) (hp : Measurable p)
    (h : ∀ᵐ a ∂μ, L.withDensity (fun y => p (a,y)) = ν.map (fun s => f (a,s))) :
    (μ.prod L).withDensity p = (μ.prod ν).map (fun z => (z.1,f z)) := by
  apply Measure.ext
  intro t ht
  rw [withDensity_apply _ ht,←lintegral_indicator ht,lintegral_prod _ (hp.indicator ht).aemeasurable,
    Measure.map_apply (measurable_fst.prodMk hf) ht,
    Measure.prod_apply (ht.preimage (measurable_fst.prodMk hf))]
  apply lintegral_congr_ae
  filter_upwards [h] with a ha
  have ht' : MeasurableSet {y : Y | (a,y) ∈ t} := ht.preimage (measurable_const.prodMk measurable_id)
  have hf' : Measurable (fun s : S => f (a,s)) := hf.comp (measurable_const.prodMk measurable_id)
  calc
    _ = L.withDensity (fun y => p (a,y)) {y | (a,y) ∈ t} := by
      rw [withDensity_apply _ ht',←lintegral_indicator ht']
      rfl
    _ = _ := by rw [ha,Measure.map_apply hf' ht']; rfl

def projectionJoint {d k : ℕ} (ρ : Measure (Sphere d)) (μ : Measure (Rows k d)) :
    Measure (Rows k d×(Fin k→ℝ)) :=
  (μ.prod ρ).map (fun z => (z.1,label z.1 (z.2:Vector d)))

lemma projectionJoint_withDensity {d k : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (μ : Measure (Rows k d)) [SFinite μ]
    (h : ∀ᵐ G ∂μ, labelLaw ρ G ≪ volume) :
    (μ.prod volume).withDensity (fun gy => exactDensity ρ gy.1 gy.2) = projectionJoint ρ μ := by
  apply map_fiber_withDensity μ ρ volume _ (measurable_own_label (d:=d) (k:=k)) _
    (measurable_exactDensity ρ)
  exact h.mono (fun G hG => labelLaw_withDensity_exact ρ G hG)



lemma gaussian_inner_sq_integrable {d : ℕ} (v : Vector d) :
    Integrable (fun a : Vector d => ⟪v,a⟫^2) (stdGaussian (Vector d)) := by
  exact (IsGaussian.memLp_dual (stdGaussian (Vector d)) (innerSL ℝ v) 2 (by simp)).integrable_sq

lemma gaussian_inner_sq_integral {d : ℕ} (v : Vector d) :
    (∫ a : Vector d, ⟪v,a⟫^2 ∂stdGaussian (Vector d)) = ‖v‖^2 := by
  have h := variance_dual_stdGaussian (innerSL ℝ v)
  rw [variance_eq_integral (by fun_prop),integral_strongDual_stdGaussian] at h
  simpa using h

def projectionSquare {k d : ℕ} (G : Rows k d) (v : Vector d) : ℝ := ∑ i, (label G v i)^2

lemma projectionSquare_nonneg {k d : ℕ} (G : Rows k d) (v : Vector d) :
    0 ≤ projectionSquare G v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma projectionSquare_integrable {k d : ℕ} (v : Vector d) :
    Integrable (fun G : Rows k d => projectionSquare G v) (gaussianRows k d) := by
  apply integrable_finsetSum
  intro i _
  exact integrable_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (i:=i) (gaussian_inner_sq_integrable v)

lemma projectionSquare_integral {k d : ℕ} (v : Vector d) :
    (∫ G : Rows k d, projectionSquare G v ∂gaussianRows k d) = (k:ℝ)*‖v‖^2 := by
  unfold projectionSquare
  rw [integral_finsetSum]
  · simp only [label,gaussianRows,integral_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (by fun_prop : AEStronglyMeasurable (fun a : Vector d => ⟪v,a⟫^2) (stdGaussian _)),gaussian_inner_sq_integral,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · intro i _
    exact integrable_comp_eval (μ:=fun _ : Fin k => stdGaussian (Vector d)) (i:=i) (gaussian_inner_sq_integrable v)

def normalizer (R : ℝ) : ℝ := Real.sqrt (2*Real.pi*(R^2))

def radiusVariance (R : ℝ) : ℝ≥0 := ⟨R^2,sq_nonneg R⟩

lemma radiusVariance_ne_zero {R : ℝ} (hR : 0 < R) : radiusVariance R ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ≥0 => (v:ℝ)) h
  exact (sq_pos_of_pos hR).ne' this

def gaussianProductPDF {k : ℕ} (R : ℝ) (c y : Fin k → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (c i) (radiusVariance R) (y i)

lemma gaussianProductPDF_pos {k : ℕ} {R : ℝ} (hR : 0 < R) (c y : Fin k→ℝ) :
    0 < gaussianProductPDF R c y := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (radiusVariance_ne_zero hR)

lemma measurable_gaussianProductPDF {k : ℕ} (R : ℝ) :
    Measurable (fun cy : (Fin k→ℝ)×(Fin k→ℝ) => gaussianProductPDF R cy.1 cy.2) := by
  unfold gaussianProductPDF
  fun_prop

lemma integrable_gaussianProductPDF {k : ℕ} (R : ℝ) (c : Fin k→ℝ) :
    Integrable (gaussianProductPDF R c) volume :=
  Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (c i) _)

lemma integral_gaussianProductPDF {k : ℕ} {R : ℝ} (hR : 0<R) (c : Fin k→ℝ) :
    (∫ y, gaussianProductPDF R c y) = 1 := by
  unfold gaussianProductPDF
  change (∫ y, ∏ i, gaussianPDFReal (c i) (radiusVariance R) (y i) ∂Measure.pi (fun _ : Fin k => (volume : Measure ℝ))) = 1
  rw [integral_fintype_prod_eq_prod]
  simp [integral_gaussianPDFReal_eq_one _ (radiusVariance_ne_zero hR)]

lemma normalizer_pos {R : ℝ} (hR : 0 < R) : 0 < normalizer R := by
  unfold normalizer
  positivity

lemma log_gaussianProductPDF {k : ℕ} {R : ℝ} (hR : 0<R) (c y : Fin k→ℝ) :
    Real.log (gaussianProductPDF R c y) = -(k:ℝ)*Real.log (normalizer R) -
      (∑ i, (y i-c i)^2)/(2*R^2) := by
  unfold gaussianProductPDF
  rw [Real.log_prod (fun i _ => (gaussianPDFReal_pos _ _ _ (radiusVariance_ne_zero hR)).ne')]
  simp only [gaussianPDFReal,show (radiusVariance R : ℝ) = R^2 from rfl]
  change (∑ i, Real.log ((normalizer R)⁻¹ * Real.exp (-(y i-c i)^2/(2*R^2)))) = _
  simp_rw [Real.log_mul (inv_ne_zero (normalizer_pos hR).ne') (Real.exp_pos _).ne',Real.log_inv,Real.log_exp]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [neg_div,Finset.sum_neg_distrib,←Finset.sum_div]
  ring

lemma log_normalizer_le {R : ℝ} (hR : 0<R) :
    Real.log (normalizer R) ≤ Real.log R + 3 := by
  have he : normalizer R = Real.sqrt (2*Real.pi)*R := by
    rw [normalizer,Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_of_pos hR]
  rw [he,Real.log_mul (by positivity) hR.ne']
  have hs : Real.sqrt (2*Real.pi) ≤ 4 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · linarith [Real.pi_lt_four]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt (2*Real.pi) by positivity)
  linarith

def coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) (G : Rows k d) (y : Fin k→ℝ) : ℝ :=
  (C.card:ℝ)⁻¹ * ∑ c ∈ C, gaussianProductPDF R (label G (c:Vector d)) y

lemma coverPDF_pos {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) (y : Fin k→ℝ) : 0 < coverPDF C R G y := by
  apply mul_pos (inv_pos.mpr (by exact_mod_cast hC.card_pos))
  exact Finset.sum_pos (fun c _ => gaussianProductPDF_pos hR _ _) hC

lemma measurable_coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) :
    Measurable (fun gy : Rows k d×(Fin k→ℝ) => coverPDF C R gy.1 gy.2) := by
  have hf (c : Sphere d) : Measurable (fun gy : Rows k d×(Fin k→ℝ) =>
      gaussianProductPDF R (label gy.1 (c:Vector d)) gy.2) := by
    unfold gaussianProductPDF
    apply Finset.measurable_prod
    intro i _
    have h1 : Measurable (fun gy : Rows k d×(Fin k→ℝ) => label gy.1 (c:Vector d) i) :=
      (measurable_pi_apply i).comp ((measurable_fixed_label (k:=k) c).comp measurable_fst)
    have h2 : Measurable (fun gy : Rows k d×(Fin k→ℝ) => gy.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact measurable_uncurry_gaussianPDFReal.comp (h1.prodMk (measurable_const.prodMk h2))
  have hsum : Measurable (fun gy : Rows k d×(Fin k→ℝ) =>
      ∑ c ∈ C, gaussianProductPDF R (label gy.1 (c:Vector d)) gy.2) :=
    Finset.measurable_sum C (fun c _ => hf c)
  exact hsum.const_mul _

lemma integral_coverPDF {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) : (∫ y, coverPDF C R G y) = 1 := by
  unfold coverPDF
  rw [integral_const_mul,integral_finsetSum]
  · simp only [integral_gaussianProductPDF hR,Finset.sum_const,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hC.card_pos.ne')
  · intro c _
    exact integrable_gaussianProductPDF R _

lemma integrable_coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) (G : Rows k d) :
    Integrable (coverPDF C R G) volume :=
  (integrable_finsetSum _ (fun _ _ => integrable_gaussianProductPDF R _)).const_mul _

lemma lintegral_coverPDF {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) : (∫⁻ y, ENNReal.ofReal (coverPDF C R G y)) = 1 := by
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_coverPDF C R G)
    (ae_of_all _ (fun y => (coverPDF_pos hC hR G y).le)),integral_coverPDF hC hR]
  simp

lemma gaussianProductPDF_le_exp {k : ℕ} {R : ℝ} (hR : 0<R) (c y : Fin k→ℝ) :
    gaussianProductPDF R c y ≤ Real.exp (-(k:ℝ)*Real.log (normalizer R)) := by
  rw [←Real.log_le_iff_le_exp (gaussianProductPDF_pos hR c y),log_gaussianProductPDF hR]
  have hn : 0 ≤ (∑ i, (y i-c i)^2)/(2*R^2) := by positivity
  linarith

lemma log_coverPDF_upper {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (G : Rows k d) (y : Fin k→ℝ) :
    Real.log (coverPDF C R G y) ≤ -(k:ℝ)*Real.log (normalizer R) := by
  rw [Real.log_le_iff_le_exp (coverPDF_pos hC hR G y)]
  calc
    _ ≤ (C.card:ℝ)⁻¹ * ∑ c ∈ C, Real.exp (-(k:ℝ)*Real.log (normalizer R)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun c _ => gaussianProductPDF_le_exp hR _ _)
    _ = _ := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hC.card_pos.ne'),one_mul]

lemma neg_log_coverPDF_le {k d : ℕ} {C : Finset (Sphere d)} {c : Sphere d}
    (hc : c ∈ C) {R : ℝ} (hR : 0<R) (G : Rows k d) (s : Sphere d) :
    -Real.log (coverPDF C R G (label G (s:Vector d))) ≤
      Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) +
        projectionSquare G ((s:Vector d)-(c:Vector d))/(2*R^2) := by
  have hC : C.Nonempty := ⟨c,hc⟩
  have hcard : 0 < (C.card:ℝ) := by exact_mod_cast hC.card_pos
  have hb : (C.card:ℝ)⁻¹ * gaussianProductPDF R (label G (c:Vector d)) (label G (s:Vector d)) ≤
      coverPDF C R G (label G (s:Vector d)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (f:=fun x : Sphere d => gaussianProductPDF R (label G (x:Vector d)) (label G (s:Vector d))) (fun x _ => (gaussianProductPDF_pos hR _ _).le) hc
  have hl := Real.log_le_log (mul_pos (inv_pos.mpr hcard) (gaussianProductPDF_pos hR _ _)) hb
  rw [Real.log_mul (inv_ne_zero hcard.ne') (gaussianProductPDF_pos hR _ _).ne',
    Real.log_inv,log_gaussianProductPDF hR] at hl
  have he : (∑ i, (label G (s:Vector d) i - label G (c:Vector d) i)^2) =
      projectionSquare G ((s:Vector d)-(c:Vector d)) := by
    simp only [projectionSquare,label,inner_sub_left]
  rw [he] at hl
  linarith

lemma projectionSquare_joint_integrable {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (c : Sphere d) :
    Integrable (fun z : Rows k d×Sphere d => projectionSquare z.1 ((z.2:Vector d)-(c:Vector d)))
      ((gaussianRows k d).prod ρ) := by
  have hm : Measurable (fun z : Rows k d×Sphere d => projectionSquare z.1 ((z.2:Vector d)-(c:Vector d))) := by
    unfold projectionSquare label
    exact Finset.measurable_sum _ (fun i _ => ((measurable_subtype_coe.comp measurable_snd).sub measurable_const |>.inner ((measurable_pi_apply i).comp measurable_fst) |>.pow_const 2))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun s => projectionSquare_integrable ((s:Vector d)-(c:Vector d)))
  · have he (s : Sphere d) : (∫ G : Rows k d, ‖projectionSquare G ((s:Vector d)-(c:Vector d))‖ ∂gaussianRows k d) =
        (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2 := by
      simp_rw [Real.norm_eq_abs,abs_of_nonneg (projectionSquare_nonneg _ _)]
      exact projectionSquare_integral _
    simp_rw [he]
    apply (integrable_const (4*(k:ℝ))).mono' (by fun_prop)
    apply ae_of_all
    intro s
    have hs : ‖(s:Vector d)-(c:Vector d)‖ ≤ 2 := by
      rw [←dist_eq_norm]
      exact sphere_dist_le_two s c
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hsq : ‖(s:Vector d)-(c:Vector d)‖^2 ≤ 4 := by nlinarith [norm_nonneg ((s:Vector d)-(c:Vector d))]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α:=ℝ) k)]

lemma log_coverPDF_integrable_rows {k d : ℕ} {C : Finset (Sphere d)} (hC : C.Nonempty)
    {R : ℝ} (hR : 0<R) (s : Sphere d) :
    Integrable (fun G : Rows k d => Real.log (coverPDF C R G (label G (s:Vector d)))) (gaussianRows k d) := by
  obtain ⟨c,hc⟩ := hC
  have hm := ((measurable_coverPDF (k:=k) C R).comp (measurable_id.prodMk (measurable_fixed_label s))).log
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (ae_of_all _ (fun G => neg_le.mp (neg_log_coverPDF_le hc hR G s)))
    (ae_of_all _ (fun G => log_coverPDF_upper ⟨c,hc⟩ hR G _))
  · exact ((integrable_const _).add ((projectionSquare_integrable ((s:Vector d)-(c:Vector d))).div_const _)).neg
  · exact integrable_const _

lemma log_coverPDF_joint_integrable {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R) :
    Integrable (fun z : Rows k d×Sphere d => Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ) := by
  obtain ⟨c,hc⟩ := hC
  have hm := ((measurable_coverPDF (k:=k) C R).comp (measurable_fst.prodMk measurable_own_label)).log
  apply integrable_of_le_of_le hm.aestronglyMeasurable
    (ae_of_all _ (fun z => neg_le.mp (neg_log_coverPDF_le hc hR z.1 z.2)))
    (ae_of_all _ (fun z => log_coverPDF_upper ⟨c,hc⟩ hR z.1 _))
  · exact ((integrable_const _).add ((projectionSquare_joint_integrable ρ c).div_const _)).neg
  · exact integrable_const _

lemma integral_neg_log_coverPDF_rows_le {k d : ℕ} {C : Finset (Sphere d)} {c : Sphere d}
    (hc : c∈C) {R : ℝ} (hR : 0<R) (s : Sphere d) (hs : dist s c ≤ 2*R) :
    (∫ G : Rows k d, -Real.log (coverPDF C R G (label G (s:Vector d))) ∂gaussianRows k d) ≤
      Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  have hi := (log_coverPDF_integrable_rows (k:=k) ⟨c,hc⟩ hR s).neg
  have hqi := ((projectionSquare_integrable (k:=k) ((s:Vector d)-(c:Vector d))).div_const (2*R^2))
  calc
    _ ≤ ∫ G : Rows k d, Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) +
        projectionSquare G ((s:Vector d)-(c:Vector d))/(2*R^2) ∂gaussianRows k d :=
      integral_mono hi ((integrable_const _).add hqi) (fun G => neg_log_coverPDF_le hc hR G s)
    _ = Real.log (C.card:ℝ) + (k:ℝ)*Real.log (normalizer R) + (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2/(2*R^2) := by
      rw [integral_add (integrable_const _) hqi,integral_const,probReal_univ,one_smul,integral_div,projectionSquare_integral]
    _ ≤ _ := by
      have hs' : ‖(s:Vector d)-(c:Vector d)‖ ≤ 2*R := hs
      have hb : (k:ℝ)*‖(s:Vector d)-(c:Vector d)‖^2/(2*R^2) ≤ 2*k := by
        apply (div_le_iff₀ (by positivity)).mpr
        have hn : ‖(s:Vector d)-(c:Vector d)‖^2 ≤ (2*R)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hs'
        nlinarith [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α:=ℝ) k)]
      nlinarith [mul_le_mul_of_nonneg_left (log_normalizer_le hR) (Nat.cast_nonneg (α:=ℝ) k)]

lemma integral_neg_log_coverPDF_le {k d : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R)
    (hcover : ∀ᵐ s ∂ρ, ∃ c∈C, dist s c ≤ 2*R) :
    (∫ z : Rows k d×Sphere d, -Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d)))
      ∂(gaussianRows k d).prod ρ) ≤ Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  have hi := (log_coverPDF_joint_integrable (k:=k) ρ hC hR).neg
  rw [integral_prod_symm (fun z : Rows k d×Sphere d => -Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d)))) hi]
  calc
    _ ≤ ∫ _s, Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k ∂ρ := by
      apply integral_mono_ae hi.integral_prod_right (integrable_const _)
      filter_upwards [hcover] with s hs
      obtain ⟨c,hc,hsc⟩ := hs
      exact integral_neg_log_coverPDF_rows_le hc hR s hsc
    _ = _ := by simp



instance projectionJoint_probability {d k : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    (μ : Measure (Rows k d)) [IsProbabilityMeasure μ] : IsProbabilityMeasure (projectionJoint ρ μ) := by
  unfold projectionJoint
  infer_instance



lemma projection_cover_entropy {d k : ℕ} (ρ : Measure (Sphere d)) [IsProbabilityMeasure ρ]
    (hAC : ∀ᵐ G ∂gaussianRows k d, labelLaw ρ G ≪ volume)
    (hpos : Integrable (fun z : Rows k d×Sphere d => logPositive (exactDensity ρ z.1 (label z.1 (z.2:Vector d))))
      ((gaussianRows k d).prod ρ))
    {C : Finset (Sphere d)} (hC : C.Nonempty) {R : ℝ} (hR : 0<R)
    (hcover : ∀ᵐ s ∂ρ, ∃ c∈C, dist s c ≤ 2*R) :
    Integrable (fun z : Rows k d×Sphere d => Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal)
      ((gaussianRows k d).prod ρ) ∧
    -(∫ z : Rows k d×Sphere d, Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal
      ∂(gaussianRows k d).prod ρ) ≤ Real.log (C.card:ℝ) + (k:ℝ)*Real.log R + 5*k := by
  let Λ : Measure (Rows k d×(Fin k→ℝ)) := (gaussianRows k d).prod volume
  let p : Rows k d×(Fin k→ℝ) → ℝ≥0∞ := fun z => exactDensity ρ z.1 z.2
  let g : Rows k d×(Fin k→ℝ) → ℝ := fun z => coverPDF C R z.1 z.2
  let Q := Λ.withDensity (fun z => ENNReal.ofReal (g z))
  have hp : Measurable p := measurable_exactDensity ρ
  have hg : Measurable g := measurable_coverPDF C R
  have hgpos : ∀ z, 0 < g z := fun z => coverPDF_pos hC hR z.1 z.2
  let : IsProbabilityMeasure Q := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ]
    rw [lintegral_prod _ hg.ennreal_ofReal.aemeasurable]
    simp only [g,lintegral_coverPDF hC hR,lintegral_const,measure_univ,mul_one]
  have hm : Measurable (fun z : Rows k d×Sphere d => (z.1,label z.1 (z.2:Vector d))) :=
    measurable_fst.prodMk measurable_own_label
  have hpi : Integrable (fun z => max (Real.log (p z).toReal) 0) (projectionJoint ρ (gaussianRows k d)) :=
    (integrable_map_measure (hp.ennreal_toReal.log.max measurable_const).aestronglyMeasurable hm.aemeasurable).mpr hpos
  have hgi : Integrable (fun z => Real.log (g z)) (projectionJoint ρ (gaussianRows k d)) :=
    (integrable_map_measure hg.log.aestronglyMeasurable hm.aemeasurable).mpr (log_coverPDF_joint_integrable ρ hC hR)
  obtain ⟨hlog,hbound⟩ := density_gibbs_integrable (projectionJoint ρ (gaussianRows k d)) Q Λ p hp
    (projectionJoint_withDensity ρ (gaussianRows k d) hAC) g hg hgpos rfl hpi hgi
  have hlog' := (integrable_map_measure hp.ennreal_toReal.log.aestronglyMeasurable hm.aemeasurable).mp hlog
  refine ⟨hlog',?_⟩
  have heP : (∫ z, Real.log (p z).toReal ∂projectionJoint ρ (gaussianRows k d)) =
      ∫ z : Rows k d×Sphere d, Real.log (exactDensity ρ z.1 (label z.1 (z.2:Vector d))).toReal ∂(gaussianRows k d).prod ρ :=
    integral_map hm.aemeasurable hp.ennreal_toReal.log.aestronglyMeasurable
  have heQ : (∫ z, Real.log (g z) ∂projectionJoint ρ (gaussianRows k d)) =
      ∫ z : Rows k d×Sphere d, Real.log (coverPDF C R z.1 (label z.1 (z.2:Vector d))) ∂(gaussianRows k d).prod ρ :=
    integral_map hm.aemeasurable hg.log.aestronglyMeasurable
  rw [heP,heQ] at hbound
  have hb := integral_neg_log_coverPDF_le (k:=k) ρ hC hR hcover
  rw [integral_neg] at hb
  linarith



end CurrentProjection

end

end OAI
