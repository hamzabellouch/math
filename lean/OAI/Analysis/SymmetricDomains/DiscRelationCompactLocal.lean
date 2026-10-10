import Mathlib
import OAI.Analysis.SymmetricDomains.ZeroLocusPolynomialSmooth

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

noncomputable def coordinateEnergy {n : ℕ} (z : Affine n) : ℝ := ∑ i, ‖z i‖ ^ 2

def peakLinear {n : ℕ} (p q : Affine n) : ℂ :=
  ∑ i, (2 : ℂ) * (starRingEnd ℂ (p i) * (q i - p i))

theorem peakLinear_re {n : ℕ} (p q : Affine n) :
    (peakLinear p q).re = coordinateEnergy q - coordinateEnergy p - coordinateEnergy (q-p) := by
  simp only [peakLinear, coordinateEnergy, Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

theorem coordinateEnergy_nonneg {n : ℕ} (z : Affine n) : 0 ≤ coordinateEnergy z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sq_norm_le_coordinateEnergy {n : ℕ} (z : Affine n) : ‖z‖^2 ≤ coordinateEnergy z := by
  have h : ‖z‖ ≤ Real.sqrt (coordinateEnergy z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i)
  exact (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mp h

theorem coordinateEnergy_continuous {n : ℕ} : Continuous (@coordinateEnergy n) := by
  unfold coordinateEnergy
  fun_prop

 theorem peakLinear_analytic {n : ℕ} (p : Affine n) : AnalyticOnNhd ℂ (peakLinear p) univ := by
  intro q _
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_const.mul (((ContinuousLinearMap.proj i : (Affine n) →L[ℂ] ℂ).analyticAt q).sub analyticAt_const))

 theorem peak_norm_identity {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (p q : Affine n) :
    ‖(MvPolynomial.eval q P / MvPolynomial.eval p P) * Complex.exp (peakLinear p q)‖ =
      (‖MvPolynomial.eval q P‖ * Real.exp (coordinateEnergy q)) /
      (‖MvPolynomial.eval p P‖ * Real.exp (coordinateEnergy p)) *
      Real.exp (-coordinateEnergy (q-p)) := by
  rw [norm_mul, norm_div, Complex.norm_exp, peakLinear_re, Real.exp_sub,
    Real.exp_sub, Real.exp_neg]
  ring

 theorem polynomial_compact_peak_energy {n : ℕ}
    (K : Set (Affine n)) (hK : IsCompact K) (P : MvPolynomial (Fin n) ℂ)
    (hne : ∃ q ∈ K, MvPolynomial.eval q P ≠ 0) :
    ∃ p ∈ K, MvPolynomial.eval p P ≠ 0 ∧
      ∃ h : Affine n → ℂ, AnalyticOnNhd ℂ h univ ∧ h p = 1 ∧
        ∀ q ∈ K, ‖h q‖ ≤ Real.exp (-coordinateEnergy (q-p)) := by
  let w : Affine n → ℝ := fun q => ‖MvPolynomial.eval q P‖ * Real.exp (coordinateEnergy q)
  have hw : Continuous w := (MvPolynomial.continuous_eval P).norm.mul
    (Real.continuous_exp.comp coordinateEnergy_continuous)
  obtain ⟨a,haK,haP⟩ := hne
  obtain ⟨p,hpK,hpmax⟩ := hK.exists_isMaxOn ⟨a,haK⟩ hw.continuousOn
  have hapos : 0 < w a := mul_pos (norm_pos_iff.mpr haP) (Real.exp_pos _)
  have hppos : 0 < w p := hapos.trans_le (hpmax haK)
  have hpP : MvPolynomial.eval p P ≠ 0 := by
    intro he
    simp only [w, he, _root_.norm_zero, zero_mul] at hppos
    exact lt_irrefl _ hppos
  let h : Affine n → ℂ := fun q =>
    (MvPolynomial.eval q P / MvPolynomial.eval p P) * Complex.exp (peakLinear p q)
  have hhol : AnalyticOnNhd ℂ h univ := by
    intro q _
    exact (((AnalyticOnNhd.eval_mvPolynomial P) q (mem_univ _)).mul analyticAt_const).mul
      ((peakLinear_analytic p q (mem_univ _)).cexp)
  have hpp : h p = 1 := by
    simp [h, peakLinear, hpP]
  refine ⟨p,hpK,hpP,h,hhol,hpp,fun q hq => ?_⟩
  change ‖(MvPolynomial.eval q P / MvPolynomial.eval p P) * Complex.exp (peakLinear p q)‖ ≤ _
  rw [peak_norm_identity]
  have hquot : w q / w p ≤ 1 := (div_le_one hppos).mpr (hpmax hq)
  exact (mul_le_mul_of_nonneg_right hquot (Real.exp_pos _).le).trans_eq (one_mul _)

theorem polynomial_compact_peak {n : ℕ}
    (K : Set (Affine n)) (hK : IsCompact K) (P : MvPolynomial (Fin n) ℂ)
    (hne : ∃ q ∈ K, MvPolynomial.eval q P ≠ 0) :
    ∃ p ∈ K, MvPolynomial.eval p P ≠ 0 ∧
      ∃ h : Affine n → ℂ, AnalyticOnNhd ℂ h univ ∧ h p = 1 ∧
        ∀ q ∈ K, ‖h q‖ ≤ Real.exp (-(dist q p)^2) := by
  obtain ⟨p,hpK,hpP,h,hhol,hpp,hb⟩ := polynomial_compact_peak_energy K hK P hne
  refine ⟨p,hpK,hpP,h,hhol,hpp,fun q hq => (hb q hq).trans ?_⟩
  apply Real.exp_le_exp.mpr
  rw [dist_eq_norm]
  exact neg_le_neg (sq_norm_le_coordinateEnergy (q-p))

theorem HolomorphicOnSubset.entire_scalar_comp {n m : ℕ} {S : Set (Affine n)}
    {F : S → Affine m} (hF : HolomorphicOnSubset S F)
    {h : Affine m → ℂ} (hh : AnalyticOnNhd ℂ h univ) (q : S) :
    ScalarAnalyticAt (fun x => h (F x)) q := by
  obtain ⟨W,hW,hqW,G,hG,he⟩ := hF q
  refine ⟨h ∘ G,(hh (G q) (mem_univ _)).comp (hG q hqW),?_⟩
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hW.mem_nhds hqW)] with x hx
  exact congrArg h (he x hx).symm

noncomputable def actionBiholomorph {n : ℕ} (U : Set (Affine n))
    (Γ : Type*) [Group Γ] [MulAction Γ U] [ContinuousConstSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (γ : Γ) : Biholomorph U U where
  toHomeomorph := Homeomorph.smul γ
  holomorphic_toFun := hhol γ
  holomorphic_invFun := hhol γ⁻¹

theorem cocompact_bounded_affine_smooth {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [MulAction Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U := by
  classical
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  obtain ⟨P,hPne,hPsmooth⟩ := hV.polynomial_smooth_patch hUV hU hconn.nonempty
  have hPcl : ∃ a ∈ closure U, MvPolynomial.eval a P ≠ 0 := by
    obtain ⟨a,ha,hap⟩ := hPne
    exact ⟨a,subset_closure ha,hap⟩
  obtain ⟨p,hpcl,hpP,h,hh,hp,hpeak⟩ := polynomial_compact_peak (closure U)
    hbounded.isCompact_closure P hPcl
  obtain ⟨q,hq,hqp⟩ := mem_closure_iff_seq_limit.mp hpcl
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  choose k hk γ hγ using fun j => hrep (⟨q j,hq j⟩ : U)
  obtain ⟨k₀,_hk₀,ψ,hψ,hkconv⟩ := hK.tendsto_subseq hk
  let H : ℕ → U → ℂ := fun j x => h ((γ (ψ j) • x : U).val)
  have hHg : ∀ j x, ScalarAnalyticAt (H j) x := fun j x =>
    (hhol (γ (ψ j))).entire_scalar_comp hh x
  have hHb : ∀ j x, ‖H j x‖ ≤ 1 := by
    intro j x
    apply (hpeak _ (subset_closure (γ (ψ j) • x).property)).trans
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  obtain ⟨f,hfc,_,φ,hφ,hconv⟩ := scalar_singular_montel hV hUV hU H hHg hHb
  have hkmov : Tendsto (fun j => k (ψ (φ j))) atTop (𝓝 k₀) :=
    hkconv.comp hφ.tendsto_atTop
  have hfmover : Tendsto (fun j => H (φ j) (k (ψ (φ j)))) atTop (𝓝 (f k₀)) :=
    hconv.tendsto_comp hfc.continuousAt hkmov
  have hqconv : Tendsto (fun j => q (ψ (φ j))) atTop (𝓝 p) :=
    hqp.comp (hψ.tendsto_atTop.comp hφ.tendsto_atTop)
  have hhqconv : Tendsto (fun j => H (φ j) (k (ψ (φ j)))) atTop (𝓝 (1 : ℂ)) := by
    have hc := hh.continuous.continuousAt.tendsto.comp hqconv
    have he : (fun j => H (φ j) (k (ψ (φ j)))) = (fun j => h (q (ψ (φ j)))) := by
      funext j
      change h ((γ (ψ (φ j)) • k (ψ (φ j)) : U).val) = _
      rw [hγ]
    rw [he]
    convert! hc using 1
    simp only [hp]
  have hfk : f k₀ = 1 := tendsto_nhds_unique hfmover hhqconv
  have hf1 : ∀ x, f x = 1 := scalar_maximum_of_holomorphy hV hUV hU hconn.isPreconnected
    (fun j => H (φ j)) (fun j => hHg (φ j)) (fun j => hHb (φ j)) f hfc
    (fun x => hconv.tendsto_comp hfc.continuousAt (g := fun _ => x) tendsto_const_nhds) hfk
  have hf : f = fun _ => 1 := funext hf1
  rw [hf] at hconv
  let F : ℕ → U → Affine n := fun j x => (γ (ψ (φ j)) • x : U).val
  have hFconv : TendstoLocallyUniformly F (fun _ => p) atTop :=
    peak_localization F h p (fun j x => hpeak _ (subset_closure (γ (ψ (φ j)) • x).property)) hconv
  intro x
  have hPx : Tendsto (fun j => MvPolynomial.eval (F j x) P) atTop
      (𝓝 (MvPolynomial.eval p P)) := (MvPolynomial.continuous_eval P).continuousAt.tendsto.comp
        (hFconv.tendsto_comp continuousAt_const (g := fun _ => x) tendsto_const_nhds)
  have hevent : ∀ᶠ j in atTop, MvPolynomial.eval (F j x) P ≠ 0 :=
    hPx.eventually (isOpen_ne.mem_nhds hpP)
  obtain ⟨j,hj⟩ := hevent.exists
  have hjV := hPsmooth (F j x) (hUV (γ (ψ (φ j)) • x).property) hj
  have hjU := smoothAtSubset_restrict_open hUV hU (γ (ψ (φ j)) • x).property hjV
  exact (actionBiholomorph U Γ hhol (γ (ψ (φ j)))).smoothAt_pullback x hjU

section IntrinsicCompactness
open Set Metric Filter
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def DiscRelation (S : Set E) (r : ℝ) (x y : S) : Prop :=
  ∃ f : ℂ → E, DifferentiableOn ℂ f (ball 0 1) ∧ MapsTo f (ball 0 1) S ∧
    ∃ a b : ℂ, ‖a‖ < r ∧ ‖b‖ < r ∧ f a = x.val ∧ f b = y.val

theorem discRelation_symm {S : Set E} {r : ℝ} {x y : S}
    (h : DiscRelation S r x y) : DiscRelation S r y x := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  exact ⟨f,hf,hS,b,a,hb,ha,hby,hax⟩

theorem discRelation_refl {S : Set E} {r : ℝ} (hr : 0 < r) (x : S) :
    DiscRelation S r x x := by
  exact ⟨fun _ => x.val,(differentiableOn_const _),fun _ _ => x.property,0,0,
    by simpa,by simpa,rfl,rfl⟩

theorem discRelation_dist_le {S : Set E} {r M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ S, ‖x‖ ≤ M) (hr : r ≤ 1/8)
    {x y : S} (h : DiscRelation S r x y) : dist x y ≤ 8*M*r := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  have har : ‖a‖ < 1/8 := ha.trans_le hr
  have hbr : ‖b‖ < 1/8 := hb.trans_le hr
  have haball : ball a (1/2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    have ht := norm_le_norm_sub_add z a
    rw [mem_ball,dist_eq_norm] at hz
    linarith
  have hfa : a ∈ ball (0 : ℂ) 1 := by simpa using (har.trans (by norm_num : (1:ℝ)/8 < 1))
  have hmaps : MapsTo f (ball a (1/2 : ℝ)) (closedBall (f a) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbound _ (hS (haball hz)),hbound _ (hS hfa)])
  have hba : b ∈ ball a (1/2 : ℝ) := by
    rw [mem_ball,dist_eq_norm]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hd := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hf.mono haball) hmaps hba
  have hab : dist b a ≤ 2*r := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    dist x y = dist (f b) (f a) := by rw [hax,hby]; exact dist_comm _ _
    _ ≤ (2*M/(1/2)) * dist b a := hd
    _ ≤ (2*M/(1/2)) * (2*r) := mul_le_mul_of_nonneg_left hab (by positivity)
    _ = 8*M*r := by ring

theorem bounded_disc_relation_compact_local {S : Set E} [LocallyCompactSpace S]
    (hbounded : Bornology.IsBounded S) {K : Set S} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/8 ∧ ∃ L : Set S, IsCompact L ∧
      ∀ x ∈ K, ∀ y, DiscRelation S r x y → y ∈ L := by
  obtain ⟨ε,hε,hcompact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨M,hM,hbound⟩ := hbounded.exists_pos_norm_le
  let r := min (1/8 : ℝ) (ε/(16*M))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hrsmall : r ≤ 1/8 := min_le_left _ _
  have hrε : 8*M*r < ε := by
    have hh : r ≤ ε/(16*M) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 16*M)).mp hh
    nlinarith
  refine ⟨r,hr,hrsmall,cthickening ε K,hcompact,?_⟩
  intro x hx y hxy
  apply thickening_subset_cthickening ε K
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  rw [dist_comm]
  exact (discRelation_dist_le hM.le hbound hrsmall hxy).trans_lt hrε

end IntrinsicCompactness
end Release061

end OAI
