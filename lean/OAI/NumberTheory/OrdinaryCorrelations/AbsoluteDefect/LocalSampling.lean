import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryMellinSampling
open OrdinaryDirichletMeanSquare

lemma local_sampling (F G : ℝ → ℂ) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : Continuous G) (t : ℝ) :
    ‖F t‖^2 ≤ ∫ x in t..t+1, 2*‖F x‖^2+‖G x‖^2 := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)
  let U : ℝ → ℝ := fun x => ‖F x‖^2
  let B : ℝ → ℝ := fun x => ‖F x‖^2+‖G x‖^2
  have huc : Continuous U := hc.norm.pow 2
  have hbc : Continuous B := (hc.norm.pow 2).add (hG.norm.pow 2)
  have hb0 : ∀ x, 0 ≤ B x := fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hud : ∀ x, DifferentiableAt ℝ U x := fun x => (hF x).norm_sq.differentiableAt
  have hbd : ∀ x, ‖deriv U x‖ ≤ B x := by
    intro x
    dsimp only [U]
    rw [(hF x).norm_sq.deriv, norm_mul]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (F x) (G x)
    norm_num only [Real.norm_ofNat]
    dsimp only [B]
    nlinarith [sq_nonneg (‖F x‖-‖G x‖)]
  have hp (x : ℝ) (hx : x ∈ Set.Icc t (t+1)) :
      U t ≤ U x + ∫ z in t..t+1, B z := by
    have hd := norm_sub_le_integral_of_norm_deriv_le_of_le hx.1 huc.continuousOn
      (fun z hz => (hud z).differentiableWithinAt)
      (Filter.Eventually.of_forall (fun z _ => hbd z)) (hbc.intervalIntegrable t x)
    have hm := intervalIntegral.integral_mono_interval («μ» := volume) (le_refl t) hx.1 hx.2
      (Filter.Eventually.of_forall hb0) (hbc.intervalIntegrable t (t+1))
    rw [Real.norm_eq_abs] at hd
    have ha := neg_le_abs (U x-U t)
    linarith
  have hh := intervalIntegral.integral_mono_on («μ» := volume) (by linarith : t ≤ t+1)
    intervalIntegrable_const
    (huc.intervalIntegrable t (t+1) |>.add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_add (huc.intervalIntegrable t (t+1))
    intervalIntegrable_const] at hh
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hh
  have he : ∫ x in t..t+1, 2*‖F x‖^2+‖G x‖^2 =
      (∫ x in t..t+1, U x)+(∫ x in t..t+1, B x) := by
    rw [← intervalIntegral.integral_add (huc.intervalIntegrable t (t+1))
      (hbc.intervalIntegrable t (t+1))]
    congr 1
    ext x
    dsimp [U,B]
    ring
  rw [he]
  dsimp only [U] at hh
  convert hh using 1 <;> ring

theorem spaced_sampling (F G : ℝ → ℂ) (hF : ∀ x, HasDerivAt F (G x) x)
    (hG : Continuous G) (R : Finset ℝ) {T : ℝ}
    (hR : ∀ t ∈ R, t ∈ Set.Icc (-T) T)
    (hsep : ∀ t ∈ R, ∀ u ∈ R, t ≠ u → 1 ≤ |t-u|) :
    ∑ t ∈ R, ‖F t‖^2 ≤
      ∫ x in Set.Icc (-T) (T+1), 2*‖F x‖^2+‖G x‖^2 := by
  classical
  let E : ℝ → ℝ := fun x => 2*‖F x‖^2+‖G x‖^2
  have hfc : Continuous F := continuous_iff_continuousAt.mpr
    (fun x => (hF x).continuousAt)
  have hec : Continuous E := by dsimp [E]; fun_prop
  have he'd : Set.Pairwise (↑R) (fun t u : ℝ => Disjoint (Set.Ioc t (t+1)) (Set.Ioc u (u+1))) := by
    intro t ht u hu htu
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hb := hsep t ht u hu htu
    have hlt : |t-u| < 1 := abs_lt.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2],
      by linarith [hx.1,hx.2,hy.1,hy.2]⟩
    linarith
  have hsub : (⋃t∈R, Set.Ioc t (t+1)) ⊆ Set.Icc (-T) (T+1) := by
    intro x hx
    obtain ⟨t,htR,htx⟩ := Set.mem_iUnion₂.mp hx
    have ht := hR t htR
    exact ⟨by linarith [htx.1,ht.1],by linarith [htx.2,ht.2]⟩
  calc
    _ ≤ ∑t∈R, ∫x in Set.Ioc t (t+1), E x := by
      apply Finset.sum_le_sum
      intro t ht
      simpa only [intervalIntegral.integral_of_le (by linarith : t ≤ t+1)] using
        local_sampling F G hF hG t
    _ = ∫x in ⋃t∈R,Set.Ioc t (t+1), E x := by
      exact (integral_biUnion_finset R (fun _ _ => measurableSet_Ioc) he'd
        (fun t _ => hec.integrableOn_Ioc)).symm
    _ ≤ _ := setIntegral_mono_set hec.integrableOn_Icc
      (Filter.Eventually.of_forall (fun x => by dsimp [E]; positivity)) hsub.eventuallyLE

lemma phase_hasDerivAt (u x : ℝ) :
    HasDerivAt (phase u) (Complex.I*u*phase u x) x := by
  have h := (((hasDerivAt_id x).const_mul u).ofReal_comp.const_mul Complex.I).cexp
  convert h using 1
  · ext y
    simp [phase]
  · simp only [mul_one]
    change Complex.I*u*phase u x = phase u x*(Complex.I*u)
    ring

lemma polynomial_hasDerivAt {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) (x : ℝ) :
    HasDerivAt (polynomial s a u)
      (polynomial s (fun n => a n*(Complex.I*u n)) u x) x := by
  change HasDerivAt (fun y => ∑n∈s,a n*phase (u n) y)
    (∑n∈s,(a n*(Complex.I*u n))*phase (u n) x) x
  simpa only [mul_assoc] using
    HasDerivAt.fun_sum (fun n (_ : n ∈ s) => (phase_hasDerivAt (u n) x).const_mul (a n))

lemma shifted_polynomial_norm {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (u : ι → ℝ) (c x : ℝ) :
    ‖polynomial s a (fun n => u n-c) x‖ = ‖polynomial s a u x‖ := by
  have he : polynomial s a (fun n => u n-c) x =
      polynomial s a u x * star (phase c x) := by
    simp only [polynomial, ← phase_mul_conj, Finset.sum_mul, mul_assoc]
  rw [he, norm_mul, norm_star, norm_phase, mul_one]

lemma one_sided_interval_energy (s : Finset ℕ) (a : ℕ → ℂ) {N T : ℝ}
    (hN : 0<N) (hT : 0≤T)
    (hs : ∀n∈s,0<(n:ℝ) ∧ (n:ℝ)≤N) :
    (∫x in Set.Icc (-T) (T+1), ‖polynomial s a (fun n => Real.log n) x‖^2) ≤
      4*Real.exp (1+1/4)*gaussianConstant*(T+1+N)*∑n∈s,‖a n‖^2 := by
  have hc : Continuous (fun x => ‖polynomial s a (fun n => Real.log n) x‖^2) := by
    unfold polynomial phase
    fun_prop
  have hm := setIntegral_mono_set («μ» := volume) (f := fun x =>
      ‖polynomial s a (fun n => Real.log n) x‖^2)
    (s := Set.Icc (-T) (T+1)) (t := Set.Icc (-(T+1)) (T+1))
    hc.integrableOn_Icc (Filter.Eventually.of_forall (fun x => sq_nonneg _))
    (Set.Icc_subset_Icc (by linarith) (le_refl _) |>.eventuallyLE)
  exact hm.trans (logarithmic_interval_energy s a hN (by linarith) hs)

theorem band_spaced_mean_square (s : Finset ℕ) (a : ℕ → ℂ) (R : Finset ℝ)
    {N T c B : ℝ} (hN : 0<N) (hT : 0≤T) (_hB : 0≤B)
    (hs : ∀n∈s,0<(n:ℝ) ∧ (n:ℝ)≤N)
    (hband : ∀n∈s, |Real.log (n:ℝ)-c|≤B)
    (hR : ∀t∈R,t∈Set.Icc (-T) T)
    (hsep : ∀t∈R,∀u∈R,t≠u → 1≤|t-u|) :
    ∑t∈R, ‖polynomial s a (fun n => Real.log n) t‖^2 ≤
      4*Real.exp (1+1/4)*gaussianConstant*(T+1+N)*(2+B^2)*∑n∈s,‖a n‖^2 := by
  let b : ℕ → ℂ := fun n => a n*(Complex.I*((Real.log (n:ℝ)-c:ℝ):ℂ))
  let F := polynomial s a (fun n => Real.log (n:ℝ)-c)
  let G := polynomial s b (fun n => Real.log (n:ℝ)-c)
  have hf : ∀x,HasDerivAt F (G x) x := by
    intro x
    simpa only [F,G,b,Complex.ofReal_sub] using
      polynomial_hasDerivAt s a (fun n => Real.log (n:ℝ)-c) x
  have hg : Continuous G := by unfold G polynomial phase; fun_prop
  have hm := spaced_sampling F G hf hg R hR hsep
  have ha := one_sided_interval_energy s a hN hT hs
  have hb := one_sided_interval_energy s b hN hT hs
  have hcoef : ∑n∈s,‖b n‖^2 ≤ B^2*∑n∈s,‖a n‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    dsimp only [b]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, mul_comm (B^2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (hband n hn) 2
  have hfa (x : ℝ) : ‖F x‖ = ‖polynomial s a (fun n => Real.log n) x‖ :=
    shifted_polynomial_norm s a _ c x
  have hgb (x : ℝ) : ‖G x‖ = ‖polynomial s b (fun n => Real.log n) x‖ :=
    shifted_polynomial_norm s b _ c x
  simp_rw [hfa,hgb] at hm
  have hca : Continuous (fun x => ‖polynomial s a (fun n => Real.log n) x‖^2) := by
    unfold polynomial phase; fun_prop
  have hcb : Continuous (fun x => ‖polynomial s b (fun n => Real.log n) x‖^2) := by
    unfold polynomial phase; fun_prop
  have hIa : IntegrableOn (fun x => 2*‖polynomial s a (fun n => Real.log n) x‖^2)
      (Set.Icc (-T) (T+1)) := hca.integrableOn_Icc.const_mul 2
  rw [integral_add hIa hcb.integrableOn_Icc, MeasureTheory.integral_const_mul] at hm
  have hK : 0 ≤ 4*Real.exp (1+1/4)*gaussianConstant*(T+1+N) := by
    unfold gaussianConstant
    positivity
  have hh := mul_le_mul_of_nonneg_left hcoef hK
  nlinarith

end OrdinaryMellinSampling

end

end OAI
