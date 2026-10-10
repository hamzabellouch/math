import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.Add

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma potential_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ)
    (s : Spins n) (V : Configuration n → ℝ)
    (hψ : Integrable (fun x => V x * ‖ψ.value s x‖^2))
    (hφ : Integrable (fun x => V x * ‖φ.value s x‖^2))
    (hadd : Integrable (fun x => V x * ‖(ψ.add φ).value s x‖^2)) :
    (∫ x, V x * ‖(ψ.add (φ.rsmul t)).value s x‖^2) =
      (1-t)*(∫ x, V x * ‖ψ.value s x‖^2) +
      (t^2-t)*(∫ x, V x * ‖φ.value s x‖^2) +
      t*(∫ x, V x * ‖(ψ.add φ).value s x‖^2) := by
  have heq : ∀ x, V x * ‖(ψ.add (φ.rsmul t)).value s x‖^2 =
      (1-t)*(V x*‖ψ.value s x‖^2) + (t^2-t)*(V x*‖φ.value s x‖^2) +
      t*(V x*‖(ψ.add φ).value s x‖^2) := by
    intro x
    change V x * ‖ψ.value s x + (t : ℂ)*φ.value s x‖^2 = _
    rw [norm_add_rsmul_sq]
    change _ = (1-t)*(V x*‖ψ.value s x‖^2) + (t^2-t)*(V x*‖φ.value s x‖^2) +
      t*(V x*‖ψ.value s x + φ.value s x‖^2)
    ring
  simp_rw [heq]
  have hsum : Integrable (fun x => (1-t)*(V x*‖ψ.value s x‖^2) +
      (t^2-t)*(V x*‖φ.value s x‖^2)) := (hψ.const_mul _).add (hφ.const_mul _)
  rw [integral_add hsum (hadd.const_mul t),
    integral_add (hψ.const_mul (1-t)) (hφ.const_mul (t^2-t))]
  simp only [integral_const_mul]

lemma nuclearEnergy_add_rsmul {M n : ℕ} (S : Nuclei M) (ψ φ : H1Vector n) (t : ℝ) :
    nuclearEnergy S (ψ.add (φ.rsmul t)) =
      (1-t)*nuclearEnergy S ψ + (t^2-t)*nuclearEnergy S φ +
      t*nuclearEnergy S (ψ.add φ) := by
  unfold nuclearEnergy
  simp_rw [potential_add_rsmul ψ φ t _ _ (ψ.nuclear_integrable S _)
    (φ.nuclear_integrable S _) ((ψ.add φ).nuclear_integrable S _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma pairEnergy_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    pairEnergy (ψ.add (φ.rsmul t)) =
      (1-t)*pairEnergy ψ + (t^2-t)*pairEnergy φ + t*pairEnergy (ψ.add φ) := by
  unfold pairEnergy
  simp_rw [potential_add_rsmul ψ φ t _ _ (ψ.pair_integrable _)
    (φ.pair_integrable _) ((ψ.add φ).pair_integrable _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma form_add_rsmul {M n : ℕ} (S : Nuclei M) (ψ φ : H1Vector n) (t : ℝ) :
    form S (ψ.add (φ.rsmul t)) =
      (1-t)*form S ψ + (t^2-t)*form S φ + t*form S (ψ.add φ) := by
  rw [form, kinetic_add_rsmul, nuclearEnergy_add_rsmul, pairEnergy_add_rsmul]
  unfold form
  ring

open scoped Topology

lemma linear_term_zero_of_eventually_quadratic_nonneg (A B : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ A*t+B*t^2) : A = 0 := by
  have hc : ContinuousAt (fun t : ℝ => A+B*t) 0 := by fun_prop
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ A+B*t := by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht hpos
    have hpos' : 0 < t := hpos
    have heq : A*t+B*t^2 = (A+B*t)*t := by ring
    rw [heq] at ht
    exact nonneg_of_mul_nonneg_left ht hpos'
  have hm : ∀ᶠ t : ℝ in 𝓝[<] 0, A+B*t ≤ 0 := by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht hneg
    have hneg' : t < 0 := hneg
    have heq : A*t+B*t^2 = (- (A+B*t))*(-t) := by ring
    rw [heq] at ht
    have hu := nonneg_of_mul_nonneg_left ht (neg_pos.mpr hneg')
    linarith
  have htp : Filter.Tendsto (fun t : ℝ => A+B*t) (𝓝[>] (0 : ℝ)) (𝓝 (A+B*0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have htm : Filter.Tendsto (fun t : ℝ => A+B*t) (𝓝[<] (0 : ℝ)) (𝓝 (A+B*0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hge := ge_of_tendsto htp hp
  have hle := le_of_tendsto htm hm
  simp only [mul_zero, add_zero] at hge hle
  exact le_antisymm hle hge

lemma GroundState.polarization {M n : ℕ} {S : Nuclei M} {ψ : H1Vector n}
    (hψ : GroundState S ψ) (hn : n ≠ 0) (φ : H1Vector n)
    (hφ : Antisymmetric φ) :
    form S (ψ.add φ) - form S ψ - form S φ =
      energy S n * (mass (ψ.add φ) - mass ψ - mass φ) := by
  let E := energy S n
  let A := form S (ψ.add φ) - form S ψ - form S φ -
    E * (mass (ψ.add φ) - mass ψ - mass φ)
  let B := form S φ - E * mass φ
  have hc : Continuous (fun t : ℝ => mass (ψ.add (φ.rsmul t))) := by
    simp_rw [mass_add_rsmul]
    fun_prop
  have hm0 : mass (ψ.add (φ.rsmul 0)) = 1 := by
    rw [mass_add_rsmul]
    simpa using hψ.2.1
  have hm : ∀ᶠ t : ℝ in 𝓝 0, 0 < mass (ψ.add (φ.rsmul t)) :=
    continuousAt_const.eventually_lt hc.continuousAt (by rw [hm0]; norm_num)
  have hpoly : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ A*t+B*t^2 := by
    filter_upwards [hm] with t ht
    have hbound := energy_mul_mass_le_form S hn (ψ.add (φ.rsmul t))
      (hψ.1.add (hφ.rsmul t)) ht
    rw [mass_add_rsmul, form_add_rsmul] at hbound
    have he : form S ψ = E * mass ψ := by rw [hψ.2.1, mul_one]; exact hψ.2.2
    dsimp [A, B, E]
    nlinarith [he]
  have hA := linear_term_zero_of_eventually_quadratic_nonneg A B hpoly
  dsimp [A, E] at hA
  linarith

lemma norm_double_multiplier_identity (f d : ℝ) (u v : ℂ) :
    ‖(d : ℂ)*u+(f : ℂ)*v‖^2 =
      (‖v+((d : ℂ)*((f : ℂ)*u)+(f : ℂ)*((d : ℂ)*u+(f : ℂ)*v))‖^2 -
        ‖v‖^2 - ‖(d : ℂ)*((f : ℂ)*u)+(f : ℂ)*((d : ℂ)*u+(f : ℂ)*v)‖^2)/2 +
      d^2*‖u‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma norm_double_mass_identity (f : ℝ) (u : ℂ) :
    ‖(f : ℂ)*u‖^2 =
      (‖u+(f : ℂ)*((f : ℂ)*u)‖^2-‖u‖^2-‖(f : ℂ)*((f : ℂ)*u)‖^2)/2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma integral_quadratic_expansion {n : ℕ} (A B C D F : Configuration n → ℝ)
    (hB : Integrable B) (hC : Integrable C) (hD : Integrable D) (hF : Integrable F)
    (heq : ∀ x, A x = (B x-C x-D x)/2+F x) :
    (∫ x, A x) = ((∫ x, B x)-(∫ x, C x)-(∫ x, D x))/2+(∫ x, F x) := by
  simp_rw [heq]
  have hsub : Integrable (fun x => B x-C x-D x) := (hB.sub hC).sub hD
  have hbc : Integrable (fun x => B x-C x) := hB.sub hC
  rw [integral_add (hsub.div_const 2) hF, integral_div,
    integral_sub hbc hD, integral_sub hB hC]

lemma mass_double_smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    mass χ = (mass (ψ.add θ)-mass ψ-mass θ)/2 := by
  dsimp only
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  change mass χ = (mass (ψ.add θ)-mass ψ-mass θ)/2
  have hblock : ∀ s, (∫ x, ‖χ.value s x‖^2) =
      ((∫ x, ‖(ψ.add θ).value s x‖^2)-(∫ x, ‖ψ.value s x‖^2)-
        (∫ x, ‖θ.value s x‖^2))/2 := by
    intro s
    have h := integral_quadratic_expansion
      (fun x => ‖χ.value s x‖^2) (fun x => ‖(ψ.add θ).value s x‖^2)
      (fun x => ‖ψ.value s x‖^2) (fun x => ‖θ.value s x‖^2) (fun _ => 0)
      (((ψ.add θ).value_L2 s).integrable_norm_pow (p := 2) (by decide))
      ((ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide))
      ((θ.value_L2 s).integrable_norm_pow (p := 2) (by decide)) (integrable_zero _ _ _)
      (fun x => by
        change ‖(f x : ℂ)*ψ.value s x‖^2 =
          (‖ψ.value s x+(f x : ℂ)*((f x : ℂ)*ψ.value s x)‖^2-
            ‖ψ.value s x‖^2-‖(f x : ℂ)*((f x : ℂ)*ψ.value s x)‖^2)/2+0
        simpa only [add_zero] using norm_double_mass_identity (f x) (ψ.value s x))
    simpa only [integral_zero, add_zero] using h
  unfold mass
  simp_rw [hblock]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

lemma potential_double_smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D)
    (s : Spins n) (V : Configuration n → ℝ)
    (hψ : Integrable (fun x => V x*‖ψ.value s x‖^2))
    (hθ : Integrable (fun x => V x*
      ‖((ψ.smoothMul f hf B D hB hD).smoothMul f hf B D hB hD).value s x‖^2))
    (hadd : Integrable (fun x => V x*
      ‖(ψ.add ((ψ.smoothMul f hf B D hB hD).smoothMul f hf B D hB hD)).value s x‖^2)) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    (∫ x, V x*‖χ.value s x‖^2) =
      ((∫ x, V x*‖(ψ.add θ).value s x‖^2)-(∫ x, V x*‖ψ.value s x‖^2)-
        (∫ x, V x*‖θ.value s x‖^2))/2 := by
  dsimp only
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  have h := integral_quadratic_expansion
    (fun x => V x*‖χ.value s x‖^2) (fun x => V x*‖(ψ.add θ).value s x‖^2)
    (fun x => V x*‖ψ.value s x‖^2) (fun x => V x*‖θ.value s x‖^2) (fun _ => 0)
    hadd hψ hθ (integrable_zero _ _ _) (fun x => by
      change V x*‖(f x : ℂ)*ψ.value s x‖^2 = _
      rw [norm_double_mass_identity]
      change _ = (V x*‖ψ.value s x +(f x : ℂ)*((f x : ℂ)*ψ.value s x)‖^2 -
        V x*‖ψ.value s x‖^2 - V x*‖(f x : ℂ)*((f x : ℂ)*ψ.value s x)‖^2)/2+0
      ring)
  simpa only [integral_zero, add_zero] using h

lemma kinetic_double_smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    kinetic χ = (kinetic (ψ.add θ)-kinetic ψ-kinetic θ)/2 +
      (1/2 : ℝ)*∑ s, ∑ a, ∫ x,
        (fderiv ℝ f x (EuclideanSpace.single a 1))^2*‖ψ.value s x‖^2 := by
  dsimp only
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  have hblock : ∀ s a, (∫ x, ‖χ.gradient s a x‖^2) =
      ((∫ x, ‖(ψ.add θ).gradient s a x‖^2)-(∫ x, ‖ψ.gradient s a x‖^2)-
        (∫ x, ‖θ.gradient s a x‖^2))/2 +
      ∫ x, (fderiv ℝ f x (EuclideanSpace.single a 1))^2*‖ψ.value s x‖^2 := by
    intro s a
    have hL := memLp_two_real_mul (ψ.value_L2 s)
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)
    have herr : Integrable (fun x =>
        (fderiv ℝ f x (EuclideanSpace.single a 1))^2*‖ψ.value s x‖^2) := by
      simpa only [norm_real_mul_sq] using hL.integrable_norm_pow (p := 2) (by decide)
    apply integral_quadratic_expansion _ _ _ _ _
      (((ψ.add θ).partial_L2 s a).integrable_norm_pow (p := 2) (by decide))
      ((ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide))
      ((θ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)) herr
    intro x
    exact norm_double_multiplier_identity (f x)
      (fderiv ℝ f x (EuclideanSpace.single a 1)) (ψ.value s x) (ψ.gradient s a x)
  change (1/2 : ℝ)*(∑ s, ∑ a, ∫ x, ‖χ.gradient s a x‖^2) = _
  simp_rw [hblock]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  unfold kinetic
  ring

lemma nuclearEnergy_double_smoothMul {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    nuclearEnergy S χ =
      (nuclearEnergy S (ψ.add θ)-nuclearEnergy S ψ-nuclearEnergy S θ)/2 := by
  dsimp only
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  unfold nuclearEnergy
  simp_rw [potential_double_smoothMul ψ f hf B D hB hD _ _ (ψ.nuclear_integrable S _)
    (θ.nuclear_integrable S _) ((ψ.add θ).nuclear_integrable S _)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

lemma pairEnergy_double_smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    pairEnergy χ = (pairEnergy (ψ.add θ)-pairEnergy ψ-pairEnergy θ)/2 := by
  dsimp only
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  unfold pairEnergy
  simp_rw [potential_double_smoothMul ψ f hf B D hB hD _ _ (ψ.pair_integrable _)
    (θ.pair_integrable _) ((ψ.add θ).pair_integrable _)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

lemma form_double_smoothMul {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) :
    let χ := ψ.smoothMul f hf B D hB hD
    let θ := χ.smoothMul f hf B D hB hD
    form S χ = (form S (ψ.add θ)-form S ψ-form S θ)/2 +
      (1/2 : ℝ)*∑ s, ∑ a, ∫ x,
        (fderiv ℝ f x (EuclideanSpace.single a 1))^2*‖ψ.value s x‖^2 := by
  dsimp only
  rw [form, kinetic_double_smoothMul, nuclearEnergy_double_smoothMul,
    pairEnergy_double_smoothMul]
  unfold form
  ring

theorem GroundState.smooth_multiplier_identity {M n : ℕ} {S : Nuclei M}
    {ψ : H1Vector n} (hψ : GroundState S ψ) (hn : n ≠ 0)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D)
    (hsymm : ∀ p x, f (permute p x) = f x) :
    form S (ψ.smoothMul f hf B D hB hD) =
      energy S n * mass (ψ.smoothMul f hf B D hB hD) +
      (1/2 : ℝ)*∑ s, ∑ a, ∫ x,
        (fderiv ℝ f x (EuclideanSpace.single a 1))^2*‖ψ.value s x‖^2 := by
  let χ := ψ.smoothMul f hf B D hB hD
  let θ := χ.smoothMul f hf B D hB hD
  have hχ : Antisymmetric χ :=
    ψ.smoothMul_antisymmetric hψ.1 f hf B D hB hD hsymm
  have hθ : Antisymmetric θ :=
    χ.smoothMul_antisymmetric hχ f hf B D hB hD hsymm
  have hp := hψ.polarization hn θ hθ
  rw [form_double_smoothMul, mass_double_smoothMul]
  change (form S (ψ.add θ)-form S ψ-form S θ)/2+_ =
    energy S n*((mass (ψ.add θ)-mass ψ-mass θ)/2)+_
  rw [hp]
  ring

end Coulomb

end
end

end OAI
