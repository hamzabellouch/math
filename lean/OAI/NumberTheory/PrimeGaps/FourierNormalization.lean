import OAI.NumberTheory.PrimeGaps.EulerProducts

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

section FourierNormalization

open scoped FourierTransform SchwartzMap

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def frequencyDilation : V ≃L[ℝ] V :=
  Units.mk0 ((2*Real.pi)⁻¹) (inv_ne_zero (by positivity)) • ContinuousLinearEquiv.refl ℝ V

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem frequencyDilation_apply (u : V) :
    frequencyDilation u = (2*Real.pi)⁻¹ • u := rfl

noncomputable def radianFourier (G : SchwartzMap V ℂ) : SchwartzMap V ℂ :=
  (((2*Real.pi)^Module.finrank ℝ V)⁻¹ : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ frequencyDilation (𝓕⁻ G)

theorem radianFourier_apply (G : SchwartzMap V ℂ) (u : V) :
    radianFourier G u = (((2*Real.pi)^Module.finrank ℝ V)⁻¹ : ℝ) •
      ∫ v : V, Complex.exp (Complex.I*(inner ℝ u v : ℂ))*G v := by
  simp only [radianFourier, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    frequencyDilation_apply, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  rw [real_inner_smul_right, real_inner_comm v u]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp

theorem radianFourier_inversion (G : SchwartzMap V ℂ) (v : V) :
    (∫ u : V, radianFourier G u * Complex.exp (-Complex.I*(inner ℝ u v : ℂ))) = G v := by
  let A : ℝ := 2*Real.pi
  have hA : 0<A := by dsimp [A]; positivity
  let f := fun u : V => (𝓕⁻ G) u * Complex.exp (-Complex.I*((A*inner ℝ u v : ℝ):ℂ))
  have hscale : (∫ u : V, f (A⁻¹ • u)) = A^Module.finrank ℝ V • ∫ u : V, f u := by
    simpa only [inv_pow, inv_inv] using Measure.integral_comp_smul_of_nonneg volume f A⁻¹ (hR:= (inv_pos.mpr hA).le)
  have hinv : (∫ u : V, f u) = G v := by
    have hh := congrArg (fun H : SchwartzMap V ℂ => H v) (FourierTransform.fourier_fourierInv_eq (F := SchwartzMap V ℂ) G)
    rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp only [f, A]
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring_nf
  calc
    _ = ∫ u : V, (A^Module.finrank ℝ V)⁻¹ • f (A⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [radianFourier, smul_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        frequencyDilation_apply]
      dsimp only [f, A]
      rw [real_inner_smul_left]
      have ht : 2*Real.pi*((2*Real.pi)⁻¹*inner ℝ u v) = inner ℝ u v := by field_simp
      rw [ht]
      simp only [Complex.real_smul, mul_assoc]
    _ = (A^Module.finrank ℝ V)⁻¹ • ∫ u : V, f (A⁻¹ • u) := integral_smul _ _
    _ = (A^Module.finrank ℝ V)⁻¹ • (A^Module.finrank ℝ V • G v) := by rw [hscale, hinv]
    _ = G v := by rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hA.ne'), one_smul]

noncomputable def laplaceSchwartz (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  (show HasCompactSupport (fun v => Complex.exp (ℓ v : ℂ)*F v) from hF.mul_left).toSchwartzMap
    (((Complex.ofRealCLM.contDiff.comp ℓ.contDiff).cexp).mul hFs)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
@[simp] theorem laplaceSchwartz_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    laplaceSchwartz ℓ F hF hFs v = Complex.exp (ℓ v : ℂ)*F v := rfl

noncomputable def sourceFourier (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) : SchwartzMap V ℂ :=
  radianFourier (laplaceSchwartz ℓ F hF hFs)

theorem sourceFourier_apply (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (u : V) :
    sourceFourier ℓ F hF hFs u = (((2*Real.pi)^Module.finrank ℝ V)⁻¹ : ℝ) •
      ∫ v : V, Complex.exp (ℓ v : ℂ)*F v*Complex.exp (Complex.I*(inner ℝ u v : ℂ)) := by
  rw [sourceFourier, radianFourier_apply]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  rw [laplaceSchwartz_apply]
  ring_nf

theorem sourceFourier_inversion (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (v : V) :
    (∫ u : V, sourceFourier ℓ F hF hFs u *
      Complex.exp (-(ℓ v : ℂ)-Complex.I*(inner ℝ u v : ℂ))) = F v := by
  calc
    _ = Complex.exp (-(ℓ v : ℂ)) *
        ∫ u : V, sourceFourier ℓ F hF hFs u *
          Complex.exp (-Complex.I*(inner ℝ u v : ℂ)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with u
      rw [sub_eq_add_neg, Complex.exp_add]
      ring_nf
    _ = Complex.exp (-(ℓ v : ℂ)) * (Complex.exp (ℓ v : ℂ)*F v) := by
      rw [sourceFourier, radianFourier_inversion, laplaceSchwartz_apply]
    _ = F v := by rw [← mul_assoc, ← Complex.exp_add]; simp

theorem sourceFourier_integrable_pow_mul (ℓ : V →L[ℝ] ℝ) (F : V → ℂ)
    (hF : HasCompactSupport F) (hFs : ContDiff ℝ ∞ F) (k : ℕ) :
    Integrable (fun u : V => ‖u‖^k*‖sourceFourier ℓ F hF hFs u‖) :=
  SchwartzMap.integrable_pow_mul volume _ k

end FourierNormalization

def primePrefix (y : ℕ) : Finset Nat.Primes := (Nat.primesLE y).subtype Nat.Prime

@[simp] theorem mem_primePrefix (y : ℕ) (p : Nat.Primes) :
    p∈primePrefix y ↔ (p:ℕ)≤y := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE y) (a := p)).trans
    (by rw [Nat.mem_primesLE]; exact and_iff_left p.property)

noncomputable def eulerGlobal {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏' p : Nat.Primes, eulerH p δ (A p) B z

noncomputable def genericEulerConstant (m : ℕ) : ℝ :=
  (1+m)*(4*(m:ℝ)^2*2^m+2*m)+2*m+2*(m:ℝ)^2

theorem genericEulerConstant_nonneg (m : ℕ) : 0≤genericEulerConstant m := by
  unfold genericEulerConstant
  positivity

theorem eulerH_summable_error {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    Summable (fun p : Nat.Primes => ‖eulerH p δ (A p) B z-1‖) := by
  apply (primePrefix y).summable_compl_iff.mp
  apply (summable_tsum_le_of_reciprocal_sq
    (fun p : {p : Nat.Primes // p∉primePrefix y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [mem_primePrefix, not_le] at this; exact this)
    (fun p => ‖eulerH p.val δ (A p.val) B z-1‖)
    (genericEulerConstant_nonneg B.card) (fun _ => norm_nonneg _) ?_).1
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [mem_primePrefix, not_le] using this
  rw [hgen p.val hp]
  exact eulerH_generic_error p.val.property.two_le hδ B z (fun _ _ i _ => hz i)

theorem eulerH_tail_sum {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y : ℕ} (hy : 0<y)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    (∑' p : {p : Nat.Primes // p∉primePrefix y}, ‖eulerH p.val δ (A p.val) B z-1‖) ≤
      genericEulerConstant B.card/(y:ℝ) := by
  apply (summable_tsum_le_of_reciprocal_sq
    (fun p : {p : Nat.Primes // p∉primePrefix y} => (p.val:ℕ))
    (fun _ _ he => Subtype.ext (Subtype.ext he)) hy
    (fun p => by have := p.property; simp only [mem_primePrefix, not_le] at this; exact this)
    (fun p => ‖eulerH p.val δ (A p.val) B z-1‖)
    (genericEulerConstant_nonneg B.card) (fun _ => norm_nonneg _) ?_).2
  intro p
  have hp : y<(p.val:ℕ) := by
    have := p.property
    simpa only [mem_primePrefix, not_le] using this
  rw [hgen p.val hp]
  exact eulerH_generic_error p.val.property.two_le hδ B z (fun _ _ i _ => hz i)

noncomputable def primeReciprocalPrefix (y : ℕ) : ℝ :=
  ∑ p∈primePrefix y, (p:ℝ)⁻¹

theorem eulerGlobal_comparison {ι : Type*} [Fintype ι] {δ : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι))
    (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) {y R : ℕ} (hy : 2≤y)
    (hA : ∀ p : Nat.Primes, (A p).card≤R) (hB : B.card≤R)
    (hgen : ∀ p : Nat.Primes, y<(p:ℕ) → A p=B) :
    ‖eulerGlobal δ A B z-eulerGlobal δ A B (fun _ => 0)‖ ≤
      Real.exp (4*R*primeReciprocalPrefix y)*
        (Real.exp (2*R)*6*R*Real.log y*(∑ i, ‖z i‖)*primeReciprocalPrefix y+
          2*(Real.exp (genericEulerConstant B.card/(y:ℝ))-1)) := by
  let Z : ℝ := ∑ i, ‖z i‖
  have hZ : 0≤Z := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hy0 : 0<y := by omega
  have hyR : (0:ℝ)<y := by exact_mod_cast hy0
  have hly : 0≤Real.log (y:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1≤y))
  have hf := eulerH_summable_error hδ A B z hz hy0 hgen
  have hg := eulerH_summable_error hδ A B (fun _ => 0) (by simp) hy0 hgen
  let b : Nat.Primes → ℝ := fun p => Real.exp (4*R*(p:ℝ)⁻¹)
  let e : Nat.Primes → ℝ := fun p => Real.exp (2*R)*6*R*Real.log y*Z*(p:ℝ)⁻¹
  have hbn (p : Nat.Primes) : 1≤b p := Real.one_le_exp (by positivity)
  have hnorm (w : ι → ℂ) (hw : ∀ i, 0≤(w i).re) (p : Nat.Primes) :
      ‖eulerH p δ (A p) B w‖≤b p := by
    apply (norm_eulerH_le p.property.two_le hδ (A p) B w hw).trans
    apply Real.exp_le_exp.mpr
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : 0≤(p:ℝ)⁻¹ := by positivity
    nlinarith
  have hd (p : Nat.Primes) (hp : p∈primePrefix y) :
      ‖eulerH p δ (A p) B z-eulerH p δ (A p) B (fun _ => 0)‖≤e p := by
    have haR : ((A p).card:ℝ)≤R := by exact_mod_cast hA p
    have hbR : (B.card:ℝ)≤R := by exact_mod_cast hB
    have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
    have hpl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_le)
    have hpu : Real.log (p:ℝ)≤Real.log (y:ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast (mem_primePrefix y p).mp hp)
    have hp2 : (p:ℝ)⁻¹≤1/2 := prime_inv_le_half p.property.two_le
    have hpe : 2*((A p).card+B.card)*(p:ℝ)⁻¹≤2*R := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ)≤R) (sub_nonneg.mpr hp2),
        mul_nonneg (show 0≤(p:ℝ)⁻¹ by positivity) (show (0:ℝ)≤2*R-((A p).card+B.card) by linarith)]
    have hpc : (2*(A p).card+4*B.card:ℝ)≤6*R := by linarith
    calc
      _ ≤ Real.exp (2*((A p).card+B.card)*(p:ℝ)⁻¹)*
          ((2*(A p).card+4*B.card)*(p:ℝ)⁻¹*Real.log p*Z) :=
        norm_eulerH_sub_zero_le p.property.two_le hδ (A p) B z hz
      _ ≤ Real.exp (2*R)*((6*R)*(p:ℝ)⁻¹*Real.log y*Z) := by gcongr
      _ = e p := by dsimp only [e]; ring
  have hh := norm_tprod_sub_tprod_le (primePrefix y) hf hg b e
    (fun p _ => hbn p) (fun p _ => hnorm z hz p)
    (fun p _ => hnorm (fun _ => 0) (by simp) p) hd
  have hbprod : (∏ p∈primePrefix y, b p) = Real.exp (4*R*primeReciprocalPrefix y) := by
    dsimp only [b, primeReciprocalPrefix]
    rw [← Real.exp_sum, Finset.mul_sum]
  have hesum : (∑ p∈primePrefix y, e p) =
      Real.exp (2*R)*6*R*Real.log y*Z*primeReciprocalPrefix y := by
    simp only [e, primeReciprocalPrefix, Finset.mul_sum]
  have htf := eulerH_tail_sum hδ A B z hz hy0 hgen
  have htg := eulerH_tail_sum hδ A B (fun _ => 0) (by simp) hy0 hgen
  rw [hbprod, hesum] at hh
  calc
    _ ≤ Real.exp (4*R*primeReciprocalPrefix y)*
        (Real.exp (2*R)*6*R*Real.log y*Z*primeReciprocalPrefix y+
          (Real.exp (genericEulerConstant B.card/(y:ℝ))-1)+
          (Real.exp (genericEulerConstant B.card/(y:ℝ))-1)) := by
      apply hh.trans
      gcongr
    _ = _ := by dsimp only [Z]; ring

theorem eq_of_emod_eq_of_bound {a b : ℤ} {D p : ℕ}
    (ha : a.natAbs≤D) (hb : b.natAbs≤D) (hp : 2*D<p)
    (hab : a%(p:ℤ)=b%(p:ℤ)) : a=b := by
  have hd : (p:ℤ)∣a-b := Int.dvd_of_emod_eq_zero
    (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hab)
  have hdN : p∣(a-b).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hlt : (a-b).natAbs<p := by have := Int.natAbs_sub_le a b; omega
  exact sub_eq_zero.mp (Int.natAbs_eq_zero.mp (Nat.eq_zero_of_dvd_of_lt hdN hlt))

theorem residueFamily_generic_of_bound {ι : Type*} [Fintype ι] (b : ι → ℤ)
    {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D) (hp : 2*D<p) :
    residueFamily b p=shiftFamily b :=
  residueFamily_eq_shiftFamily b p (fun i j he => eq_of_emod_eq_of_bound (hb i) (hb j) hp he)

theorem markedResidueFamily_generic_of_bound {ι : Type*} [Fintype ι] (b : ι → ℤ)
    (a : ℤ) (ha : ∀ i, b i≠a) {D p : ℕ} (hb : ∀ i, (b i).natAbs≤D)
    (haD : a.natAbs≤D) (hp : 2*D<p) :
    markedResidueFamily b p a=shiftFamily b :=
  markedResidueFamily_eq_shiftFamily b p a
    (fun i j he => eq_of_emod_eq_of_bound (hb i) (hb j) hp he)
    (fun i he => ha i (eq_of_emod_eq_of_bound (hb i) haD hp he))

theorem subsetFamily_card_le {ι : Type*} [Fintype ι] (S : Finset (Finset ι)) :
    S.card≤2^Fintype.card ι := by
  classical
  simpa only [Fintype.card_finset] using Finset.card_le_univ S

theorem unmarked_eulerGlobal_comparison {ι : Type*} [Fintype ι]
    (b : ι → ℤ) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re)
    {D y : ℕ} (hy : 2≤y) (hb : ∀ i, (b i).natAbs≤D) (hyD : 2*D≤y) :
    ‖eulerGlobal 0 (residueFamily b) (shiftFamily b) z-
        eulerGlobal 0 (residueFamily b) (shiftFamily b) (fun _ => 0)‖ ≤
      Real.exp (4*(2^Fintype.card ι:ℕ)*primeReciprocalPrefix y)*
        (Real.exp (2*(2^Fintype.card ι:ℕ))*6*(2^Fintype.card ι:ℕ)*Real.log y*
          (∑ i, ‖z i‖)*primeReciprocalPrefix y+
          2*(Real.exp (genericEulerConstant (shiftFamily b).card/(y:ℝ))-1)) :=
  eulerGlobal_comparison (by omega) (residueFamily b) (shiftFamily b) z hz hy
    (fun _ => subsetFamily_card_le _) (subsetFamily_card_le _)
    (fun _ hp => residueFamily_generic_of_bound b hb (hyD.trans_lt hp))

theorem marked_eulerGlobal_comparison {ι : Type*} [Fintype ι]
    (b : ι → ℤ) (a : ℤ) (ha : ∀ i, b i≠a) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re)
    {D y : ℕ} (hy : 2≤y) (hb : ∀ i, (b i).natAbs≤D) (haD : a.natAbs≤D) (hyD : 2*D≤y) :
    ‖eulerGlobal 1 (fun p => markedResidueFamily b p a) (shiftFamily b) z-
        eulerGlobal 1 (fun p => markedResidueFamily b p a) (shiftFamily b) (fun _ => 0)‖ ≤
      Real.exp (4*(2^Fintype.card ι:ℕ)*primeReciprocalPrefix y)*
        (Real.exp (2*(2^Fintype.card ι:ℕ))*6*(2^Fintype.card ι:ℕ)*Real.log y*
          (∑ i, ‖z i‖)*primeReciprocalPrefix y+
          2*(Real.exp (genericEulerConstant (shiftFamily b).card/(y:ℝ))-1)) :=
  eulerGlobal_comparison (by omega) (fun p => markedResidueFamily b p a) (shiftFamily b) z hz hy
    (fun _ => subsetFamily_card_le _) (subsetFamily_card_le _)
    (fun _ hp => markedResidueFamily_generic_of_bound b a ha hb haD (hyD.trans_lt hp))

theorem singularSeries_cast_hasProd (H : Finset ℤ) :
    HasProd (fun p : Nat.Primes => (singularLocal H p : ℂ)) (singularSeries H : ℂ) := by
  exact (singularSeries_multipliable H).hasProd.map Complex.ofRealHom.toMonoidHom
    Complex.continuous_ofReal

theorem unmarked_eulerGlobal_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) :
    eulerGlobal 0 (residueFamily b) (shiftFamily b) (fun _ => 0) =
      (singularSeries (Finset.univ.image b) : ℂ) := by
  rw [eulerGlobal]
  exact ((singularSeries_cast_hasProd _).congr_fun fun p =>
    eulerH_unmarked_zero b p.property.two_le).tprod_eq

theorem marked_eulerGlobal_zero {ι : Type*} [Fintype ι] (b : ι → ℤ) (a : ℤ)
    (ha : ∀ i, b i≠a) :
    eulerGlobal 1 (fun p => markedResidueFamily b p a) (shiftFamily b) (fun _ => 0) =
      (singularSeries (insert a (Finset.univ.image b)) : ℂ) := by
  rw [eulerGlobal]
  exact ((singularSeries_cast_hasProd _).congr_fun fun p =>
    eulerH_marked_zero b a ha p.property.two_le).tprod_eq

theorem primeMonomial_cpow {ι : Type*} {p : ℕ} (hp : 0<p)
    (z : ι → ℂ) (S : Finset ι) :
    (p:ℂ)^(-(1+∑ i∈S, z i)) = (p:ℂ)⁻¹*primeMonomial p z S := by
  have hp0 : (p:ℂ)≠0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hp0, ← Complex.natCast_log]
  rw [show (Real.log p : ℂ)*(-(1+∑ i∈S, z i)) =
    -(Real.log p : ℂ)+(-(Real.log p : ℂ)*(∑ i∈S, z i)) by ring,
    Complex.exp_add, Complex.exp_neg, Complex.natCast_log, Complex.exp_log hp0]
  simp only [primeMonomial, Complex.natCast_log]

noncomputable def eulerZetaProduct {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ) : ℂ :=
  ∏ S∈B, riemannZeta (1+∑ i∈S, z i)^((-1:ℤ)^S.card)

theorem eulerZetaProduct_hasProd {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) :
    HasProd (fun p : Nat.Primes =>
      ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card)))
      (eulerZetaProduct B z) := by
  apply hasProd_prod
  intro S hS
  have hs : 1<(1+∑ i∈S, z i).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.re_sum]
    exact lt_add_of_pos_right _ (Finset.sum_pos (fun i _ => hz i) (hB S hS))
  have he := riemannZeta_eulerProduct_hasProd hs
  have hc (p : Nat.Primes) : (p:ℂ)^(-(1+∑ i∈S, z i)) =
      (p:ℂ)⁻¹*primeMonomial p z S := primeMonomial_cpow p.property.pos z S
  rcases sign_zpow_cases S.card with hp | hn
  · simpa only [hp, zpow_neg_one, zpow_one, hc] using he
  · have he' := he.inv₀ (riemannZeta_ne_zero_of_one_lt_re hs)
    simpa only [hn, neg_neg, zpow_one, zpow_neg_one, inv_inv, hc] using he'

theorem eulerZetaProduct_ne_zero {ι : Type*} (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) :
    eulerZetaProduct B z ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro S hS
  apply zpow_ne_zero _
  apply riemannZeta_ne_zero_of_one_lt_re
  simp only [Complex.add_re, Complex.one_re, Complex.re_sum]
  exact lt_add_of_pos_right _ (Finset.sum_pos (fun i _ => hz i) (hB S hS))

theorem local_zeta_factor_ne_zero {ι : Type*} {p : ℕ} (hp : 2≤p)
    (z : ι → ℂ) (S : Finset ι) (hz : ∀ i∈S, 0≤(z i).re) :
    1-(p:ℂ)⁻¹*primeMonomial p z S ≠ 0 := by
  have hpR : (1:ℝ)<p := by exact_mod_cast (by omega : 1<p)
  have hb := (primeMonomial_scaled_norm (by omega) z S hz).trans_lt
    ((inv_lt_one₀ (by positivity : (0:ℝ)<p)).mpr hpR)
  intro he
  rw [← sub_eq_zero.mp he, norm_one] at hb
  exact hb.false

theorem eulerP_eq_eulerH_mul {ι : Type*} {p : ℕ} (hp : 2≤p) (δ : ℕ)
    (A B : Finset (Finset ι)) (z : ι → ℂ) (hz : ∀ i, 0≤(z i).re) :
    eulerP p δ A z = eulerH p δ A B z *
      ∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card)) := by
  rw [eulerH, mul_assoc, ← Finset.prod_mul_distrib]
  have he : (∏ S∈B, (1-(p:ℂ)⁻¹*primeMonomial p z S)^((-1:ℤ)^S.card) *
      (1-(p:ℂ)⁻¹*primeMonomial p z S)^(-((-1:ℤ)^S.card))) = 1 := by
    apply Finset.prod_eq_one
    intro S _
    rw [← zpow_add₀ (local_zeta_factor_ne_zero hp z S (fun i _ => hz i)), add_neg_cancel,
      zpow_zero]
  rw [he, mul_one]

theorem eulerP_hasProd {ι : Type*} (δ : ℕ)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ)
    (hB : ∀ S∈B, S.Nonempty) (hz : ∀ i, 0<(z i).re) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => eulerH p δ (A p) B z) H) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z) (H*eulerZetaProduct B z) := by
  exact (hH.mul (eulerZetaProduct_hasProd B z hB hz)).congr_fun fun p =>
    eulerP_eq_eulerH_mul p.property.two_le δ (A p) B z (fun i => (hz i).le)

abbrev EulerChoices {κ : Type*} (A : κ → Type*) :=
  Σ P : Finset κ, (p : P) → A p

noncomputable def eulerChoiceTerm {κ : Type*} {A : κ → Type*}
    (w : (p : κ) → A p → ℂ) (c : EulerChoices A) : ℂ :=
  ∏ p : c.1, w p (c.2 p)

noncomputable def eulerChoiceNorm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : ℝ := ∑ a, ‖w p a‖

theorem eulerChoiceNorm_nonneg {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (p : κ) : 0≤eulerChoiceNorm w p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem eulerChoice_sum_norm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, ‖eulerChoiceTerm w ⟨P,c⟩‖) = ∏ p∈P, eulerChoiceNorm w p := by
  classical
  simp only [eulerChoiceTerm, norm_prod, eulerChoiceNorm]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => ‖w p a‖)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, ‖w p a‖)

theorem eulerChoice_sum {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (P : Finset κ) :
    (∑ c : (p : P) → A p, eulerChoiceTerm w ⟨P,c⟩) = ∏ p∈P, ∑ a, w p a := by
  classical
  simp only [eulerChoiceTerm]
  rw [← Fintype.prod_sum (fun (p : P) (a : A p) => w p a)]
  exact Finset.prod_coe_sort P (fun p => ∑ a, w p a)

theorem eulerChoice_summable_norm {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    Summable (fun c : EulerChoices A => ‖eulerChoiceTerm w c‖) := by
  classical
  apply (summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp_rw [tsum_fintype, eulerChoice_sum_norm]
  exact summable_finsetProd_of_summable_nonneg (eulerChoiceNorm_nonneg w) hw

theorem eulerChoices_hasProd {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    HasProd (fun p => 1+∑ a, w p a) (∑' c : EulerChoices A, eulerChoiceTerm w c) := by
  classical
  have hs := (eulerChoice_summable_norm w hw).of_norm
  apply hasProd_one_add_of_hasSum_prod
  exact hs.hasSum.sigma fun P => by
    simpa only [eulerChoice_sum] using
      hasSum_fintype (fun c : (p : P) → A p => eulerChoiceTerm w ⟨P,c⟩)

end LargePrimeGaps

end OAI
