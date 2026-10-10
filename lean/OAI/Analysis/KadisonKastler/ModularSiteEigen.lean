import OAI.Analysis.KadisonKastler.KMSScalarStrip
import OAI.Analysis.KadisonKastler.PointedSiteBalance
import OAI.Analysis.KadisonKastler.PublishedModularSpectral

namespace OAI

/-! # Modular eigenoperators from the site-state balance identity -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

theorem state_balance_unitary
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates v M M)
    (hfix : (v : H →L[ℂ] H) Ω = Ω) (x : H →L[ℂ] H) (r : ℂ)
    (hbal : ∀ y ∈ M, productVectorState Ω (y * x) =
      r * productVectorState Ω (x * y)) :
    ∀ y ∈ M, productVectorState Ω (y * unitaryConj v x) =
      r * productVectorState Ω (unitaryConj v x * y) := by
  intro y hy
  let y₀ := unitaryConj (star v) y
  have hy₀ : y₀ ∈ M := by
    have h : y₀ ∈ unitaryConj (star v) '' (M : Set (H →L[ℂ] H)) :=
      Set.mem_image_of_mem _ hy
    rwa [hv.symm] at h
  have hcancel : unitaryConj v y₀ = y := by
    simpa only [star_star] using unitaryConj_star_unitaryConj (star v) y
  have hmul (a b : H →L[ℂ] H) :
      unitaryConj v (a * b) = unitaryConj v a * unitaryConj v b := by
    unfold unitaryConj
    symm
    calc
      _ = (v : H →L[ℂ] H) * a * (star (v : H →L[ℂ] H) * v) * b *
          star (v : H →L[ℂ] H) := by noncomm_ring
      _ = _ := by rw [Unitary.star_mul_self_of_mem v.property]; simp only [mul_one, mul_assoc]
  have hl := productVectorState_unitaryConj_of_fixes Ω v hfix (y₀ * x)
  have hr := productVectorState_unitaryConj_of_fixes Ω v hfix (x * y₀)
  rw [hmul, hcancel] at hl hr
  rw [hl, hr, hbal y₀ hy₀]

/-- The KMS condition turns a weighted trace identity into an operator eigenvalue. -/
theorem modular_eigen_of_state_balance
    (m : ModularSpectralResolution M Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (x : H →L[ℂ] H) (hx : x ∈ M) (L : ℝ) (hL : 0 ≤ L)
    (hbal : ∀ y ∈ M, productVectorState Ω (y * x) =
      (Real.exp (-L) : ℂ) * productVectorState Ω (x * y)) (t : ℝ) :
    unitaryConj (m.group (Multiplicative.ofAdd t)) x =
      Complex.exp (Complex.I * (L : ℂ) * t) • x := by
  let v := m.group (Multiplicative.ofAdd t)
  let c := Complex.exp (Complex.I * (L : ℂ) * t)
  have hcoeff (y : H →L[ℂ] H) (hy : y ∈ M) :
      productVectorState Ω (unitaryConj v x * y) = c * productVectorState Ω (x * y) := by
    obtain ⟨f, hfc, hfd, hfb, hf₀, hf₁⟩ := m.isModular.kms x hx y hy
    have he (s : ℝ) : f ((s : ℂ) + Complex.I) = (Real.exp (-L) : ℂ) * f s := by
      rw [hf₁, hf₀]
      exact state_balance_unitary _ (m.normalizes _) (m.isModular.fixes_vector _) x _ hbal y hy
    have h := kms_strip_exponential hL hfc hfd hfb he t
    have hfzero : f 0 = productVectorState Ω (x * y) := by
      simpa using hf₀ (0 : ℝ)
    rw [hf₀ t, hfzero] at h
    exact h
  let d : H →L[ℂ] H := unitaryConj v x - c • x
  have hdx : d ∈ M := by
    apply M.sub_mem
    · have hmem : unitaryConj v x ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) :=
        Set.mem_image_of_mem _ hx
      rwa [m.normalizes (Multiplicative.ofAdd t)] at hmem
    · exact M.smul_mem hx c
  have hstar : star d ∈ M := M.toStarSubalgebra.star_mem' hdx
  have hz : productVectorState Ω (d * star d) = 0 := by
    have h := hcoeff (star d) hstar
    change productVectorState Ω
      ((unitaryConj v x - c • x) * star d) = 0
    simpa only [sub_mul, smul_mul_assoc, productVectorState, sub_apply, smul_apply,
      inner_sub_right, inner_smul_right, sub_eq_zero] using h
  have hinner : inner ℂ ((star d) Ω) ((star d) Ω) = 0 := by
    calc
      _ = productVectorState Ω (d * star d) := by
        change inner ℂ ((star d) Ω) ((star d) Ω) = inner ℂ Ω (d ((star d) Ω))
        exact ContinuousLinearMap.adjoint_inner_left d ((star d) Ω) Ω
      _ = 0 := hz
  have hvz : (star d) Ω = 0 := inner_self_eq_zero.mp hinner
  have hzalg : (⟨star d, hstar⟩ : M.toStarSubalgebra) = 0 := hsep (by
    change (star d) Ω = (0 : H →L[ℂ] H) Ω
    simpa using hvz)
  have hs : star d = 0 := congrArg Subtype.val hzalg
  have hd : d = 0 := by simpa only [star_star, star_zero] using congrArg star hs
  exact sub_eq_zero.mp hd

namespace PointedMatrixSites

/-- The off-diagonal matrix unit at every site has its prescribed modular frequency. -/
theorem twoRatio_site_modular_eigen
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    (m : ModularSpectralResolution M Ω) (i : TwoRatioSite) (t : ℝ) :
    unitaryConj (m.group (Multiplicative.ofAdd t)) ((S.site i).entry 0 1) =
      Complex.exp (Complex.I * ((-Real.log (twoRatioSiteParameter i) : ℝ) : ℂ) * t) •
        (S.site i).entry 0 1 := by
  have hν := S.valid i
  have hx : (S.site i).entry 0 1 ∈ M := by
    have hmem : (S.site i).entry 0 1 ∈ ⨆ j, (S.site j).algebra :=
      (le_iSup (fun j => (S.site j).algebra) i) ((S.site i).entry_mem 0 1)
    exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H => (S.site i).entry 0 1 ∈ N)
      S.generates) (subset_generatedVonNeumannAlgebra _ hmem)
  apply modular_eigen_of_state_balance m S.separating _ hx _
    (neg_nonneg.mpr (Real.log_nonpos hν.1.le hν.2.le))
  intro y hy
  have h := S.twoRatio_site_balance i 0 1 y hy
  have hw : (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    simp only [twoSiteWeight, ite_true, ne_eq, inv_eq_zero]
    linarith [hν.1]
  have hw₁ : (twoSiteWeight (twoRatioSiteParameter i) 1 : ℂ) =
      (twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ) := by
    simp [twoSiteWeight, div_eq_mul_inv]
  rw [hw₁] at h
  rw [neg_neg, Real.exp_log hν.1]
  apply mul_left_cancel₀ hw
  calc
    _ = ((twoRatioSiteParameter i : ℂ) * (twoSiteWeight (twoRatioSiteParameter i) 0 : ℂ)) *
        productVectorState Ω ((S.site i).entry 0 1 * y) := h.symm
    _ = _ := by ring

theorem twoRatio_site_modular_star_eigen
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    (m : ModularSpectralResolution M Ω) (i : TwoRatioSite) (t : ℝ) :
    unitaryConj (star (m.group (Multiplicative.ofAdd t))) ((S.site i).entry 0 1) =
      regularCharacterScalar (Real.log (twoRatioSiteParameter i)) t •
        (S.site i).entry 0 1 := by
  rw [regularGroup_star_eq]
  have h := S.twoRatio_site_modular_eigen m i (-t)
  convert h using 1
  congr 2
  rw [regularCharacterScalar, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem twoRatio_site_algebra_le
    (S : PointedMatrixSites M Ω twoRatioSiteParameter) (i : TwoRatioSite) :
    (S.site i).algebra ≤ M.toStarSubalgebra := by
  intro x hx
  have hmem : x ∈ ⨆ j, (S.site j).algebra :=
    (le_iSup (fun j => (S.site j).algebra) i) hx
  exact Eq.mpr (congrArg (fun N : VonNeumannAlgebra H => x ∈ N) S.generates)
    (subset_generatedVonNeumannAlgebra _ hmem)

end PointedMatrixSites

end

end KadisonKastler

end OAI
