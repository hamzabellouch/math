import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyDisk

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Filter Metric Fuchsian Polynomial ParametricJets
open scoped Topology

lemma jet_residual_zero (J : FamilyJet) (a : Parameter) (F : ℂ → ℂ) (z : ℂ)
    (hF : DifferentiableAt ℂ F z)
    (hAz : denominator J a (z,F z) ≠ 0)
    (hfe : z*deriv F z+((76-rho a:ℝ):ℂ)*F z=z*H J a (z,F z)) :
    Remainder.res (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) z
      (aeval z (specialize a J.p)+z^76*F z)
      (deriv (fun z => aeval z (specialize a J.p)+z^76*F z) z)=0 := by
  have hdu : deriv (fun z => aeval z (specialize a J.p)+z^76*F z) z=
      aeval z (specialize a J.p).derivative+76*z^75*F z+z^76*deriv F z := by
    simpa only [Nat.cast_ofNat,show (74:ℂ)+2=76 by norm_num] using
      (SourceSonic.derivative_jet_add (specialize a J.p) F 74 hF).deriv
  have hp : specialize a J.p=1+X*specialize a J.p1 := by
    rw [J.p_split]; simp [specialize]
  have hpz : aeval z (specialize a J.p)=1+z*aeval z (specialize a J.p1) := by rw [hp];simp
  have hS : SourceJets.residualP (sig a) (kap a) (cst a) (specialize a J.p)=
      X^77*specialize a J.S := by
    rw [← specialize_residual,J.residual];simp [specialize]
  have hsz : Remainder.res (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) z (aeval z (specialize a J.p))
      (aeval z (specialize a J.p).derivative)=z^77*aeval z (specialize a J.S) := by
    rw [← SourceSonic.aeval_residualP,hS];simp
  have hE : C (rho a)*SourceSonic.denQuotP (sig a) (specialize a J.p1)+
      SourceSonic.linP (sig a) (kap a) (cst a) (specialize a J.p)=X*specialize a J.E := by
    have he := congrArg (specialize a) J.linearization
    simpa only [map_add,map_mul,specialize_C,specialize_denQuotP,specialize_linP,
      show specialize a X=X by simp [specialize]] using he
  have hez : (rho a:ℂ)*Remainder.denQuot (sig a:ℂ) z (aeval z (specialize a J.p1))+
      Remainder.lin (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) z (aeval z (specialize a J.p))
        (aeval z (specialize a J.p).derivative)=z*aeval z (specialize a J.E) := by
    rw [← SourceSonic.aeval_denQuotP,← SourceSonic.aeval_linP]
    have he := congrArg (aeval z : Polynomial ℝ →ₐ[ℝ] ℂ) hE
    simpa using he
  have heq := Remainder.jet_identity (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) (rho a:ℂ)
    z (aeval z (specialize a J.p)) (aeval z (specialize a J.p1))
    (aeval z (specialize a J.p).derivative) (aeval z (specialize a J.S))
    (aeval z (specialize a J.E)) (F z) (deriv F z) 74 hpz hsz hez
  have hcanc : denominator J a (z,F z)*(z*deriv F z+(76-(rho a:ℂ))*F z)-
      z*numerator J a (z,F z)=0 := by
    push_cast at hfe
    rw [hfe,H]
    apply sub_eq_zero.mpr
    calc
      _ = z*((numerator J a (z,F z)/denominator J a (z,F z))*denominator J a (z,F z)) := by ac_rfl
      _ = _ := by rw [div_mul_cancel₀ _ hAz]
  rw [hdu]
  have heq' := heq
  norm_num only [Nat.cast_ofNat] at heq'
  rw [heq']
  have herr : Remainder.jetE (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) (rho a:ℂ) z
      (aeval z (specialize a J.p)) (aeval z (specialize a J.p).derivative)
      (aeval z (specialize a J.S)) (aeval z (specialize a J.E)) (F z) 74 =
      -numerator J a (z,F z) := by simp only [numerator,specialize_derivative,neg_neg]
  rw [herr]
  change z^76*(denominator J a (z,F z)*(z*deriv F z+(76-(rho a:ℂ))*F z)+
    z*(-numerator J a (z,F z)))=0
  rw [mul_neg,← sub_eq_add_neg,hcanc,mul_zero]

/-- Uniform complex neighborhood of the actual normalized sonic equation.
The parameter-to-germ map is constructed, not postulated as a shooting input. -/
structure UniformGerm where
  radius : ℝ
  radius_pos : 0<radius
  U : Parameter → ℂ → ℂ
  jointContinuous : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) radius) => U p.1 p.2)
  analytic : ∀ a, AnalyticOnNhd ℂ (U a) (ball 0 radius)
  value : ∀ a, U a 0=1
  slope : ∀ a, deriv (U a) 0=(slp a:ℂ)
  real : ∀ a (x:ℝ), (U a (x:ℂ)).im=0
  equation : ∀ a z, z ∈ ball (0:ℂ) radius →
    Remainder.res (sig a:ℂ) (kap a:ℂ) (cst a:ℂ) z (U a z) (deriv (U a) z)=0
  V : Parameter → ℂ → ℂ
  jointV : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) radius) => V p.1 p.2)
  split : ∀ a z, U a z=1+z*V a z
  Vzero : ∀ a, V a 0=(slp a:ℂ)

 theorem exists_uniform_germ : Nonempty UniformGerm := by
  obtain ⟨J⟩ := exists_familyJet
  obtain ⟨r,hr,f,hfc,hfr,hf0,hode⟩ := exists_continuous_remainder_disk J
  have hr0 : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  let F : Parameter → ℂ → ℂ := fun a z => extend (f a:DiskMap) (z/(r:ℂ))
  have hmem {z:ℂ} (hz:z ∈ ball (0:ℂ) r) : z/(r:ℂ) ∈ ball (0:ℂ) 1 := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_lt_one hr).mpr hz
  have hmemc {z:ℂ} (hz:z ∈ closedBall (0:ℂ) r) : z/(r:ℂ) ∈ closedBall (0:ℂ) 1 := by
    rw [mem_closedBall_zero_iff] at hz ⊢
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    exact (div_le_one hr).mpr hz
  have hFa (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) : AnalyticAt ℂ (F a) z := by
    have han := (f a).property.analyticAt (isOpen_ball.mem_nhds (hmem hz))
    exact han.comp (f:=fun z:ℂ=>z/(r:ℂ)) (x:=z) (analyticAt_id.div_const (c:=(r:ℂ)))
  have hF0 (a:Parameter) : F a 0=0 := by simpa only [F,zero_div] using hf0 a
  have hFreal (a:Parameter) (x:ℝ) : (F a (x:ℂ)).im=0 := by
    dsimp [F]
    unfold extend
    split
    · apply hfr a
      simp
    · rfl
  have hFcont : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) => F p.1 p.2) := by
    have hm : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) =>
        (⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩:Disk)) := by fun_prop
    have he : Continuous (fun p : Parameter × ↥(closedBall (0:ℂ) r) =>
        (f p.1:DiskMap) ⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩) :=
      continuous_eval.comp (((continuous_subtype_val.comp hfc).comp continuous_fst).prodMk hm)
    convert he using 1
    funext p
    exact extend_coe (f p.1:DiskMap) (⟨(p.2:ℂ)/(r:ℂ),hmemc p.2.property⟩:Disk)
  have hFe (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) :
      denominator J a (z,F a z) ≠ 0 ∧
      z*deriv (F a) z+((76-rho a:ℝ):ℂ)*F a z=z*H J a (z,F a z) := by
    have hd := hode a (z/(r:ℂ)) (hmem hz)
    have hzdiv : (r:ℂ)*(z/(r:ℂ))=z := by field_simp
    rw [hzdiv] at hd
    refine ⟨hd.1,?_⟩
    have he : deriv (F a) z=deriv (extend (f a:DiskMap)) (z/(r:ℂ))/(r:ℂ) := by
      simpa only [F,Function.comp_def,id_eq,one_div,div_eq_mul_inv,one_mul] using
        (((differentiableAt_extend (f a) (hmem hz)).hasDerivAt).comp z
          ((hasDerivAt_id z).div_const (r:ℂ))).deriv
    change z*deriv (F a) z+((76-rho a:ℝ):ℂ)*extend (f a:DiskMap) (z/(r:ℂ))=_
    rw [he]
    convert hd.2 using 1 ; ring
  let U : Parameter → ℂ → ℂ := fun a z => aeval z (specialize a J.p)+z^76*F a z
  have hdu (a:Parameter) {z:ℂ} (hz:z ∈ ball (0:ℂ) r) :
      deriv (U a) z=aeval z (specialize a J.p).derivative+76*z^75*F a z+z^76*deriv (F a) z := by
    simpa only [U,Nat.cast_ofNat,show (74:ℂ)+2=76 by norm_num] using
      (SourceSonic.derivative_jet_add (specialize a J.p) (F a) 74 (hFa a hz).differentiableAt).deriv
  let V : Parameter → ℂ → ℂ := fun a z => aeval z (specialize a J.p1)+z^75*F a z
  refine ⟨⟨r,hr,U,?_,?_,?_,?_,?_,?_,V,?_,?_,?_⟩⟩
  · exact ((continuous_aeval_specialize J.p).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).add
      (((continuous_subtype_val.comp continuous_snd).pow 76).mul hFcont)
  · intro a z hz
    exact (analyticAt_id.aeval_polynomial (specialize a J.p)).add
      ((analyticAt_id.pow 76).mul (hFa a hz))
  · intro a
    simp only [U,zero_pow (by norm_num : (76:ℕ)≠0),zero_mul,add_zero,
      ← coeff_zero_eq_aeval_zero',coeff_specialize,J.p_zero,ContinuousMap.one_apply,map_one]
  · intro a
    rw [hdu a (by simpa using hr)]
    simp only [zero_pow (by norm_num : (75:ℕ)≠0),zero_pow (by norm_num : (76:ℕ)≠0),
      mul_zero,zero_mul,add_zero,← coeff_zero_eq_aeval_zero',coeff_derivative,
      Nat.cast_zero,zero_add,mul_one,coeff_specialize,J.p_one,Complex.coe_algebraMap]
  · intro a x
    apply Complex.conj_eq_iff_im.mp
    have hpconj := Complex.conj_eq_iff_im.mpr
      (SourceSonic.aeval_real (specialize a J.p) (z:=(x:ℂ)) (by simp))
    have hfconj := Complex.conj_eq_iff_im.mpr (hFreal a x)
    simp only [U,map_add,map_mul,map_pow,hpconj,hfconj,Complex.conj_ofReal]
  · intro a z hz
    exact jet_residual_zero J a (F a) z (hFa a hz).differentiableAt (hFe a hz).1 (hFe a hz).2
  · exact ((continuous_aeval_specialize J.p1).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).add
      (((continuous_subtype_val.comp continuous_snd).pow 75).mul hFcont)
  · intro a z
    have hp : specialize a J.p=1+X*specialize a J.p1 := by rw [J.p_split];simp [specialize]
    change aeval z (specialize a J.p)+z^76*F a z=1+z*(aeval z (specialize a J.p1)+z^75*F a z)
    rw [hp]
    simp only [map_add,map_one,map_mul,aeval_X]
    ring
  · intro a
    simp only [V,zero_pow (by norm_num : (75:ℕ)≠0),zero_mul,add_zero,
      ← coeff_zero_eq_aeval_zero',coeff_specialize,J.p1_zero,Complex.coe_algebraMap]

end SepticProfile.SourceFamily

end
end

end OAI
