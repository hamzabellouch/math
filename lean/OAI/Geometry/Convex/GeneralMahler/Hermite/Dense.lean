import OAI.Geometry.Convex.GeneralMahler.Hermite.Multi

namespace OAI
/-! Vanishing of all chaos coefficients implies vanishing a.e.; proof via
an exponential integrability and characteristic function argument. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
variable {m:ℕ}
lemma lp_poly {f:Rn m→ℝ} (hf:PolyBound f) (hm:AEStronglyMeasurable f (normal m)) :
    MemLp f 2 (normal m) := by
  apply (memLp_two_iff_integrable_sq hm).mpr
  exact (hf.pow _).gaussian_integrable (hm.pow _)

lemma lp_EXP (t:Rn m) : MemLp (fun x:Rn m=>Real.exp |⟪x,t⟫|) 2 (normal m) := by
  obtain ⟨C,hc,h⟩ := ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (normal m)
  let f := fun x:Rn m=>Real.exp |⟪x,t⟫|
  have hm : Continuous f := by unfold f; fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (h.const_mul (Real.exp (‖t‖^2/C))).mono' (hm.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖f x^2‖≤_
  unfold f
  rw [Real.norm_of_nonneg (sq_nonneg _),pow_two,← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht := abs_real_inner_le_norm x t
  have he : 2*‖x‖*‖t‖-C*‖x‖^2≤‖t‖^2/C := by
    rw [le_div_iff₀ hc]
    nlinarith [sq_nonneg (C*‖x‖-‖t‖)]
  linarith

variable {f:Rn m→ℝ} (hf:MemLp f 2 (normal m))
include hf

lemma momentPower (hz : ∀ a, (∫ x,f x*MM a x ∂normal m)=0) (t:Rn m) :
    ∀ n:ℕ,(∫ x,f x*⟪x,t⟫^n ∂normal m)=0 := by
  have hi : PolyBound (fun x:Rn m=>⟪x,t⟫) := by
    simp_rw [real_inner_comm t]; exact PolyBound.clm (innerSL ℝ t)
  let W (n:ℕ) (a) (x:Rn m) := f x*⟪x,t⟫^n*MM a x
  have iw (n a) : Integrable (W n a) (normal m) := by
    unfold W; simp_rw [mul_assoc]
    exact hf.integrable_mul (lp_poly ((hi.pow _).mul (M_poly a))
      ((((continuous_id.inner continuous_const).pow _).mul (M_cont a)).aestronglyMeasurable))
  have h (n:ℕ) : ∀ a,(∫ x,W n a x ∂normal m)=0 := by
    induction n with
    | zero=>
      intro a; simpa [W] using hz a
    | succ n ih=>
      intro a
      let g (i:Fin m) (x:Rn m) := (t i*sn (a i+1))*W n (inc a i) x+(t i*sn (a i))*W n (decM a i) x
      have he (x) : W (n+1) a x= ∑ i,g i x := by
        have hu (i:Fin m) : g i x=(f x*⟪x,t⟫^n*MM a x)*(t i*x i) := by
          have hh := ladder a i x
          unfold g W
          calc
            _ = t i*(f x*⟪x,t⟫^n)*(sn (a i+1)*MM (inc a i) x+sn (a i)*MM (decM a i) x) := by ring
            _ = _ := by rw [← hh]; ring
        simp_rw [hu]; rw [← Finset.mul_sum]
        have hv : (∑ i,t i*x i)= ⟪x,t⟫ := by simp [PiLp.inner_apply]
        rw [hv]; unfold W; rw [pow_succ]; ring
      simp_rw [he]; rw [integral_finsetSum]
      · apply Finset.sum_eq_zero
        intro i _
        unfold g; rw [integral_add]
        · simp_rw [integral_const_mul,ih]; ring
        all_goals exact (iw ..).const_mul _
      exact fun i _ => ((iw n (inc a i)).const_mul _).add ((iw n (decM a i)).const_mul _)
  intro n
  simpa [W,MM,H] using h n (fun _=>0)

local notation "ii" => Complex.I
lemma wave_zero (hm:Measurable f) (hz:∀ a, (∫ x,f x*MM a x ∂normal m)=0) (t:Rn m) :
    (∫ x, (f x:ℂ)* Complex.exp ((⟪x,t⟫:ℝ)*ii) ∂normal m)=0 := by
  let w (x:Rn m) := (⟪x,t⟫:ℂ)*ii
  let A (n:ℕ) (x:Rn m) := w x^n/(n.factorial:ℂ)
  let P (n:ℕ) (x:Rn m) := (f x:ℂ)*∑ i∈Finset.range n,A i x
  have ha : Continuous w := by unfold w; fun_prop
  have hmul (x:Rn m) : HasSum (fun i=>A i x) (Complex.exp (w x)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp (w x)
  have he (n:ℕ) : (∫ x,P n x ∂normal m)=0 := by
    have hA (i:ℕ) (x:Rn m) :
        (f x:ℂ)*A i x= ii^i/(i.factorial:ℂ)*((f x*⟪x,t⟫^i:ℝ):ℂ) := by
      unfold A w; push_cast; rw [mul_pow]; ring
    have ih : PolyBound (fun x:Rn m=>⟪x,t⟫) := by
      simp_rw [real_inner_comm t]; exact PolyBound.clm (innerSL ℝ t)
    have hi (n:ℕ) : Integrable (fun x=>f x*⟪x,t⟫^n) (normal m) :=
      hf.integrable_mul (lp_poly (ih.pow _) (((continuous_id.inner continuous_const).pow _).aestronglyMeasurable))
    unfold P; simp_rw [Finset.mul_sum,hA]; rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i _
      rw [integral_const_mul,integral_complex_ofReal,momentPower hf hz]
      simp
    intro i _
    exact (hi _).ofReal.const_mul _
  let g := fun x:Rn m=> ‖f x‖*Real.exp |⟪x,t⟫|
  have ih : Integrable g (normal m) := hf.norm.integrable_mul (lp_EXP t)
  have hb (x:Rn m) :
      HasSum (fun i=>‖A i x‖) (Real.exp |⟪x,t⟫|) := by
    rw [Real.exp_eq_exp_ℝ]
    convert NormedSpace.expSeries_div_hasSum_exp (|⟪x,t⟫|) using 1
    all_goals first | rfl | (funext i; unfold A w; simp)
  have hh := tendsto_integral_of_dominated_convergence
    (μ:=normal m) g (fun n=> (by unfold P A; fun_prop : Measurable (P n)).aestronglyMeasurable) (F:=P)
    ih (fun n=>ae_of_all _ fun x=> ?_) (ae_of_all _ fun x=> ?_)
    (f:=fun x=>(f x:ℂ)*Complex.exp (w x))
  · simp_rw [he] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · unfold P; rw [norm_mul,Complex.norm_real]
    unfold g; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_sum_le ..).trans (sum_le_hasSum _ (fun i _=> norm_nonneg _) (hb x))
  exact ((hmul x).tendsto_sum_nat).const_mul _

lemma pospart_char (hm:Measurable f) (hp:∀ x,0≤f x) :
    let μ := (normal m).withDensity (fun x=>ENNReal.ofReal (f x))
    IsFiniteMeasure μ ∧ ∀ t:Rn m,charFun μ t=∫ x,(f x:ℂ)*Complex.exp ((⟪x,t⟫:ℝ)*ii) ∂normal m := by
  intro μ
  have hi : Integrable f (normal m) := hf.integrable (by norm_num)
  have HH : Measurable fun x=>ENNReal.ofReal (f x) := hm.ennreal_ofReal
  constructor
  · constructor
    unfold μ; rw [withDensity_apply _ (by simp),restrict_univ,← ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ hp)]
    exact ENNReal.ofReal_lt_top
  intro t
  unfold charFun μ
  rw [integral_withDensity_eq_integral_toReal_smul HH (by simp)]
  simp_rw [ENNReal.toReal_ofReal (hp _),Complex.real_smul]

lemma measurable_zero (hm:Measurable f) (hz:∀ a,(∫ x,f x*MM a x ∂normal m)=0) :
    ∀ᵐ x∂normal m,f x=0 := by
  let l := fun x=> (‖f x‖+f x)
  let k := fun x=> (‖f x‖-f x)
  have hp (x):0≤l x := by unfold l; rw [Real.norm_eq_abs]; grind
  have hq (x):0≤k x := by unfold k; exact sub_nonneg.mpr (le_abs_self _)
  have i₁ : MemLp l 2 (normal m) := hf.norm.add hf
  have i₂ : MemLp k 2 (normal m) := hf.norm.sub hf
  have hl : Measurable l := hm.norm.add hm
  have hk : Measurable k := hm.norm.sub hm
  let F := fun x=>ENNReal.ofReal (l x)
  let G := fun x=>ENNReal.ofReal (k x)
  let μ := normal m; let L := μ.withDensity F; let K := μ.withDensity G
  have ha := pospart_char i₁ hl hp
  have hb := pospart_char i₂ hk hq
  have : IsFiniteMeasure L := ha.1
  have : IsFiniteMeasure K := hb.1
  have he : L=K := by
    apply Measure.ext_of_charFun
    funext t
    rw [ha.2,hb.2]
    let w := fun x:Rn m=> Complex.exp ((⟪x,t⟫:ℝ)*ii)
    have iw (f:Rn m→ℝ) (hi:MemLp f 2 μ) :
        Integrable (fun x=>(f x:ℂ)*w x) μ := by
      have hF : Integrable (fun x=>(f x:ℂ)) μ := (hi.integrable (by norm_num)).ofReal
      apply hF.mono (hF.aestronglyMeasurable.mul (by
        unfold w; exact (by fun_prop : Continuous _).aestronglyMeasurable))
      apply ae_of_all
      intro x; change ‖_*w x‖≤ _
      unfold w; simp
    have hu : (∫ x,((l x:ℂ)*w x-(k x:ℂ)*w x) ∂μ)=0 := by
      have he (x:Rn m) : (l x:ℂ)*w x-(k x:ℂ)*w x=2*((f x:ℂ)*w x) := by
        unfold l k; push_cast; ring
      simp_rw [he]
      rw [integral_const_mul]
      have hi := wave_zero hf hm hz t
      change _*(∫ x, (f x:ℂ)*Complex.exp _ ∂normal m)=_; rw [hi,mul_zero]
    rw [integral_sub (iw l i₁) (iw k i₂)] at hu
    exact sub_eq_zero.mp hu
  have h : F=ᵐ[μ] G := (withDensity_eq_iff_of_sigmaFinite (by unfold F; fun_prop)
    (by unfold G; fun_prop)).mp he
  filter_upwards [h] with x hx
  have hi := congrArg ENNReal.toReal hx
  rw [show F x= _ from (rfl : F x=ENNReal.ofReal (l x)), show G x=_ from
    (rfl : G x=ENNReal.ofReal (k x)),ENNReal.toReal_ofReal (hp _),ENNReal.toReal_ofReal (hq _)] at hi
  unfold l k at hi; linarith

theorem ae_zero (hz:∀ a,(∫ x,f x*MM a x ∂normal m)=0) : ∀ᵐ x∂normal m,f x=0 := by
  obtain ⟨g,hg,he⟩ := hf.aemeasurable
  have hi := measurable_zero (hf.ae_eq he) hg (fun a=> (integral_congr_ae (he.symm.mul (ae_eq_refl _))).trans (hz a))
  filter_upwards [hi,he] with x hx he; exact he.trans hx
end GeneralMahler.HMode

end

end OAI
