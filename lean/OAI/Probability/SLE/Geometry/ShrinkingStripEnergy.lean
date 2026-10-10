import OAI.Probability.SLE.Geometry.HolomorphicStripSections

namespace OAI

/-! Finite energy at the left end of a strip supplies arbitrarily far-left
angular sections of arbitrarily small oscillation. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma holomorphic_left_strip_energy_tendsto_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0<z.im ∧ z.im<Real.pi})
    (he : (∫⁻ z in {z : ℂ | z.re<0 ∧ 0<z.im ∧ z.im<Real.pi},
      ENNReal.ofReal (‖deriv f z‖^2))<∞) :
    Tendsto (fun n : ℕ => ∫ z in {z : ℂ | z.re< -(n:ℝ) ∧ 0<z.im ∧ z.im<Real.pi},
      ‖deriv f z‖^2) atTop (𝓝 0) := by
  let S (n : ℕ) : Set ℂ := {z | z.re< -(n:ℝ) ∧ 0<z.im ∧ z.im<Real.pi}
  have hs (n : ℕ) : IsOpen (S n) := (isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))
  have ha : Antitone S := by
    intro m n hmn z hz
    exact ⟨hz.1.trans_le (neg_le_neg (by exact_mod_cast hmn)),hz.2⟩
  have hi : IntegrableOn (fun z => ‖deriv f z‖^2) (S 0) := by
    have hm := deriv_memLp_two_of_energy (hs 0) (hf.mono fun _ hz => hz.2)
      (by simpa [S] using he)
    exact hm.norm.integrable_sq
  have hempty : (⋂ n, S n)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨n,hn⟩ := exists_nat_gt (-z.re)
    have hz' := (mem_iInter.mp hz n).1
    linarith
  simpa only [hempty,setIntegral_empty] using
    (tendsto_setIntegral_of_antitone (fun n => (hs n).measurableSet) ha ⟨0,hi⟩)

lemma exists_small_holomorphic_section {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0<z.im ∧ z.im<Real.pi})
    (he : (∫⁻ z in {z : ℂ | z.re<0 ∧ 0<z.im ∧ z.im<Real.pi},
      ENNReal.ofReal (‖deriv f z‖^2))<∞)
    (Q ε : ℝ) (hε : 0<ε) :
    ∃ v : ℝ, v<Q ∧
      MemLp (deriv (fun θ : ℝ => f ((v:ℂ)+(θ:ℂ)*Complex.I))) 2
        (volume.restrict (Ioo 0 Real.pi)) ∧
      ∀ θ∈Ioo 0 Real.pi, ∀ φ∈Ioo 0 Real.pi,
      ‖f ((v:ℂ)+(θ:ℂ)*Complex.I)-f ((v:ℂ)+(φ:ℂ)*Complex.I)‖<ε := by
  let S (n : ℕ) : Set ℂ := {z | z.re< -(n:ℝ) ∧ 0<z.im ∧ z.im<Real.pi}
  let E (n : ℕ) := ∫ z in S n, ‖deriv f z‖^2
  have hlim : Tendsto E atTop (𝓝 0) := holomorphic_left_strip_energy_tendsto_zero hf he
  have hsmall : ∀ᶠ n in atTop, Real.sqrt Real.pi * Real.sqrt (E n)<ε := by
    have hlim' : Tendsto (fun n => Real.sqrt Real.pi * Real.sqrt (E n)) atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero,mul_zero] using hlim.sqrt.const_mul (Real.sqrt Real.pi)
    exact hlim'.eventually (gt_mem_nhds hε)
  have hfar : ∀ᶠ n : ℕ in atTop, -(n:ℝ)<Q :=
    (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_atBot Q)
  obtain ⟨n,hn,hne⟩ := (hfar.and hsmall).exists
  let q := -(n:ℝ)-1
  let T : Set ℂ := {z | q<z.re ∧ z.re<q+1 ∧ 0<z.im ∧ z.im<Real.pi}
  have hTS : T⊆S n := by
    intro z hz
    exact ⟨by linarith [hz.2.1],hz.2.2⟩
  have hSn : IsOpen (S n) := (isOpen_lt Complex.continuous_re continuous_const).inter
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const))
  have hS0 : S n⊆{z : ℂ | z.re<0 ∧ 0<z.im ∧ z.im<Real.pi} :=
    fun _ hz => ⟨hz.1.trans_le (by simp),hz.2⟩
  have heSn : (∫⁻ z in S n, ENNReal.ofReal (‖deriv f z‖^2))<∞ :=
    (lintegral_mono_set hS0).trans_lt he
  have hTfinite : (∫⁻ z in T, ENNReal.ofReal (‖deriv f z‖^2))<∞ :=
    (lintegral_mono_set hTS).trans_lt heSn
  obtain ⟨v,hv,hvm,hvE⟩ := exists_holomorphic_energy_section hf q hTfinite
  have hES : (∫ z in T, ‖deriv f z‖^2) ≤ E n := by
    apply setIntegral_mono_set
      (deriv_memLp_two_of_energy hSn (hf.mono fun _ hz => hz.2) heSn).norm.integrable_sq
      (ae_of_all _ (fun _ => sq_nonneg _)) hTS.eventuallySubset
  have hS : IsOpen {z : ℂ | 0<z.im ∧ z.im<Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hd (θ : ℝ) (hθ : θ∈Ioo 0 Real.pi) :
      DifferentiableAt ℝ (fun θ : ℝ => f ((v:ℂ)+(θ:ℂ)*Complex.I)) θ := by
    have hz : (v:ℂ)+(θ:ℂ)*Complex.I∈{z : ℂ | 0<z.im ∧ z.im<Real.pi} := by
      simpa using hθ
    exact ((hf.differentiableAt (hS.mem_nhds hz)).restrictScalars ℝ).comp θ
      ((Complex.ofRealCLM.differentiableAt.mul_const Complex.I).const_add (v:ℂ))
  refine ⟨v,lt_of_lt_of_le hv.2 (by dsimp [q]; linarith),hvm,?_⟩
  intro θ hθ φ hφ
  have hb := complex_angular_oscillation hφ hθ
    (fun s hs => hd s (ordConnected_Ioo.uIcc_subset hφ hθ hs)) hvm
  exact hb.trans_lt ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hvE.trans hES))
    (Real.sqrt_nonneg _)).trans_lt hne)

end SLEExactGauge

end

end OAI
