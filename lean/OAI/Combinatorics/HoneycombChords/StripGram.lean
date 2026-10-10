import OAI.Combinatorics.HoneycombChords.EntireCosine

namespace OAI

/-! Beta kernel moments and positive strip Gram determinants. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset MeasureTheory Filter Topology
noncomputable def stripDensity (p : ℝ) : ℝ := p*(2*Real.cosh (angle*p)-1)/Real.sinh (4*angle*p)
lemma stripDensity_pos {p : ℝ} (hp : 0<p) : 0<stripDensity p := by
  unfold stripDensity
  have h:=Real.one_le_cosh (angle*p)
  exact div_pos (mul_pos hp (by linarith)) (Real.sinh_pos_iff.mpr (by have : 0 < angle := (by unfold angle;positivity);positivity))
lemma stripDensity_bound {p : ℝ} (hp : 0 ≤ p) :
    stripDensity p ≤ 2*p*Real.exp (angle*p)/Real.sinh (Real.pi*p/2) := by
  have he : 4*angle*p=Real.pi*p/2 := by unfold angle;ring
  unfold stripDensity
  rw [he]
  apply div_le_div_of_nonneg_right _ (Real.sinh_nonneg_iff.mpr (by positivity))
  have h:=Analytic.cosh_abs_le_exp_abs (angle*p)
  rw [abs_of_pos (Real.cosh_pos _),abs_of_nonneg (by have : 0 < angle := (by unfold angle;positivity);positivity)] at h
  nlinarith only [mul_nonneg hp (show 0 ≤ Real.exp (angle*p)-Real.cosh (angle*p) by linarith),hp]
lemma cosineKernelJet_pair_integrable {b c δ : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0<δ)
    (hbc : Real.sqrt (b+δ)+Real.sqrt (c+δ)+angle < Real.pi/2) (r s : ℕ) :
    IntegrableOn (fun p=>cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*stripDensity p)
      (Set.Ioi 0) := by
  let a := Real.sqrt (b+δ)+Real.sqrt (c+δ)+angle
  have ha : 0 ≤ a := by dsimp [a];have : 0 < angle := (by unfold angle;positivity);positivity
  have hi := (Analytic.polynomial_kernel_integrable 0 ha hbc).const_mul (2*δ^(-(r:ℤ))*δ^(-(s:ℤ)))
  apply hi.mono'
  · have hf : Continuous (fun p : ℝ=>cosineKernelJet r 0 b (p^2)) :=
      (cosineKernelJet_contDiff_right r 0 b 0).continuous.comp (by fun_prop)
    have hg : Continuous (fun p : ℝ=>cosineKernelJet s 0 c (p^2)) :=
      (cosineKernelJet_contDiff_right s 0 c 0).continuous.comp (by fun_prop)
    exact (hf.measurable.mul hg.measurable |>.mul (by unfold stripDensity;fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (stripDensity_pos hp)]
    calc
      _ ≤ (δ^(-(r:ℤ))*Real.exp (Real.sqrt (b+δ)*p))*(δ^(-(s:ℤ))*Real.exp (Real.sqrt (c+δ)*p))*
          (2*p*Real.exp (angle*p)/Real.sinh (Real.pi*p/2)) := by
        gcongr
        · exact le_of_lt (stripDensity_pos hp)
        · exact cosineKernelJet_exp_bound hb hd r hp.le
        · exact cosineKernelJet_exp_bound hc hd s hp.le
        · exact stripDensity_bound hp.le
      _ = _ := by
        simp only [a,add_mul,Real.exp_add]
        ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Equiv MeasureTheory Filter
noncomputable def jetGram {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>∫ p in Set.Ioi (0:ℝ),cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
    cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p
noncomputable def jetPointDensity {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (p : Fin n → ℝ) : ℝ :=
  (∏ i,w (p i))*(jetEvaluation b (fun i=>(p i)^2)).det*(jetEvaluation c (fun i=>(p i)^2)).det
lemma weighted_jet_evaluation {n : ℕ} (w : ℝ → ℝ) (b : ℕ → ℝ) (p : Fin n → ℝ) :
    (evaluationMatrix (fun i : Fin n=>fun q=>cosineKernelJet (nodalOrder b i) 0 (b i) (q^2)*w q) p).det=
      (∏ i,w (p i))*(jetEvaluation b (fun i=>(p i)^2)).det := by
  change (Matrix.of (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i) ((p j)^2)*w (p j))).det=_
  have he : Matrix.of (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i) ((p j)^2)*w (p j))=
      Matrix.of (fun i j : Fin n=>w (p j)*cosineKernelJet (nodalOrder b i) 0 (b i) ((p j)^2)) := by
    ext i j
    exact mul_comm _ _
  rw [he]
  exact Matrix.det_mul_row (fun j=>w (p j)) (jetEvaluation b (fun i=>(p i)^2))
lemma jet_gram_andreief {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0)) :
    Integrable (jetPointDensity (n:=n) w b c) (Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) ∧
    (∫ p,jetPointDensity (n:=n) w b c p ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))))=
      Fintype.card (Perm (Fin n))*(jetGram (n:=n) w b c).det := by
  let F : Fin n → ℝ → ℝ := fun i p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p
  let G : Fin n → ℝ → ℝ := fun i p=>cosineKernelJet (nodalOrder c i) 0 (c i) (p^2)
  have hFG i j : Integrable (fun p=>F i p*G j p) (volume.restrict (Set.Ioi (0:ℝ))) := by
    apply (hi i j).congr
    filter_upwards with p
    dsimp [F,G]
    ring
  have he p : (evaluationMatrix F p).det*(evaluationMatrix G p).det=jetPointDensity w b c p := by
    rw [show (evaluationMatrix F p).det=(∏ i,w (p i))*(jetEvaluation b (fun i=>(p i)^2)).det from weighted_jet_evaluation w b p]
    rfl
  have hgram : gramMatrix (volume.restrict (Set.Ioi (0:ℝ))) F G=jetGram w b c := by
    ext i j
    apply integral_congr_ae
    filter_upwards with p
    dsimp [F,G]
    ring
  constructor
  · simpa only [he] using integrable_det_evaluation_product _ F G hFG
  · simpa only [he,hgram] using andreief _ F G hFG
lemma jetPointDensity_pos {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (p : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hp : ∀ i,0<p i) (hw : ∀ q,0<q → 0<w q) (hpi : Function.Injective p) :
    0 < jetPointDensity w b c p := by
  have hin : Function.Injective (fun i=>(p i)^2) := by
    intro i j hij
    apply hpi
    exact (sq_eq_sq₀ (hp i).le (hp j).le).mp hij
  rw [jetPointDensity,mul_assoc]
  exact mul_pos (prod_pos (fun i _=>hw _ (hp i)))
    (jetEvaluation_det_product_pos b c _ hb hc hb0 hc0 hin (fun i=>sq_nonneg _))
lemma jetGram_det_pos {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i) (hw : ∀ q,0<q → 0<w q)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0)) :
    0 < (jetGram (n:=n) w b c).det := by
  let μ : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))
  obtain ⟨hI,hA⟩ := jet_gram_andreief w b c hi
  have hae : ∀ᵐ p ∂μ,∀ i,0<p i := by
    apply eventually_all.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ:=fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (i:=i)).eventually (ae_restrict_mem measurableSet_Ioi)
  have hnn : 0 ≤ᵐ[μ] jetPointDensity w b c := by
    filter_upwards [hae] with p hp
    dsimp only [Pi.zero_apply]
    rw [jetPointDensity,mul_assoc]
    exact mul_nonneg (prod_nonneg (fun i _=>(hw _ (hp i)).le))
      (jetEvaluation_det_product_nonneg b c _ hb hc hb0 hc0 (fun i=>sq_nonneg _))
  let box : Set (Fin n → ℝ) := Set.pi Set.univ (fun i=>Set.Ioo ((i:ℝ)+1) ((i:ℝ)+3/2))
  have hbox : box ⊆ Function.support (jetPointDensity w b c) := by
    intro p hp
    have hp' (i : Fin n) : (i:ℝ)+1<p i ∧ p i<(i:ℝ)+3/2 := hp i (Set.mem_univ _)
    have hp0 i : 0<p i := by have hn : (0:ℝ) ≤ i := Nat.cast_nonneg _;linarith [(hp' i).1]
    have hmono : StrictMono p := by
      intro i j hij
      have hnat : i.val+1 ≤ j.val := hij
      have hreal : (i:ℝ)+1 ≤ j := by exact_mod_cast hnat
      linarith [(hp' i).2,(hp' j).1]
    exact (jetPointDensity_pos w b c p hb hc hb0 hc0 hp0 hw hmono.injective).ne'
  have hboxpos : 0<μ box := by
    change 0<Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ))) (Set.pi Set.univ _)
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply ne_of_gt
    rw [Measure.restrict_apply measurableSet_Ioo,Set.inter_eq_left.mpr,Real.volume_Ioo]
    · exact ENNReal.ofReal_pos.mpr (by norm_num)
    · intro p hp
      have hn : (0:ℝ) ≤ i := Nat.cast_nonneg _
      exact lt_trans (by linarith) hp.1
  have hpos : 0<∫ p,jetPointDensity w b c p ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnn hI).mpr (hboxpos.trans_le (measure_mono hbox))
  rw [hA] at hpos
  exact (mul_pos_iff.mp hpos).elim (fun h=>h.2) (fun h=>False.elim (not_lt_of_ge (Nat.cast_nonneg _) h.1))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset MeasureTheory Filter Topology
lemma cosineKernelJet_pair_moment_integrable {b c δ : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0<δ)
    (hbc : Real.sqrt (b+δ)+Real.sqrt (c+δ)+angle < Real.pi/2) (r s k : ℕ) :
    IntegrableOn (fun p=>p^k*cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*stripDensity p)
      (Set.Ioi 0) := by
  let a := Real.sqrt (b+δ)+Real.sqrt (c+δ)+angle
  have ha : 0 ≤ a := by dsimp [a];have : 0 < angle := (by unfold angle;positivity);positivity
  have hi := (Analytic.polynomial_kernel_integrable k ha hbc).const_mul (2*δ^(-(r:ℤ))*δ^(-(s:ℤ)))
  apply hi.mono'
  · have hf : Continuous (fun p : ℝ=>cosineKernelJet r 0 b (p^2)) :=
      (cosineKernelJet_contDiff_right r 0 b 0).continuous.comp (by fun_prop)
    have hg : Continuous (fun p : ℝ=>cosineKernelJet s 0 c (p^2)) :=
      (cosineKernelJet_contDiff_right s 0 c 0).continuous.comp (by fun_prop)
    exact ((by fun_prop : Measurable (fun p : ℝ=>p^k)).mul hf.measurable |>.mul hg.measurable |>.mul (by unfold stripDensity;fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,abs_of_nonneg (pow_nonneg hp.le k),abs_of_pos (stripDensity_pos hp)]
    calc
      _ ≤ (p^k*(δ^(-(r:ℤ))*Real.exp (Real.sqrt (b+δ)*p)))*(δ^(-(s:ℤ))*Real.exp (Real.sqrt (c+δ)*p))*
          (2*p*Real.exp (angle*p)/Real.sinh (Real.pi*p/2)) := by
        have hp0 : 0 ≤ p := le_of_lt hp
        gcongr <;> first | positivity | exact le_of_lt (stripDensity_pos hp) | exact cosineKernelJet_exp_bound hb hd r hp0 | exact cosineKernelJet_exp_bound hc hd s hp0 | exact stripDensity_bound hp0
      _ = _ := by
        simp only [pow_succ,a,add_mul,Real.exp_add]
        ring
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix MeasureTheory Filter Topology
lemma strip_label_margin {b c : ℝ} (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) :
    Real.sqrt (b+angle^2/100)+Real.sqrt (c+angle^2/100)+angle < Real.pi/2 := by
  have hL : 0<angle := by unfold angle;positivity
  have hb' : Real.sqrt (b+angle^2/100) ≤ 8*angle/5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg angle]
  have hc' : Real.sqrt (c+angle^2/100) ≤ 6*angle/5 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg angle]
  unfold angle at *
  linarith
lemma strip_jet_pair_moment_integrable {b c : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) (r s k : ℕ) :
    IntegrableOn (fun p=>p^k*cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*stripDensity p)
      (Set.Ioi 0) := by
  have hd : 0<angle^2/100 := by unfold angle;positivity
  exact cosineKernelJet_pair_moment_integrable hb0 hc0 hd (strip_label_margin hb hc) r s k
lemma strip_jet_pair_integrable {b c : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) (r s : ℕ) :
    IntegrableOn (fun p=>cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*stripDensity p)
      (Set.Ioi 0) := by
  simpa only [pow_zero,one_mul] using strip_jet_pair_moment_integrable hb0 hc0 hb hc r s 0
lemma strip_jet_gram_det_pos {n : ℕ} (b c : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    0 < (jetGram (n:=n) stripDensity b c).det := by
  apply jetGram_det_pos stripDensity b c hb hc hb0 hc0 (fun _ h=>stripDensity_pos h)
  intro i j
  exact strip_jet_pair_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) _ _
noncomputable def poleAdjustedDensity (z p : ℝ) : ℝ := stripDensity p/(p^2+z^2)
lemma poleAdjustedDensity_pos {z p : ℝ} (hz : 0<z) (hp : 0<p) : 0<poleAdjustedDensity z p :=
  div_pos (stripDensity_pos hp) (by positivity)
lemma pole_adjusted_pair_moment_integrable {b c z : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) (hz : 0<z) (r s k : ℕ) :
    IntegrableOn (fun p=>p^k*cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*poleAdjustedDensity z p)
      (Set.Ioi 0) := by
  have hi := (strip_jet_pair_moment_integrable hb0 hc0 hb hc r s k).div_const (z^2)
  have hf : Continuous (fun p : ℝ=>cosineKernelJet r 0 b (p^2)) :=
    (cosineKernelJet_contDiff_right r 0 b 0).continuous.comp (by fun_prop)
  have hg : Continuous (fun p : ℝ=>cosineKernelJet s 0 c (p^2)) :=
    (cosineKernelJet_contDiff_right s 0 c 0).continuous.comp (by fun_prop)
  apply hi.mono'
  · exact ((by fun_prop : Measurable (fun p : ℝ=>p^k)).mul hf.measurable |>.mul hg.measurable |>.mul
      (by unfold poleAdjustedDensity stripDensity;fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hp0 : 0 ≤ p := le_of_lt hp
    have hf0 := cosineKernelJet_nonneg hb0 (sq_nonneg p) r 0
    have hg0 := cosineKernelJet_nonneg hc0 (sq_nonneg p) s 0
    have hw0 := (stripDensity_pos hp).le
    rw [Real.norm_of_nonneg (by unfold poleAdjustedDensity;positivity)]
    unfold poleAdjustedDensity
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hz) (by nlinarith [sq_nonneg p])
lemma pole_adjusted_gram_det_pos {n : ℕ} (b c : ℕ → ℝ) {z : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    0 < (jetGram (n:=n) (poleAdjustedDensity z) b c).det := by
  apply jetGram_det_pos _ b c hb hc hb0 hc0 (fun _ h=>poleAdjustedDensity_pos hz h)
  intro i j
  simpa only [pow_zero,one_mul] using pole_adjusted_pair_moment_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz _ _ 0
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset MeasureTheory Filter
noncomputable def jetPencil {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  jetGram (fun p=>(p^2-t)*w p) b c
noncomputable def characteristicRatio (y z p : ℝ) : ℝ := (p^2+y^2)/(p^2+z^2)
lemma jetPointDensity_tilt {n : ℕ} (w r : ℝ → ℝ) (b c : ℕ → ℝ) (p : Fin n → ℝ) :
    jetPointDensity (fun q=>r q*w q) b c p=(∏ i,r (p i))*jetPointDensity w b c p := by
  simp only [jetPointDensity,prod_mul_distrib]
  ring
lemma pole_jet_pair_pencil_integrable {b c z : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb : b ≤ (3*angle/2)^2) (hc : c ≤ angle^2) (hz : 0<z) (r s : ℕ) (t : ℝ) :
    IntegrableOn (fun p=>cosineKernelJet r 0 b (p^2)*cosineKernelJet s 0 c (p^2)*
      ((p^2-t)*poleAdjustedDensity z p)) (Set.Ioi 0) := by
  have h0 := pole_adjusted_pair_moment_integrable hb0 hc0 hb hc hz r s 0
  have h2 := pole_adjusted_pair_moment_integrable hb0 hc0 hb hc hz r s 2
  apply (h2.sub (h0.const_mul t)).congr
  filter_upwards with p
  simp only [Pi.sub_apply,pow_zero,one_mul]
  ring
lemma jetPencil_affine {n : ℕ} (w : ℝ → ℝ) (b c : ℕ → ℝ) (t : ℝ)
    (hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0))
    (h2 : ∀ i j : Fin n,IntegrableOn (fun p=>p^2*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0)) :
    jetPencil (n:=n) w b c t=jetPencil w b c 0-t • jetGram w b c := by
  ext i j
  change (∫ p in Set.Ioi (0:ℝ),_)= (∫ p in Set.Ioi (0:ℝ),_)-t*(∫ p in Set.Ioi (0:ℝ),_)
  rw [←integral_const_mul,←integral_sub]
  · apply integral_congr_ae
    filter_upwards with p
    ring
  · apply (h2 i j).congr
    filter_upwards with p
    ring
  · exact (hi i j).const_mul t
lemma pole_jetPencil_det_pos_nonpos {n : ℕ} (b c : ℕ → ℝ) {z t : ℝ} (hz : 0<z) (ht : t ≤ 0)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    0 < (jetPencil (n:=n) (poleAdjustedDensity z) b c t).det := by
  apply jetGram_det_pos _ b c hb hc hb0 hc0
  · intro p hp
    exact mul_pos (by nlinarith [sq_pos_of_pos hp]) (poleAdjustedDensity_pos hz hp)
  · intro i j
    exact pole_jet_pair_pencil_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz _ _ t
lemma pole_jetPencil_real_root_positive {n : ℕ} (b c : ℕ → ℝ) {z t : ℝ} (hz : 0<z)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2)
    (hroot : (jetPencil (n:=n) (poleAdjustedDensity z) b c t).det=0) : 0<t := by
  by_contra h
  have hpos:=pole_jetPencil_det_pos_nonpos b c hz (le_of_not_gt h) hb hc hb0 hc0 hb1 hc1
  exact hpos.ne' hroot
lemma pole_pencil_restore_weight {z : ℝ} (hz : 0<z) :
    (fun p : ℝ=>(p^2-(-(z^2)))*poleAdjustedDensity z p)=stripDensity := by
  funext p
  have hd : p^2+z^2 ≠ 0 := ne_of_gt (by positivity)
  dsimp [poleAdjustedDensity]
  field_simp
  ring
lemma pole_pencil_tilt_weight (y z : ℝ) :
    (fun p : ℝ=>(p^2-(-(y^2)))*poleAdjustedDensity z p)=
      (fun p=>characteristicRatio y z p*stripDensity p) := by
  funext p
  dsimp [poleAdjustedDensity,characteristicRatio]
  ring

theorem strip_jet_characteristic_product {n : ℕ} (b c : ℕ → ℝ) (y : ℝ) {z : ℝ} (hz : 0<z)
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin n,c i ≤ angle^2) :
    (∫ p,(∏ i,characteristicRatio y z (p i))*jetPointDensity (n:=n) stripDensity b c p
      ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) /
    (∫ p,jetPointDensity (n:=n) stripDensity b c p
      ∂Measure.pi (fun _ : Fin n=>volume.restrict (Set.Ioi (0:ℝ)))) =
      (jetPencil (n:=n) (poleAdjustedDensity z) b c (-(y^2))).det /
      (jetPencil (n:=n) (poleAdjustedDensity z) b c (-(z^2))).det := by
  have hi : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*stripDensity p) (Set.Ioi 0) :=
    fun i j=>strip_jet_pair_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) _ _
  have hit : ∀ i j : Fin n,IntegrableOn (fun p=>cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0) := by
    intro i j
    have h:=pole_jet_pair_pencil_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz (nodalOrder b i) (nodalOrder c j) (-(y^2))
    apply h.congr
    filter_upwards with p
    rw [congrFun (pole_pencil_tilt_weight y z) p]
  simp_rw [←jetPointDensity_tilt]
  rw [(jet_gram_andreief _ b c hit).2,(jet_gram_andreief _ b c hi).2]
  have hn : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hn]
  rw [jetPencil,jetPencil,pole_pencil_restore_weight hz,pole_pencil_tilt_weight y z]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
