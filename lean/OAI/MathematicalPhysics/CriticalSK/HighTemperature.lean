import OAI.MathematicalPhysics.CriticalSK.GapMixing
import OAI.MathematicalPhysics.CriticalSK.Mixing

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open scoped BigOperators Topology
namespace CriticalSK


section

open Set Filter MeasureTheory ProbabilityTheory

lemma spinValue_abs (b : Bool) : |spinValue b|=1 := by cases b <;> norm_num [spinValue]

lemma hamiltonian_gaussianLinear {n : ℕ} (x : Spin n) (W : Disorder n) :
    hamiltonian W x = gaussianLinear (fun e : Edge n => spinValue (x e.val.1)*spinValue (x e.val.2)) W := by
  unfold hamiltonian gaussianLinear
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma edge_card_le_sq (n : ℕ) : Fintype.card (Edge n) ≤ n^2 := by
  simpa only [Edge,Fintype.card_prod,Fintype.card_fin,pow_two] using Fintype.card_subtype_le (fun p : Fin n × Fin n => p.1 < p.2)

lemma hamiltonian_exp_moment {n : ℕ} (hn : 0<n) (x : Spin n) (a : ℝ) (ha : |a|=1) :
    Integrable (fun W : Disorder n => Real.exp (a*hamiltonian W x)) (disorderLaw n) ∧
    (∫ W : Disorder n, Real.exp (a*hamiltonian W x) ∂disorderLaw n) ≤ Real.exp ((n:ℝ)/2) := by
  let c := fun e : Edge n => a*(spinValue (x e.val.1)*spinValue (x e.val.2))
  have he (W : Disorder n) : a*hamiltonian W x = gaussianLinear c W := by
    rw [hamiltonian_gaussianLinear]
    simp only [gaussianLinear,Finset.mul_sum,c]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simp_rw [he]
  constructor
  · exact gaussian_exp_integrable _ c
  · change (∫ W, Real.exp (gaussianLinear c W) ∂gaussianScalarPi (n : ℝ≥0)⁻¹) ≤ _
    rw [gaussian_exp_integral]
    apply Real.exp_le_exp.mpr
    have hc (e : Edge n) : c e^2=1 := by
      have hh : |c e|=1 := by simp only [c,abs_mul,ha,spinValue_abs,mul_one]
      nlinarith [sq_abs (c e)]
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,NNReal.coe_inv,NNReal.coe_natCast]
    have hN : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hcard : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast edge_card_le_sq n
    have hh := mul_le_mul_of_nonneg_left hcard (inv_nonneg.mpr hN.le)
    have hi : (n:ℝ)⁻¹*(n:ℝ)^2=(n:ℝ) := by field_simp
    rw [hi] at hh
    linarith

lemma hamiltonian_one_sided_tail {n : ℕ} (hn : 0<n) (x : Spin n) (a : ℝ) (ha : |a|=1) :
    (disorderLaw n).real {W | 3*(n:ℝ) ≤ a*hamiltonian W x} ≤ Real.exp (-(5/2:ℝ)*(n:ℝ)) := by
  obtain ⟨hi,hm⟩ := hamiltonian_exp_moment hn x a ha
  have hp := integral_dominates_event (E := {W : Disorder n | 3*(n:ℝ)≤a*hamiltonian W x})
    (hi.div_const (Real.exp (3*(n:ℝ)))) (fun W => div_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    (fun W hW => by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      simpa only [one_mul] using Real.exp_le_exp.mpr hW)
  rw [integral_div] at hp
  apply hp.trans
  calc
    _ ≤ Real.exp ((n:ℝ)/2)/Real.exp (3*(n:ℝ)) := div_le_div_of_nonneg_right hm (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

lemma hamiltonian_abs_tail {n : ℕ} (hn : 0<n) (x : Spin n) :
    (disorderLaw n).real {W | 3*(n:ℝ) ≤ |hamiltonian W x|} ≤ 2*Real.exp (-(5/2:ℝ)*(n:ℝ)) := by
  have hs : {W : Disorder n | 3*(n:ℝ)≤|hamiltonian W x|} ⊆
      {W | 3*(n:ℝ)≤(1:ℝ)*hamiltonian W x} ∪ {W | 3*(n:ℝ)≤(-1:ℝ)*hamiltonian W x} := by
    intro W hW
    rcases le_abs.mp (show 3*(n:ℝ) ≤ |hamiltonian W x| from hW) with h|h
    · exact Or.inl (by dsimp; linarith)
    · exact Or.inr (by dsimp; linarith)
  have hp := (measureReal_mono (μ := disorderLaw n) hs).trans (measureReal_union_le _ _)
  have h1 := hamiltonian_one_sided_tail hn x 1 (by norm_num)
  have h2 := hamiltonian_one_sided_tail hn x (-1) (by norm_num)
  linarith

lemma spin_card_le_exp (n : ℕ) : (Fintype.card (Spin n):ℝ)≤Real.exp (n:ℝ) := by
  have h : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) h n
  rw [← Real.exp_nat_mul,mul_one] at hp
  simpa only [Spin,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat] using hp

lemma maximum_energy_tail {n : ℕ} (hn : 0<n) :
    (disorderLaw n).real {W | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|} ≤ 2*Real.exp (-(3/2:ℝ)*(n:ℝ)) := by
  have he : {W : Disorder n | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|} =
      ⋃ x : Spin n, {W | 3*(n:ℝ)≤|hamiltonian W x|} := by ext W; simp
  rw [he]
  calc
    _ ≤ ∑ x : Spin n, (disorderLaw n).real {W | 3*(n:ℝ)≤|hamiltonian W x|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : Spin n, 2*Real.exp (-(5/2:ℝ)*(n:ℝ)) := Finset.sum_le_sum (fun x _ => hamiltonian_abs_tail hn x)
    _ = (Fintype.card (Spin n):ℝ)*(2*Real.exp (-(5/2:ℝ)*(n:ℝ))) := by simp
    _ ≤ Real.exp (n:ℝ)*(2*Real.exp (-(5/2:ℝ)*(n:ℝ))) := mul_le_mul_of_nonneg_right (spin_card_le_exp n) (by positivity)
    _ = _ := by rw [← mul_assoc,mul_comm _ 2,mul_assoc,← Real.exp_add]; congr 2; ring

lemma maximum_energy_tendsto : Tendsto (fun n : ℕ => (disorderLaw n).real
    {W | ∃ x : Spin n, 3*(n:ℝ) < |hamiltonian W x|}) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => 2*Real.exp (-(3/2:ℝ)*(n:ℝ))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (-(3/2:ℝ))*(n:ℝ)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by norm_num) tendsto_natCast_atTop_atTop
    simpa only [mul_zero,Function.comp_def] using (Real.tendsto_exp_atBot.comp hh).const_mul 2
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => measureReal_nonneg)) _ he
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (measureReal_mono (fun W hW => by obtain ⟨x,hx⟩ := hW; exact ⟨x,hx.le⟩)).trans (maximum_energy_tail hn)

end

section

open Set Filter MeasureTheory

lemma polynomial_exp_eventually_le (C : ℝ) {a : ℝ} (ha : 0<a) :
    ∀ᶠ n : ℕ in atTop, C*(n:ℝ)^2 ≤ Real.exp (a*(n:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => C*((n:ℝ)^2*Real.exp (-a*(n:ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha).comp tendsto_natCast_atTop_atTop).const_mul C
    simpa only [Function.comp_def,Real.rpow_two,mul_zero] using hh
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  have hm := mul_le_mul_of_nonneg_right hn.le (Real.exp_nonneg (a*(n:ℝ)))
  have he : Real.exp (-a*(n:ℝ))*Real.exp (a*(n:ℝ))=1 := by
    rw [← Real.exp_add,show -a*(n:ℝ)+a*(n:ℝ)=0 by ring,Real.exp_zero]
  simpa only [one_mul,mul_assoc,he,mul_one] using hm

lemma finite_tempered_mixing {n : ℕ} (hn : 0<n) (W : Disorder n) {β C : ℝ}
    (hβ : β≤1) (hC : 1≤C) (hH : ∀ x, |hamiltonian W x|≤3*(n:ℝ))
    (hgap : ∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) :
    continuousMixingTime W ≤ 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) ∧
    (discreteMixingTime W:ℝ) ≤ 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) := by
  have hN : (1:ℝ)≤n := by exact_mod_cast hn
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hE : 1≤Real.exp (6*(1-β)*(n:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hg (f : Spin n → ℝ) : variance W f ≤ (C*Real.exp (6*(1-β)*(n:ℝ)))*dirichlet W f := by
    convert poincare_temperature_comparison W hβ hCp.le hH hgap f using 1
    congr 3
    ring
  have hb := finite_gap_mixing_bounds W hn (by nlinarith : 1≤C*Real.exp (6*(1-β)*(n:ℝ)))
    (by positivity : (0:ℝ)≤3*(n:ℝ)) hg hH
  have hN2 : (n:ℝ)≤(n:ℝ)^2 := by nlinarith
  have hP : 0 ≤ C*Real.exp (6*(1-β)*(n:ℝ)) := by positivity
  constructor
  · refine hb.1.trans ?_
    have hh := mul_le_mul_of_nonneg_right (show 4*(2*(3*(n:ℝ))+(n:ℝ)+4) ≤ 44*(n:ℝ)^2 by nlinarith) hP
    nlinarith only [hh]
  · refine hb.2.trans ?_
    have hh := mul_le_mul_of_nonneg_right (show (n:ℝ)*(2*(3*(n:ℝ))+(n:ℝ)+4)+1 ≤ 44*(n:ℝ)^2 by nlinarith) hP
    have hc : 1≤C*Real.exp (6*(1-β)*(n:ℝ)) := by nlinarith
    nlinarith only [hh,hc]

lemma tempered_mixing_eventual_implication {ε β C : ℝ} (hε : 0<ε) (hβ : β≤1)
    (hsmall : 6*(1-β) ≤ ε/2) (hC : 1≤C) :
    ∀ᶠ n : ℕ in atTop, ∀ W : Disorder n,
      (∀ x, |hamiltonian W x|≤3*(n:ℝ)) →
      (∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f) →
      continuousMixingTime W ≤ Real.exp (ε*(n:ℝ)) ∧
      (discreteMixingTime W:ℝ) ≤ Real.exp (ε*(n:ℝ)) := by
  filter_upwards [eventually_gt_atTop (0:ℕ),polynomial_exp_eventually_le (44*C) (by positivity : 0<ε/2)] with n hn hp W hH hg
  have hb := finite_tempered_mixing hn W hβ hC hH hg
  have hh : 44*C*(n:ℝ)^2*Real.exp (6*(1-β)*(n:ℝ)) ≤ Real.exp (ε*(n:ℝ)) := by
    calc
      _ ≤ Real.exp ((ε/2)*(n:ℝ))*Real.exp (6*(1-β)*(n:ℝ)) := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
      _ = Real.exp ((ε/2)*(n:ℝ)+6*(1-β)*(n:ℝ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)])
  exact ⟨hb.1.trans hh,hb.2.trans hh⟩

lemma temperature_close_to_one {ε : ℝ} (hε : 0<ε) : ∃ β : ℝ, 0<β ∧ β<1 ∧ 6*(1-β)≤ε/2 := by
  let δ := min (ε/12) (1/2)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ≤1/2 := min_le_right _ _
  have hδε : δ≤ε/12 := min_le_left _ _
  refine ⟨1-δ,by linarith,by linarith,?_⟩
  linarith

end

open Set Filter MeasureTheory

lemma fiberMass_continuous {n : ℕ} (i : Fin n) (x : Spin n) :
    Continuous (fun W : Disorder n => fiberMass W i x) := by
  unfold fiberMass
  apply continuous_finsetSum
  intro y _
  by_cases hy : sameExcept i x y
  · simp only [ite_eq_left hy]; exact gibbs_continuous y
  · simp only [ite_eq_right hy]; exact continuous_const

lemma siteKernel_continuous {n : ℕ} (i : Fin n) (x y : Spin n) :
    Continuous (fun W : Disorder n => siteKernel W i x y) := by
  by_cases h : sameExcept i x y
  · simp only [siteKernel,ite_eq_left h]
    exact (gibbs_continuous y).div (fiberMass_continuous i x) (fun W => (fiberMass_pos W i x).ne')
  · simp only [siteKernel,ite_eq_right h]; exact continuous_const

lemma mean_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => mean W f) := by
  unfold mean
  exact continuous_finsetSum _ (fun x _ => (gibbs_continuous x).mul continuous_const)

lemma variance_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => variance W f) := by
  unfold variance
  change Continuous (fun W : Disorder n => ∑ x, gibbs W x*(f x-mean W f)^2)
  apply continuous_finsetSum
  intro x _
  exact (gibbs_continuous x).mul ((continuous_const.sub (mean_continuous f)).pow 2)

lemma dirichlet_continuous {n : ℕ} (f : Spin n → ℝ) : Continuous (fun W : Disorder n => dirichlet W f) := by
  unfold dirichlet mean
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro x _
  apply (gibbs_continuous x).mul
  apply Continuous.pow
  apply continuous_const.sub
  exact continuous_finsetSum _ (fun y _ => (siteKernel_continuous i x y).mul continuous_const)

def poincareEvent (n : ℕ) (β C : ℝ) : Set (Disorder n) :=
  {W | ∀ f : Spin n → ℝ, variance (β • W) f ≤ C*dirichlet (β • W) f}

lemma poincareEvent_closed (n : ℕ) (β C : ℝ) : IsClosed (poincareEvent n β C) := by
  have he : poincareEvent n β C = ⋂ f : Spin n → ℝ,
      {W : Disorder n | variance (β • W) f ≤ C*dirichlet (β • W) f} := by ext W; simp [poincareEvent]
  rw [he]
  apply isClosed_iInter
  intro f
  have hs : Continuous (fun W : Disorder n => β • W) := continuous_const_smul β
  exact isClosed_le ((variance_continuous f).comp hs)
    (continuous_const.mul ((dirichlet_continuous f).comp hs))

lemma tempered_mixing_probability_lower {ε β C : ℝ} (hε : 0<ε) (hβ : β≤1)
    (hsmall : 6*(1-β)≤ε/2) (hC : 1≤C) :
    ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (poincareEvent n β C)-2*Real.exp (-(3/2:ℝ)*(n:ℝ)) ≤
        (disorderLaw n).real {W | continuousMixingTime W≤Real.exp (ε*(n:ℝ)) ∧
          (discreteMixingTime W:ℝ)≤Real.exp (ε*(n:ℝ))} := by
  filter_upwards [tempered_mixing_eventual_implication hε hβ hsmall hC,eventually_gt_atTop (0:ℕ)] with n hn hnp
  let U : Set (Disorder n) := {W | continuousMixingTime W≤Real.exp (ε*(n:ℝ)) ∧
    (discreteMixingTime W:ℝ)≤Real.exp (ε*(n:ℝ))}
  let B : Set (Disorder n) := {W | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|}
  have hs : poincareEvent n β C ⊆ U ∪ B := by
    intro W hW
    by_cases hb : W∈B
    · exact Or.inr hb
    · apply Or.inl
      apply hn W _ hW
      intro x
      by_contra hx
      exact hb ⟨x,(lt_of_not_ge hx).le⟩
  have hp := (measureReal_mono (μ := disorderLaw n) hs).trans (measureReal_union_le U B)
  have hb := maximum_energy_tail hnp
  change (disorderLaw n).real B ≤ _ at hb
  change _ ≤ (disorderLaw n).real U
  linarith

noncomputable def mixingReductionError (n : ℕ) (ε : ℝ) : ℝ :=
  2*Real.exp (-(3/2:ℝ)*(n:ℝ)) +
    (disorderLaw n).real {W | (1:ℝ)≤|continuousGoodMass W ((n:ℝ)^(2/3-ε))-1|} +
    (disorderLaw n).real {W | (1:ℝ)≤|discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊-1|}

def twoClockMixingEvent (n : ℕ) (ε : ℝ) : Set (Disorder n) :=
  {W | (n:ℝ)^(2/3-ε) ≤ continuousMixingTime W ∧
    continuousMixingTime W ≤ Real.exp (ε*(n:ℝ)) ∧
    (n:ℝ)^(5/3-ε) ≤ (discreteMixingTime W:ℝ) ∧
    (discreteMixingTime W:ℝ) ≤ Real.exp (ε*(n:ℝ))}

lemma mixingReductionError_tendsto {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => mixingReductionError n ε) atTop (𝓝 0) := by
  have hc := realized_continuous_initial_states (fun n => (n:ℝ)^(2/3-ε))
    (fun _ => by positivity) (rpow_ratio_tendsto_zero hε) 1 zero_lt_one
  have hd := realized_discrete_initial_states (fun n => ⌈(n:ℝ)^(5/3-ε)⌉₊)
    (ceil_rpow_ratio_tendsto_zero (by norm_num : (0:ℝ)<5/3) hε) 1 zero_lt_one
  have he : Tendsto (fun n : ℕ => 2*Real.exp (-(3/2:ℝ)*(n:ℝ))) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => -(3/2:ℝ)*(n:ℝ)) atTop atBot :=
      (tendsto_const_mul_atBot_of_neg (by norm_num : -(3/2:ℝ)<0)).mpr tendsto_natCast_atTop_atTop
    simpa using (Real.tendsto_exp_atBot.comp ht).const_mul 2
  simpa only [mixingReductionError,add_zero] using (he.add hc).add hd

lemma mixingGapReduction_lower {ε β C : ℝ} (hε : 0<ε) (hβ : β≤1)
    (hsmall : 6*(1-β)≤ε/2) (hC : 1≤C) :
    ∀ᶠ n : ℕ in atTop,
      (disorderLaw n).real (poincareEvent n β C)-mixingReductionError n ε ≤
        (disorderLaw n).real (twoClockMixingEvent n ε) := by
  filter_upwards [tempered_mixing_eventual_implication hε hβ hsmall hC,
    eventually_gt_atTop (0:ℕ)] with n hn hnp
  let B : Set (Disorder n) := {W | ∃ x : Spin n, 3*(n:ℝ)≤|hamiltonian W x|}
  let Lc : Set (Disorder n) := {W | (1:ℝ)≤|continuousGoodMass W ((n:ℝ)^(2/3-ε))-1|}
  let Ld : Set (Disorder n) := {W | (1:ℝ)≤|discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊-1|}
  have hs : poincareEvent n β C ⊆ ((twoClockMixingEvent n ε ∪ B) ∪ Lc) ∪ Ld := by
    intro W hW
    by_cases hb : W∈B
    · exact Or.inl (Or.inl (Or.inr hb))
    by_cases hc : W∈Lc
    · exact Or.inl (Or.inr hc)
    by_cases hd : W∈Ld
    · exact Or.inr hd
    apply Or.inl ∘ Or.inl ∘ Or.inl
    have hH : ∀ x, |hamiltonian W x|≤3*(n:ℝ) := by
      intro x
      by_contra hx
      exact hb ⟨x,(lt_of_not_ge hx).le⟩
    have hu := hn W hH hW
    have hc' : 0<continuousGoodMass W ((n:ℝ)^(2/3-ε)) := by
      have hh : |continuousGoodMass W ((n:ℝ)^(2/3-ε))-1|<1 := lt_of_not_ge hc
      have hl := (abs_lt.mp hh).1
      linarith
    have hd' : 0<discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊ := by
      have hh : |discreteGoodMass W ⌈(n:ℝ)^(5/3-ε)⌉₊-1|<1 := lt_of_not_ge hd
      have hl := (abs_lt.mp hh).1
      linarith
    exact ⟨continuousMixingTime_lower W hnp hc',hu.1,
      (Nat.le_ceil _).trans (Nat.cast_le.mpr (discreteMixingTime_lower W hnp hd')),hu.2⟩
  have hp := measureReal_mono (μ := disorderLaw n) hs
  have h1 := measureReal_union_le (μ := disorderLaw n) ((twoClockMixingEvent n ε ∪ B) ∪ Lc) Ld
  have h2 := measureReal_union_le (μ := disorderLaw n) (twoClockMixingEvent n ε ∪ B) Lc
  have h3 := measureReal_union_le (μ := disorderLaw n) (twoClockMixingEvent n ε) B
  have hb := maximum_energy_tail hnp
  change (disorderLaw n).real B ≤ _ at hb
  change (disorderLaw n).real (poincareEvent n β C)-
    (2*Real.exp (-(3/2:ℝ)*(n:ℝ))+(disorderLaw n).real Lc+(disorderLaw n).real Ld) ≤ _
  linarith

end CriticalSK

end

end OAI
