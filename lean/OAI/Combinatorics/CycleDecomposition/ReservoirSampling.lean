import OAI.Combinatorics.CycleDecomposition.SamplingCuts

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
namespace ErdosGallai.Sampling

lemma eventually_monomial_lt (K c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∀ᶠ D : ℝ in atTop, K * D^a < c * D^b := by
  have ht : Tendsto (fun D : ℝ => K * D^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K
    simpa only [neg_sub, mul_zero] using hh
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_lt_const hc] with D hD htD
  have hb : 0 < D^b := Real.rpow_pos_of_pos hD b
  have heq : D^a = D^(a-b) * D^b := by rw [← Real.rpow_add hD]; congr 1; ring
  rw [heq, ← mul_assoc]
  exact mul_lt_mul_of_pos_right htD hb

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma eventually_log_le_small_power : ∀ᶠ D : ℝ in atTop, log D ≤ D^(1/10 : ℝ) := by
  filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/10 by norm_num)).eventuallyLE,
    eventually_ge_atTop (1 : ℝ)] with D hD h1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hD

def samplingScaleError (c p D : ℝ) : ℝ :=
  exp (-p/3 * D^(9/10 : ℝ)) +
    D^(51/50 : ℝ) * exp (-(p*c/8) * D^(9/10 : ℝ)) +
    (2*(4/c+2)) * (D^(23/20 : ℝ) * exp (-(p^3*c^2/512) * D^(39/50 : ℝ)))

lemma samplingScaleError_tendsto (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    Tendsto (samplingScaleError c p) atTop (𝓝 0) := by
  have h0 := tendsto_monomial_exp_neg_power 0 (9/10) (p/3) (by norm_num) (by positivity)
  have h1 := tendsto_monomial_exp_neg_power (51/50) (9/10) (p*c/8) (by norm_num) (by positivity)
  have h2 := (tendsto_monomial_exp_neg_power (23/20) (39/50) (p^3*c^2/512)
    (by norm_num) (by positivity)).const_mul (2*(4/c+2))
  unfold samplingScaleError
  simpa [neg_div, Real.rpow_zero] using (h0.add h1).add h2

def SamplingScaleReady (c p D : ℝ) (r : ℕ) : Prop :=
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  2 ≤ r ∧ τ < p*h/4 ∧ M ≤ h ∧ (r : ℝ)*exp (-p*M/4) < 1/2 ∧
    4*τ/(p*h)+4*τ*M/h ≤ 1/2 ∧
    τ+r*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8 ∧
    exp (-p*r/3) + r*exp (-p*h/8) +
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) * (r : ℝ)^⌈4*r*M/h⌉₊ *
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D

lemma sampling_witness_error_le (c p D : ℝ) (r : ℕ) (hc : 0 < c) (hp : 0 < p)
    (hD : 1 ≤ D) (hrpos : 0 < (r : ℝ)) (hrhi : (r : ℝ) ≤ D^(51/50 : ℝ))
    (hlog : log D ≤ D^(1/10 : ℝ))
    (hcost : ((51/50)*(4/c+2))*D^(23/100 : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ)) :
    let h := c*D^(9/10 : ℝ)
    let M := D^(1/100 : ℝ)
    2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤
      (2*(4/c+2))*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
  let h := c*D^(9/10 : ℝ)
  let M := D^(1/100 : ℝ)
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hDpos : 0 < D := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have hrNat : 0 < r := by exact_mod_cast hrpos
  have hs : ((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤ K*D^(13/100 : ℝ) := by
    have hnorm : 4*D^(51/50 : ℝ)*M/h = (4/c)*D^(13/100 : ℝ) := by
      dsimp [M,h]
      rw [show (13/100 : ℝ) = (51/50+1/100)-9/10 by norm_num,
        Real.rpow_sub hDpos, Real.rpow_add hDpos]
      field_simp
    calc
      _ ≤ 4*r*M/h+2 := by
        have hs := (Nat.ceil_lt_add_one (show 0 ≤ 4*(r : ℝ)*M/h by positivity)).le
        push_cast
        linarith
      _ ≤ 4*D^(51/50 : ℝ)*M/h+2 := by gcongr
      _ = (4/c)*D^(13/100 : ℝ)+2 := by rw [hnorm]
      _ ≤ K*D^(13/100 : ℝ) := by
        have hd := Real.one_le_rpow hD (show (0 : ℝ) ≤ 13/100 by norm_num)
        dsimp [K]
        nlinarith
  have hln : log (r : ℝ) ≤ (51/50)*log D := by
    simpa only [Real.log_rpow hDpos] using Real.log_le_log hrpos hrhi
  have hecost : (⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ) := by
    have hs' : (⌈4*r*M/h⌉₊ : ℝ) ≤ K*D^(13/100 : ℝ) := by push_cast at hs; linarith
    calc
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*log D) := by
        apply mul_le_mul hs' hln
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
        · positivity
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*D^(1/10 : ℝ)) := by gcongr
      _ = ((51/50)*K)*D^(23/100 : ℝ) := by
        have he := Real.rpow_add hDpos (13/100 : ℝ) (1/10)
        norm_num at he
        rw [he]
        ring
      _ ≤ _ := hcost
  have hratio : c^2*D^(39/50 : ℝ) ≤ h^2/(r : ℝ) := by
    have he : c^2*D^(39/50 : ℝ) = h^2/D^(51/50 : ℝ) := by
      dsimp [h]
      rw [show (39/50 : ℝ) = (9/10)*2-51/50 by norm_num,
        Real.rpow_sub hDpos]
      have he2 := Real.rpow_mul_natCast hDpos.le (9/10 : ℝ) 2
      norm_num only [Nat.cast_ofNat] at he2
      rw [show (9/10 : ℝ)*2=9/5 by norm_num, he2]
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (sq_nonneg h) hrpos hrhi
  have hexpcost : exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) - p^3*h^2/(256*r)) ≤
      exp (-(p^3*c^2/512)*D^(39/50 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hratio (show 0 ≤ p^3/256 by positivity)
    have hid : (p^3/256)*(h^2/(r : ℝ)) =p^3*h^2/(256*r) := by ring
    rw [hid] at hn
    nlinarith
  have hpoly : 2*(r : ℝ)*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤
      2*K*D^(23/20 : ℝ) := by
    calc
      _ ≤ 2*D^(51/50 : ℝ)*(K*D^(13/100 : ℝ)) := by gcongr
      _ = _ := by
        have he := Real.rpow_add hDpos (51/50 : ℝ) (13/100)
        norm_num at he
        rw [he]
        ring
  have hwitness : 2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
      exp (-p^3*h^2/(256*r)) ≤
      (2*K)*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
    have heq : (r : ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r)) =
        exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ)-p^3*h^2/(256*r)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hrpos]
      simp only [neg_mul,  Real.exp_neg, div_eq_mul_inv]
    rw [mul_assoc (2*(r : ℝ)*_) _ _, heq]
    exact (mul_le_mul hpoly hexpcost (exp_pos _).le (by positivity)).trans_eq (by ring)
  exact hwitness

lemma eventually_samplingScaleReady (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℕ,
      D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) → SamplingScaleReady c p D r := by
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hmiss : Tendsto (fun D : ℝ => D^(51/50 : ℝ) * exp (-p/4*D^(1/100 : ℝ)))
      atTop (𝓝 0) := by
    convert tendsto_monomial_exp_neg_power (51/50) (1/100) (p/4)
      (by norm_num) (by positivity) using 1 ; simp [neg_div]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 9/10 by norm_num)).eventually_ge_atTop 2,
    eventually_monomial_lt 1 (p*c/4) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt 1 c (1/100) (9/10) hc (by norm_num),
    hmiss.eventually_lt_const (show (0 : ℝ) < 1/2 by norm_num),
    eventually_monomial_lt (4/(p*c)) (1/4) (-4/25) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt (4/c) (1/4) (-3/20) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt 1 (p^2*c/24) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/(p*c)) (p^2*c/24) (43/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/c) (p^2*c/24) (87/100) (9/10) (by positivity) (by norm_num),
    eventually_log_le_small_power,
    eventually_monomial_lt ((51/50)*K) (p^3*c^2/512) (23/100) (39/50)
      (by positivity) (by norm_num)] with D hD h2 hτ hM hm hε₁ hε₂ ht₀ ht₁ ht₂ hlog hcost
  intro r hrlo hrhi
  have hDpos : 0 < D := by linarith
  have hr2 : 2 ≤ r := by exact_mod_cast h2.trans hrlo
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hDpos _
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have he₁ : 4*τ/(p*h) = (4/(p*c))*D^(-4/25 : ℝ) := by
    dsimp [τ,h]
    rw [show (-4/25 : ℝ) =37/50-9/10 by norm_num, Real.rpow_sub hDpos]
    field_simp
  have he₂ : 4*τ*M/h = (4/c)*D^(-3/20 : ℝ) := by
    dsimp [τ,M,h]
    rw [show (-3/20 : ℝ) =(37/50+1/100)-9/10 by norm_num,
      Real.rpow_sub hDpos, Real.rpow_add hDpos]
    field_simp
  have hm₁ : D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)) =
      (4/(p*c))*D^(43/50 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  have hm₂ : D^(51/50 : ℝ)*((4/c)*D^(-3/20 : ℝ)) =
      (4/c)*D^(87/100 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  refine ⟨hr2, ?_, (by simpa only [one_mul] using hM.le), ?_, ?_, ?_, ?_⟩
  · change τ < p*h/4
    dsimp [τ,h]
    simpa only [one_mul, div_mul_eq_mul_div, mul_assoc] using hτ
  · change (r : ℝ)*exp (-p*M/4) < 1/2
    calc
      _ ≤ D^(51/50 : ℝ)*exp (-p*M/4) := mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
      _ < _ := by simpa [M, div_mul_eq_mul_div] using hm
  · change 4*τ/(p*h)+4*τ*M/h ≤ 1/2
    rw [he₁, he₂]
    simp only [Real.rpow_zero, mul_one] at hε₁ hε₂
    linarith
  · change τ+(r : ℝ)*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8
    rw [he₁,he₂]
    have ht : (r : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) ≤
        (4/(p*c))*D^(43/50 : ℝ)+(4/c)*D^(87/100 : ℝ) := by
      calc
        _ ≤ D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hrhi; positivity
        _ = _ := by rw [mul_add, hm₁, hm₂]
    dsimp [τ,h]
    nlinarith
  · change exp (-p*r/3)+r*exp (-p*h/8)+
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D
    have hwitness := sampling_witness_error_le c p D r hc hp hD hrpos hrhi hlog hcost.le
    have hsize : exp (-p*r/3) ≤ exp (-p/3*D^(9/10 : ℝ)) := by
      apply exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hrlo hp.le
      nlinarith
    have hdegree : (r : ℝ)*exp (-p*h/8) ≤
        D^(51/50 : ℝ)*exp (-(p*c/8)*D^(9/10 : ℝ)) := by
      have heq : -p*h/8=-(p*c/8)*D^(9/10 : ℝ) := by dsimp [h]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
    exact add_le_add (add_le_add hsize hdegree) hwitness

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Filter MeasureTheory Real

universe u

theorem vertex_sampling_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (_hp1 : (p : ℝ) < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      CutExpansion P (c*D^(9/10 : ℝ)) →
      (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω} ≤ ε := by
  have hevent : ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧
      (∀ r : ℕ, D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) →
        SamplingScaleReady c (p : ℝ) D r) ∧
      samplingScaleError c (p : ℝ) D ≤ ε := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_samplingScaleReady c (p : ℝ) hc hp,
      (samplingScaleError_tendsto c (p : ℝ) hc hp).eventually_le_const hε] with D h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hrlo hrhi hexp
  obtain ⟨h1, hready, herr⟩ := hD₀ D hD
  have hDpos : 0 < D := by linarith
  obtain ⟨hr,hτ,hM,hmiss,he,hperturb,hbound⟩ := hready (Fintype.card V) hrlo hrhi
  exact (vertex_sampling_failure_bound P p hp (by positivity) (by positivity)
    hτ (by positivity) hM hr hmiss he hperturb hexp).trans (hbound.trans herr)

end ErdosGallai.Sampling

open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Sampling

def reservoirLabelPMF (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) : PMF (Fin 4) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (if i = 3 then 1-3*(p : ℝ) else (p : ℝ))) (by
    rw [Fin.sum_univ_four]
    simp only [show (0 : Fin 4) ≠ 3 by decide, show (1 : Fin 4) ≠ 3 by decide,
      show (2 : Fin 4) ≠ 3 by decide, ↓reduceIte,  ]
    rw [← ENNReal.ofReal_add p.property.1 p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) p.property.1,
      ← ENNReal.ofReal_add (by linarith [p.property.1]) (by linarith)]
    norm_num [show (p : ℝ)+(p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1 by ring])

def labelIs (i : Fin 3) (j : Fin 4) : Bool := decide (j = i.castSucc)

lemma ofReal_unitInterval (p : unitInterval) :
    ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ENNReal) := by
  unfold ENNReal.ofReal
  apply congrArg (fun x : NNReal => (x : ENNReal))
  apply Subtype.ext
  exact Real.coe_toNNReal _ p.property.1

lemma labelIs_preserving (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (labelIs i) (reservoirLabelPMF p hp).toMeasure
      (bernoulliMeasure true false p) := by
  have hnon : 0 ≤ (p : ℝ) := p.property.1
  have hnon' : 0 ≤ 1-3*(p : ℝ) := by linarith
  refine ⟨measurable_of_finite _, ?_⟩
  apply Measure.ext_iff_singleton.mpr
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  rw [PMF.toMeasure_apply_fintype]
  simp only [reservoirLabelPMF]
  cases b <;> fin_cases i <;>
    simp [labelIs, Fin.sum_univ_four,  PMF.ofFintype_apply]
  all_goals
    first
    | exact ofReal_unitInterval p
    | rw [← ENNReal.ofReal_add hnon hnon,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (p : ℝ)+(p : ℝ)) hnon']
      convert ofReal_unitInterval (unitInterval.symm p) using 1
      congr 1
      change (p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1-(p : ℝ)
      ring

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory
noncomputable section
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

def reservoirSample (i : Fin 3) (ω : V → Fin 4) : V → Bool := fun v => labelIs i (ω v)

def reservoirMeasure (V : Type cycleUniverse2) [Fintype V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    Measure (V → Fin 4) := Measure.pi (fun _ : V => (reservoirLabelPMF p hp).toMeasure)

instance reservoirMeasure_probability (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) :
    IsProbabilityMeasure (reservoirMeasure V p hp) := by unfold reservoirMeasure; infer_instance

lemma reservoirSample_preserving {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (reservoirSample i) (reservoirMeasure V p hp) (sampleMeasure V p) := by
  exact measurePreserving_pi _ _ (fun _ => labelIs_preserving p hp i)

lemma reservoirSamples_disjoint {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (ω : V → Fin 4) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (sampleVertices (reservoirSample i ω)) (sampleVertices (reservoirSample j ω)) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    reservoirSample, labelIs, decide_eq_true_eq] at hi hj
  exact hij (Fin.castSucc_injective 3 (hi.symm.trans hj))

universe u

theorem three_reservoirs_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp3 : 3*(p : ℝ) ≤ 1) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (P i).Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      (∀ i, CutExpansion (P i) (c*D^(9/10 : ℝ))) →
      ∃ W : Fin 3 → Finset V,
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*(p : ℝ)*Fintype.card V) ∧
        (∀ i v, (p : ℝ)*(c*D^(9/10 : ℝ))/2 ≤ ((neighborsIn (P i) v (W i)).card : ℝ)) ∧
        (∀ i, CutExpansionOn (P i) (W i) (D^(37/50 : ℝ))) := by
  have hp1 : (p : ℝ) < 1 := by linarith
  obtain ⟨D₀,hD₀⟩ := vertex_sampling_uniform.{u} c hc p hp hp1 (1/4) (by norm_num)
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hlo hhi hcut
  let μ := reservoirMeasure V p hp3
  let B : Fin 3 → Set (V → Fin 4) := fun i =>
    {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) (reservoirSample i ω)}
  have hB : ∀ i, μ.real (B i) ≤ 1/4 := by
    intro i
    have hm := (reservoirSample_preserving (V := V) p hp3 i).measure_preimage
      ((Set.Finite.measurableSet (Set.toFinite {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω})).nullMeasurableSet)
    change (μ (B i)).toReal ≤ 1/4
    rw [show μ (B i) = (sampleMeasure V p) {ω | ¬SampleGood (P i) (p : ℝ)
      (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) ω} from hm]
    exact hD₀ D hD V (P i) hlo hhi (hcut i)
  have hi : ∑ i ∈ (Finset.univ : Finset (Fin 3)), μ.real (B i) < 1 := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (1/4 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ => hB i)
      _ < 1 := by norm_num
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events (μ := μ) Finset.univ B hi
  have hgood : ∀ i, SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ))
      (reservoirSample i ω) := by
    intro i
    exact not_not.mp (hω i (Finset.mem_univ i))
  refine ⟨fun i => sampleVertices (reservoirSample i ω), reservoirSamples_disjoint ω,
    fun i => (hgood i).1, fun i => (hgood i).2.1, fun i => (hgood i).2.2⟩

end
end ErdosGallai.Sampling

end
end
end

end OAI
