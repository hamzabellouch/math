import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.TrialSmoothTest
import OAI.Analysis.CoulombIonization.FieldAnalysis.HardyField
import OAI.Analysis.CoulombIonization.Variational.Electrostatic

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom

lemma linearMap_ne_zero_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure]
    (P : E →L[ℝ] Space) (hP : P ≠ 0) : ∀ᵐ x : E, P x ≠ 0 := by
  rw [ae_iff]
  have hk : P.toLinearMap.ker ≠ ⊤ := by
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    apply hP
    ext1 x
    exact LinearMap.congr_fun h x
  have he : {a | P a = 0} = (P.toLinearMap.ker : Set E) := by
    ext x
    rfl
  simpa only [not_not, he] using
    Measure.addHaar_submodule (volume : Measure E) P.toLinearMap.ker hk

lemma configuration_ae_nonsingular (N : ℕ) :
    ∀ᵐ x : Configuration N, (∀ i, x i ≠ 0) ∧ Function.Injective x := by
  have h0 : ∀ i : Fin N, ∀ᵐ x : Configuration N, x i ≠ 0 := by
    intro i
    apply linearMap_ne_zero_ae (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space)
    intro h
    have hh := congrArg (fun F : Configuration N →L[ℝ] Space => F (direction i 0)) h
    have ht := congrArg (fun y : Space => y 0) hh
    simp [direction, EuclideanSpace.single] at ht
  have hp : ∀ i j : Fin N, ∀ᵐ x : Configuration N, i ≠ j → x i ≠ x j := by
    intro i j
    by_cases hij : i = j
    · subst j; exact Eventually.of_forall fun _ => by simp
    · have hh := linearMap_ne_zero_ae
        ((ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space) - ContinuousLinearMap.proj j)
        (by
          intro h
          have hq := congrArg (fun F : Configuration N →L[ℝ] Space => F (direction i 0)) h
          have ht := congrArg (fun y : Space => y 0) hq
          simp [direction, Ne.symm hij, EuclideanSpace.single] at ht)
      filter_upwards [hh] with x hx
      exact fun _ => sub_ne_zero.mp hx
  filter_upwards [ae_all_iff.mpr h0, ae_all_iff.mpr fun i => ae_all_iff.mpr (hp i)] with x hx hxp
  refine ⟨hx, ?_⟩
  intro i j hij
  by_contra h
  exact hxp i j h hij

lemma nuclear_hardy {N : ℕ} (i : Fin N)
    {f : Configuration N → ℂ} {g : Fin 3 → Configuration N → ℂ}
    (hf : MemLp f 2) (hg : ∀ a, MemLp (g a) 2)
    (hweak : ∀ a (φ : Configuration N → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ y, f y * Complex.ofReal (lineDeriv ℝ φ y (direction i a))) =
        -(∫ y, g a y * (φ y : ℂ))) :
    Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖ ^ 2) ∧
    (∫ x, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) ≤ 4 * ∑ a, ∫ x, ‖g a x‖ ^ 2 := by
  let P : Configuration N →L[ℝ] Space := ContinuousLinearMap.proj i
  have hp : ∀ a, P (direction i a) = EuclideanSpace.single a 1 := by
    intro a
    change direction i a i = _
    simp [direction]
  exact linear_hardy_integrable_bound P (direction i) hp hf hg hweak

lemma integrated_potential_stability {N M : ℕ} {Z : ℝ} (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M)
    {f : Configuration N → ℂ} (hf : MemLp f 2)
    (hnu : ∀ i, Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖))
    (hrep : ∀ i j, i ≠ j → Integrable (fun x => ‖f x‖ ^ 2 / ‖x i - x j‖))
    (hH : ∀ i, Integrable (fun x => ‖f x‖ ^ 2 / ‖x i‖ ^ 2)) :
    -(1 / 8 : ℝ) * (∑ i, ∫ x, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) -
      2 * Z ^ 2 * M * (∫ x, ‖f x‖ ^ 2) ≤
      -Z * (∑ i, ∫ x, ‖f x‖ ^ 2 / ‖x i‖) +
        ∑ i, ∑ j, if i < j then (∫ x, ‖f x‖ ^ 2 / ‖x i - x j‖) else 0 := by
  classical
  have hpair (i j : Fin N) : Integrable
      (fun x => if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0) := by
    by_cases h : j < i
    · simpa only [h, ite_true] using hrep i j h.ne'
    · simp only [h, ite_false]; exact integrable_zero _ ℝ volume
  have hp := integral_mono_ae
    (((integrable_finsetSum _ fun i _ => hH i).const_mul (-(1 / 8 : ℝ))).sub
      (hf.norm.integrable_sq.const_mul (2 * Z ^ 2 * M)))
    (((integrable_finsetSum _ fun i _ => hnu i).const_mul (-Z)).add
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j))
    (show ∀ᵐ x : Configuration N,
      -(1 / 8 : ℝ) * (∑ i, ‖f x‖ ^ 2 / ‖x i‖ ^ 2) - 2 * Z ^ 2 * M * ‖f x‖ ^ 2 ≤
        -Z * (∑ i, ‖f x‖ ^ 2 / ‖x i‖) +
          ∑ i, ∑ j, if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0 from by
      filter_upwards [configuration_ae_nonsingular N] with x hx
      have hh := mul_le_mul_of_nonneg_right (potential_stability hZ hM x hx.1 hx.2)
        (sq_nonneg ‖f x‖)
      simp only [sub_mul, add_mul, pairPotential, Finset.sum_mul, ite_mul, zero_mul] at hh
      simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum] at hh
      simpa only [Finset.mul_sum, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm, mul_comm] using hh)
  simp only [Pi.sub_apply, Pi.add_apply] at hp
  rw [integral_sub
    ((integrable_finsetSum _ fun i _ => hH i).const_mul (-(1 / 8 : ℝ)))
    (hf.norm.integrable_sq.const_mul (2 * Z ^ 2 * M)),
    integral_add ((integrable_finsetSum _ fun i _ => hnu i).const_mul (-Z))
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j)] at hp
  simp only [integral_const_mul] at hp
  rw [integral_finsetSum _ (fun i _ => hH i), integral_finsetSum _ (fun i _ => hnu i),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hpair i j)] at hp
  simp_rw [integral_finsetSum _ (fun j _ => hpair _ j)] at hp
  have he : (∑ i : Fin N, ∑ j : Fin N,
      ∫ x, if j < i then ‖f x‖ ^ 2 / ‖x i - x j‖ else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        if i < j then (∫ x, ‖f x‖ ^ 2 / ‖x i - x j‖) else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp only [h, ite_true]
      congr 1; funext x; rw [norm_sub_rev]
    · simp only [h, ite_false, integral_zero]
  rwa [he] at hp

theorem formEnergy_uniform_lower_bound {N M : ℕ} {Z : ℝ}
    (hZ : 0 ≤ Z) (hM : 2 * Z ≤ M) {ψ : FormVector N} (hψ : FormAdmissible ψ) :
    -2 * Z ^ 2 * M ≤ formEnergy Z ψ := by
  rcases hψ with ⟨hf, hg, hw, _, hnorm, hnu, hrep⟩
  have hh (s : Spins N) (i : Fin N) := nuclear_hardy i (hf s) (hg s i) (hw s i)
  have hp (s : Spins N) := integrated_potential_stability hZ hM (hf s) (hnu s) (hrep s)
    (fun i => (hh s i).1)
  have ht (s : Spins N) : (∑ i : Fin N, ∫ x, ‖ψ.value s x‖ ^ 2 / ‖x i‖ ^ 2) ≤
      4 * ∑ i : Fin N, ∑ a : Fin 3, ∫ x, ‖ψ.gradient s i a x‖ ^ 2 := by
    simpa only [← Finset.mul_sum] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hh s i).2)
  have hps := Finset.sum_le_sum (s := Finset.univ) fun s _ => hp s
  have hts := Finset.sum_le_sum (s := Finset.univ) fun s _ => ht s
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hnorm,
    mul_one] at hps hts
  unfold formEnergy
  nlinarith


def DeficitSecants (G d : ℝ → ℝ) : Prop :=
  ∀ v t : ℝ, 0 < v → v < t →
    -(t - v) * d t ≤ G t - G v ∧ G t - G v ≤ -(t - v) * d v

theorem DeficitSecants.monotoneOn {G d : ℝ → ℝ} (h : DeficitSecants G d) :
    MonotoneOn d (Set.Ioi 0) := by
  intro v hv t _ hvt
  rcases hvt.eq_or_lt with rfl | hvt
  · exact le_rfl
  · have hs := (h v t hv hvt).1.trans (h v t hv hvt).2
    have hh : 0 < t - v := sub_pos.mpr hvt
    nlinarith

theorem grid_increment_error {G d P D : ℝ → ℝ}
    (hG : DeficitSecants G d) (hP : DeficitSecants P D)
    {a h η : ℝ} (ha : 0 < a) (hh : 0 < h) {N : ℕ}
    (hclose : ∀ i ≤ N, |d (a + i * h) - D (a + i * h)| ≤ η) :
    |(G (a + N * h) - G a) - (P (a + N * h) - P a)| ≤
      h * (D (a + N * h) - D a) + N * h * η := by
  have hind : ∀ i ≤ N,
      |(G (a + i * h) - G a) - (P (a + i * h) - P a)| ≤
        h * (D (a + i * h) - D a) + i * h * η := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
      have hix : 0 < a + i * h := by positivity
      have hxy : a + i * h < a + (i + 1 : ℕ) * h := by
        push_cast
        nlinarith
      have hsG := hG (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hsP := hP (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hcl := (abs_le.mp (hclose i hiN))
      have hcr := (abs_le.mp (hclose (i + 1) hi))
      have hcl' := mul_le_mul_of_nonneg_left hcl.1 hh.le
      have hcr' := mul_le_mul_of_nonneg_left hcr.2 hh.le
      have heq : a + (i + 1 : ℕ) * h - (a + i * h) = h := by
        push_cast
        ring
      rw [heq] at hsG hsP
      have hstep : |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| ≤
          h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsG.1, hsG.2, hsP.1, hsP.2]
      have htel : (G (a + (i + 1 : ℕ) * h) - G a) -
          (P (a + (i + 1 : ℕ) * h) - P a) =
          ((G (a + i * h) - G a) - (P (a + i * h) - P a)) +
          ((G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))) := by ring
      rw [htel]
      calc
        _ ≤ |(G (a + i * h) - G a) - (P (a + i * h) - P a)| +
            |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
            (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| := abs_add_le _ _
        _ ≤ (h * (D (a + i * h) - D a) + i * h * η) +
            (h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η) :=
          add_le_add (ih hiN) hstep
        _ = _ := by push_cast; ring
  exact hind N le_rfl

theorem deficit_secant_increments_tendsto {G d : ℕ → ℝ → ℝ} {P D : ℝ → ℝ}
    (hG : ∀ n, DeficitSecants (G n) (d n)) (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => G n b - G n a) atTop (𝓝 (P b - P a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * ((b - a) * (D b - D a)) / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hwidth : 0 < b - a := sub_pos.mpr hab
  let h : ℝ := (b - a) / N
  let η : ℝ := ε / (2 * (b - a))
  have hh : 0 < h := div_pos hwidth hNpos
  have hη : 0 < η := div_pos hε (by positivity)
  have hxN : a + N * h = b := by dsimp [h]; field_simp; ring
  have hmesh : h * (D b - D a) < ε / 2 := by
    have hnr : 2 * ((b - a) * (D b - D a)) / ε < N :=
      (le_max_right _ _).trans_lt hN
    have hnr' := (div_lt_iff₀ hε).mp hnr
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ hNpos (show (0 : ℝ) < 2 by norm_num)).mpr
    nlinarith
  have hηeq : (N : ℝ) * h * η = ε / 2 := by
    dsimp [h, η]
    field_simp
  have hev : ∀ i : Fin (N + 1), ∀ᶠ n in atTop,
      |d n (a + (i : ℕ) * h) - D (a + (i : ℕ) * h)| ≤ η := by
    intro i
    have hxi : 0 < a + (i : ℕ) * h := by positivity
    exact ((Metric.tendsto_nhds.mp (hd _ hxi)) η hη).mono fun n hn =>
      le_of_lt (by simpa only [Real.dist_eq] using hn)
  filter_upwards [Filter.eventually_all.mpr hev] with n hn
  rw [Real.dist_eq]
  have he := grid_increment_error (hG n) hP ha hh
    (N := N) (η := η) (fun i hi => hn ⟨i, Nat.lt_succ_iff.mpr hi⟩)
  rw [hxN, hηeq] at he
  linarith

theorem deficit_secant_energy_tendsto {G d : ℕ → ℝ → ℝ} {P D : ℝ → ℝ}
    {err : ℕ → ℝ} (hG : ∀ n, DeficitSecants (G n) (d n))
    (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    (he : Tendsto err atTop (𝓝 0))
    (hzero : ∀ v, 0 < v → ∀ᶠ n in atTop, -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    (hPc : ContinuousAt P 0) (hP0 : P 0 = 0) (hDc : ContinuousAt D 0)
    {t : ℝ} (ht : 0 < t) : Tendsto (fun n => G n t) atTop (𝓝 (P t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : ContinuousAt (fun v : ℝ => |P v| + |v * D v|) 0 :=
    hPc.abs.add ((continuousAt_id.mul hDc).abs)
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), |P v| + |v * D v| < ε / 4 := by
    have hconv : Tendsto (fun v : ℝ => |P v| + |v * D v|) (𝓝 0) (𝓝 0) := by
      simpa [hP0] using hc.tendsto
    exact hconv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  obtain ⟨δ, hδ, hδevent⟩ := Metric.eventually_nhds_iff.mp hevent
  let v : ℝ := min (t / 2) (δ / 2)
  have hv : 0 < v := lt_min (by positivity) (by positivity)
  have hvt : v < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvδ : dist v 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hv]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall := hδevent hvδ
  have hinc := deficit_secant_increments_tendsto hG hP hd hv hvt
  have hbound : Tendsto (fun n => err n + v * d n v) atTop (𝓝 (v * D v)) := by
    simpa using he.add ((hd v hv).const_mul v)
  filter_upwards [(Metric.tendsto_nhds.mp hinc) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hbound) (ε / 4) (by positivity), hzero v hv] with n hn hb hz
  rw [Real.dist_eq] at hn hb ⊢
  have hGv : |G n v| ≤ err n + v * d n v := by
    rw [abs_of_nonpos hz.2]
    linarith [hz.1]
  have hbound' : err n + v * d n v < |v * D v| + ε / 4 := by
    have hb' := (abs_lt.mp hb).2
    linarith [le_abs_self (v * D v)]
  have halg : G n t - P t =
      ((G n t - G n v) - (P t - P v)) + (G n v - P v) := by ring
  rw [halg]
  have htri := abs_add_le ((G n t - G n v) - (P t - P v)) (G n v - P v)
  have hsub := abs_sub (G n v) (P v)
  linarith

def limitPriceEnergy (q t : ℝ) : ℝ := -(4 / 7 : ℝ) * q * t ^ (7 / 4 : ℝ)

def limitDeficit (q t : ℝ) : ℝ := q * t ^ (3 / 4 : ℝ)

theorem hasDerivAt_limitPriceEnergy {q t : ℝ} (ht : 0 < t) :
    HasDerivAt (limitPriceEnergy q) (-limitDeficit q t) t := by
  have h : HasDerivAt (fun x : ℝ => -(4 / 7 : ℝ) * q * x ^ (7 / 4 : ℝ))
      (-(4 / 7 : ℝ) * q * ((7 / 4 : ℝ) * t ^ ((7 / 4 : ℝ) - 1))) t :=
    ((Real.hasStrictDerivAt_rpow_const_of_ne ht.ne' (7 / 4 : ℝ)).hasDerivAt).const_mul _
  have he : -(4 / 7 : ℝ) * q * ((7 / 4 : ℝ) * t ^ ((7 / 4 : ℝ) - 1)) =
      -limitDeficit q t := by
    norm_num [limitDeficit]
    ring
  rw [he] at h
  exact h

theorem deficitSecants_limitPriceEnergy {q : ℝ} (hq : 0 ≤ q) :
    DeficitSecants (limitPriceEnergy q) (limitDeficit q) := by
  have hconc : ConcaveOn ℝ (Set.Ici 0) (limitPriceEnergy q) := by
    have h := ((convexOn_rpow (p := (7 / 4 : ℝ)) (by norm_num)).smul
      (c := (4 / 7 : ℝ) * q) (by positivity)).neg
    have he : (-fun x : ℝ => ((4 / 7 : ℝ) * q) • x ^ (7 / 4 : ℝ)) =
        limitPriceEnergy q := by
      funext x
      simp only [Pi.neg_apply, smul_eq_mul, limitPriceEnergy]
      ring
    rw [he] at h
    exact h
  intro v t hv hvt
  have ht : 0 < t := hv.trans hvt
  have hL := hconc.le_slope_of_hasDerivAt hv.le ht.le hvt (hasDerivAt_limitPriceEnergy ht)
  have hU := hconc.slope_le_of_hasDerivAt hv.le ht.le hvt (hasDerivAt_limitPriceEnergy hv)
  rw [slope_def_field] at hL hU
  have hL' := (le_div_iff₀ (sub_pos.mpr hvt)).mp hL
  have hU' := (div_le_iff₀ (sub_pos.mpr hvt)).mp hU
  constructor <;> nlinarith

def limitSectorEnergy (q t : ℝ) : ℝ := (3 / 7 : ℝ) * q * t ^ (7 / 4 : ℝ)

theorem limitPriceEnergy_add {q t : ℝ} (ht : 0 < t) :
    limitPriceEnergy q t + t * limitDeficit q t = limitSectorEnergy q t := by
  have hp : t ^ (7 / 4 : ℝ) = t * t ^ (3 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num, Real.rpow_add ht, Real.rpow_one]
  simp only [limitPriceEnergy, limitDeficit, limitSectorEnergy, hp]
  ring

theorem continuous_limitPriceEnergy (q : ℝ) : Continuous (limitPriceEnergy q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem continuous_limitDeficit (q : ℝ) : Continuous (limitDeficit q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem continuous_limitSectorEnergy (q : ℝ) : Continuous (limitSectorEnergy q) :=
  continuous_const.mul (Real.continuous_rpow_const (by norm_num))

theorem limitDeficit_strictMonoOn {q : ℝ} (hq : 0 < q) :
    StrictMonoOn (limitDeficit q) (Set.Ioi 0) := by
  intro a ha b _ hab
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow ha.le hab (by norm_num)) hq

theorem limitDeficit_target {q : ℝ} (hq : 0 < q) :
    limitDeficit q (q ^ (-4 / 3 : ℝ)) = 1 := by
  rw [limitDeficit, ← Real.rpow_mul hq.le]
  norm_num
  simpa only [Real.rpow_neg_one] using mul_inv_cancel₀ hq.ne'

theorem limitSectorEnergy_target {q : ℝ} (hq : 0 < q) :
    limitSectorEnergy q (q ^ (-4 / 3 : ℝ)) = (3 / 7 : ℝ) * q ^ (-4 / 3 : ℝ) := by
  have hp : (q ^ (-4 / 3 : ℝ)) ^ (7 / 4 : ℝ) =
      q ^ (-4 / 3 : ℝ) * (q ^ (-4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
    rw [show (7 / 4 : ℝ) = 1 + 3 / 4 by norm_num,
      Real.rpow_add (Real.rpow_pos_of_pos hq _), Real.rpow_one]
  have hD := limitDeficit_target hq
  dsimp [limitDeficit] at hD
  dsimp [limitSectorEnergy]
  rw [hp]
  calc
    _ = (3 / 7 : ℝ) * (q * (q ^ (-4 / 3 : ℝ)) ^ (3 / 4 : ℝ)) * q ^ (-4 / 3 : ℝ) := by ring
    _ = _ := by rw [hD]; ring

theorem priced_energy_limits {G d : ℕ → ℝ → ℝ} {err : ℕ → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hG : ∀ n, DeficitSecants (G n) (d n))
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (limitDeficit q t)))
    (he : Tendsto err atTop (𝓝 0))
    (hzero : ∀ n v, 0 < v → -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => G n t) atTop (𝓝 (limitPriceEnergy q t)) ∧
    Tendsto (fun n => G n t + t * d n t) atTop (𝓝 (limitSectorEnergy q t)) := by
  have hprice := deficit_secant_energy_tendsto hG (deficitSecants_limitPriceEnergy hq)
    hd he (fun v hv => Eventually.of_forall fun n => hzero n v hv) (continuous_limitPriceEnergy q).continuousAt
    (by simp [limitPriceEnergy]) (continuous_limitDeficit q).continuousAt ht
  exact ⟨hprice, by simpa only [limitPriceEnergy_add ht] using hprice.add ((hd t ht).const_mul t)⟩

theorem tendsto_of_deficit_brackets {J d : ℕ → ℝ → ℝ} {F : ℕ → ℝ} {L D : ℝ → ℝ}
    {c : ℝ} (hc : 0 < c) (hD : StrictMonoOn D (Set.Ioi 0)) (hDc : D c = 1)
    (hL : ContinuousAt L c)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) atTop (𝓝 (D t)))
    (hJ : ∀ t : ℝ, 0 < t → Tendsto (fun n => J n t) atTop (𝓝 (L t)))
    (hbelow : ∀ n t, 0 < t → d n t < 1 → J n t ≤ F n)
    (habove : ∀ n t, 0 < t → 1 < d n t → F n ≤ J n t) :
    Tendsto F atTop (𝓝 (L c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδL⟩ := Metric.continuousAt_iff.mp hL (ε / 2) (by positivity)
  let η : ℝ := min (c / 2) (δ / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηc : η ≤ c / 2 := min_le_left _ _
  have hηδ : η < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hminus : 0 < c - η := by linarith
  have hplus : 0 < c + η := by linarith
  have hDm : D (c - η) < 1 := by rw [← hDc]; exact hD hminus hc (by linarith)
  have hDp : 1 < D (c + η) := by rw [← hDc]; exact hD hc hplus (by linarith)
  have hLm : |L (c - η) - L c| < ε / 2 := by
    apply (show dist (L (c - η)) (L c) < ε / 2 → _ from fun h => by simpa [Real.dist_eq] using h)
    apply hδL
    simpa [Real.dist_eq, abs_of_pos hη, abs_neg] using hηδ
  have hLp : |L (c + η) - L c| < ε / 2 := by
    apply (show dist (L (c + η)) (L c) < ε / 2 → _ from fun h => by simpa [Real.dist_eq] using h)
    apply hδL
    simpa [Real.dist_eq, abs_of_pos hη] using hηδ
  filter_upwards [(hd _ hminus).eventually (gt_mem_nhds hDm),
    (hd _ hplus).eventually (lt_mem_nhds hDp),
    (Metric.tendsto_nhds.mp (hJ _ hminus)) (ε / 2) (by positivity),
    (Metric.tendsto_nhds.mp (hJ _ hplus)) (ε / 2) (by positivity)] with n hdm hdp hjm hjp
  have hfm := hbelow n _ hminus hdm
  have hfp := habove n _ hplus hdp
  rw [Real.dist_eq] at hjm hjp ⊢
  obtain ⟨hlm, hum⟩ := abs_lt.mp hLm
  obtain ⟨hlp, hup⟩ := abs_lt.mp hLp
  obtain ⟨hjmL, hjmU⟩ := abs_lt.mp hjm
  obtain ⟨hjpL, hjpU⟩ := abs_lt.mp hjp
  apply abs_lt.mpr
  constructor <;> linarith

def PriceMinimizes (E : ℕ → ℝ) (lam : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, E n + lam * n ≤ E k + lam * k

def priceEnergy (E : ℕ → ℝ) (lam : ℝ) : ℝ := sInf (Set.range (fun n : ℕ => E n + lam * n))

theorem priceEnergy_eq_of_minimizes {E : ℕ → ℝ} {lam : ℝ} {n : ℕ}
    (hn : PriceMinimizes E lam n) : priceEnergy E lam = E n + lam * n := by
  have hb : BddBelow (Set.range (fun k : ℕ => E k + lam * k)) := by
    refine ⟨E n + lam * n, ?_⟩
    rintro e ⟨k, rfl⟩
    exact hn k
  apply le_antisymm
  · exact csInf_le hb ⟨n, rfl⟩
  · apply le_csInf (s := Set.range (fun k : ℕ => E k + lam * k)) ⟨_, n, rfl⟩
    rintro e ⟨k, rfl⟩
    exact hn k

theorem exists_priceMinimizes {E : ℕ → ℝ} (hE : BddBelow (Set.range E))
    {lam : ℝ} (hlam : 0 < lam) : ∃ n, PriceMinimizes E lam n := by
  obtain ⟨b, hb⟩ := hE
  obtain ⟨K, hK⟩ := exists_nat_gt ((E 0 - b) / lam)
  obtain ⟨n, hn, hmin⟩ := (Finset.range (K + 1)).exists_min_image
    (fun k : ℕ => E k + lam * k) (by simp)
  refine ⟨n, fun k => ?_⟩
  by_cases hk : k < K + 1
  · exact hmin k (Finset.mem_range.mpr hk)
  · have hk' : K ≤ k := by omega
    have hmin0 := hmin 0 (by simp)
    have hEb := hb ⟨k, rfl⟩
    have hK' := (div_lt_iff₀ hlam).mp hK
    have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk'
    have hmul := mul_le_mul_of_nonneg_left hcast hlam.le
    simp only [Nat.cast_zero, mul_zero, add_zero] at hmin0
    linarith

theorem priceMinimizes_antitone {E : ℕ → ℝ} {lam μ : ℝ} {n k : ℕ}
    (hn : PriceMinimizes E lam n) (hk : PriceMinimizes E μ k) (hlamμ : lam < μ) : k ≤ n := by
  have h₁ := hn k
  have h₂ := hk n
  have h : (k : ℝ) ≤ n := by nlinarith
  exact_mod_cast h

theorem priceMinimizes_strict_binding {E : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam)
    {n : ℕ} (hn : PriceMinimizes E lam n) (hn0 : 0 < n) : E n < E (n - 1) := by
  have h := hn (n - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one] at h
  linarith

theorem priceEnergy_secants {E : ℕ → ℝ} {lam μ : ℝ} {n k : ℕ}
    (hn : PriceMinimizes E lam n) (hk : PriceMinimizes E μ k) :
    (μ - lam) * k ≤ priceEnergy E μ - priceEnergy E lam ∧
    priceEnergy E μ - priceEnergy E lam ≤ (μ - lam) * n := by
  rw [priceEnergy_eq_of_minimizes hn, priceEnergy_eq_of_minimizes hk]
  have h₁ := hn k
  have h₂ := hk n
  constructor <;> nlinarith

theorem priceEnergy_neutral_bounds {E : ℕ → ℝ} {Z n : ℕ} {lam C : ℝ}
    (ho : ∀ k : ℕ, E Z - C ≤ E k) (hn : PriceMinimizes E lam n) :
    -C - lam * ((Z : ℝ) - n) ≤ priceEnergy E lam - lam * Z - E Z ∧
    priceEnergy E lam - lam * Z - E Z ≤ 0 := by
  rw [priceEnergy_eq_of_minimizes hn]
  have hz := hn Z
  have hl := ho n
  constructor <;> linarith

def scaledPrice (E : ℕ → ℝ) (Z : ℕ) (m t : ℝ) : ℝ :=
  (priceEnergy E (t * m ^ (4 / 3 : ℝ)) - t * m ^ (4 / 3 : ℝ) * Z - E Z) /
    m ^ (7 / 3 : ℝ)

def scaledDeficit (Z n : ℕ) (m : ℝ) : ℝ := ((Z : ℝ) - n) / m

theorem rpow_seven_thirds {m : ℝ} (hm : 0 < m) :
    m ^ (7 / 3 : ℝ) = m * m ^ (4 / 3 : ℝ) := by
  rw [show (7 / 3 : ℝ) = 1 + 4 / 3 by norm_num, Real.rpow_add hm, Real.rpow_one]

theorem scaledDeficit_mul {Z n : ℕ} {m : ℝ} (hm : 0 < m) :
    scaledDeficit Z n m * m ^ (7 / 3 : ℝ) = m ^ (4 / 3 : ℝ) * ((Z : ℝ) - n) := by
  rw [scaledDeficit, rpow_seven_thirds hm]
  field_simp

theorem scaledPrice_sector {E : ℕ → ℝ} {Z n : ℕ} {m t : ℝ} (hm : 0 < m)
    (hn : PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) n) :
    scaledPrice E Z m t + t * scaledDeficit Z n m =
      (E n - E Z) / m ^ (7 / 3 : ℝ) := by
  rw [scaledPrice, priceEnergy_eq_of_minimizes hn, scaledDeficit, rpow_seven_thirds hm]
  field_simp
  ring

theorem scaledPrice_secants {E : ℕ → ℝ} {Z : ℕ} {m : ℝ} (hm : 0 < m)
    {N : ℝ → ℕ} (hN : ∀ t, 0 < t → PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) (N t)) :
    DeficitSecants (scaledPrice E Z m) (fun t => scaledDeficit Z (N t) m) := by
  intro v t hv hvt
  have ht : 0 < t := hv.trans hvt
  have hs := priceEnergy_secants (hN v hv) (hN t ht)
  have hpos := Real.rpow_pos_of_pos hm (7 / 3 : ℝ)
  have heq : scaledPrice E Z m t - scaledPrice E Z m v =
      (priceEnergy E (t * m ^ (4 / 3 : ℝ)) - priceEnergy E (v * m ^ (4 / 3 : ℝ)) -
        (t - v) * m ^ (4 / 3 : ℝ) * Z) / m ^ (7 / 3 : ℝ) := by
    simp only [scaledPrice]
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    simp only [mul_assoc, scaledDeficit_mul hm]
    nlinarith [hs.1]
  · apply (div_le_iff₀ hpos).mpr
    simp only [mul_assoc, scaledDeficit_mul hm]
    nlinarith [hs.2]

theorem scaledPrice_zero_bounds {E : ℕ → ℝ} {Z n : ℕ} {m t C : ℝ} (hm : 0 < m)
    (ho : ∀ k : ℕ, E Z - C ≤ E k)
    (hn : PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) n) :
    -C / m ^ (7 / 3 : ℝ) - t * scaledDeficit Z n m ≤ scaledPrice E Z m t ∧
    scaledPrice E Z m t ≤ 0 := by
  have hs := priceEnergy_neutral_bounds ho hn
  have hpos := Real.rpow_pos_of_pos hm (7 / 3 : ℝ)
  constructor
  · apply (le_div_iff₀ hpos).mpr
    rw [sub_mul, div_mul_cancel₀ _ hpos.ne', mul_assoc, scaledDeficit_mul hm]
    nlinarith [hs.1]
  · exact (div_nonpos_iff).mpr (Or.inr ⟨hs.2, hpos.le⟩)

theorem scaledPrice_nonpos {E : ℕ → ℝ} {Z n : ℕ} {m t : ℝ} (hm : 0 < m)
    (hn : PriceMinimizes E (t * m ^ (4 / 3 : ℝ)) n) : scaledPrice E Z m t ≤ 0 := by
  rw [scaledPrice, priceEnergy_eq_of_minimizes hn]
  apply div_nonpos_of_nonpos_of_nonneg _ (Real.rpow_nonneg hm.le _)
  have hz := hn Z
  linarith

theorem scaledPrice_limits {E : ℕ → ℕ → ℝ} {Z : ℕ → ℕ} {m : ℕ → ℝ}
    {N : ℕ → ℝ → ℕ} {q : ℝ} (hq : 0 < q) (hm : ∀ j, 0 < m j)
    (hmono : ∀ j, Antitone (E j))
    (hN : ∀ j t, 0 < t → PriceMinimizes (E j) (t * m j ^ (4 / 3 : ℝ)) (N j t))
    (hd : ∀ t, 0 < t → Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit q t)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j => scaledPrice (E j) (Z j) (m j) t) atTop (𝓝 (limitPriceEnergy q t)) ∧
    Tendsto (fun j => (E j (N j t) - E j (Z j)) / m j ^ (7 / 3 : ℝ))
      atTop (𝓝 (limitSectorEnergy q t)) := by
  have hz : ∀ v, 0 < v → ∀ᶠ j in atTop,
      -(0 : ℝ) - v * scaledDeficit (Z j) (N j v) (m j) ≤ scaledPrice (E j) (Z j) (m j) v ∧
      scaledPrice (E j) (Z j) (m j) v ≤ 0 := by
    intro v hv
    have hD : 0 < limitDeficit q v := mul_pos hq (Real.rpow_pos_of_pos hv _)
    filter_upwards [(hd v hv).eventually (lt_mem_nhds hD)] with j hj
    have hdiff : 0 < (Z j : ℝ) - N j v := by
      simpa using (lt_div_iff₀ (hm j)).mp hj
    have hnZ : N j v ≤ Z j := by exact_mod_cast (show (N j v : ℝ) ≤ Z j by linarith)
    have hle := hmono j hnZ
    have henergy : 0 ≤ (E j (N j v) - E j (Z j)) / m j ^ (7 / 3 : ℝ) :=
      div_nonneg (sub_nonneg.mpr hle) (Real.rpow_nonneg (hm j).le _)
    rw [← scaledPrice_sector (hm j) (hN j v hv)] at henergy
    exact ⟨by linarith, scaledPrice_nonpos (hm j) (hN j v hv)⟩
  have hp := deficit_secant_energy_tendsto
    (fun j => scaledPrice_secants (hm j) (hN j)) (deficitSecants_limitPriceEnergy hq.le)
    hd tendsto_const_nhds hz (continuous_limitPriceEnergy q).continuousAt
    (by simp [limitPriceEnergy]) (continuous_limitDeficit q).continuousAt ht
  refine ⟨hp, ?_⟩
  have h := hp.add ((hd t ht).const_mul t)
  simpa only [scaledPrice_sector (hm _) (hN _ t ht), limitPriceEnergy_add ht] using h

theorem fixed_sector_limit_of_priced_deficit {E : ℕ → ℕ → ℝ} {Z m : ℕ → ℕ}
    {N : ℕ → ℝ → ℕ} {q : ℝ} (hq : 0 < q)
    (hm : ∀ j, 1 ≤ m j ∧ m j ≤ Z j) (hmono : ∀ j, Antitone (E j))
    (hN : ∀ j t, 0 < t → PriceMinimizes (E j) (t * (m j : ℝ) ^ (4 / 3 : ℝ)) (N j t))
    (hd : ∀ t, 0 < t → Tendsto (fun j => scaledDeficit (Z j) (N j t) (m j))
      atTop (𝓝 (limitDeficit q t))) :
    Tendsto (fun j => (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 ((3 / 7 : ℝ) * q ^ (-4 / 3 : ℝ))) := by
  have hmp : ∀ j, (0 : ℝ) < m j := fun j => by exact_mod_cast (show 0 < m j by have := (hm j).1; omega)
  have hJ : ∀ t, 0 < t → Tendsto
      (fun j => (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ))
      atTop (𝓝 (limitSectorEnergy q t)) := fun t ht => (scaledPrice_limits hq hmp hmono hN hd ht).2
  have hlo : ∀ j t, 0 < t → scaledDeficit (Z j) (N j t) (m j) < 1 →
      (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) ≤
      (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) := by
    intro j t _ hdj
    have hn : Z j - m j ≤ N j t := by
      have hh : (Z j : ℝ) - N j t < m j := (div_lt_one (hmp j)).mp hdj
      have hh' : (Z j - m j : ℕ) ≤ N j t := by
        apply (Nat.cast_le (α := ℝ)).mp
        rw [Nat.cast_sub (hm j).2]
        linarith
      exact hh'
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hmono j hn) _) (Real.rpow_nonneg (hmp j).le _)
  have hup : ∀ j t, 0 < t → 1 < scaledDeficit (Z j) (N j t) (m j) →
      (E j (Z j - m j) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) ≤
      (E j (N j t) - E j (Z j)) / (m j : ℝ) ^ (7 / 3 : ℝ) := by
    intro j t _ hdj
    have hn : N j t ≤ Z j - m j := by
      have hh : (m j : ℝ) < (Z j : ℝ) - N j t := (one_lt_div (hmp j)).mp hdj
      apply (Nat.cast_le (α := ℝ)).mp
      rw [Nat.cast_sub (hm j).2]
      linarith
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hmono j hn) _) (Real.rpow_nonneg (hmp j).le _)
  have h := tendsto_of_deficit_brackets (Real.rpow_pos_of_pos hq (-4 / 3 : ℝ))
    (limitDeficit_strictMonoOn hq) (limitDeficit_target hq)
    (continuous_limitSectorEnergy q).continuousAt hd hJ hlo hup
  simpa only [limitSectorEnergy_target hq] using h

theorem energy_uniform_lower_bound {Z : ℝ} (hZ : 0 ≤ Z) (N : ℕ) :
    -2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ) ≤ energy Z N := by
  by_cases hN : N = 0
  · simp only [energy, hN, ↓reduceIte]
    have : 0 ≤ 2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ) := by positivity
    linarith
  · rw [energy, ite_eq_right hN]
    apply le_csInf (formValues_nonempty Z N)
    rintro e ⟨ψ, hψ, rfl⟩
    exact formEnergy_uniform_lower_bound hZ (Nat.le_ceil (2 * Z)) hψ

theorem energy_range_bddBelow {Z : ℝ} (hZ : 0 ≤ Z) :
    BddBelow (Set.range (energy Z)) := by
  refine ⟨-2 * Z ^ 2 * (⌈2 * Z⌉₊ : ℝ), ?_⟩
  rintro e ⟨N, rfl⟩
  exact energy_uniform_lower_bound hZ N

theorem quantum_exists_priceMinimizes {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∃ n, PriceMinimizes (energy Z) lam n :=
  exists_priceMinimizes (energy_range_bddBelow hZ) hlam

end CoulombAtom

end

end OAI
