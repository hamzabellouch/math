import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierStepWeakBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierNuclearScale_barrier_scope

open Filter
open scoped Topology

namespace CoulombAtom
open CoulombObservation

lemma nuclear_radius_relation {Z ε : ℝ} (hZ : 0 < Z) :
    Z*(ε*Z^(-1/3:ℝ))^3 = ε^3 := by
  rw [mul_pow,←Real.rpow_natCast (Z^(-1/3:ℝ)) 3,←Real.rpow_mul hZ.le]
  norm_num [Real.rpow_neg_one]
  field_simp

lemma nuclear_energy_relation {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε)
    (hrel : Z*r^3 = ε^3) : Z^(7/3:ℝ)*r^7 = ε^7 := by
  have hh := congrArg (fun t : ℝ => t^(7/3:ℝ)) hrel
  rw [Real.mul_rpow hZ.le (pow_nonneg hr.le 3),←Real.rpow_natCast,
    ←Real.rpow_mul hr.le,←Real.rpow_natCast,←Real.rpow_mul hε.le] at hh
  norm_num at hh
  exact hh

lemma initial_event_ratio {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r) (hε : 0 < ε)
    (hrel : Z*r^3 = ε^3) :
    (r^(-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)/Z^(7/3:ℝ) =
      (r^(7-2.02:ℝ)*(Real.log (Real.exp 1/r^40))^5)/ε^7 := by
  have hE := nuclear_energy_relation hZ hr hε hrel
  have he : r^(7-2.02:ℝ) = r^(-2.02:ℝ)*r^7 := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr]; congr 1; norm_num
  rw [he,←hE]
  field_simp

lemma initial_event_ratio_vanishes {ι : Type*} {l : Filter ι} {Z r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hr : ∀ᶠ i in l, 0 < r i)
    (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3) (hr0 : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => ((r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/(r i)^40))^5)/(Z i)^(7/3:ℝ)) l (𝓝 0) := by
  have ht : Tendsto r l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hr0,hr⟩
  have hh := (initial_event_cost_small.comp ht).div_const (ε^7)
  simp only [zero_div] at hh
  exact hh.congr' (by filter_upwards [hZ,hr,hrel] with i hZi hri hli; exact (initial_event_ratio hZi hri hε hli).symm)

lemma nuclear_inverse_energy_vanishes {ι : Type*} {l : Filter ι} {Z r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hr : ∀ᶠ i in l, 0 < r i)
    (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3) (hr0 : Tendsto r l (𝓝 0)) :
    Tendsto (fun i => (Z i)^(-(7/3):ℝ)) l (𝓝 0) := by
  have hh := (hr0.pow 7).div_const (ε^7)
  simp only [zero_pow (by norm_num : (7:ℕ) ≠ 0),zero_div] at hh
  apply hh.congr'
  filter_upwards [hZ,hr,hrel] with i hZi hri hli
  rw [Real.rpow_neg hZi.le,←nuclear_energy_relation hZi hri hε hli]
  field_simp

theorem initial_budget_eventually {ι : Type*} {l : Filter ι} {Z s r : ι → ℝ}
    {ε : ℝ} (hε : 0 < ε) (hZ : ∀ᶠ i in l, 0 < Z i) (hs : ∀ᶠ i in l, 0 < s i)
    (hr : ∀ᶠ i in l, 0 < r i) (hrel : ∀ᶠ i in l, Z i*(r i)^3 = ε^3)
    (hr0 : Tendsto r l (𝓝 0)) (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop)
    (δ : ℝ) :
    ∀ᶠ i in l, 3*Z i*(s i)^(-4:ℝ)+observationFisherConstant*(r i)^(-2.02:ℝ)*
      (Real.log (Real.exp 1/(r i)^40))^5+δ ≤ (Z i)^(7/3:ℝ) := by
  have h1 := coarse_offset_nuclear_vanishes hZ hs hscale
  have h2 := (initial_event_ratio_vanishes hε hZ hr hrel hr0).const_mul observationFisherConstant
  have h3 := (nuclear_inverse_energy_vanishes hε hZ hr hrel hr0).const_mul δ
  have ht := (h1.add h2).add h3
  simp only [mul_zero,add_zero] at ht
  have he := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [he,hZ] with i hi hZi
  have hden : 0 < (Z i)^(7/3:ℝ) := Real.rpow_pos_of_pos hZi _
  apply le_of_lt
  apply (div_lt_one hden).mp
  change (3*Z i*(s i)^(-4:ℝ))/(Z i)^(7/3:ℝ)+
    observationFisherConstant*((r i)^(-2.02:ℝ)*(Real.log (Real.exp 1/(r i)^40))^5/(Z i)^(7/3:ℝ))+
    δ*(Z i)^(-(7/3):ℝ) < 1 at hi
  rw [Real.rpow_neg hZi.le] at hi
  convert hi using 1
  first | rfl | ring

lemma nuclear_radius_tendsto {ι : Type*} {l : Filter ι} {Z s : ι → ℝ}
    (hs0 : Tendsto s l (𝓝 0)) (hs : ∀ᶠ i in l, 0 < s i)
    (hscale : Tendsto (fun i => Z i*(s i)^3) l atTop) (ε : ℝ) :
    Tendsto (fun i => ε*(Z i)^(-1/3:ℝ)) l (𝓝 0) := by
  have hb : ∀ᶠ i in l, s i < 1 := hs0.eventually (Iio_mem_nhds (by norm_num))
  have hz : ∀ᶠ i in l, 0 < Z i := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0),hs] with i hi hsi
    exact (mul_pos_iff_of_pos_right (pow_pos hsi 3)).mp hi
  have hZtop : Tendsto Z l atTop := tendsto_atTop_mono' l (by
    filter_upwards [hb,hz,hs] with i hbi hzi hsi
    have hp : (s i)^3 ≤ 1 := pow_le_one₀ hsi.le hbi.le
    nlinarith) hscale
  simpa only [mul_zero,neg_div,Function.comp_def] using
    ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hZtop).const_mul ε

end CoulombAtom

end Work_BarrierNuclearScale_barrier_scope

open Filter Set
open scoped Topology

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

def initialQuadraticConstant (k : ℝ) : ℝ := 1+(4*Real.pi*k*2^(3/2:ℝ))/6

def initialQuadratic (C Z r : ℝ) : ℝ := C*(Z/r)^(3/2:ℝ)

lemma initialQuadraticConstant_pos {k : ℝ} (hk : 0 ≤ k) : 0 < initialQuadraticConstant k := by
  unfold initialQuadraticConstant
  positivity

lemma initialQuadratic_reaction {k Z r : ℝ} (hZ : 0 < Z) (hr : 0 < r) :
    reaction k (2*(Z/r)) ≤ 6*initialQuadratic (initialQuadraticConstant k) Z r := by
  have hp : 0 ≤ Z/r := (div_pos hZ hr).le
  rw [reaction, max_eq_left (by positivity : 0 ≤ 2*(Z/r)),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hp]
  unfold initialQuadratic initialQuadraticConstant
  have hq := Real.rpow_nonneg hp (3/2:ℝ)
  nlinarith

lemma initialQuadratic_scale {Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hε : 0 < ε) (hrel : Z*r^3 = ε^3) :
    (Z/r)^(3/2:ℝ)*r^3 = Z*ε^(3/2:ℝ) := by
  have he : ε^(3/2:ℝ) = Z^(1/2:ℝ)*r^(3/2:ℝ) := by
    calc
      _ = (ε^3)^(1/2:ℝ) := by rw [←Real.rpow_natCast,←Real.rpow_mul hε.le]; norm_num
      _ = (Z*r^3)^(1/2:ℝ) := by rw [hrel]
      _ = _ := by rw [Real.mul_rpow hZ.le (pow_nonneg hr.le 3),←Real.rpow_natCast,
        ←Real.rpow_mul hr.le]; norm_num
  rw [he,Real.div_rpow hZ.le hr.le]
  have hZp : Z^(3/2:ℝ) = Z*Z^(1/2:ℝ) := by
    calc
      _ = Z^((1:ℝ)+(1/2:ℝ)) := by norm_num
      _ = Z^(1:ℝ)*Z^(1/2:ℝ) := Real.rpow_add hZ 1 (1/2)
      _ = _ := by rw [Real.rpow_one]
  have hrp : r^3 = r^(3/2:ℝ)*r^(3/2:ℝ) := by
    rw [←Real.rpow_add hr]; norm_num
  rw [hZp,hrp]
  field_simp

lemma initialQuadratic_small {C Z r ε : ℝ} (hZ : 0 < Z) (hr : 0 < r)
    (hε : 0 < ε) (hrel : Z*r^3 = ε^3) (hsmall : 4*C*ε^(3/2:ℝ) ≤ 1/20) :
    4*initialQuadratic C Z r*r^2 ≤ Z/(20*r) := by
  apply (le_div_iff₀ (by positivity : 0 < 20*r)).mpr
  have hi := initialQuadratic_scale hZ hr hε hrel
  unfold initialQuadratic
  calc
    _ = (4*C*((Z/r)^(3/2:ℝ)*r^3))*20 := by ring
    _ = Z*(4*C*ε^(3/2:ℝ))*20 := by rw [hi]; ring
    _ ≤ Z*(1/20)*20 := by gcongr
    _ = Z := by ring

lemma exists_barrier_epsilon (k : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
    initialDensityConstant*ε^(6/5:ℝ) < 1/20 ∧
    4*initialQuadraticConstant k*ε^(3/2:ℝ) ≤ 1/20 := by
  have ht (a : ℝ) (ha : 0 < a) (C : ℝ) :
      Tendsto (fun ε : ℝ => C*ε^a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow ha.ne',mul_zero] using ((Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto.const_mul C).mono_left
      (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have h1 := (ht (6/5) (by norm_num) initialDensityConstant).eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))
  have h2 := (ht (3/2) (by norm_num) (4*initialQuadraticConstant k)).eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 0, ε < 1 from Iio_mem_nhds (by norm_num)).filter_mono inf_le_left
  have h4 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hε1,hi,hq⟩ := (h4.and (h3.and (h1.and h2))).exists
  exact ⟨ε,hε,hε1,hi,hq.le⟩

lemma exists_barrier_B {ε k : ℝ} (hε : 0 < ε) : ∃ B : ℝ,
    0 < B ∧ B ≤ ε^3/10 ∧ 4*Real.pi*k*Real.sqrt B ≤ 19/2 := by
  have ht : Tendsto (fun B : ℝ => 4*Real.pi*k*Real.sqrt B) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).const_mul (4*Real.pi*k)).mono_left
      (show (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ) from inf_le_left)
  have h1 := ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 19/2))
  have h2 : ∀ᶠ B : ℝ in 𝓝[>] 0, B < ε^3/10 :=
    (show ∀ᶠ B : ℝ in 𝓝 0, B < ε^3/10 from Iio_mem_nhds (by positivity)).filter_mono inf_le_left
  have h3 : ∀ᶠ B : ℝ in 𝓝[>] 0, 0 < B := self_mem_nhdsWithin
  obtain ⟨B,hB,hBs,hBk⟩ := (h3.and (h2.and h1)).exists
  exact ⟨B,hB,hBs.le,hBk.le⟩

lemma initial_interpolation_eventually {ι : Type*} {l : Filter ι} {r : ι → ℝ}
    (hr : Tendsto r l (𝓝 0)) (C : ℝ) : ∀ᶠ i in l,
    C*(r i)^(1-3*masterExponent) ≤ 1/20 := by
  have hp : 0 < 1-3*masterExponent := by
    norm_num [masterExponent]
  have ht := ((Real.continuousAt_rpow_const 0 _ (Or.inr hp.le)).tendsto.comp hr).const_mul C
  simp only [Real.zero_rpow hp.ne',mul_zero] at ht
  exact (ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/20))).mono fun _ h => h.le

end CoulombBarrier

end

end OAI
