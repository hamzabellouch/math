import Mathlib
import OAI.Probability.ThreeState.Observation

namespace OAI

/-! Boundary score moments and reconstruction above the Kesten–Stigum threshold. -/

namespace ThreeState

noncomputable def listScore {α : Type*} (f : α → ℝ) (as : List α) : ℝ := (as.map f).sum
noncomputable def multisetScore {α : Type*} (f : α → ℝ) (as : Multiset α) : ℝ := (as.map f).sum

lemma listScore_cons {α : Type*} (f : α → ℝ) (a : α) (as : List α) :
    listScore f (a::as) = f a+listScore f as := by simp [listScore]

lemma multisetScore_coe {α : Type*} (f : α → ℝ) (as : List α) :
    multisetScore f (as : Multiset α) = listScore f as := by
  simp [multisetScore, listScore]

lemma iidList_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (n : ℕ) :
    Moments (iidList p n) (listScore f)
      ((n:ℝ)*m) ((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2) := by
  induction n with
  | zero => simpa [iidList, listScore] using Moments.pure ([] : List α) (listScore f)
  | succ n ih =>
    have hi := Moments.independent_add h ih
    have hm := Moments.map (g := fun ab : α × List α => ab.1::ab.2) (f := listScore f) hi
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hm
    change Moments (iidList p (n+1)) (listScore f)
      (m+(n:ℝ)*m) (s+2*m*((n:ℝ)*m)+((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2)) at hm
    convert hm using 1 <;> push_cast <;> ring

lemma iidMultiset_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s : ℝ}
    (h : Moments p f m s) (n : ℕ) :
    Moments ((iidList p n).map (fun as : List α => (as : Multiset α))) (multisetScore f)
      ((n:ℝ)*m) ((n:ℝ)*s+(n:ℝ)*((n:ℝ)-1)*m^2) := by
  apply Moments.map (g := fun as : List α => (as : Multiset α))
  simpa only [multisetScore_coe] using iidList_moments h n

 

lemma compound_moments {α : Type*} {p : PMF α} {f : α → ℝ} {m s d e : ℝ}
    {offspring : PMF ℕ} (hp : Moments p f m s)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) :
    Moments (offspring.bind (fun k =>
      (iidList p k).map (fun as : List α => (as : Multiset α)))) (multisetScore f)
      (d*m) (d*s+e*m^2) := by
  apply Moments.bind (fun k => iidMultiset_moments hp k)
  · exact ((hD.hasMean.mul_const s).add ((hD.square.sub hD.hasMean).mul_const (m^2))).congr
      (fun k => by ring)
  · rw [mean_mul_const, hD.first]
  · rw [mean_congr offspring (g := fun k => (k:ℝ)*s+((k:ℝ)^2-(k:ℝ))*m^2) (fun k => by ring),
      mean_add (hD.hasMean.mul_const s) ((hD.square.sub hD.hasMean).mul_const (m^2)),
      mean_mul_const, mean_mul_const, mean_sub hD.square hD.hasMean, hD.first, hD.second]
    ring

 

def spinScore (i : Spin) : ℝ := if i=0 then 2 else -1

noncomputable def boundaryScore : (n : ℕ) → Observation n → ℝ
  | 0 => spinScore
  | n+1 => multisetScore (boundaryScore n)

lemma mass_channel (lam : ℝ) (h : Admissible lam) (i j : Spin) :
    mass (channelPMF lam h i) j = channel lam i j := by
  exact ENNReal.toReal_ofReal (channel_nonneg h i j)

lemma channel_score (lam : ℝ) (h : Admissible lam) (i : Spin) :
    mean (channelPMF lam h i) spinScore = lam*spinScore i := by
  rw [mean_fintype]
  simp only [mass_channel]
  fin_cases i <;> simp [Fin.sum_univ_succ, channel, spinScore] <;> ring

noncomputable def scoreSecond (d e lam : ℝ) (h : Admissible lam) : ℕ → Spin → ℝ
  | 0, i => (spinScore i)^2
  | n+1, i => d*mean (channelPMF lam h i) (scoreSecond d e lam h n) +
      e*((d*lam)^n*lam*spinScore i)^2

 
theorem boundaryScore_moments (offspring : PMF ℕ) (d e lam : ℝ) (h : Admissible lam)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) (n : ℕ) (i : Spin) :
    Moments (observedLaw offspring lam h n i) (boundaryScore n)
      ((d*lam)^n*spinScore i) (scoreSecond d e lam h n i) := by
  induction n generalizing i with
  | zero =>
    change Moments (PMF.pure i) spinScore ((d*lam)^0*spinScore i) ((spinScore i)^2)
    simpa only [pow_zero, one_mul] using Moments.pure i spinScore
  | succ n ih =>
    have hedge : Moments ((channelPMF lam h i).bind (observedLaw offspring lam h n))
        (boundaryScore n) ((d*lam)^n*lam*spinScore i)
        (mean (channelPMF lam h i) (scoreSecond d e lam h n)) := by
      apply Moments.bind ih (hasMean_fintype _ _) ?_ rfl
      rw [mean_const_mul, channel_score]
      ring
    have hh := compound_moments hedge hD
    change Moments (observedLaw offspring lam h (n+1) i) (boundaryScore (n+1))
      (d*((d*lam)^n*lam*spinScore i)) (scoreSecond d e lam h (n+1) i) at hh
    convert hh using 1
    rw [pow_succ]
    ring

lemma hasMean_marginal {α : Type*} {law : Spin → PMF α} {f : α → ℝ}
    (h : ∀ i, HasMean (law i) f) : HasMean (marginal law) f :=
  HasMean.bind h (hasMean_fintype _ _)

lemma mean_uniform (f : Spin → ℝ) : mean uniformSpin f = (∑ i : Spin, f i)/3 := by
  rw [mean_fintype]
  simp only [mass_uniform, ← Finset.mul_sum]
  ring

lemma mean_marginal {α : Type*} {law : Spin → PMF α} {f : α → ℝ}
    (h : ∀ i, HasMean (law i) f) :
    mean (marginal law) f = mean uniformSpin (fun i => mean (law i) f) :=
  mean_bind h (hasMean_fintype _ _)

lemma mean_uniform_spinScore : mean uniformSpin spinScore = 0 := by
  simp [mean_uniform, Fin.sum_univ_succ, spinScore]

lemma mean_uniform_spinScore_square : mean uniformSpin (fun i => (spinScore i)^2) = 2 := by
  norm_num [mean_uniform, Fin.sum_univ_succ, spinScore]

lemma mean_uniform_channel (lam : ℝ) (h : Admissible lam) (f : Spin → ℝ) :
    mean uniformSpin (fun i => mean (channelPMF lam h i) f) = mean uniformSpin f := by
  simp [mean_fintype, mass_uniform, mass_channel, Fin.sum_univ_succ, channel]
  ring

lemma pow_square_comm (a : ℝ) (n : ℕ) : (a^n)^2 = (a^2)^n := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]

lemma scoreSecond_average_zero (d e lam : ℝ) (h : Admissible lam) :
    mean uniformSpin (scoreSecond d e lam h 0) = 2 := mean_uniform_spinScore_square

lemma scoreSecond_average_succ (d e lam : ℝ) (h : Admissible lam) (n : ℕ) :
    mean uniformSpin (scoreSecond d e lam h (n+1)) =
      d*mean uniformSpin (scoreSecond d e lam h n)+2*e*lam^2*((d*lam)^2)^n := by
  change mean uniformSpin (fun i =>
    d*mean (channelPMF lam h i) (scoreSecond d e lam h n) +
      e*((d*lam)^n*lam*spinScore i)^2) = _
  rw [mean_add (hasMean_fintype _ _) (hasMean_fintype _ _), mean_const_mul,
    mean_uniform_channel]
  congr 1
  rw [mean_congr uniformSpin (g := fun i => (e*lam^2*((d*lam)^2)^n)*(spinScore i)^2)
    (fun i => by rw [mul_pow, mul_pow, pow_square_comm]; ring), mean_const_mul,
    mean_uniform_spinScore_square]
  ring

 

lemma scoreSecond_bound (d e lam C : ℝ) (h : Admissible lam)
    (hd : 0 ≤ d) (hC : 2 ≤ C) (hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2) (n : ℕ) :
    mean uniformSpin (scoreSecond d e lam h n) ≤ C*((d*lam)^2)^n := by
  induction n with
  | zero => simpa only [scoreSecond_average_zero, pow_zero, mul_one] using hC
  | succ n ih =>
    rw [scoreSecond_average_succ, pow_succ ((d*lam)^2) n]
    have h1 := mul_le_mul_of_nonneg_left ih hd
    have h2 := mul_le_mul_of_nonneg_right hstep (pow_nonneg (sq_nonneg (d*lam)) n)
    nlinarith

lemma boundaryScore_marginal_moments (offspring : PMF ℕ) (d e lam : ℝ) (h : Admissible lam)
    (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d)) (n : ℕ) :
    Moments (marginal (observedLaw offspring lam h n)) (boundaryScore n) 0
      (mean uniformSpin (scoreSecond d e lam h n)) := by
  apply Moments.bind (fun i => boundaryScore_moments offspring d e lam h hD n i)
    (hasMean_fintype _ _) ?_ rfl
  rw [mean_const_mul, mean_uniform_spinScore, mul_zero]

end ThreeState

namespace ThreeState

lemma HasMean.mul_of_square {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (hg : HasMean p (fun a => (g a)^2)) :
    HasMean p (fun a => f a*g a) := by
  apply HasMean.of_abs
  apply ((hf.add hg).mul_const (1/2)).mono (fun a => abs_nonneg _)
  intro a
  rw [abs_mul]
  nlinarith [sq_nonneg (|f a|-|g a|), sq_abs (f a), sq_abs (g a)]

 
lemma mean_cauchy_square {α : Type*} {p : PMF α} {f g : α → ℝ}
    (hf : HasMean p (fun a => (f a)^2)) (hg : HasMean p (fun a => (g a)^2)) :
    (mean p (fun a => f a*g a))^2 ≤
      mean p (fun a => (f a)^2)*mean p (fun a => (g a)^2) := by
  have hfg := hf.mul_of_square hg
  have hp (t : ℝ) : 0 ≤ mean p (fun a => (g a)^2)*(t*t) +
      (-2*mean p (fun a => f a*g a))*t + mean p (fun a => (f a)^2) := by
    have hn := mean_nonneg p (fun a => sq_nonneg (f a-t*g a))
    have he : mean p (fun a => (f a-t*g a)^2) =
        mean p (fun a => (g a)^2)*(t*t) +
        (-2*mean p (fun a => f a*g a))*t + mean p (fun a => (f a)^2) := by
      rw [mean_congr p (g := fun a => (g a)^2*(t*t)+(f a*g a)*(-2*t)+(f a)^2)
        (fun a => by ring),
        mean_add ((hg.mul_const (t*t)).add (hfg.mul_const (-2*t))) hf,
        mean_add (hg.mul_const (t*t)) (hfg.mul_const (-2*t)), mean_mul_const, mean_mul_const]
      ring
    rwa [he] at hn
  have hd := discrim_le_zero hp
  dsimp [discrim] at hd
  nlinarith

lemma posterior_le_one {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    posterior law y i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => posterior_nonneg law y j)
    (Finset.mem_univ i)
  simpa only [posterior_sum] using h

noncomputable def posteriorTV {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  (∑ i : Spin, |posterior law y i-1/3|)/2

lemma posteriorTV_nonneg {α : Type*} (law : Spin → PMF α) (y : α) :
    0 ≤ posteriorTV law y := by
  exact div_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by norm_num)

lemma posteriorTV_le_two {α : Type*} (law : Spin → PMF α) (y : α) :
    posteriorTV law y ≤ 2 := by
  have hh (i : Spin) : |posterior law y i-1/3| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [posterior_nonneg law y i, posterior_le_one law y i]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  norm_num at h
  dsimp [posteriorTV]
  linarith

lemma hasMean_posteriorTV {α : Type*} (law : Spin → PMF α) :
    HasMean (marginal law) (posteriorTV law) :=
  (hasMean_const (marginal law) 2).mono (posteriorTV_nonneg law) (posteriorTV_le_two law)

lemma mean_posteriorTV {α : Type*} (law : Spin → PMF α) :
    mean (marginal law) (posteriorTV law) = advantage law := rfl

noncomputable def posteriorScore {α : Type*} (law : Spin → PMF α) (y : α) : ℝ :=
  3*posterior law y 0-1

lemma posteriorScore_square_le {α : Type*} (law : Spin → PMF α) (y : α) :
    (posteriorScore law y)^2 ≤ 12*posteriorTV law y := by
  have hn := posterior_nonneg law y 0
  have hu := posterior_le_one law y 0
  have hr : |posteriorScore law y| ≤ 2 := by
    rw [abs_le]
    dsimp [posteriorScore]
    constructor <;> linarith
  have he : |posteriorScore law y| = 3*|posterior law y 0-1/3| := by
    rw [show posteriorScore law y = 3*(posterior law y 0-1/3) by dsimp [posteriorScore]; ring, abs_mul]
    norm_num
  have h0 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => abs_nonneg (posterior law y i-1/3))
    (Finset.mem_univ (0:Spin))
  dsimp [posteriorTV]
  nlinarith [sq_abs (posteriorScore law y),
    mul_nonneg (abs_nonneg (posteriorScore law y)) (sub_nonneg.mpr hr)]

lemma hasMean_posteriorScore_square {α : Type*} (law : Spin → PMF α) :
    HasMean (marginal law) (fun y => (posteriorScore law y)^2) :=
  ((hasMean_posteriorTV law).const_mul 12).mono
    (fun y => sq_nonneg (posteriorScore law y)) (posteriorScore_square_le law)

lemma mean_posteriorScore_square_le {α : Type*} (law : Spin → PMF α) :
    mean (marginal law) (fun y => (posteriorScore law y)^2) ≤ 12*advantage law := by
  have h := mean_le (hasMean_posteriorScore_square law) ((hasMean_posteriorTV law).const_mul 12)
    (posteriorScore_square_le law)
  simpa only [mean_const_mul, mean_posteriorTV] using h

lemma weighted_posteriorScore {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y*posteriorScore law y = mass (law 0) y-mass (marginal law) y := by
  have h := weighted_posterior law y 0
  dsimp [posteriorScore]
  linarith

lemma mean_score_correlation {α : Type*} (law : Spin → PMF α) (f : α → ℝ)
    (h0 : HasMean (law 0) f) (hm : HasMean (marginal law) f) :
    mean (marginal law) (fun y => posteriorScore law y*f y) = mean (law 0) f-mean (marginal law) f := by
  unfold mean
  rw [← h0.tsum_sub hm]
  apply tsum_congr
  intro y
  rw [← mul_assoc, weighted_posteriorScore]
  ring

 

theorem advantage_lower_from_score {α : Type*} (law : Spin → PMF α) (f : α → ℝ)
    (h0 : HasMean (law 0) f) (hf : HasMean (marginal law) (fun y => (f y)^2)) :
    (mean (law 0) f-mean (marginal law) f)^2 ≤
      12*advantage law*mean (marginal law) (fun y => (f y)^2) := by
  have h := mean_cauchy_square (hasMean_posteriorScore_square law) hf
  rw [mean_score_correlation law f h0 (hasMean_of_square hf)] at h
  exact h.trans (mul_le_mul_of_nonneg_right (mean_posteriorScore_square_le law)
    (mean_nonneg _ (fun y => sq_nonneg _)))

end ThreeState

namespace ThreeState

 

lemma supercritical_advantage_bound (offspring : PMF ℕ) (d e lam C : ℝ)
    (h : Admissible lam) (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d))
    (hd : 0 ≤ d) (hq : 0 < (d*lam)^2) (hC : 2 ≤ C)
    (hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2) (n : ℕ) :
    1/(3*C) ≤ advantage (observedLaw offspring lam h n) := by
  have hm := boundaryScore_marginal_moments offspring d e lam h hD n
  have h0 := boundaryScore_moments offspring d e lam h hD n (0:Spin)
  have hc := advantage_lower_from_score (observedLaw offspring lam h n) (boundaryScore n)
    h0.hasMean hm.square
  rw [h0.first, hm.first, hm.second] at hc
  have hs := scoreSecond_bound d e lam C h hd hC hstep n
  have ha := advantage_nonneg (observedLaw offspring lam h n)
  have hp := pow_pos hq n
  have hu := mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) ha)
  have he : (((d*lam)^n*spinScore (0:Spin))-0)^2 = 4*((d*lam)^2)^n := by
    simp only [spinScore, ↓reduceIte, sub_zero, mul_pow, pow_square_comm]
    ring
  rw [he] at hc
  have hh : (4:ℝ)*((d*lam)^2)^n ≤
      (12*C*advantage (observedLaw offspring lam h n))*((d*lam)^2)^n := by
    calc
      _ ≤ 12*advantage (observedLaw offspring lam h n) *
          (C*((d*lam)^2)^n) := hc.trans hu
      _ = _ := by ring
  have hh' := (mul_le_mul_iff_left₀ hp).mp hh
  apply (div_le_iff₀ (show 0 < 3*C by linarith)).mpr
  nlinarith

 

theorem reconstructs_supercritical_of_moments (offspring : PMF ℕ) (d e lam : ℝ)
    (h : Admissible lam) (hD : Moments offspring (fun k : ℕ => (k:ℝ)) d (e+d))
    (hd : 0 < d) (he : 0 ≤ e) (hcrit : 1 < d*lam^2) :
    Reconstructs (fun n => advantage (observedLaw offspring lam h n)) := by
  have hgap : 0 < (d*lam)^2-d := by
    have hp := mul_pos hd (sub_pos.mpr hcrit)
    nlinarith
  have hq : 0 < (d*lam)^2 := by linarith
  let C : ℝ := 2+2*e*lam^2/((d*lam)^2-d)
  have hC : 2 ≤ C := by
    dsimp [C]
    have hh : 0 ≤ 2*e*lam^2/((d*lam)^2-d) := by positivity
    linarith
  have hCpos : 0 < C := by linarith
  have hCeq : C*((d*lam)^2-d) = 2*((d*lam)^2-d)+2*e*lam^2 := by
    dsimp [C]
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hgap)]
  have hstep : d*C+2*e*lam^2 ≤ C*(d*lam)^2 := by nlinarith
  obtain ⟨L,hL0,hL1,hL⟩ := observedAdvantage_tendsto offspring lam h
  have hb : 1/(3*C) ≤ L := ge_of_tendsto' hL
    (fun n => supercritical_advantage_bound offspring d e lam C h hD hd.le hq hC hstep n)
  exact ⟨L, (by positivity : 0 < 1/(3*C)).trans_le hb, hL⟩

 

theorem regular_supercritical (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b:ℝ)*lam^2) : Reconstructs (regularAdvantage b lam h) := by
  have hd : 0 < (b:ℝ) := by exact_mod_cast (show 0 < b by omega)
  have he : 0 ≤ (b:ℝ)^2-(b:ℝ) := by
    have hb' : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
    nlinarith
  apply reconstructs_supercritical_of_moments (PMF.pure b) (b:ℝ) ((b:ℝ)^2-(b:ℝ)) lam h
    ?_ hd he hcrit
  simpa only [sub_add_cancel] using regular_moments b

 

theorem poisson_supercritical (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d*lam^2) : Reconstructs (poissonAdvantage d hd lam h) := by
  apply reconstructs_supercritical_of_moments (poissonOffspring d (le_trans (by norm_num) hd.le))
    d (d^2) lam h (poisson_moments d _) (by linarith) (sq_nonneg d) hcrit

end ThreeState

end OAI
