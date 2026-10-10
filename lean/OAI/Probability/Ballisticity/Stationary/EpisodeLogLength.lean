import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeGlobalRetention
import OAI.Probability.Ballisticity.Stationary.EpisodeLength

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

private lemma episode_log_geometric_bound (A B h : ℝ) (J : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hbound : h ≤ (J:ℝ)*A*Real.exp B^J) :
    Real.log (1+h) ≤ (Real.log (1+A)+1+B)*(1+(J:ℝ)) := by
  have hJ : (J:ℝ) ≤ Real.exp (J:ℝ) := by linarith [Real.add_one_le_exp (J:ℝ)]
  have hE : 1 ≤ Real.exp ((1+B)*(J:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
  have hprod : Real.exp (J:ℝ)*Real.exp B^J = Real.exp ((1+B)*(J:ℝ)) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hJ (mul_nonneg hA (by positivity : 0 ≤ Real.exp B^J))
  have hl : 1+h ≤ (1+A)*Real.exp ((1+B)*(J:ℝ)) := by
    have he : Real.exp (J:ℝ)*(A*Real.exp B^J) = A*Real.exp ((1+B)*(J:ℝ)) := by
      rw [←hprod]
      ring
    rw [he] at hmul
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 1+h) hl
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',Real.log_exp] at hlog
  have hlogA : 0 ≤ Real.log (1+A) := Real.log_nonneg (by linarith)
  have hjA := mul_nonneg hlogA (Nat.cast_nonneg J : (0:ℝ) ≤ J)
  nlinarith

lemma episodeRun_logLength {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hq : 0 < q.scale) (n : ℕ) :
    let p := episodeRun e f hef r fexp g χ b sfloor N q ω n
    let J := episodeSteps e f hef r fexp g χ b sfloor N q ω n
    Real.log (1+(p.height-q.height:ℕ)) ≤
      (Real.log (1+q.scale*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ)) := by
  dsimp only
  have hlen := (episodeRun_length_scale e f hef r fexp g χ b sfloor N q ω hf hg hb hq n).2.2
  have hmono := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω n
  apply episode_log_geometric_bound (q.scale*Real.exp (χ*b)) (g*b) _ _
    (by positivity) (mul_nonneg hg hb) (Nat.cast_nonneg _)
  rw [Nat.cast_sub hmono]
  nlinarith [hlen]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

theorem episode_log_length_bound {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N t : ℕ)
    (ω : Environment d) (hf : 0 ≤ fexp) (hg : 0 ≤ g) (hb : 0 ≤ b) (hs : 0 < sfloor) :
    Real.log (1+((episodeFinal (k:=k) e f hef r fexp g χ b sfloor hR N t ω).height-t:ℕ)) ≤
      (Real.log 2+Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*
        (1+(episodeStageCount (k:=k) e f hef r fexp g χ b sfloor hR N t ω : ℝ)) := by
  let q := episodeInitial (k:=k) e f hef r sfloor hR t ω
  let p := episodeRun e f hef r fexp g χ b sfloor N q ω N
  let J := episodeSteps e f hef r fexp g χ b sfloor N q ω N
  have h := episodeRun_logLength e f hef r fexp g χ b sfloor N q ω hf hg hb hs N
  have hm := episodeRun_height_mono e f hef r fexp g χ b sfloor N q ω N
  have hqt : q.height=t+1 := rfl
  have he : p.height-t=(p.height-q.height)+1 := by dsimp only [p] at ⊢; omega
  change Real.log (1+(p.height-t:ℕ)) ≤ _
  rw [he,Nat.cast_add,Nat.cast_one]
  have hl := Real.log_le_log (by positivity : 0 < 1+((p.height-q.height:ℕ):ℝ)+1)
    (show 1+((p.height-q.height:ℕ):ℝ)+1 ≤ 2*(1+((p.height-q.height:ℕ):ℝ)) by nlinarith [(show (0:ℝ) ≤ (p.height-q.height:ℕ) from Nat.cast_nonneg _)])
  rw [Real.log_mul (by norm_num) (by positivity)] at hl
  have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hjtwo := mul_nonneg htwo (Nat.cast_nonneg J : (0:ℝ) ≤ J)
  change Real.log (1+((p.height-q.height:ℕ):ℝ)) ≤
    (Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ)) at h
  change Real.log (1+(((p.height-q.height:ℕ):ℝ)+1)) ≤
    (Real.log 2+Real.log (1+sfloor*Real.exp (χ*b))+1+g*b)*(1+(J:ℝ))
  rw [add_assoc] at hl
  nlinarith

end DirectionalTransience

end

end OAI
