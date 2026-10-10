import OAI.Analysis.LipschitzHilbert.Fourier.AnnularCutoffConstruction
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalProjectionAlgebra

namespace OAI

/-! A fixed nonzero, real and even narrow cutoff for the
p=2 band-to-full reduction. Its positive part is in [1,101/100]. -/
noncomputable section
namespace LipschitzHilbert.PacketRepresentation

def narrowBandBump : ContDiffBump (201/200:ℝ) where
  rIn := 1/1000
  rOut := 1/400
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def narrowBandPositive : SchwartzMap ℝ ℂ :=
  (narrowBandBump.hasCompactSupport.toSchwartzMap narrowBandBump.contDiff).postcompCLM Complex.ofRealCLM

@[simp] theorem narrowBandPositive_apply (s : ℝ) : narrowBandPositive s=(narrowBandBump s:ℂ) := rfl

theorem narrowBandPositive_support (s : ℝ) (hs : narrowBandPositive s≠0) :
    1≤s ∧ s≤101/100 := by
  have hn : narrowBandBump s≠0 := by
    intro h
    exact hs (by simp only [narrowBandPositive_apply,h,Complex.ofReal_zero])
  have hm : s∈Function.support narrowBandBump := hn
  rw [narrowBandBump.support_eq] at hm
  have hd : |s-201/200|<1/400 := by
    simpa only [Metric.mem_ball,Real.dist_eq,narrowBandBump] using hm
  exact ⟨by linarith [(abs_lt.mp hd).1],by linarith [(abs_lt.mp hd).2]⟩

theorem narrowBandPositive_band (s : ℝ) (hs : narrowBandPositive s≠0) : 1≤s ∧ s≤2 := by
  have h := narrowBandPositive_support s hs
  exact ⟨h.1,by linarith only [h.2]⟩

theorem narrowBandPositive_center : narrowBandPositive (201/200)=1 := by
  simp only [narrowBandPositive_apply,narrowBandBump.one_of_mem_closedBall
    (show (201/200:ℝ)∈Metric.closedBall (201/200) narrowBandBump.rIn by
      simp only [Metric.mem_closedBall,dist_self,narrowBandBump]; norm_num),Complex.ofReal_one]

theorem narrowBandPositive_real (s : ℝ) : star (narrowBandPositive s)=narrowBandPositive s := by
  simp only [narrowBandPositive_apply,Complex.star_def,Complex.conj_ofReal]

def narrowBandProfile : SchwartzMap ℝ ℂ :=
  narrowBandPositive+conjugateReflectedCutoff narrowBandPositive

@[simp] theorem narrowBandProfile_apply (s : ℝ) :
    narrowBandProfile s=narrowBandPositive s+narrowBandPositive (-s) := by
  simp only [narrowBandProfile,add_apply,conjugateReflectedCutoff_apply]
  change narrowBandPositive s+star (narrowBandPositive (-s))=_
  rw [narrowBandPositive_real]

theorem narrowBandProfile_even (s : ℝ) : narrowBandProfile (-s)=narrowBandProfile s := by
  simp only [narrowBandProfile_apply,neg_neg,add_comm]

theorem narrowBandProfile_nonneg (s : ℝ) : 0≤(narrowBandProfile s).re := by
  simp only [narrowBandProfile_apply,narrowBandPositive_apply,Complex.add_re,Complex.ofReal_re]
  exact add_nonneg narrowBandBump.nonneg narrowBandBump.nonneg

theorem narrowBandProfile_real (s : ℝ) : star (narrowBandProfile s)=narrowBandProfile s := by
  rw [narrowBandProfile_apply,star_add,narrowBandPositive_real,narrowBandPositive_real]

theorem narrowBandProfile_center : narrowBandProfile (201/200)=1 := by
  have hz : narrowBandPositive (-(201/200))=0 := by
    by_contra hn
    have h := (narrowBandPositive_support _ hn).1
    norm_num at h
  rw [narrowBandProfile_apply,narrowBandPositive_center,hz,add_zero]

theorem narrowBandProfile_support (s : ℝ) (hs : narrowBandProfile s≠0) :
    1≤|s| ∧ |s|≤101/100 := by
  have hn : narrowBandPositive s≠0 ∨ narrowBandPositive (-s)≠0 := by
    by_contra h
    simp only [not_or,ne_eq,not_not] at h
    exact hs (by rw [narrowBandProfile_apply,h.1,h.2,add_zero])
  rcases hn with hp|hp
  · have h := narrowBandPositive_support s hp
    rw [abs_of_nonneg (by linarith only [h.1])]
    exact h
  · have h := narrowBandPositive_support (-s) hp
    rw [abs_of_nonpos (by linarith only [h.1])]
    exact h

end LipschitzHilbert.PacketRepresentation

end

end OAI
