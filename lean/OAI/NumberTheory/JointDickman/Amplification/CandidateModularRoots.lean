import OAI.NumberTheory.JointDickman.Arithmetic.CandidateExceptionalPrimes
import OAI.NumberTheory.JointDickman.Arithmetic.BlockPrimeSites

namespace OAI

/-! # Modular collisions force the explicit integer obstructions -/

namespace JointDickman

noncomputable def candidateModRoot {M : ℕ} (p : ℕ) [Fact p.Prime]
    (e : BlockCandidateIndex M) : ZMod p :=
  (candidateRootNumerator e : ZMod p)/(candidateQuotient e : ZMod p)

theorem candidateModRoot_collision {M p : ℕ} [Fact p.Prime]
    (e f : BlockCandidateIndex M)
    (he : ¬ p ∣ candidateQuotient e) (hf : ¬ p ∣ candidateQuotient f)
    (hroot : candidateModRoot p e = candidateModRoot p f) :
    p ∣ (candidateRootDifference e f).natAbs := by
  have he0 : (candidateQuotient e : ZMod p) ≠ 0 :=
    fun h => he ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hf0 : (candidateQuotient f : ZMod p) ≠ 0 :=
    fun h => hf ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hh := (div_eq_div_iff he0 hf0).mp hroot
  apply Int.natCast_dvd.mp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simpa only [candidateRootDifference,Int.cast_sub,Int.cast_mul,Int.cast_natCast,
    sub_eq_zero] using hh

theorem candidateModRoot_site_collision {M p : ℕ} [Fact p.Prime]
    (e : BlockCandidateIndex M) (s : Fin M) (he : ¬ p ∣ candidateQuotient e)
    (hroot : candidateModRoot p e = blockSiteRoot M p s) :
    p ∣ (candidateSiteValue e s).natAbs := by
  have he0 : (candidateQuotient e : ZMod p) ≠ 0 :=
    fun h => he ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hh := (div_eq_iff he0).mp hroot
  have hv : candidateSiteValue e s =
      candidateRootNumerator e + (s.val+1)*candidateQuotient e := by
    unfold candidateSiteValue candidateRootNumerator
    ring
  apply Int.natCast_dvd.mp
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [hv,Int.cast_add,Int.cast_mul]
  rw [hh]
  simp only [blockSiteRoot,Int.cast_add,Int.cast_one,Int.cast_natCast,
    Nat.cast_add,Nat.cast_one,neg_mul]
  ring

end JointDickman

end OAI
