import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.MoserCoordinateDifferences
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CappedKernelProgram

namespace OAI

/-! Coordinate differences of a rational scalar sampler approximate the
actual gradient and Laplacian. The real extension below is only a proof
device; the numerical expressions evaluate the sampler at rational points. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb.RationalFieldDifferences
open CappedKernelProgram (Triple position)
open NeutralAtom (axis dirPartial coordinateLaplacian)

theorem position_injective : Function.Injective position := by
  rintro ⟨a,ay,az⟩ ⟨b,byCoord,bz⟩ h
  have h0 := congrArg (fun x : Position => x 0) h
  have h1 := congrArg (fun x : Position => x 1) h
  have h2 := congrArg (fun x : Position => x 2) h
  change (a:ℝ) = (b:ℝ) at h0
  change (ay:ℝ) = (byCoord:ℝ) at h1
  change (az:ℝ) = (bz:ℝ) at h2
  have h0' : a=b := by exact_mod_cast h0
  have h1' : ay=byCoord := by exact_mod_cast h1
  have h2' : az=bz := by exact_mod_cast h2
  simp only [h0',h1',h2']

def extend (V : Position → ℝ) (sample : Triple → ℚ) (x : Position) : ℝ := by
  classical
  exact if h : ∃ q, position q=x then (sample (Classical.choose h):ℝ) else V x

theorem extend_at (V : Position → ℝ) (sample : Triple → ℚ) (q : Triple) :
    extend V sample (position q) = (sample q:ℝ) := by
  rw [extend,dite_eq_left (show ∃ r, position r=position q from ⟨q,rfl⟩)]
  congr 1
  exact congrArg sample (position_injective
    (Classical.choose_spec (show ∃ r, position r=position q from ⟨q,rfl⟩)))

theorem extend_error (V : Position → ℝ) (sample : Triple → ℚ) {ε : ℝ}
    (hε : 0 ≤ ε) (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (x : Position) :
    |extend V sample x-V x| ≤ ε := by
  unfold extend
  split_ifs with h
  · have hs := he (Classical.choose h)
    simpa only [Classical.choose_spec h] using hs
  · simpa only [sub_self,abs_zero] using hε

def shift (q : Triple) (h : ℚ) (a : Fin 3) : Triple :=
  (q.1+(if a=0 then h else 0),
    (q.2.1+(if a=1 then h else 0),q.2.2+(if a=2 then h else 0)))

theorem shift_position (q : Triple) (h : ℚ) (a : Fin 3) :
    position (shift q h a) = position q+(h:ℝ) • axis a := by
  ext b
  fin_cases a <;> fin_cases b <;> simp [position,shift,axis]

def first (sample : Triple → ℚ) (h : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  (sample (shift q h a)-sample q)/h

def second (sample : Triple → ℚ) (h : ℚ) (q : Triple) (a : Fin 3) : ℚ :=
  (sample (shift q h a)+sample (shift q (-h) a)-2*sample q)/h^2

def laplacian (sample : Triple → ℚ) (h : ℚ) (q : Triple) : ℚ := ∑ a, second sample h q a

theorem first_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) (a : Fin 3) :
    |(first sample h q a:ℝ)-dirPartial V (axis a) (position q)| ≤ B*(h:ℝ)+2*ε/(h:ℝ) := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hd := MoserCoordinateDifferences.first_error V (extend V sample) hV hB hε hhR hb
    (extend_error V sample hε he) (position q) a
  rw [← shift_position,extend_at,extend_at] at hd
  simpa only [first,Rat.cast_div,Rat.cast_sub] using hd

theorem second_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) (a : Fin 3) :
    |(second sample h q a:ℝ)-dirPartial (dirPartial V (axis a)) (axis a) (position q)| ≤
      B*(h:ℝ)+4*ε/(h:ℝ)^2 := by
  have hhR : (0:ℝ) < h := by exact_mod_cast hh
  have hd := MoserCoordinateDifferences.second_error V (extend V sample) hV hB hhR hb
    (extend_error V sample hε he) (position q) a
  have hm : position q-(h:ℝ) • axis a = position (shift q (-h) a) := by
    rw [shift_position,Rat.cast_neg,neg_smul,sub_eq_add_neg]
  rw [← shift_position,hm,extend_at,extend_at,extend_at] at hd
  simpa only [second,Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_sub,Rat.cast_ofNat] using hd

theorem laplacian_error (V : Position → ℝ) (hV : ContDiff ℝ 6 V) (sample : Triple → ℚ)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε) {h : ℚ} (hh : 0 < h)
    (hb : ∀ k ≤ 6, ∀ x, ‖iteratedFDeriv ℝ k V x‖ ≤ B)
    (he : ∀ q, |(sample q:ℝ)-V (position q)| ≤ ε) (q : Triple) :
    |(laplacian sample h q:ℝ)-coordinateLaplacian V (position q)| ≤
      3*(B*(h:ℝ)+4*ε/(h:ℝ)^2) := by
  rw [laplacian,Rat.cast_sum,NeutralAtom.coordinateLaplacian_eq_partials
    ((hV.of_le (by norm_num : (2:WithTop ℕ∞) ≤ 6)).contDiffAt),← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _a : Fin 3, (B*(h:ℝ)+4*ε/(h:ℝ)^2) :=
      Finset.sum_le_sum (fun a _ => second_error V hV sample hB hε hh hb he q a)
    _ = _ := by simp; ring

end ContinuumCoulomb.RationalFieldDifferences

end

end OAI
