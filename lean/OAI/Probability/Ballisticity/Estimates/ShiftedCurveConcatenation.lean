import Mathlib
import OAI.Probability.Ballisticity.Estimates.RecordOrPrefixAdd
import OAI.Probability.Ballisticity.Estimates.CurveWordDisjoint

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

lemma shiftedCurvePrefixAt_concatenate {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ a z : ℝ) {s : ℕ} (hs : 0 < s) (n k m : ℕ) (X : Path d) (h0 : X 0=x)
    (hnn : ∀ j, ∃ g, X (j+1)=X j+step g)
    (hpre : X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) z s n)
    (hpost : (fun j => X (n+j)) ∈ CurvePrefixAt (realPosition (step e)) f (X n)
      (fun j => (j:ℝ)*θ-(a+signedCoordinate f (X n-x)-(s:ℝ)*θ)) z k m) :
    X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) z (s+k) (n+m) := by
  let ℓ := realPosition (step e)
  have hheight : dot (realPosition (X n)) ℓ = dot (realPosition x) ℓ+(s:ℝ) := by
    have hh := coordinate_hitAt_exact e x X h0 hnn s n hpre.1
    simp only [ℓ,signedHeight_projection,hh,Int.cast_add,Int.cast_natCast]
  have hrec : (fun j => X j-x) ∈ RecordOrZeroPrefix ℓ s n := by
    simpa only [RecordOrZeroPrefix,ite_eq_right (Nat.ne_of_gt hs)] using
      coordinate_hitAt_recordPrefix e x X h0 hnn hs hpre.1
  refine ⟨⟨?_,?_⟩,?_⟩
  · have hh := hpost.1.1
    change dot (realPosition (X n)) ℓ+(k:ℝ) ≤ dot (realPosition (X (n+m))) ℓ at hh
    change dot (realPosition x) ℓ+((s+k:ℕ):ℝ) ≤ dot (realPosition (X (n+m))) ℓ
    rw [hheight,Nat.cast_add] at *
    linarith
  · intro j hj
    change dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ ∧
      dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+((s+k:ℕ):ℝ)
    rw [Nat.cast_add]
    by_cases hjn : j<n
    · have hh := hpre.1.2 j hjn
      change dot (realPosition x) ℓ ≤ dot (realPosition (X j)) ℓ ∧
        dot (realPosition (X j)) ℓ < dot (realPosition x) ℓ+(s:ℝ) at hh
      exact ⟨hh.1,by linarith [hh.2,show (0:ℝ) ≤ k by positivity]⟩
    · have hh := hpost.1.2 (j-n) (by omega)
      change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j-n)))) ℓ ∧
        dot (realPosition (X (n+(j-n)))) ℓ < dot (realPosition (X n)) ℓ+(k:ℝ) at hh
      rw [Nat.add_sub_of_le (show n ≤ j by omega),hheight] at hh
      exact ⟨by linarith [hh.1,show (0:ℝ) ≤ s by positivity],by linarith [hh.2]⟩
  · intro j hj
    by_cases hjs : j ≤ s
    · obtain ⟨a,ha,hra,hga⟩ := hpre.2 j hjs
      exact ⟨a,by omega,hra,hga⟩
    · obtain ⟨a,ha,hra,hga⟩ := hpost.2 (j-s) (by omega)
      refine ⟨n+a,by omega,?_,?_⟩
      · have hh := recordOrZeroPrefix_add ℓ (fun b => X b-x) (by rw [h0,sub_self]) s n (j-s) a hrec
          (by convert hra using 1; ext b; dsimp; abel)
        simpa only [Nat.add_sub_of_le (show s ≤ j by omega)] using hh
      · have he : X (n+a)-x = (X n-x)+(X (n+a)-X n) := by abel
        have hadd (u v : Lattice d) : signedCoordinate f (u+v)=signedCoordinate f u+signedCoordinate f v := by
          simp only [signedCoordinate,Pi.add_apply,Int.cast_add]
          split_ifs <;> ring
        have hcast : (j:ℝ)=(s:ℝ)+((j-s:ℕ):ℝ) := by exact_mod_cast (Nat.add_sub_of_le (show s ≤ j by omega)).symm
        dsimp only at hga ⊢
        rw [he,hadd,hcast]
        convert hga using 1
        congr 1
        ring

end DirectionalTransience

end

end

end OAI
