import Mathlib
import OAI.Probability.Ballisticity.Estimates.ShiftedCurveConcatenation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma curvePrefixAt_center_comparison {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b c : ℕ → ℝ) (B D : ℝ) (H n : ℕ) (X : Path d)
    (hc : ∀ j ≤ H, |b j-c j| ≤ D) (hX : X ∈ CurvePrefixAt ℓ f x b B H n) :
    X ∈ CurvePrefixAt ℓ f x c (B+D) H n := by
  refine ⟨hX.1,?_⟩
  intro j hj
  obtain ⟨a,ha,hr,hg⟩ := hX.2 j hj
  refine ⟨a,ha,hr,?_⟩
  calc
    _ = |(signedCoordinate f (X a-x)-b j)+(b j-c j)| := by congr 1; ring
    _ ≤ |signedCoordinate f (X a-x)-b j|+|b j-c j| := abs_add_le _ _
    _ ≤ B+D := add_le_add hg (hc j hj)

lemma curvePrefixAt_radius_mono {d : ℕ} (ℓ : Vector d) (f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B C : ℝ} (hBC : B ≤ C) (H n : ℕ) (X : Path d)
    (hX : X ∈ CurvePrefixAt ℓ f x b B H n) : X ∈ CurvePrefixAt ℓ f x b C H n := by
  refine ⟨hX.1,?_⟩
  intro j hj
  obtain ⟨a,ha,hr,hg⟩ := hX.2 j hj
  exact ⟨a,ha,hr,hg.trans hBC⟩

lemma curveWordEvent_shifted_tube {d : ℕ} (e f : Direction d) (x : Lattice d)
    (b : ℕ → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) {H : ℕ} (hH : 0 < H)
    (θ a r : ℝ) (hb : ∀ j ≤ H, |b j-(j:ℝ)*θ| ≤ D)
    (w : List (Lattice d))
    (hp : ∀ k ≤ w.length, |a+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r)
    (X : Path d) (h0 : X 0=x) (hnn : ∀ j, ∃ g, X (j+1)=X j+step g)
    (hX : X ∈ curveWordEvent (realPosition (step e)) f b B H x w) :
    ∃ n, X ∈ CurvePrefixAt (realPosition (step e)) f x
      (fun j => (j:ℝ)*θ-a) (r+B+D) (w.length*H) n := by
  induction w generalizing x X a with
  | nil =>
    have ha : |a| ≤ r := by simpa [signedCoordinate] using hp 0 le_rfl
    refine ⟨0,⟨?_,?_⟩,?_⟩
    · simp [Upper,h0]
    · intro j hj; omega
    · intro j hj
      have hj0 : j=0 := by simpa using hj
      subst j
      refine ⟨0,le_rfl,?_,?_⟩
      · simp [RecordOrZeroPrefix]
      · simpa [h0,signedCoordinate] using ha.trans (by linarith : r ≤ r+B+D)
  | cons u w ih =>
    obtain ⟨n,hn,hnu,hnt⟩ := (curveWordEvent_cons_mem _ f b B H x u w X).mp hX
    let a' := a+signedCoordinate f u-(H:ℝ)*θ
    have hp' : ∀ k ≤ w.length, |a'+signedCoordinate f (w.take k).sum-(k:ℝ)*(H:ℝ)*θ| ≤ r := by
      intro k hk
      have hh := hp (k+1) (by simp only [List.length_cons]; omega)
      simp only [List.take_succ_cons,List.sum_cons,signedCoordinate_add,Nat.cast_add,Nat.cast_one] at hh
      dsimp [a']
      convert hh using 1; congr 1; ring
    have hnt' : (fun j => X (n+j)) ∈ curveWordEvent (realPosition (step e)) f b B H (X n) w := by simpa only [hnu] using hnt
    obtain ⟨m,hm⟩ := ih (X n) a' hp' (fun j => X (n+j)) (by simp)
      (fun j => by simpa only [Nat.add_assoc] using hnn (n+j)) hnt'
    have ha : |a| ≤ r := by simpa [signedCoordinate] using hp 0 (Nat.zero_le _)
    have hc : ∀ j ≤ H, |b j-((j:ℝ)*θ-a)| ≤ D+r := by
      intro j hj
      calc
        _ = |(b j-(j:ℝ)*θ)+a| := by congr 1; ring
        _ ≤ |b j-(j:ℝ)*θ|+|a| := abs_add_le _ _
        _ ≤ D+r := add_le_add (hb j hj) ha
    have hn' := curvePrefixAt_center_comparison _ f x b (fun j => (j:ℝ)*θ-a) B (D+r) H n X hc hn
    have hn'' : X ∈ CurvePrefixAt (realPosition (step e)) f x (fun j => (j:ℝ)*θ-a) (r+B+D) H n := by
      simpa only [add_comm,add_left_comm,add_assoc] using hn'
    have ha' : a'=a+signedCoordinate f (X n-x)-(H:ℝ)*θ := by
      simp only [a',hnu,add_sub_cancel_left]
    rw [ha'] at hm
    have hh := shiftedCurvePrefixAt_concatenate e f x θ a (r+B+D) hH n (w.length*H) m X h0 hnn hn'' hm
    refine ⟨n+m,?_⟩
    simpa only [List.length_cons,Nat.add_mul,one_mul,Nat.add_comm] using hh

end DirectionalTransience

end

end

end OAI
