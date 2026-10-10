import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.CompactCharging

namespace OAI

/-! Metric assigned geometry. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (clamp clamped_affine_disjoint_sum)

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_nonneg (x y : J → ℝ) : 0 ≤ normDistance x y := norm_nonneg _

omit [PseudoMetricSpace J] in
lemma normDistance_reverse (x y z : J → ℝ) :
    |normDistance x z-normDistance y z| ≤ normDistance x y := by
  simpa only [normDistance,sub_sub_sub_cancel_right] using
    abs_norm_sub_norm_le (x-z) (y-z)

lemma profile_shell_edge_bound {I : Type*} [Fintype I]
    {x y : J → ℝ} (hx : inPolytope x) (hy : inPolytope y)
    (z : I → J → ℝ) (hz : ∀i, isProfile (z i)) (a b : I → ℝ)
    (hab : ∀i, a i ≤ b i)
    (hdis : ∀i j, i ≠ j → ∀w, inPolytope w →
      ¬(a i < normDistance w (z i) ∧ normDistance w (z i)<b i ∧
        a j < normDistance w (z j) ∧ normDistance w (z j)<b j)) :
    ∑i, |clamp (a i) (b i) (normDistance x (z i))-
      clamp (a i) (b i) (normDistance y (z i))| ≤ normDistance x y := by
  apply clamped_affine_disjoint_sum a b _ _ (normDistance_nonneg x y) hab
  · intro i
    simpa only [normDistance_comm y x] using normDistance_reverse y x (z i)
  · intro i j hij t ht hbad
    have htc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    apply hdis i j hij (fun j => x j+t*(y j-x j)) (inPolytope_segment hx hy htc)
    simpa only [isProfile_radial_affine hx hy (hz i) htc,
      isProfile_radial_affine hx hy (hz j) htc] using hbad

lemma profile_radial_max {x z : Doubled J → ℝ} (hx : isProfile x) (hz : inPolytope z) :
    normDistance z x ≤ commonRadius J := by
  obtain ⟨⟨s,a⟩,rfl⟩ := hx
  have h := opposite_radii hz a
  cases s
  · change normDistance z (profile (minus a)) ≤ commonRadius J
    unfold normDistance
    linarith [norm_nonneg (z-profile (plus a))]
  · change normDistance z (profile (plus a)) ≤ commonRadius J
    unfold normDistance
    linarith [norm_nonneg (z-profile (minus a))]

lemma profile_radial_move {x z : Doubled J → ℝ} (hx : isProfile x) (hz : inPolytope z)
    {r : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ commonRadius J) :
    ∃w : Doubled J → ℝ, inPolytope w ∧ normDistance w x = r ∧
      normDistance w z = |r-normDistance z x| := by
  obtain ⟨⟨s,a⟩,rfl⟩ := hx
  cases s
  · obtain ⟨w,hw,hwplus,hwz⟩ := radial_motion hz a
      (show commonRadius J-r ∈ Set.Icc (0:ℝ) (commonRadius J) from
        ⟨by linarith,by linarith⟩)
    have hwp := opposite_radii hw a
    have hzp := opposite_radii hz a
    refine ⟨w,hw,?_,?_⟩
    · change ‖w-profile (minus a)‖ = r
      linarith
    · change ‖w-z‖ = |r-‖z-profile (minus a)‖|
      rw [hwz]
      have heq : commonRadius J-r-‖z-profile (plus a)‖ =
          -(r-‖z-profile (minus a)‖) := by linarith
      rw [heq,abs_neg]
  · exact radial_motion hz a ⟨hr,hrmax⟩

namespace RadialShell
variable {V : Type*} {X : V → Doubled J → ℝ}

lemma ball_meets_radial {B : RadialShell V} (hX : ∀v, isProfile (X v))
    (hB : B.Valid X) (z : V) {δ : ℝ} (hδ : 0 < δ)
    (hlo : B.inner-δ < normDistance (X z) (X B.center))
    (hhi : normDistance (X z) (X B.center) < B.outer+δ) :
    ¬Disjoint ((ball z δ).support X) (B.support X) := by
  have hinterval : max B.inner (normDistance (X z) (X B.center)-δ) <
      min B.outer (normDistance (X z) (X B.center)+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    exact ⟨⟨hB.2.1,by linarith⟩,⟨by linarith,by linarith⟩⟩
  obtain ⟨r,hl,hr⟩ := exists_between hinterval
  have hlo' : B.inner < r := (le_max_left _ _).trans_lt hl
  have hhi' : r < B.outer := hr.trans_le (min_le_left _ _)
  have hradlo : normDistance (X z) (X B.center)-δ < r := (le_max_right _ _).trans_lt hl
  have hradhi : r < normDistance (X z) (X B.center)+δ := hr.trans_le (min_le_right _ _)
  obtain ⟨v,hv⟩ := hB.2.2.2.2
  have hmax : B.outer ≤ commonRadius J := hv.trans (profile_radial_max (hX _) (isProfile_inPolytope (hX v)))
  obtain ⟨w,hw,hwr,hwz⟩ := profile_radial_move (hX B.center) (isProfile_inPolytope (hX z))
    (hB.1.trans hlo'.le) (hhi'.le.trans hmax)
  have hwA : w ∈ (ball z δ).support X := by
    rw [support_ball]
    refine ⟨hw,?_⟩
    rw [hwz,abs_lt]
    constructor <;> linarith
  have hwB : w ∈ B.support X := ⟨hw,hwr ▸ hhi',Or.inr (hwr ▸ hlo')⟩
  exact fun hdis => Set.disjoint_left.mp hdis hwA hwB

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
