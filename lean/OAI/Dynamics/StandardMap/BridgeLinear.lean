import OAI.Dynamics.StandardMap.SegmentObservations

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma wedge_quarterTurn_both (a b : ℂ) : wedge (quarterTurn a) (quarterTurn b)=wedge a b := by
  simp [wedge,quarterTurn]
  ring
lemma wedge_chain_bound (s : ℕ → ℂ) (e : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b)
    (hu : ∀ i, a ≤ i → i ≤ b → ‖s i‖=1)
    (he : ∀ i, a ≤ i → i < b → |wedge (s i) (s (i+1))| ≤ e i) :
    |wedge (s a) (s b)| ≤ ∑ i ∈ Finset.Ico a b, e i := by
  induction b,hab using Nat.le_induction with
  | base => simp [wedge_refl]
  | succ b hab ih =>
    have hh:=ih (fun i hai hib => hu i hai (by omega)) (fun i hai hib => he i hai (by omega))
    have ht:=wedge_sine_triangle (s a) (s b) (s (b+1)) (hu a le_rfl (by omega))
      (hu b hab (by omega)) (hu (b+1) (by omega) le_rfl)
    rw [Finset.sum_Ico_succ_top hab]
    exact ht.trans (add_le_add hh (he b hab (by omega)))

lemma stable_direction_step {A B : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A)
    (a b : ℂ) (ha : ‖a‖=1) (_hb : ‖b‖=1)
    (hAa : ‖A a‖=‖A‖) (hBb : ‖B (quarterTurn b)‖=‖B‖⁻¹)
    (M : ℝ) (hB : 0 < ‖B‖) (hstep : ∀ z, ‖A z‖ ≤ M*‖B z‖) :
    |wedge (quarterTurn a) (quarterTurn b)| ≤ M/(‖A‖*‖B‖) := by
  have hpos : 0 < ‖A‖ := lt_of_lt_of_le zero_lt_one hA.singular_pair.choose_spec.2.2.2.2
  have hp:=expanded_projection_bound hA a ha hAa (quarterTurn b)
  rw [dot_quarterTurn_right] at hp
  have hs:=hstep (quarterTurn b)
  rw [hBb] at hs
  rw [wedge_quarterTurn_both]
  apply (le_div_iff₀ (mul_pos hpos hB)).mpr
  rw [abs_neg] at hp
  have hh := mul_le_mul_of_nonneg_right (hp.trans hs) hB.le
  calc
    _ = (‖A‖*|wedge a b|)*‖B‖ := by ring
    _  ≤  (M*‖B‖⁻¹)*‖B‖ := hh
    _ = M := by field_simp

lemma stable_prefix_finite_bound (A : ℕ → ℂ →L[ℝ] ℂ) (a : ℕ → ℂ)
    (D : ℕ → ℝ) (M : ℝ) (l B : ℕ) (hl : 1 ≤ l) (hlB : l ≤ B)
    (harea : ∀ i, 1 ≤ i → i ≤ B → PlaneAreaPreserving (A i))
    (hunit : ∀ i, 1 ≤ i → i ≤ B → ‖a i‖=1)
    (hnorm : ∀ i, 1 ≤ i → i ≤ B → ‖A i‖=D i)
    (hmax : ∀ i, 1 ≤ i → i ≤ B → ‖A i (a i)‖=D i)
    (hstable : ∀ i, 1 ≤ i → i ≤ B → ‖A i (quarterTurn (a i))‖=(D i)⁻¹)
    (hstep : ∀ i, 1 ≤ i → i < B → ∀ z, ‖A i z‖ ≤ M*‖A (i+1) z‖) :
    ‖A l (quarterTurn (a B))‖ ≤ (D l)⁻¹+D l*∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)) := by
  have hpos (i : ℕ) (hi : 1 ≤ i) (hiB : i ≤ B) : 0 < ‖A i‖ :=
    lt_of_lt_of_le zero_lt_one (harea i hi hiB).singular_pair.choose_spec.2.2.2.2
  have hchain:=wedge_chain_bound (fun i => quarterTurn (a i))
    (fun i => M/(D i*D (i+1))) l B hlB
    (fun i hli hiB => by rw [norm_quarterTurn]; exact hunit i (by omega) hiB)
    (by
      intro i hli hiB
      have hh:=stable_direction_step (harea i (by omega) (by omega)) (a i) (a (i+1))
        (hunit i (by omega) (by omega)) (hunit (i+1) (by omega) (by omega))
        (by rw [hmax i (by omega) (by omega),hnorm i (by omega) (by omega)])
        (by rw [hstable (i+1) (by omega) (by omega),hnorm (i+1) (by omega) (by omega)])
        M (hpos (i+1) (by omega) (by omega)) (hstep i (by omega) hiB)
      simpa only [hnorm i (by omega) (by omega),hnorm (i+1) (by omega) (by omega)] using hh)
  rw [wedge_quarterTurn_both] at hchain
  have hup:=two_singular_upper (harea l hl hlB) (a l) (hunit l hl hlB)
    (by rw [hmax l hl hlB,hnorm l hl hlB]) (quarterTurn (a B))
  rw [dot_quarterTurn_right,abs_neg,hnorm l hl hlB] at hup
  have hw:=abs_wedge_le_norm_mul (a l) (quarterTurn (a B))
  rw [norm_quarterTurn,hunit l hl hlB,hunit B (by omega) le_rfl,mul_one] at hw
  have hD : 0 ≤ D l := by rw [← hnorm l hl hlB]; exact norm_nonneg _
  calc
    _  ≤  D l*|wedge (a l) (a B)|+(D l)⁻¹*|wedge (a l) (quarterTurn (a B))| := hup
    _  ≤  D l*(∑ i ∈ Finset.Ico l B, M/(D i*D (i+1)))+(D l)⁻¹*1 :=
      add_le_add (mul_le_mul_of_nonneg_left hchain hD) (mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hD))
    _ = _ := by ring
end StandardMapEntropy

end OAI
