import OAI.Geometry.Arnold.Extension

namespace OAI

universe uE uX

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology

open Set
open scoped ContDiff

namespace ArnoldCounterexample.Descent

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A second-derivative bound uniformly converts an infinitesimal descent
`-S` into a strict smooth discrete descent using the step `c*S`.
It works even when `S` vanishes to arbitrarily high order. -/
theorem adaptive_step {K : Set E} (hK : IsCompact K)
    (Φ : ℝ × E → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (S : E → ℝ) (hS : Continuous S)
    (hSnon : ∀ z ∈ K, 0 ≤ S z)
    (hd0 : ∀ z ∈ K, fderiv ℝ Φ (0, z) (1, 0) = -S z) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K,
      0 ≤ c * S z ∧ c * S z ≤ 1 ∧
      Φ (c * S z, z) ≤ Φ (0, z) ∧
      (S z ≠ 0 → Φ (c * S z, z) < Φ (0, z)) := by
  let P : ℝ × E → ℝ := fun p ↦ fderiv ℝ Φ p (1, 0)
  let Q : ℝ × E → ℝ := fun p ↦ fderiv ℝ P p (1, 0)
  have hP : ContDiff ℝ ∞ P := (hΦ.fderiv_right (by simp)).clm_apply contDiff_const
  have hQ : ContDiff ℝ ∞ Q := (hP.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hS.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hQ.continuous.continuousOn : ContinuousOn Q (Icc (0 : ℝ) 1 ×ˢ K))
  let R := |B| + |M| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let c := (2 * R)⁻¹
  have hc : 0 < c := inv_pos.mpr (mul_pos (by norm_num) hR)
  have hcR : c * R = 1 / 2 := by dsimp [c]; field_simp
  have hBlt : B < R := by dsimp [R]; linarith [le_abs_self B, abs_nonneg M]
  have hMlt : M < R := by dsimp [R]; linarith [le_abs_self M, abs_nonneg B]
  refine ⟨c, hc, fun z hz ↦ ?_⟩
  have hs : 0 ≤ S z := hSnon z hz
  have hsB : S z ≤ B := (le_abs_self (S z)).trans (hB z hz)
  have ht0 : 0 ≤ c * S z := mul_nonneg hc.le hs
  have ht1 : c * S z ≤ 1 := by
    have htR := mul_le_mul_of_nonneg_left (hsB.trans hBlt.le) hc.le
    rw [hcR] at htR
    linarith
  have hp (t : ℝ) : HasDerivAt (fun s ↦ Φ (s, z)) (P (t, z)) t :=
    (hΦ.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hq (t : ℝ) : HasDerivAt (fun s ↦ P (s, z)) (Q (t, z)) t :=
    (hP.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hvariation (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |P (t, z) - P (0, z)| ≤ M * t := by
    simpa using norm_image_sub_le_of_norm_deriv_le_segment'
      (fun s (_ : s ∈ Icc (0 : ℝ) 1) ↦ (hq s).hasDerivWithinAt)
      (fun s (hs : s ∈ Ico (0 : ℝ) 1) ↦ hM (s, z) ⟨⟨hs.1, hs.2.le⟩, hz⟩) t ht
  have hstrict (hne : S z ≠ 0) : Φ (c * S z, z) < Φ (0, z) := by
    have hsp : 0 < S z := lt_of_le_of_ne hs hne.symm
    have hneg (t : ℝ) (ht : t ∈ interior (Icc 0 (c * S z))) :
        deriv (fun s ↦ Φ (s, z)) t < 0 := by
      have ht' : t ∈ Icc 0 (c * S z) := interior_subset ht
      have hv := hvariation t ⟨ht'.1, ht'.2.trans ht1⟩
      have hbound : M * t ≤ R * (c * S z) := by
        exact (mul_le_mul_of_nonneg_right hMlt.le ht'.1).trans
          (mul_le_mul_of_nonneg_left ht'.2 hR.le)
      have hrc : R * (c * S z) = S z / 2 := by nlinarith [hcR]
      have hd : P (0, z) = -S z := hd0 z hz
      rw [(hp t).deriv]
      have hu := (abs_le.mp hv).2
      rw [hd] at hu
      rw [hrc] at hbound
      linarith
    exact strictAntiOn_of_deriv_neg (convex_Icc 0 (c * S z))
      (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn hneg
      (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0) (mul_pos hc hsp)
  refine ⟨ht0, ht1, ?_, hstrict⟩
  by_cases hzero : S z = 0
  · simp [hzero]
  · exact (hstrict hzero).le

end ArnoldCounterexample.Descent

open Set Function

namespace ArnoldCounterexample.Descent

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

omit [TopologicalSpace X] [CompactSpace X] in
/-- Values of a Lyapunov function are nonincreasing under iteration. -/
lemma iterate_le {D : X → X} {f : X → ℝ}
    (hdec : ∀ x, f (D x) ≤ f x) (n : ℕ) (x : X) : f (D^[n] x) ≤ f x := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hdec _).trans ih

/-- A compact band without stationary points is crossed in a uniform finite
number of iterations. The conclusion is strict, as needed by the level-cover argument. -/
theorem uniform_drop {D : X → X} {f : X → ℝ}
    (hD : Continuous D) (hf : Continuous f)
    (hdec : ∀ x, f (D x) ≤ f x) (a b : ℝ)
    (hstrict : ∀ x, a ≤ f x → f x ≤ b → f (D x) < f x) :
    ∃ N : ℕ, ∀ x, f x ≤ b → f (D^[N] x) < a := by
  let K : Set X := {x | a ≤ f x ∧ f x ≤ b}
  have hK : IsCompact K := (isClosed_le continuous_const hf |>.inter
    (isClosed_le hf continuous_const)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne (hf.sub (hf.comp hD)).continuousOn
    let δ := f z - f (D z)
    have hδ : 0 < δ := sub_pos.mpr (hstrict z hz.1 hz.2)
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    refine ⟨N, fun x hx ↦ ?_⟩
    by_contra hn
    have ha : a ≤ f (D^[N] x) := le_of_not_gt hn
    have hp : ∀ n, a ≤ f (D^[n] x) → f (D^[n] x) ≤ f x - n * δ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro han
        rw [Function.iterate_succ_apply'] at han ⊢
        have hprev : a ≤ f (D^[n] x) := han.trans (hdec _)
        have hbprev : f (D^[n] x) ≤ b := (iterate_le hdec n x).trans hx
        have hgap := hmin (show D^[n] x ∈ K from ⟨hprev, hbprev⟩)
        have hi := ih hprev
        push_cast
        dsimp [δ] at *
        linarith
    have hnum : b - a < N * δ := (div_lt_iff₀ hδ).mp hN
    have hlast := hp N ha
    linarith
  · refine ⟨0, fun x hx ↦ ?_⟩
    by_contra ha
    exact hne ⟨x, le_of_not_gt ha, hx⟩

/-- Strict sublevel containment on the zero set of a continuous coordinate
persists on a slightly larger closed sublevel. -/
theorem thicken_sublevel {f g : X → ℝ} {ℓ : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hℓ : Continuous ℓ)
    (c a : ℝ) (h : ∀ x, f x ≤ c → ℓ x = 0 → g x < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x, f x ≤ c + ε → ℓ x = 0 → g x < a := by
  let K : Set X := {x | ℓ x = 0 ∧ a ≤ g x}
  have hK : IsCompact K := ((isClosed_eq hℓ continuous_const).inter
    (isClosed_le continuous_const hg)).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
    have hcz : c < f z := by
      by_contra hc
      exact (not_lt_of_ge hz.2) (h z (le_of_not_gt hc) hz.1)
    refine ⟨(f z - c) / 2, by linarith, fun x hx hzero ↦ ?_⟩
    by_contra hxa
    have hbound : f z ≤ f x := hmin (show x ∈ K from ⟨hzero, le_of_not_gt hxa⟩)
    linarith
  · refine ⟨1, zero_lt_one, fun x _ hzero ↦ ?_⟩
    by_contra hxa
    exact hne ⟨x, hzero, le_of_not_gt hxa⟩

/-- The finite critical-value LS cover, expressed without manifold jargon.
Every cover member is the inverse image of the same nonvanishing-coordinate
chart under an iterate of a single strict Lyapunov descent. -/
theorem critical_level_cover {D : X → X} {f : X → ℝ} {ℓ : X → ℂ}
    (hD : Continuous D) (hf : Continuous f) (hℓ : Continuous ℓ)
    (hdec : ∀ x, f (D x) ≤ f x)
    (hchart : ∀ x, ℓ x = 0 → f (D x) < f x)
    (s : Finset ℝ) (a : ℝ)
    (hstationary : ∀ x, f x ≤ a → f (D x) = f x → f x ∈ s) :
    ∃ T : Finset ℕ, T.card ≤ s.card ∧
      ∀ x, f x ≤ a → ∃ n ∈ T, ℓ (D^[n] x) ≠ 0 := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · let c := s.max' hs
      have hc : c ∈ s := Finset.max'_mem s hs
      have herase : s.erase c ⊂ s := Finset.erase_ssubset hc
      by_cases hca : c ≤ a
      · let K : Set X := {x | f x ≤ c ∧ ℓ x = 0}
        have hK : IsCompact K := ((isClosed_le hf continuous_const).inter
          (isClosed_eq hℓ continuous_const)).isCompact
        have hd : ∃ d : ℝ, d < c ∧ ∀ x ∈ K, f (D x) ≤ d := by
          by_cases hne : K.Nonempty
          · obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hf.comp hD).continuousOn
            exact ⟨f (D z), (hchart z hz.2).trans_le hz.1, fun x hx ↦ hmax hx⟩
          · exact ⟨c - 1, by linarith, fun x hx ↦ False.elim (hne ⟨x, hx⟩)⟩
        obtain ⟨d, hdc, hd⟩ := hd
        let b := (d + c) / 2
        have hdb : d < b := by dsimp [b]; linarith
        have hbc : b < c := by dsimp [b]; linarith
        obtain ⟨T, hTcard, hT⟩ := ih (s.erase c) herase b (by
          intro x hx heq
          refine Finset.mem_erase.mpr ⟨?_, hstationary x (hx.trans (hbc.le.trans hca)) heq⟩
          exact ne_of_lt (hx.trans_lt hbc))
        obtain ⟨ε, hε, hdrop⟩ := thicken_sublevel hf (hf.comp hD) hℓ c b (by
          intro x hx hz
          exact (hd x ⟨hx, hz⟩).trans_lt hdb)
        obtain ⟨N, hN⟩ := uniform_drop hD hf hdec (c + ε) a (by
          intro x hx hxa
          refine lt_of_le_of_ne (hdec x) ?_
          intro heq
          have hsx := hstationary x hxa heq
          have hxc : f x ≤ c := Finset.le_max' s (f x) hsx
          linarith)
        let T' := insert 0 (T.image Nat.succ)
        refine ⟨T'.image (fun n ↦ n + N), ?_, ?_⟩
        · calc
            (T'.image (fun n ↦ n + N)).card ≤ T'.card := Finset.card_image_le
            _ ≤ T.card + 1 := by
              exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
            _ ≤ s.card := by
              have herasecard := Finset.card_erase_add_one hc
              omega
        · intro x hx
          have hy : f (D^[N] x) < c + ε := hN x hx
          by_cases hzero : ℓ (D^[N] x) = 0
          · have hb : f (D (D^[N] x)) < b := hdrop _ hy.le hzero
            obtain ⟨n, hn, hnonzero⟩ := hT _ hb.le
            refine ⟨n.succ + N, Finset.mem_image.mpr ⟨n.succ, ?_, rfl⟩, ?_⟩
            · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
            · simpa only [Function.iterate_add_apply, Function.iterate_succ_apply] using hnonzero
          · exact ⟨0 + N, Finset.mem_image.mpr ⟨0, Finset.mem_insert_self _ _, rfl⟩,
              by simpa using hzero⟩
      · have hac : a < c := lt_of_not_ge hca
        obtain ⟨T, hTcard, hT⟩ := ih (s.erase c) herase a (by
          intro x hx heq
          exact Finset.mem_erase.mpr ⟨ne_of_lt (hx.trans_lt hac), hstationary x hx heq⟩)
        exact ⟨T, hTcard.trans (Finset.card_le_card (Finset.erase_subset _ _)), hT⟩
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      refine ⟨∅, by simp, fun x hx ↦ ?_⟩
      have hK : IsCompact {x | f x ≤ a} := (isClosed_le hf continuous_const).isCompact
      obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ hf.continuousOn
      have hDz : f (D z) ≤ a := (hdec z).trans hz
      have heq : f (D z) = f z := le_antisymm (hdec z) (hmin hDz)
      have hm := hstationary z hz heq
      simp [hempty] at hm

end ArnoldCounterexample.Descent

end

end OAI
