import OAI.Geometry.HeilbronnTriangle.Definitions
import OAI.Geometry.HeilbronnTriangle.PowerGap

namespace OAI


namespace Problem355

theorem not_eventualAlmostUpperBound_of_sequence
    {c epsilon : ℝ} (he : epsilon < c)
    {n : ℕ → ℕ} {P : ℕ → Finset Point}
    (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hP : ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
      triangleAreasAtLeast (P j) (Real.rpow (n j : ℝ) (-2 + c))) :
    ¬ eventualAlmostUpperBound epsilon := by
  rintro ⟨C, hC, n0, hupper⟩
  have hgap := eventually_mul_rpow_lt_rpow hn
    (show (-2 + epsilon : ℝ) < -2 + c by linarith) C
  obtain ⟨j, hjgap, hjn⟩ :=
    (hgap.and (hn.eventually (Filter.eventually_ge_atTop n0))).exists
  obtain ⟨hn3, hcard, hsquare, hlower⟩ := hP j
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr, harea⟩ :=
    hupper (n j) hjn hn3 (P j) hcard hsquare
  exact (not_lt_of_ge ((hlower p hp q hq r hr hpq hpr hqr).trans harea)) hjgap

end Problem355

end OAI
