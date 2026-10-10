import OAI.Analysis.PlanarPacking.HalfGapCore

namespace OAI

namespace SharpPlanar
lemma halfGap_absmul {y v : ℝ} (hv : v  ∈  Set.Icc 0 1) : |y*v| ≤ |y| := by
  rw [abs_mul,abs_of_nonneg hv.1]
  nlinarith [mul_nonneg (abs_nonneg y) (sub_nonneg.mpr hv.2)]
lemma halfGap_segment_lower {v m y s N : ℝ} (hv : v  ∈  Set.Icc 0 1)
    (hm : N ≤ m) (hy : N ≤ m+y) (hs : s ∈ Set.uIcc m (m+y*v)) : N ≤ s := by
  have he : N ≤ m+y*v := by
    nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hy),
      mul_nonneg (sub_nonneg.mpr hv.2) (sub_nonneg.mpr hm)]
  exact (le_min hm he).trans hs.1
lemma halfGap_nonneg {a : Bool} {m y v E R L : ℝ} {nu : ℕ}
    (hv : v  ∈  Set.Icc 0 1) (hpow : (y*v)^nu=|y*v|^nu)
    (hj : ∀ k<nu,exactJet a k m=0)
    (hE : ∀ s  ∈  Set.uIcc m (m+y*v), |exactJet a nu s-tableHJet a nu s| ≤ E)
    (hR : ∀ s  ∈  Set.uIcc m (m+y*v), |tableHJet a (nu+29) s| ≤ R)
    (hB : ∀ k : Fin 29,L  ≤  powerToBernstein 28 (sourcePower a m y nu) k.val)
    (hc : E/(nu.factorial:ℝ)+R*|y|^29/((nu+29).factorial:ℝ) ≤ L) :
    0  ≤  (if a then 1 else -1)*exactJet a 0 (m+y*v) := by
  have he := halfGap_lower hv (halfGap_absmul hv) hpow hj hE hR hB
  exact (mul_nonneg (by linarith : 0 ≤ L-E/(nu.factorial:ℝ)-R*|y|^29/((nu+29).factorial:ℝ))
    (pow_nonneg (abs_nonneg _) _)).trans he
lemma exactJet_jets_two (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true) :
    ∀ k<2,exactJet a k n.val=0 := by
  intro k hk
  interval_cases k
  · exact exactJet_node_zero a n
  · exact exactJet_node_first a n hn
end SharpPlanar

end OAI
