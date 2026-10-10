import OAI.Analysis.PlanarPacking.SignCaps
import OAI.Analysis.PlanarPacking.RationalEnvelopes
import OAI.Analysis.PlanarPacking.HalfGapAnalytic

namespace OAI

namespace SharpPlanar
lemma halfGap_nonneg_Y {a : Bool} {m y v Y E R L : ℝ} {nu : ℕ}
    (hv : v  ∈  Set.Icc 0 1) (hy : |y*v|  ≤  Y) (hpow : (y*v)^nu=|y*v|^nu)
    (hj : ∀ k<nu,exactJet a k m=0)
    (hE : ∀ s  ∈  Set.uIcc m (m+y*v), |exactJet a nu s-tableHJet a nu s| ≤ E)
    (hR : ∀ s  ∈  Set.uIcc m (m+y*v), |tableHJet a (nu+29) s| ≤ R)
    (hB : ∀ k : Fin 29,L  ≤  powerToBernstein 28 (sourcePower a m y nu) k.val)
    (hc : E/(nu.factorial:ℝ)+R*Y^29/((nu+29).factorial:ℝ) ≤ L) :
    0  ≤  (if a then 1 else -1)*exactJet a 0 (m+y*v) := by
  have he := halfGap_lower hv hy hpow hj hE hR hB
  exact (mul_nonneg (by linarith : 0 ≤ L-E/(nu.factorial:ℝ)-R*Y^29/((nu+29).factorial:ℝ))
    (pow_nonneg (abs_nonneg _) _)).trans he
lemma segment_bound {m y v s Y : ℝ} (hv : v  ∈  Set.Icc 0 1) (hy : |y|  ≤  Y)
    (hs : s  ∈  Set.uIcc m (m+y*v)) : m-Y  ≤  s := by
  apply halfGap_segment_lower hv (by linarith [(abs_nonneg y).trans hy]) _ hs
  have hyy: -Y ≤ y := (abs_le.mp hy).1
  linarith
lemma analytic_large (a : Bool) (n : Node) (hn : 7 ≤ n.val) {y v : ℝ}
    (hy : |y| ≤ 3/2) (hv : v  ∈  Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(9:ℝ)/1000  ≤  powerToBernstein 28 (sourcePower a n.val y 2) k.val) :
    0  ≤  (if a then 1 else -1)*exactJet a 0 (n.val+y*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v)) : 5 ≤ s := by
    have h:=segment_bound hv hy hss
    have hn' : (7:ℝ) ≤ n.val := by exact_mod_cast hn
    linarith
  apply halfGap_nonneg_Y (E := 4/1000) (R := taylorEnvelope 31 5) (Y := 3/2) hv
    ((halfGap_absmul hv).trans hy) (by rw [sq_abs])
    (exactJet_jets_two a n (Or.inl (by omega)))
  · intro s hss
    have h:=error_large_cap a (by linarith [hs s hss] : (2:ℝ) ≤ s)
    linarith
  · intro s hss
    exact table_jet_rat a 31 5 (hs s hss)
  · exact hB
  · have hh:=taylor_cap7
    norm_num [Nat.factorial] at hh ⊢
    linarith
lemma analytic_zero {v : ℝ} (hv : v  ∈  Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(37:ℝ)/50  ≤  powerToBernstein 28 (sourcePower true 0 (1/2) 0) k.val) :
    (7:ℝ)/10  ≤  exactJet true 0 (0+(1/2)*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 0 (0+(1/2)*v)) : 0 ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have he := halfGap_lower (a := true) (E := 4/1000) (R := taylorEnvelope 29 0)
    (Y := 1/2) hv (by simpa using halfGap_absmul (y := (1:ℝ)/2) hv)
    (by simp : ((1/2)*v)^0=|(1/2)*v|^0) (by omega : ∀ k<0,exactJet true k 0=0)
    (fun s hss => (error_zero_cap true (hs s hss)).le)
    (fun s hss => table_jet_rat true 29 0 (by simpa using hs s hss)) hB
  have hc:=taylor_cap0
  norm_num [Nat.factorial] at he hc
  simp only [zero_add]
  linarith
end SharpPlanar

end OAI
