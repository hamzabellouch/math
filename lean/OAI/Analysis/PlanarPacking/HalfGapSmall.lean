import OAI.Analysis.PlanarPacking.HalfGapTypes

namespace OAI

namespace SharpPlanar
lemma analytic_two_cap (a : Bool) (n : Node) (hn : n.val≠1 ∨ a=true)
    {N : ℕ} {y v Y E R L : ℝ}
    (hv : v ∈ Set.Icc 0 1) (hy : |y| ≤ Y)
    (hseg : ∀ s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v), (N:ℝ) ≤ s)
    (herr : ∀ s ∈ Set.uIcc (n.val:ℝ) (n.val+y*v),
      |exactJet a 2 s-tableHJet a 2 s|/2 < E)
    (hB : ∀ k : Fin 29,L ≤ powerToBernstein 28 (sourcePower a n.val y 2) k.val)
    (hcap : taylorEnvelope 31 N*Y^29/((31:ℕ).factorial:ℝ) < R)
    (hr : E+R ≤ L) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (n.val+y*v) := by
  apply halfGap_nonneg_Y (E := 2*E) (R := taylorEnvelope 31 N) (Y := Y) hv
    ((halfGap_absmul hv).trans hy) (by rw [sq_abs]) (exactJet_jets_two a n hn)
  · intro s hs
    have hh := herr s hs
    linarith
  · intro s hs
    exact table_jet_rat a 31 N (hseg s hs)
  · exact hB
  · norm_num [Nat.factorial] at hcap ⊢
    linarith
lemma analytic_first_left {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(18:ℝ)/100 ≤ powerToBernstein 28 (sourcePower true 1 (-1/2) 2) k.val) :
    0 ≤ exactJet true 0 (1+(-1/2)*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 1 (1+(-1/2)*v)) : (1:ℝ)/2 ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap true firstNode (Or.inr rfl) (N := 0) (y := -1/2)
    (Y := (1:ℝ)/2) (E := 11/1000) (R := 1/1000) (L := 18/100) hv (by norm_num)
    (fun s hss => by have h := hs s (by simpa only [firstNode,Nat.cast_one] using hss); norm_num; linarith)
    (fun s hss => error_two_cap true (hs s (by simpa only [firstNode,Nat.cast_one] using hss))) (by simpa only [firstNode,Nat.cast_one] using hB) taylor_cap1 (by norm_num)
  simpa [firstNode] using hh
lemma analytic_first_right_true {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(18:ℝ)/100 ≤ powerToBernstein 28 (sourcePower true 1 1 2) k.val) :
    0 ≤ exactJet true 0 (1+1*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 1 (1+1*v)) : (1:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap true firstNode (Or.inr rfl) (N := 1) (y := 1)
    (Y := (1:ℝ)) (E := 11/1000) (R := 1/1000) (L := 18/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [firstNode,Nat.cast_one] using hss))
    (fun s hss => error_two_cap true (by have h := hs s (by simpa only [firstNode,Nat.cast_one] using hss); linarith)) (by simpa only [firstNode,Nat.cast_one] using hB) taylor_cap3 (by norm_num)
  simpa [firstNode] using hh
lemma analytic_first_right_false {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(18:ℝ)/100 ≤ powerToBernstein 28 (sourcePower false 1 1 1) k.val) :
    0 ≤ -exactJet false 0 (1+1*v) := by
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 1 (1+1*v)) : (1:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hz : ∀ k<1,exactJet false k 1=0 := by
    intro k hk; have he : k=0 := by omega
    rw [he]; simpa only [firstNode,Nat.cast_one] using exactJet_node_zero false firstNode
  have hh := halfGap_nonneg_Y (a := false) (E := 11/1000)
    (R := taylorEnvelope 30 1) (Y := 1) hv
    (by simpa using halfGap_absmul (y := (1:ℝ)) hv)
    (by simp [abs_of_nonneg hv.1]) hz
    (fun s hss => (error_one_cap false (by linarith [hs s hss])).le)
    (fun s hss => table_jet_rat false 30 1 (by simpa using hs s hss)) hB
    (by have hh := taylor_cap2; norm_num [Nat.factorial] at hh ⊢; linarith)
  simpa using hh
lemma analytic_3_left (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 3 (-1) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (3+(-1)*v) := by
  let n : Node := ⟨3,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 3 (3+(-1)*v)) : (2:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 2) (y := -1)
    (Y := (1:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap4 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_3_right (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 3 (1/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (3+(1/2)*v) := by
  let n : Node := ⟨3,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 3 (3+(1/2)*v)) : (3:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 3) (y := 1/2)
    (Y := (1/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap5 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_4_left (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 4 (-1/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (4+(-1/2)*v) := by
  let n : Node := ⟨4,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 4 (4+(-1/2)*v)) : (3:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 3) (y := -1/2)
    (Y := (1/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap5 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
lemma analytic_4_right (a : Bool) {v : ℝ} (hv : v ∈ Set.Icc 0 1)
    (hB : ∀ k : Fin 29,(2:ℝ)/100 ≤ powerToBernstein 28 (sourcePower a 4 (3/2) 2) k.val) :
    0 ≤ (if a then 1 else -1)*exactJet a 0 (4+(3/2)*v) := by
  let n : Node := ⟨4,by decide +kernel⟩
  have hs (s : ℝ) (hss : s ∈ Set.uIcc 4 (4+(3/2)*v)) : (4:ℝ) ≤ s :=
    halfGap_segment_lower hv (by norm_num) (by norm_num) hss
  have hh := analytic_two_cap a n (Or.inl (by decide)) (N := 4) (y := 3/2)
    (Y := (3/2:ℝ)) (E := 2/1000) (R := 1/1000) (L := 2/100) hv (by norm_num)
    (fun s hss => by simpa using hs s (by simpa only [n,Nat.cast_ofNat] using hss))
    (fun s hss => error_large_cap a (by have h := hs s (by simpa only [n,Nat.cast_ofNat] using hss); linarith)) (by simpa only [n,Nat.cast_ofNat] using hB) taylor_cap6 (by norm_num)
  simpa only [n,Nat.cast_ofNat] using hh
end SharpPlanar

end OAI
