import OAI.Analysis.StrictMeans.LatticeEuler

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

def latticeBox (N M : ℕ) : Set Lattice := {v | |(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)}

def latticeTaxicab (v : Lattice) : ℝ := |((ofLex v).1:ℝ)|+|((ofLex v).2:ℝ)|

lemma latticeTaxicab_nonneg (v : Lattice) : 0≤latticeTaxicab v := add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma latticeBox_finite (N M : ℕ) : (latticeBox N M).Finite := by
  have he : latticeBox N M=ofLex ⁻¹' ((Icc (-(N:ℤ)) N) ×ˢ (Icc (-(M:ℤ)) M)) := by
    ext v
    change (|(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)) ↔
      ((-(N:ℤ)≤(ofLex v).1 ∧ (ofLex v).1≤(N:ℤ)) ∧
       (-(M:ℤ)≤(ofLex v).2 ∧ (ofLex v).2≤(M:ℤ)))
    simp only [abs_le]
  rw [he]
  exact ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).preimage ofLex.injective.injOn

lemma outside_box_ascent {N M : ℕ} {v : Lattice} (hv : v∉latticeBox N M) :
    ∃ w, (w=v+ex ∨ w=v+ey ∨ w=v-ex ∨ w=v-ey) ∧ w∉latticeBox N M ∧
      latticeTaxicab v<latticeTaxicab w := by
  have hpos {i : ℤ} {n : ℕ} (hi : (n:ℤ) < |i|) :
      (0 ≤ i ∧ (n:ℤ) < i) ∨ (i < 0 ∧ i < -(n:ℤ)) := by
    rcases le_or_gt 0 i with h|h
    · exact Or.inl ⟨h,by simpa [abs_of_nonneg h] using hi⟩
    · exact Or.inr ⟨h,by rw [abs_of_neg h] at hi; omega⟩
  rcases not_and_or.mp hv with hx|hy
  · have hi := hpos (lt_of_not_ge hx)
    rcases hi with ⟨hi,hiN⟩|⟨hi,hiN⟩
    · refine ⟨v+ex,Or.inl rfl,?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_add,ex,ofLex_toLex,Prod.fst_add,Prod.snd_add]
        rw [abs_of_nonneg (by omega : 0≤(ofLex v).1+1)]
        omega
      · have hi' : (0:ℝ)≤(ofLex v).1 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_add,ex,ofLex_toLex,Prod.fst_add,Prod.snd_add,
          Int.cast_add,Int.cast_one,add_zero]
        rw [abs_of_nonneg hi',abs_of_nonneg (by linarith : (0:ℝ)≤(ofLex v).1+1)]
        linarith
    · refine ⟨v-ex,Or.inr (Or.inr (Or.inl rfl)),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_sub,ex,ofLex_toLex,Prod.fst_sub,Prod.snd_sub]
        rw [abs_of_neg (by omega : (ofLex v).1-1<0)]
        omega
      · have hi' : ((ofLex v).1:ℝ)<0 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_sub,ex,ofLex_toLex,Prod.fst_sub,Prod.snd_sub,
          Int.cast_sub,Int.cast_one,sub_zero]
        rw [abs_of_neg hi',abs_of_neg (by linarith : ((ofLex v).1:ℝ)-1<0)]
        linarith
  · have hi := hpos (lt_of_not_ge hy)
    rcases hi with ⟨hi,hiN⟩|⟨hi,hiN⟩
    · refine ⟨v+ey,Or.inr (Or.inl rfl),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_add,ey,ofLex_toLex,Prod.fst_add,Prod.snd_add]
        rw [abs_of_nonneg (by omega : 0≤(ofLex v).2+1)]
        omega
      · have hi' : (0:ℝ)≤(ofLex v).2 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_add,ey,ofLex_toLex,Prod.fst_add,Prod.snd_add,
          Int.cast_add,Int.cast_one,add_zero]
        rw [abs_of_nonneg hi',abs_of_nonneg (by linarith : (0:ℝ)≤(ofLex v).2+1)]
        linarith
    · refine ⟨v-ey,Or.inr (Or.inr (Or.inr rfl)),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_sub,ey,ofLex_toLex,Prod.fst_sub,Prod.snd_sub]
        rw [abs_of_neg (by omega : (ofLex v).2-1<0)]
        omega
      · have hi' : ((ofLex v).2:ℝ)<0 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_sub,ey,ofLex_toLex,Prod.fst_sub,Prod.snd_sub,
          Int.cast_sub,Int.cast_one,sub_zero]
        rw [abs_of_neg hi',abs_of_neg (by linarith : ((ofLex v).2:ℝ)-1<0)]
        linarith

lemma box_sublevel_index {u : Lattice → ℝ} {N M : ℕ} {c : ℝ}
    (hne : {v | v∈latticeBox N M ∧ u v≤c}.Nonempty)
    (hstar : ∀ v, v∈latticeBox N M → u v≤c →
      ∀ w∈meshStar ex ey v, w∈latticeBox N M)
    (ha : ∀ v∈latticeBox N M,
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    ∀ S : Finset Lattice, (∀ v, v∈S ↔ v∈latticeBox N M ∧ u v≤c) →
      1≤∑ v∈S, heightIndex u ex ey v := by
  classical
  obtain ⟨B,hB⟩ := (latticeBox_finite N M).image u |>.bddAbove
  let D := max B c+1
  let w : Lattice → ℝ := fun v=>if v∈latticeBox N M then u v else D+latticeTaxicab v
  have hlow (v : Lattice) : w v≤c ↔ v∈latticeBox N M ∧ u v≤c := by
    by_cases hv : v∈latticeBox N M
    · simp [w,hv]
    · have hb : c<D+latticeTaxicab v := by
        have := latticeTaxicab_nonneg v
        dsimp [D]; linarith [le_max_right B c]
      simp [w,hv,not_le.mpr hb]
  have hfin : {v|w v≤c}.Finite := (latticeBox_finite N M).subset (fun v hv=>(hlow v).mp hv |>.1)
  have hne' : {v|w v≤c}.Nonempty := by obtain ⟨v,hv⟩:=hne; exact ⟨v,(hlow v).mpr hv⟩
  have hascent (v : Lattice) : w v<w (v+ex) ∨ w v<w (v+ey) ∨ w v<w (v-ex) ∨ w v<w (v-ey) := by
    by_cases hv : v∈latticeBox N M
    · have hstep (a : Lattice) (ha' : u v<u a) : w v<w a := by
        have hvi : u v≤B := hB ⟨v,hv,rfl⟩
        by_cases hai : a∈latticeBox N M
        · simpa [w,hv,hai] using ha'
        · simp only [w,ite_eq_left hv,ite_eq_right hai]
          have := latticeTaxicab_nonneg a
          dsimp [D]; linarith [le_max_left B c]
      exact (ha v hv).imp (hstep _) (Or.imp (hstep _) (Or.imp (hstep _) (hstep _)))
    · obtain ⟨a,ha',hai,hn⟩ := outside_box_ascent hv
      have hh : w v<w a := by simpa [w,hv,hai] using add_lt_add_left hn D
      rcases ha' with rfl|rfl|rfl|rfl
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr hh))
  have he := lattice_sublevel_index hfin hne' (fun v _=>hascent v)
  intro S hS
  have hSe : hfin.toFinset=S := by
    ext v
    exact hfin.mem_toFinset.trans ((hlow v).trans (hS v).symm)
  rw [hSe] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro v hv
  apply heightIndex_congr_star
  intro a ha'
  have hai := hstar v ((hS v).mp hv).1 ((hS v).mp hv).2 a ha'
  simp [w,hai]

end
end StrictInverseFirstPower.Grid

end

end OAI
