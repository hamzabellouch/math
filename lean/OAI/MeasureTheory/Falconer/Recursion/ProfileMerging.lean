import OAI.MeasureTheory.Falconer.Recursion.ProfileCellFamily
import OAI.MeasureTheory.Falconer.Fourier.ProfileMergeCutoff

namespace OAI

/-! Finite recursive absorption of low-slope profile cells. -/
namespace Falconer
open Set

theorem merge_profile_cells {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {H η m ε s t : ℝ} (hH : 0 < H) (hη : 0 < η) (hm : 0 < m)
    (hε : 0 ≤ ε) (hst : s < t) (hf0 : f 0 = 0)
    (hlower : ∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x) :
    ∀ (S : List (ℝ × ℝ)) (b : ℝ), 0 ≤ b → b ≤ m →
      ProfileCellFamily f H (η*H) η m b S →
      ∃ R : List (ℝ × ℝ), StructuredProfilePieces f (η*H) (2*η) s b R ∧
        (S.map Prod.snd).sum-η*H*(S.length : ℝ)-ε*m/(t-s) ≤ (R.map Prod.snd).sum := by
  let r := η*H
  let q := ε*m/(t-s)
  have hr : 0 < r := mul_pos hη hH
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hε hm.le) (sub_pos.mpr hst).le
  suffices hmain : ∀ n : ℕ, ∀ (S : List (ℝ × ℝ)), S.length = n →
      ∀ b : ℝ, 0 ≤ b → b ≤ m → ProfileCellFamily f H r η m b S →
      ∃ R, StructuredProfilePieces f r (2*η) s b R ∧
        (S.map Prod.snd).sum-r*(S.length : ℝ)-q ≤ (R.map Prod.snd).sum by
    intro S b hb hbm hF
    exact hmain S.length S rfl b hb hbm hF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn b hb hbm hF
    rcases List.eq_nil_or_concat S with he | ⟨P,c,he⟩
    · subst S
      refine ⟨[],StructuredProfilePieces.nil _ _ _ _ _,?_⟩
      simpa using neg_nonpos.mpr hq
    · rw [he] at hn hF ⊢
      simp only [List.concat_eq_append] at hn hF ⊢
      have hc : c ∈ P++[c] := by simp
      have hcB := hF.bounds c hc
      have hcpos : 0 < c.2 := hr.trans_le hcB.2.2.1
      have hPlt : P.length < n := by
        have hh : P.length+1 = n := by simpa only [List.length_append,List.length_singleton] using hn
        omega
      have hPO := (List.pairwise_append.mp hF.ordered).1
      have hcross : ∀ d ∈ P, d.1+H ≤ c.1 := by
        intro d hd
        exact (List.pairwise_append.mp hF.ordered).2.2 d hd c (by simp)
      have hPF : ProfileCellFamily f H r η m c.1 P := by
        refine ⟨hPO,?_,?_⟩
        · intro d hd
          have hdB := hF.bounds d (by simp [hd])
          exact ⟨hdB.1,hdB.2.1,hdB.2.2.1,hdB.2.2.2.1,
            (add_le_add le_rfl hdB.2.2.2.1).trans (hcross d hd)⟩
        · intro d hd
          exact hF.linear d (by simp [hd])
      have hclin := hF.active_linear hη hH hc
      by_cases hs : s ≤ intervalSecantSlope f c.1 c.2
      · obtain ⟨R,hR,hlen⟩ := ih P.length hPlt P rfl c.1 hcB.1 (by linarith [hcB.2.1]) hPF
        refine ⟨R++[c],hR.append_interval c le_rfl hcB.2.2.2.2 hcB.2.2.1 hcB.1
          (Or.inl ⟨hs,hclin⟩) hcpos.le,?_⟩
        simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,
          List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
        nlinarith
      · have hslow : intervalSecantSlope f c.1 c.2 < s := lt_of_not_ge hs
        let D := c.1+c.2
        have hD : 0 < D := by dsimp [D]; linarith [hcB.1]
        have hSD : ∀ d ∈ P++[c], d.1+d.2 ≤ D ∧ 0 ≤ d.2 := by
          intro d hd
          have hdB := hF.bounds d hd
          refine ⟨?_,hr.le.trans hdB.2.2.1⟩
          rcases List.mem_append.mp hd with hd | hd
          · have hdc := hcross d hd
            dsimp [D]
            linarith [hdB.2.2.2.1]
          · have hed : d = c := by simpa only [List.mem_singleton] using hd
            subst d
            exact le_rfl
        by_cases hcut : D ≤ q
        · have hsum := ordered_interval_length_le hD.le hF.actual_ordered (by
            intro d hd
            exact ⟨(hF.bounds d hd).1,hSD d hd⟩)
          refine ⟨[],StructuredProfilePieces.nil _ _ _ _ _,?_⟩
          simp only [List.map_nil,List.sum_nil]
          have hrcount : 0 ≤ r*((P++[c]).length : ℝ) := mul_nonneg hr.le (by positivity)
          linarith
        · have hwhole : s*D < f D := by
            have hlow := hlower D ⟨hD.le,hcB.2.2.2.2.trans hbm⟩
            have hqD : ε*m < D*(t-s) := (div_lt_iff₀ (sub_pos.mpr hst)).mp (lt_of_not_ge hcut)
            nlinarith
          have hc0 : 0 < c.1 := by
            by_contra hh
            have he0 : c.1 = 0 := le_antisymm (le_of_not_gt hh) hcB.1
            have hs' := (div_lt_iff₀ hcpos).mp hslow
            change (f (c.1+c.2)-f c.1)/c.2 < s at hslow
            rw [he0,hf0,zero_add] at hs'
            dsimp [D] at hwhole
            rw [he0,zero_add] at hwhole
            linarith
          have hterm : ∀ x ∈ Icc c.1 D,
              -(2*η)*(D-c.1) ≤ intervalSecantError f c.1 (D-c.1) x := by
            intro x hx
            have hh := (abs_le.mp (hclin x hx)).1
            simpa only [D,add_sub_cancel_left,neg_mul] using hh
          have hslow' : intervalSecantSlope f c.1 (D-c.1) < s := by
            simpa only [D,add_sub_cancel_left] using hslow
          obtain ⟨u,hu,hend,hw,huerr⟩ := exists_superlinear_merge_above_cutoff hf.continuous
            (show c.1 < D by dsimp [D]; linarith) hc0
            (hcB.2.2.2.2.trans hbm) hst (by positivity : 0 ≤ 2*η) hf0 hlower
            (lt_of_not_ge hcut) hslow' hterm
          let Q := clipProfilePrefix u r (P++[c])
          have hQF : ProfileCellFamily f H r η m u Q := hF.clip
          have hQlt : Q.length < n := by
            rw [← hn]
            exact clipProfilePrefix_length_lt hr (fun d hd => (hF.bounds d hd).2.2.1)
              ⟨c,hc,hu.2.le⟩
          obtain ⟨R,hR,hlen⟩ := ih Q.length hQlt Q rfl u hu.1.le
            (hu.2.le.trans (by linarith [hcB.2.1])) hQF
          have hdu : 0 < D-u := by dsimp [D]; linarith [hu.2]
          have heSlope : intervalSecantSlope f u (D-u) = s := by
            unfold intervalSecantSlope
            rw [show u+(D-u) = D by ring]
            exact (div_eq_iff hdu.ne').2 hend
          have hpiece : ∀ x ∈ Icc u (u+(D-u)),
              -(2*η)*(D-u) ≤ intervalSecantError f u (D-u) x := by
            intro x hx
            rw [show u+(D-u) = D by ring] at hx
            have hh := huerr x hx
            unfold intervalSecantError
            rw [heSlope]
            linarith
          have hnew := hR.append_interval (b := b) (u,D-u) le_rfl
            (by dsimp; linarith [hcB.2.2.2.2])
            (by dsimp [D] at hw; dsimp; linarith [hcB.2.2.1]) hu.1.le
            (Or.inr ⟨heSlope,hpiece⟩) hdu.le
          refine ⟨R++[(u,D-u)],hnew,?_⟩
          have hloss := clipProfilePrefix_loss hr.le (hu.2.le.trans (by dsimp [D]; linarith))
            hF.actual_ordered hSD
          have hcount : ((Q.length : ℕ) : ℝ)+1 ≤ ((P++[c]).length : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (show Q.length < (P++[c]).length by simpa [hn] using hQlt)
          have hcost := mul_le_mul_of_nonneg_left hcount hr.le
          simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
          change (P++[c] |>.map Prod.snd).sum ≤ (Q.map Prod.snd).sum+(D-u)+r at hloss
          simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton] at hloss
          nlinarith

end Falconer

end OAI
