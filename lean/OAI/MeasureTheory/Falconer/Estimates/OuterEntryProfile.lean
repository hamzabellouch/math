import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses
import OAI.MeasureTheory.Falconer.Estimates.ActualOuterMasks

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem outer_entry_profile_bounds {δ β lam kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10) (hlam : 0 ≤ lam)
    (hlamδ : lam < δ/1000) (hkap : 0 < kap) (hkapβ : 1000000*kap < β)
    (N : ℕ) (hN : 400 ≤ N) (hlarge : 2 ≤ β*(N:ℝ))
    (Q : Fin 2 → DyadicSquare) (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ)
    (B : ℕ) (hprof : ∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) :
    let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
    let c := outerEntry (mass 0) (mass 1) N β
    let q := sourcePolicyBlock N kap
    c < N ∧ β*(N:ℝ)/2 ≤ (c:ℝ) ∧ (c:ℝ) < (N:ℝ)/4 ∧
    kap*N ≤ (c:ℝ) ∧ 2*c ≤ N ∧ c+100*q < N ∧
    (∀ t, c ≤ t → t ≤ N → β-1/(N:ℝ) ≤ min (A 0 t) (A 1 t)) ∧
    min (height (A 0) 0 c) (height (A 1) 0 c)-
      (potential (A 0) c N (10*q)+potential (A 1) c N (10*q))/2 ≤ -β+5*lam+2/(N:ℝ) := by
  let A := fun l (t : ℕ) => mass l t-(t:ℝ)/N
  let c := outerEntry (mass 0) (mass 1) N β
  let q := sourcePolicyBlock N kap
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hβpos : 0 < β := by linarith only [hβ, hlam, hlamδ]
  have hs := outerEntry_spec (mass 0) (mass 1) N (hprof 0).zero (hprof 1).zero hβpos.le
  have hAN (l : Fin 2) : β < A l N := by
    have hh := ((hprof l).envelope N le_rfl).1
    have hid : δ*(N:ℝ)/(N:ℝ) = δ := by field_simp
    rw [hid] at hh
    dsimp only [A]
    linarith
  have hstep (t : ℕ) (ht : t < N) :
      min (A 0 (t+1)) (A 1 (t+1)) ≤ min (A 0 t) (A 1 t)+1/(N:ℝ) := by
    have hstepSide (l : Fin 2) : A l (t+1) ≤ A l t+1/(N:ℝ) := by
      have hh := (hprof l).adjusted (t:ℝ) ((t+1:ℕ):ℝ) (Nat.cast_nonneg _) (Nat.cast_le.mpr ht.le)
        (Nat.cast_nonneg _) (Nat.cast_le.mpr (by omega))
      have ht' : ((t+1:ℕ):ℝ)-(t:ℝ) = 1 := by push_cast; ring
      rw [ht',abs_one] at hh
      have hh' := (abs_le.mp hh).2
      dsimp only [A]
      linarith
    exact min_step (A 0) (A 1) (hstepSide 0) (hstepSide 1)
  have htail := last_crossing_tail (fun t => min (A 0 t) (A 1 t)) hs.1 hs.2.1
    (lt_min (hAN 0) (hAN 1)) (by positivity : 0 ≤ 1/(N:ℝ)) hs.2.2 hstep
  have hlower (l : Fin 2) : δ*((c:ℝ)/(N:ℝ))-5*lam ≤ A l c := by
    simpa only [mul_div_assoc,A] using ((hprof l).envelope c hs.1).1
  have hdepth := entry_depth_bounds (fun t => min (A 0 t) (A 1 t)) hNpos hδ hβ hlamδ hlarge
    htail.1 hs.2.1 (hs.2.2 (c+1) (by omega) (by omega))
    (le_min (hlower 0) (hlower 1))
    ((min_le_left _ _).trans ((hprof 0).envelope (c+1) (by omega)).2)
  have hkc : kap*N ≤ (c:ℝ) := by
    have hk : kap ≤ β/2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hk) hNpos.le]
  have hc2 : 2*c ≤ N := by
    have hc2' : (2:ℝ)*c ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) c]
    exact_mod_cast hc2'
  have hqR : (q:ℝ) < kap*N+1 := Nat.ceil_lt_add_one (by positivity)
  have hκsmall : kap < 1/1000 := by linarith
  have hN400 : (400:ℝ) ≤ N := by exact_mod_cast hN
  have hw : c+100*q < N := by
    have hh : (c:ℝ)+100*(q:ℝ) < N := by
      nlinarith [mul_nonneg (show 0 ≤ 1/1000-kap by linarith) hNpos.le]
    exact_mod_cast hh
  have hqpos : 0 < q := sourcePolicyBlock_pos (by omega) hkap
  have hlow (l : Fin 2) (t : ℕ) (ht : t ≤ c) : -5*lam ≤ A l t := by
    have hh := ((hprof l).envelope t (ht.trans hs.1)).1
    have hp : 0 ≤ δ*(t:ℝ)/(N:ℝ) := by positivity
    dsimp only [A]
    linarith
  have hg := outer_profile_gain (A 0) (A 1) (d := 5*lam) (by omega : 0 < 10*q)
    (by omega : c+10*q ≤ N) hs.2.1 (by simpa only [neg_mul] using hlow 0) (by simpa only [neg_mul] using hlow 1) htail.2
  refine ⟨htail.1,hdepth.1,hdepth.2,hkc,hc2,hw,htail.2,?_⟩
  dsimp only
  rw [outer_exponent_identity] at hg
  convert hg using 1; ring

end PlanarFalconer

end OAI
