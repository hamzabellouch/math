import OAI.Combinatorics.MatchingPSD.CellDecoder

namespace OAI

namespace MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder

lemma interpolation_trace_error_bound (d : ℕ) {c L r η m : ℝ}
    (hc : 0 ≤ c) (hL : 1 ≤ L)
    (hw : weightMass d L ≤ c/L^2) (hnorm : r*η*m ≤ 1/L) :
    weightMass d L*(2*(d:ℝ)*L)+r*(6+weightMass d L)*η*m ≤
      ((2*(d:ℝ)+1)*c+6)/L := by
  have hLp : 0 < L := by linarith
  have hwc : weightMass d L ≤ c := by
    apply hw.trans
    exact (div_le_self hc (by nlinarith : 1 ≤ L^2))
  have h1 := mul_le_mul_of_nonneg_right hw (show 0 ≤ 2*(d:ℝ)*L by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 6+weightMass d L by linarith [weightMass_nonneg d L])
  have h3 := mul_le_mul_of_nonneg_right (show 6+weightMass d L ≤ 6+c by linarith) (show 0 ≤ 1/L by positivity)
  calc
    _ = weightMass d L*(2*(d:ℝ)*L)+(6+weightMass d L)*(r*η*m) := by ring
    _ ≤ (c/L^2)*(2*(d:ℝ)*L)+(6+c)*(1/L) := add_le_add h1 (h2.trans h3)
    _ = _ := by field_simp; ring

lemma sqrt_error_small {q D L ε : ℝ} (hq : 0 ≤ q) (hL : 0 < L) (hε : 0 ≤ ε)
    (he : ε ≤ (q*D+1)/L) (hn : 16*q^2*(q*D+1) ≤ L) :
    q*Real.sqrt ε ≤ 1/4 := by
  have heL : ε*L ≤ q*D+1 := (le_div_iff₀ hL).mp he
  have hmult := mul_le_mul_of_nonneg_left heL (show 0 ≤ 16*q^2 by positivity)
  have h16 : 16*q^2*ε ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hL).mp
    nlinarith [hmult.trans hn]
  have hsq : (q*Real.sqrt ε)^2 = q^2*ε := by rw [mul_pow, Real.sq_sqrt hε]
  have hn0 : 0 ≤ q*Real.sqrt ε := mul_nonneg hq (Real.sqrt_nonneg _)
  nlinarith

lemma normalized_eta {r m L : ℝ} (hr : 0 < r) (hm : 0 < m) (hL : 0 < L) :
    r*(1/(r*m*L))*m = 1/L := by
  field_simp [hr.ne', hm.ne', hL.ne']

lemma conditional_cell_lower_bound (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧
    ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 1 ≤ q → 2*l*d ≤ s → 1 ≤ l → 0 < r →
    ∀ m : ℝ, 0 < m →
    ∀ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) → (∀ M, (B M).PosSemidef) →
      (∀ a y, (Q a y).trace ≤ m) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      (∀ a y M, (Q a y*B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M-1) →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤
        (1/((r:ℝ)*m*(2*l)))^2 →
      16*(q:ℝ)^2*((q:ℝ)*D+1) ≤ 2*l →
      (2:ℝ)^q/2 ≤ r := by
  obtain ⟨d,H,hd,hgood⟩ := good_cell_polynomials K
  obtain ⟨c,hc,hw⟩ := weightMass_bound d
  let D := (2*(d:ℝ)+1)*c+6
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨d,H,hd,D,hD,?_⟩
  intro s q l r hH hs hq hsl hl hr m hm Q B hQ hB htrQ htrB hpair hnum hn
  let L : ℝ := 2*l
  have hL : 1 ≤ L := by dsimp [L]; exact_mod_cast (by omega : 1 ≤ 2*l)
  have hLp : 0 < L := by linarith
  have hrp : 0 < (r:ℝ) := by exact_mod_cast hr
  let η := 1/((r:ℝ)*m*L)
  let δ := 1/(L*m)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨a,P,hP,happrox⟩ := hgood s q l r hH hs hsl B hB htrB η hη hnum
  let e := weightMass d L*(2*(d:ℝ)*L)+(r:ℝ)*(6+weightMass d L)*η*m
  have hw0 := weightMass_nonneg d L
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have he : e ≤ D/L := interpolation_trace_error_bound d hc.le hL
    (hw L hL) (le_of_eq (normalized_eta hrp hm hLp))
  have hδm : δ*m=1/L := by dsimp [δ]; field_simp [hLp.ne', hm.ne']
  have hε : 0 ≤ (q:ℝ)*e+δ*m := by positivity
  have heps : (q:ℝ)*e+δ*m ≤ ((q:ℝ)*D+1)/L := by
    have heq := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg q)
    rw [hδm]
    calc
      _ ≤ (q:ℝ)*(D/L)+1/L := add_le_add heq (le_refl (1/L))
      _ = _ := by ring
  have hsmall := sqrt_error_small (Nat.cast_nonneg q) hLp hε heps hn
  exact cell_decoder hs hq hsl (Q a) (fun M => B (Pairing.relabel a M))
    (hQ a) (fun M => hB _) (hpair a) P hP hη hδ (by omega)
      (htrQ a) happrox hε hsmall

end MatchingInterpolation

end OAI
