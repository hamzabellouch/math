import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedPrimes
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedScalarBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSamplingBounds

namespace OAI

/-! # Work and live storage of the counted prime preparation stages -/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedMeasured

variable {n : ℕ}

private theorem scale_power (I : Instance n) (hn : 10000 ≤ n) (j k : ℕ) (hjk : j ≤ k) :
    inputScale I^j ≤ inputScale I^k :=
  Nat.pow_le_pow_right (by unfold inputScale; omega) hjk

private theorem scale_positive (I : Instance n) (k : ℕ) : 1 ≤ inputScale I^k :=
  Nat.one_le_pow _ _ (by unfold inputScale; omega)

theorem nestedAtWidths_bounded (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (x y q : ℕ) (hx : x = R.factorExponents z 0)
    (hy : y = R.factorExponents z 1) (hq : q = R.factorExponents z 2)
    (w : ℕ) (hw : n ≤ w) :
    (nestedAtWidths R z x y q hx hy hq w hw).Bounded
      (4*inputScale I^5*2^((n+1)/2)) (4*inputScale I^5) (4*inputScale I^5) := by
  cases hx
  cases hy
  cases hq
  have h := triplePrime_bounded w n (R.factorExponents z 0) (R.factorExponents z 1)
    (R.factorExponents z 2) ((R.factorExponents_le_n z 0).trans hw)
    ((R.factorExponents_le_n z 1).trans hw) ((R.factorExponents_le_n z 2).trans hw)
  have h0 := WordSeedScalarBounds.factorWork_le I hn (R.factorExponents_le_n z 0)
  have h1 := WordSeedScalarBounds.factorWork_le I hn (R.factorExponents_le_n z 1)
  have h2 := WordSeedScalarBounds.factorWork_le I hn (R.factorExponents_le_n z 2)
  have hs := (WordSeedScalarBounds.scalar_cells_le I hn).1
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hp : inputScale I ≤ inputScale I^5 := by
    simpa only [pow_one] using scale_power I hn 1 5 (by decide)
  have hH := Nat.le_mul_of_pos_right (inputScale I^5)
    (Nat.one_le_two_pow (n := (n+1)/2))
  apply bounded_mono _ h
  · nlinarith only [h0,h1,h2,hu,hp,hH]
  · omega
  · omega

theorem extraAtWidth_bounded (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) (z : RepresentationSetup.Layout n)
    (x : ℕ) (hx : x = R.extraPrimeParameter z) (w : ℕ) (hw : n ≤ w) :
    (extraAtWidth R z x hx (by omega) w hw).Bounded
      (inputScale I^5*2^((n+1)/2)) (inputScale I^5) (inputScale I^5) := by
  cases hx
  exact WordSeedScalarBounds.prime_bounded_scale I hn
    (R.extraPrimeParameter_range z (by omega)).2
    (R.extraPrimeParameter_range z (by omega)).1 w
    ((R.extraPrimeParameter_range z (by omega)).2.trans hw)

private theorem preparation_work (I : Instance n) (hn : 10000 ≤ n)
    (a : WordLayoutPreparation.Layout I) :
    (WordLayoutPreparation.compute I a).1.2 ≤ inputScale I^7*2^((n+1)/2) := by
  let u := inputScale I
  let H := 2^((n+1)/2)
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hnu : n+1 ≤ u := by unfold u inputScale; omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hm : 2^mixerSize n ≤ H := Nat.pow_le_pow_right (by decide) (by unfold mixerSize; omega)
  have hw := WordLayoutPreparation.work I hn a
  have hp : n*n^3+10*(n+1)^2+4*n+7 ≤ u^6 := by
    have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by omega) 3
    have hn2 : (n+1)^2 ≤ u^2 := Nat.pow_le_pow_left hnu 2
    have hn4 : n*n^3 ≤ u^4 := by
      calc
        _ ≤ u*u^3 := Nat.mul_le_mul (by omega) hn3
        _ = _ := by ring
    have h24 : u^2 ≤ u^4 := scale_power I hn 2 4 (by decide)
    have h14 : u ≤ u^4 := by simpa only [pow_one] using scale_power I hn 1 4 (by decide)
    have h46 : 20*u^4 ≤ u^6 := by
      have h20 : 20 ≤ u^2 := by nlinarith only [hu]
      calc
        _ ≤ u^2*u^4 := Nat.mul_le_mul_right _ h20
        _ = _ := by ring
    nlinarith only [hn4,hn2,h24,h14,hnu,hu,h46]
  have h67 : 2*u^6 ≤ u^7 := by
    calc
      _ ≤ u*u^6 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  have hm' := Nat.mul_le_mul_left (u^6) hm
  have hp' := Nat.le_mul_of_pos_right (u^6) hH
  have hlast := Nat.mul_le_mul_right H h67
  change (WordLayoutPreparation.compute I a).1.2 ≤ u^7*H
  change (WordLayoutPreparation.compute I a).1.2 ≤
    n*n^3+10*(n+1)^2+4*n+7+u^6*2^mixerSize n at hw
  nlinarith only [hw,hp,hm',hp',hlast]

private theorem preparation_combine (u C H W D Q V : ℕ) (hu : 10000 ≤ u)
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hW : W ≤ u^7*H) (hD : D ≤ u^10*C+8)
    (hQ : Q ≤ 4*u^5) (hV : V ≤ 4*u^5*H) :
    W+V+2 ≤ u^8*H ∧ D+Q+8 ≤ 2*u^10*C := by
  have h57 : u^5 ≤ u^7 := Nat.pow_le_pow_right (by omega) (by decide)
  have h510 : u^5 ≤ u^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h17 : u ≤ u^7 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 7)
  have h110 : u ≤ u^10 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 10)
  have hm := Nat.le_mul_of_pos_right (u^7) hH
  have hc := Nat.le_mul_of_pos_right (u^10) hC
  have hs : 6*u^7*H ≤ u^8*H := by
    calc
      _ ≤ u*u^7*H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  have hf := Nat.mul_le_mul_right H h57
  constructor
  · nlinarith only [hW,hV,hm,h17,hu,hs,hf]
  · have h510' : 4*u^5+16 ≤ u^10 := by
      have h59 : u^5 ≤ u^9 := Nat.pow_le_pow_right (by omega) (by decide)
      have h19 : u ≤ u^9 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 9)
      have hx : 5*u^9 ≤ u^10 := by
        calc
          _ ≤ u*u^9 := Nat.mul_le_mul_right _ (by omega)
          _ = _ := by ring
      omega
    nlinarith only [hD,hQ,h510',hc]

theorem nestedPrepared_bounded (I : Instance n) (hn : 10000 ≤ n)
    (a : WordLayoutPreparation.Layout I) (w : ℕ) (hw : n ≤ w) :
    (nestedPrepared I a w hw).Bounded (inputScale I^8*2^((n+1)/2))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1)) := by
  have hp := prepareThen_bounded (fun _ => WordLayoutPreparation.compute I a)
    (fun d => nestedFromPrepared I a d w hw) _ _ _ _ _
    (preparation_work I hn a) (WordLayoutPreparation.cells I hn a)
    (fun d => nestedAtWidths_bounded I hn _ a.value _ _ _ _ _ _ w hw)
  have hc := preparation_combine (inputScale I) (compressionDictionaryCapacity n+1)
    (2^((n+1)/2)) _ _ _ _ (by unfold inputScale; omega) (by omega)
    Nat.one_le_two_pow (le_rfl) (le_rfl) (le_rfl) (le_rfl)
  apply bounded_mono _ hp hc.1
  · simpa only [Nat.mul_assoc] using hc.2
  · simpa only [Nat.mul_assoc] using hc.2

theorem extraPrepared_bounded (I : Instance n) (hn : 10000 ≤ n)
    (a : WordLayoutPreparation.Layout I) (w : ℕ) (hw : n ≤ w) :
    (extraPrepared I a (by omega) w hw).Bounded (inputScale I^8*2^((n+1)/2))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1)) := by
  have he (d : WordLayoutPreparation.Prepared I a) :
      (extraFromPrepared I a d (by omega) w hw).Bounded
        (4*inputScale I^5*2^((n+1)/2)) (4*inputScale I^5) (4*inputScale I^5) :=
    bounded_mono _ (extraAtWidth_bounded I hn _ a.value _ (by simpa [RepresentationSetup.samplerPrimeWidths] using (WordLayoutPreparation.fields I a d).2 3) w hw)
      (by
        calc
          _ ≤ 4*(inputScale I^5*2^((n+1)/2)) := Nat.le_mul_of_pos_left _ (by decide)
          _ = _ := by ring) (by omega) (by omega)
  have hp := prepareThen_bounded (fun _ => WordLayoutPreparation.compute I a)
    (fun d => extraFromPrepared I a d (by omega) w hw) _ _ _ _ _
    (preparation_work I hn a) (WordLayoutPreparation.cells I hn a) he
  have hc := preparation_combine (inputScale I) (compressionDictionaryCapacity n+1)
    (2^((n+1)/2)) _ _ _ _ (by unfold inputScale; omega) (by omega)
    Nat.one_le_two_pow (le_rfl) (le_rfl) (le_rfl) (le_rfl)
  apply bounded_mono _ hp hc.1
  · simpa only [Nat.mul_assoc] using hc.2
  · simpa only [Nat.mul_assoc] using hc.2

end LowSpaceSubsetSum.WordSeedMeasured

end

end OAI
