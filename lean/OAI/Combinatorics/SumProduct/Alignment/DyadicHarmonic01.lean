import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.UnitInterval01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section RawSuccessInlineScope6
end RawSuccessInlineScope6

 

 

section RawSuccessInlineScope7
noncomputable section
open scoped BigOperators
open Finset
namespace UnitNeighborhoodCost
open UnitIntervalCounts
variable {J:Type*} [DecidableEq J]

 

omit [DecidableEq J] in
theorem cover_count (T:Finset J) (a:J→ℕ) (R W:ℕ) (hW:0<W) (E:Finset ℕ)
    (hE:E⊆T.biUnion (fun j=>units (a j) R W)) :
    (E.card:ℝ) ≤ T.card*W.totient*((R:ℝ)/W+2) := by
  have hcard:= (card_le_card hE).trans (card_biUnion_le (s:=T) (t:=fun j=>units (a j) R W))
  have hreal:(E.card:ℝ) ≤ ∑ j∈T,((units (a j) R W).card:ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ _ := hreal
    _ ≤ ∑ _j∈T,(W.totient:ℝ)*((R:ℝ)/W+2) :=
      sum_le_sum (fun j _=>card_upper (a j) R W hW)
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

 

omit [DecidableEq J] in
theorem harmonic_cover (T:Finset J) (a:J→ℕ) (R W Y:ℕ) (hW:0<W) (hY:4*W≤Y)
    (E:Finset ℕ) (hsub:E⊆units Y Y W)
    (hE:E⊆T.biUnion (fun j=>units (a j) R W)) :
    (∑ n∈E,(n:ℝ)⁻¹)/(∑ n∈units Y Y W,(n:ℝ)⁻¹) ≤
      4*T.card*((R:ℝ)+2*W)/Y := by
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have hyN:0<Y:=by omega
  have hy:(0:ℝ)<Y:=by exact_mod_cast hyN
  have ht:(0:ℝ)<W.totient:=by exact_mod_cast (Nat.totient_pos.mpr hW)
  have hlow:=card_lower Y Y W hW hY
  have hpos:(0:ℝ)<(units Y Y W).card := lt_of_lt_of_le (by positivity) hlow
  have hp:(units Y Y W).Nonempty:=card_pos.mp (by exact_mod_cast hpos)
  have hc:=cover_count T a R W hW E hE
  calc
    _ ≤ 2*(E.card:ℝ)/(units Y Y W).card :=
      IntervalPrimeRootCount.harmonic_subset _ _ hsub hp Y hyN (by
        intro n hn
        obtain ⟨hn,_⟩:=mem_filter.mp hn
        obtain ⟨hl,hu⟩:=mem_Ico.mp hn
        exact ⟨hl,by omega⟩)
    _ ≤ (2*(T.card:ℝ)*W.totient*((R:ℝ)/W+2))/((Y:ℝ)*W.totient/(2*W)) := by
      apply div_le_div₀ (by positivity) ?_ (by positivity) hlow
      nlinarith [hc]
    _ = _ := by field_simp; ring

end UnitNeighborhoodCost
end
end RawSuccessInlineScope7

 

 

section RawSuccessInlineScope8
noncomputable section
open scoped BigOperators
open Finset
namespace MicrocellBoundary
open UnitIntervalCounts UnitNeighborhoodCost

 

def bad (Y W t H R:ℕ) : Finset ℕ :=
  (units Y Y W).filter (fun p=>t*(p-R)/H ≠ t*(p+R)/H)

lemma cover (Y W t H R:ℕ) (ht:0<t) (hH:0<H) (hR:R≤Y) :
    bad Y W t H R ⊆
      (range (3*Y*t/H+2)).biUnion (fun k=>units (k*H/t-R) (2*R+2) W) := by
  intro p hp
  obtain ⟨hp,hbad⟩:=mem_filter.mp hp
  have hbox:Y≤p ∧ p<Y+Y := mem_Ico.mp (mem_filter.mp hp).1
  have hcop:W.Coprime p := (mem_filter.mp hp).2
  have hmono:t*(p-R)/H≤t*(p+R)/H := Nat.div_le_div_right (Nat.mul_le_mul_left t (by omega))
  have hlt:t*(p-R)/H<t*(p+R)/H := lt_of_le_of_ne hmono hbad
  let k:=t*(p-R)/H+1
  have hk:k≤t*(p+R)/H := by omega
  have hu:k*H≤t*(p+R):=(Nat.le_div_iff_mul_le hH).mp hk
  have hl:t*(p-R)<k*H := by
    simpa only [k,mul_comm H] using Nat.lt_mul_div_succ (t*(p-R)) hH
  have hqlo:p-R≤k*H/t := (Nat.le_div_iff_mul_le ht).mpr (by nlinarith)
  have hqhi:k*H/t≤p+R := Nat.div_le_of_le_mul hu
  have hkl:k≤3*Y*t/H := (Nat.le_div_iff_mul_le hH).mpr (by nlinarith)
  apply mem_biUnion.mpr
  refine ⟨k,mem_range.mpr (by omega),?_⟩
  exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hcop⟩

 

theorem stable {Y W t H R p:ℕ} (hp:p∈units Y Y W) (hg:p∉bad Y W t H R)
    (z:ℕ) (hz:t*(p-R)≤z ∧ z≤t*(p+R)) : z/H=t*p/H := by
  have he:t*(p-R)/H=t*(p+R)/H := by simpa [bad,hp] using hg
  have hzl:=Nat.div_le_div_right (c:=H) hz.1
  have hzu:=Nat.div_le_div_right (c:=H) hz.2
  have hpl:=Nat.div_le_div_right (c:=H) (Nat.mul_le_mul_left t (Nat.sub_le p R))
  have hpu:=Nat.div_le_div_right (c:=H) (Nat.mul_le_mul_left t (show p≤p+R by omega))
  omega

 

theorem harmonic_bad_bound (Y W t H R:ℕ) (hW:0<W) (hY:4*W≤Y)
    (ht:0<t) (hH:0<H) (hR:R≤Y) :
    (∑ p∈bad Y W t H R,(p:ℝ)⁻¹)/(∑ p∈units Y Y W,(p:ℝ)⁻¹) ≤
      24*(t:ℝ)*(R+W+1)/H + 16*((R:ℝ)+W+1)/Y := by
  have hyN:0<Y:=by omega
  have hy:(0:ℝ)<Y:=by exact_mod_cast hyN
  have hh:(0:ℝ)<H:=by exact_mod_cast hH
  have hm:=Nat.mul_div_le (3*Y*t) H
  have hmR:(H:ℝ)*((3*Y*t/H:ℕ):ℝ)≤3*(Y:ℝ)*t:=by exact_mod_cast hm
  have hd:((3*Y*t/H:ℕ):ℝ)≤3*(Y:ℝ)*t/H := (le_div_iff₀ hh).mpr (by nlinarith)
  have hc:=harmonic_cover (range (3*Y*t/H+2)) (fun k=>k*H/t-R) (2*R+2) W Y hW hY
    (bad Y W t H R) (filter_subset _ _) (cover Y W t H R ht hH hR)
  simp only [card_range,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hc
  calc
    _ ≤ 4*(((3*Y*t/H:ℕ):ℝ)+2)*(2*(R:ℝ)+2+2*(W:ℝ))/(Y:ℝ) := hc
    _ ≤ 4*(3*(Y:ℝ)*(t:ℝ)/(H:ℝ)+2)*(2*(R:ℝ)+2+2*(W:ℝ))/(Y:ℝ) := by
      gcongr
    _ = _ := by field_simp; ring

end MicrocellBoundary
end
end RawSuccessInlineScope8

 

 

section RawSuccessInlineScope9
noncomputable section
open scoped BigOperators
open Finset
namespace DyadicHarmonicBoundary
open UnitIntervalCounts MicrocellBoundary

def mass (A B W:ℕ) : ℝ := ∑ n∈Ico A B,if W.Coprime n then (n:ℝ)⁻¹ else 0
def badMass (A B W t H R:ℕ) : ℝ :=
  ∑ n∈Ico A B,if W.Coprime n ∧ t*(n-R)/H≠t*(n+R)/H then (n:ℝ)⁻¹ else 0

lemma mass_units (Y W:ℕ) : mass Y (Y+Y) W=∑ n∈units Y Y W,(n:ℝ)⁻¹ := by
  simp only [mass,units,sum_filter]
lemma badMass_units (Y W t H R:ℕ) : badMass Y (Y+Y) W t H R=
    ∑ n∈bad Y W t H R,(n:ℝ)⁻¹ := by
  simp only [badMass,bad,units,sum_filter,←ite_and]

lemma mass_nonneg (A B W:ℕ) : 0 ≤ mass A B W := by unfold mass; positivity
lemma badMass_nonneg (A B W t H R:ℕ) : 0 ≤ badMass A B W t H R := by unfold badMass; positivity

lemma mass_mono {A B C W:ℕ} (h:B ≤ C) : mass A B W ≤ mass A C W :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl h) (fun _ _ _=>by positivity)
lemma badMass_mono {A B C W t H R:ℕ} (h:B ≤ C) : badMass A B W t H R ≤ badMass A C W t H R :=
  sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl h) (fun _ _ _=>by positivity)

lemma dyadic_lower (Y W:ℕ) (hW:0<W) (hY:4*W ≤ Y) :
    (W.totient:ℝ)/(4*W) ≤ mass Y (Y+Y) W := by
  have hyN:0<Y:=by omega
  have hy:(0:ℝ)<Y:=by exact_mod_cast hyN
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have hcard:=card_lower Y Y W hW hY
  rw [mass_units]
  calc
    _ = ((Y:ℝ)*W.totient/(2*W))/(2*Y) := by field_simp; norm_num
    _  ≤  ((units Y Y W).card:ℝ)/(2*Y) := div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ _n∈units Y Y W,(2*(Y:ℝ))⁻¹ := by simp; ring
    _  ≤  _ := sum_le_sum (by
      intro n hn
      have hn':Y ≤ n ∧ n<Y+Y:=mem_Ico.mp (mem_filter.mp hn).1
      have hn0:(0:ℝ)<n:=by exact_mod_cast (hyN.trans_le hn'.1)
      apply inv_anti₀ hn0
      exact_mod_cast (show n ≤ 2*Y by omega))

lemma dyadic_upper (Y W:ℕ) (hW:0<W) (hY:0<Y) :
    mass Y (Y+Y) W ≤ (W.totient:ℝ)/W+2*W.totient/Y := by
  have hy:(0:ℝ)<Y:=by exact_mod_cast hY
  rw [mass_units]
  calc
    _  ≤  ∑ _n∈units Y Y W,(Y:ℝ)⁻¹ := sum_le_sum (by
      intro n hn
      apply inv_anti₀ hy
      exact_mod_cast (mem_Ico.mp (mem_filter.mp hn).1).1)
    _ = ((units Y Y W).card:ℝ)/Y := by simp; ring
    _  ≤  ((W.totient:ℝ)*((Y:ℝ)/W+2))/Y := div_le_div_of_nonneg_right (card_upper Y Y W hW) hy.le
    _ = _ := by field_simp

lemma dyadic_sum (X K:ℕ) (f:ℕ→ℝ) :
    ∑ k∈range K, ∑ n∈Ico (X*2^k) (X*2^(k+1)),f n =
      ∑ n∈Ico X (X*2^K),f n := by
  induction K with
  | zero=>simp
  | succ K ih=>
    rw [sum_range_succ,ih]
    apply sum_Ico_consecutive
    · have h:=Nat.one_le_pow K 2 (by omega)
      nlinarith
    · rw [pow_succ,←mul_assoc]
      omega

 

theorem dyadic_transfer (X W t H R:ℕ) (hW:0<W) (hX:4*W ≤ X)
    (ε:ℝ) (he:0 ≤ ε)
    (hlocal:∀ k:ℕ,badMass (X*2^k) (X*2^k+X*2^k) W t H R  ≤ 
      ε*mass (X*2^k) (X*2^k+X*2^k) W) :
    badMass X (X^2) W t H R / mass X (X^2) W  ≤  7*ε := by
  have hxN:0<X:=by omega
  have hx:(0:ℝ)<X:=by exact_mod_cast hxN
  have hw:(0:ℝ)<W:=by exact_mod_cast hW
  have ht:(0:ℝ)<W.totient:=by exact_mod_cast (Nat.totient_pos.mpr hW)
  have hx2:2 ≤ X:=by omega
  let K:=Nat.log 2 X+1
  have hKlo:X<2^K := Nat.lt_pow_succ_log_self (by omega) X
  have hKup:2^K ≤ 2*X := by
    have hh:=Nat.pow_log_le_self 2 hxN.ne'
    simp only [K,pow_succ]
    omega
  have hends:X^2 ≤ X*2^K ∧ X*2^K ≤ 2*X^2 := by constructor <;> nlinarith
  have hfirst:X+X ≤ X^2:=by nlinarith
  have hlow:(W.totient:ℝ)/(4*W) ≤ mass X (X^2) W :=
    (dyadic_lower X W hW hX).trans (mass_mono hfirst)
  have hm:0< mass X (X^2) W:=lt_of_lt_of_le (by positivity) hlow
  have htail:mass (X^2) (X^2+X^2) W ≤ 6*mass X (X^2) W := by
    have hs:=dyadic_upper (X^2) W hW (by positivity)
    have hb:(W.totient:ℝ)/W+2*W.totient/(X^2:ℕ) ≤ 6*((W.totient:ℝ)/(4*W)) := by
      have hxx:(4:ℝ)*W ≤ (X^2:ℕ):=by exact_mod_cast (show 4*W ≤ X^2 by nlinarith)
      have hdiv:2*(W.totient:ℝ)/(X^2:ℕ) ≤ (W.totient:ℝ)/(2*W) := by
        calc
          _ ≤ 2*(W.totient:ℝ)/(4*W) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hxx
          _ = _ := by ring
      linear_combination hdiv
    exact hs.trans (hb.trans (mul_le_mul_of_nonneg_left hlow (by norm_num)))
  have hcover:mass X (X*2^K) W ≤ 7*mass X (X^2) W := by
    calc
      _  ≤  mass X (X^2+X^2) W := mass_mono (by omega)
      _ = mass X (X^2) W+mass (X^2) (X^2+X^2) W := by
        symm
        exact sum_Ico_consecutive _ (by nlinarith) (by omega)
      _  ≤  _ := by linarith
  have hsum:badMass X (X*2^K) W t H R ≤ ε*mass X (X*2^K) W := by
    unfold badMass mass
    rw [←dyadic_sum X K,←dyadic_sum X K,Finset.mul_sum]
    apply sum_le_sum
    intro k _
    have hend:X*2^(k+1)=X*2^k+X*2^k:=by rw [pow_succ]; ring
    rw [hend]
    exact hlocal k
  apply (div_le_iff₀ hm).mpr
  calc
    _  ≤  badMass X (X*2^K) W t H R:=badMass_mono hends.1
    _  ≤  ε*mass X (X*2^K) W:=hsum
    _  ≤  ε*(7*mass X (X^2) W):=mul_le_mul_of_nonneg_left hcover he
    _ = _:=by ring

end DyadicHarmonicBoundary

end
end RawSuccessInlineScope9
end

end OAI
