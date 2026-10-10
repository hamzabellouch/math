import OAI.Analysis.PlanarPacking.Quadrature

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def phase12 (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/6))
lemma phase12_eq_pow (n : ℕ) : phase12 n = phase12 1^n := by
  rw [phase12,phase12,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
lemma phase12_periodic (n : ℕ) : phase12 (n+12) = phase12 n := by
  unfold phase12
  have he : Complex.I*Real.pi*(((n+12:ℕ):ℂ)/6) =
      Complex.I*Real.pi*((n:ℂ)/6)+2*Real.pi*Complex.I := by push_cast; ring
  rw [he,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]
lemma phase12_mod (n : ℕ) : phase12 (n%12) = phase12 n :=
  (show Function.Periodic phase12 12 from phase12_periodic).map_mod_nat n

def phaseBase : CBox := (piI.scale 1 6).exp 1
lemma phaseBase_contains : phaseBase.Contains (phase12 1) := by
  have hi := CBox.contains_scale piI_contains 1 6 (by norm_num)
  have he := CBox.contains_exp hi 1 (by decide +kernel)
  unfold phaseBase
  convert he using 1
  unfold phase12
  congr 1
  norm_num
  ring

def phaseBox (n : ℕ) : CBox := phaseBase.powBin 4 (n%12)
lemma phaseBox_contains (n : ℕ) : (phaseBox n).Contains (phase12 n) := by
  have hh := CBox.contains_powBin phaseBase_contains 4 (n%12) (by omega)
  rw [← phase12_eq_pow,phase12_mod] at hh
  exact hh

def coefficientBox : ℕ → CBox
  | 0 => CBox.rat 5 1 0 1
  | 1 => ⟨RBox.rat (-1) 1,bBounds.scale 2 1⟩
  | 2 => ⟨RBox.rat 1 1,bBounds.scale 2 1⟩
  | 3 => CBox.rat (-2) 1 0 1
  | 4 => ⟨RBox.rat (-1) 2,bBounds⟩
  | 5 => ⟨RBox.rat (-1) 1,bBounds.scale (-2) 1⟩
  | 6 => CBox.rat 1 1 0 1
  | _ => CBox.rat 0 1 0 1
lemma coefficientBox_contains (n : ℕ) : (coefficientBox n).Contains (Pcoeff n) := by
  have hb : bBounds.Contains b := bBounds_contains
  have hp := RBox.contains_scale hb 2 1 (by norm_num)
  have hm := RBox.contains_scale hb (-2) 1 (by norm_num)
  have h0 (m k : ℤ) (hk : 0 < k) := CBox.contains_rat m k 0 1 hk (by norm_num)
  have hr (m k : ℤ) (hk : 0 < k) := RBox.contains_rat m k hk
  rcases n with _|_|_|_|_|_|_|n
  · simpa [coefficientBox,Pcoeff] using h0 5 1 (by norm_num)
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr 1 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hp
  · simpa [coefficientBox,Pcoeff] using h0 (-2) 1 (by norm_num)
  · constructor
    · convert hr (-1) 2 (by norm_num) using 1 <;> norm_num [coefficientBox,Pcoeff]
    · simpa [coefficientBox,Pcoeff] using hb
  · constructor
    · simpa [coefficientBox,Pcoeff] using hr (-1) 1 (by norm_num)
    · simpa [coefficientBox,Pcoeff] using hm
  · simpa [coefficientBox,Pcoeff] using h0 1 1 (by norm_num)
  · simpa [coefficientBox,Pcoeff] using h0 0 1 (by norm_num)

noncomputable def spectralCoefficient (n l : ℕ) : ℂ :=
  Pcoeff l*Complex.exp (Complex.I*Real.pi*(l:ℂ)/6*n)
def spectralCoefficientBox (n l : ℕ) : CBox := (coefficientBox l).mul (phaseBox (l*n))
lemma spectralCoefficientBox_contains (n l : ℕ) :
    (spectralCoefficientBox n l).Contains (spectralCoefficient n l) := by
  have hh := CBox.contains_mul (coefficientBox_contains l) (phaseBox_contains (l*n))
  unfold spectralCoefficientBox
  convert hh using 1
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

def zeroBox : CBox := ⟨⟨0,0⟩,⟨0,0⟩⟩
lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
def boxSum (f : ℕ → CBox) : ℕ → CBox
  | 0 => zeroBox
  | N+1 => (boxSum f N).add (f N)
lemma boxSum_contains {f : ℕ → CBox} {g : ℕ → ℂ} (N : ℕ)
    (h : ∀ n < N, (f n).Contains (g n)) :
    (boxSum f N).Contains (∑ n ∈ Finset.range N, g n) := by
  induction N with
  | zero => simpa [boxSum] using zeroBox_contains
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact CBox.contains_add (ih (fun n hn => h n (by omega))) (h N (by omega))
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

noncomputable def basisAlpha (n j : ℕ) : ℂ := ∑ l ∈ Finset.Icc (j+1) 6, spectralCoefficient n l
noncomputable def basisBeta (n j : ℕ) : ℂ :=
  ∑ l ∈ Finset.Icc (j+1) 6, ((l:ℂ)/6)*spectralCoefficient n l

def alphaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then spectralCoefficientBox n l else zeroBox) 7
def betaBox (n j : ℕ) : CBox := boxSum
  (fun l => if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox) 7
lemma sum_seven_Icc (f : ℕ → ℂ) (j : ℕ) :
    (∑ l ∈ Finset.range 7, if j<l then f l else 0) = ∑ l ∈ Finset.Icc (j+1) 6, f l := by
  rw [← Finset.sum_filter]
  congr 1
  ext l
  simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
  omega
lemma alphaBox_contains (n j : ℕ) : (alphaBox n j).Contains (basisAlpha n j) := by
  have hh (l : ℕ) : (if j<l then spectralCoefficientBox n l else zeroBox).Contains
      (if j<l then spectralCoefficient n l else 0) := by
    split_ifs <;> first | exact spectralCoefficientBox_contains n l | exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs
lemma betaBox_contains (n j : ℕ) : (betaBox n j).Contains (basisBeta n j) := by
  have hh (l : ℕ) : (if j<l then (spectralCoefficientBox n l).scale l 6 else zeroBox).Contains
      (if j<l then ((l:ℂ)/6)*spectralCoefficient n l else 0) := by
    split_ifs
    · simpa only [Int.cast_natCast,Int.cast_ofNat] using CBox.contains_scale (spectralCoefficientBox_contains n l) l 6 (by norm_num)
    · exact zeroBox_contains
  have hs := boxSum_contains 7 (fun l _ => hh l)
  rwa [sum_seven_Icc] at hs

lemma u_factored (n j : ℕ) (t : ℝ) : u n j t =
    -2*(Real.pi:ℂ)^2*Complex.exp (-Complex.I*Real.pi*t*n)*
      (basisBeta n j-(t:ℂ)*basisAlpha n j) := by
  unfold u basisBeta basisAlpha spectralCoefficient
  congr 1
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring
lemma v_factored (n j : ℕ) (t : ℝ) : v n j t =
    2*Complex.I*Real.pi*Complex.exp (-Complex.I*Real.pi*t*n)*basisAlpha n j := by
  unfold v basisAlpha spectralCoefficient
  rfl

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

def CBox.powFast (a : CBox) : ℕ → ℕ → CBox
  | 0, _ => CBox.rat 1 1 0 1
  | k+1,n => if n=0 then CBox.rat 1 1 0 1 else if n=1 then a else
      let b := a.powFast k (n/2)
      let b2 := b.mul b
      if n%2=0 then b2 else b2.mul a

lemma CBox.contains_powFast {a : CBox} {z : ℂ} (hz : a.Contains z) (k n : ℕ)
    (hn : n < 2^k) : (a.powFast k n).Contains (z^n) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    simpa [CBox.powFast] using CBox.contains_rat 1 1 0 1 (by norm_num) (by norm_num)
  | succ k ih =>
    have hd : n/2 < 2^k := by rw [pow_succ] at hn; omega
    have he : n%2+2*(n/2)=n := Nat.mod_add_div n 2
    simp only [CBox.powFast]
    split_ifs with h0 h1 h2
    · subst n
      simpa using CBox.contains_rat 1 1 0 1 (by norm_num) (by norm_num)
    · subst n
      simpa using hz
    · have hh := CBox.contains_mul (ih (n/2) hd) (ih (n/2) hd)
      have ht : n/2+n/2=n := by omega
      simpa only [← pow_add,ht] using hh
    · have hh := CBox.contains_mul (CBox.contains_mul (ih (n/2) hd) (ih (n/2) hd)) hz
      have ht : n/2+n/2+1=n := by omega
      simpa only [← pow_add,pow_one,← pow_succ,ht] using hh

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma spectralCoefficient_eq_phase (n l : ℕ) :
    spectralCoefficient n l = Pcoeff l*phase12 (l*n) := by
  unfold spectralCoefficient phase12
  congr 2
  push_cast
  ring
lemma spectralCoefficient_mod (n l : ℕ) :
    spectralCoefficient (n%12) l = spectralCoefficient n l := by
  simp only [spectralCoefficient_eq_phase]
  rw [← phase12_mod (l*(n%12)),← phase12_mod (l*n)]
  congr 2
  simp only [Nat.mul_mod, Nat.mod_mod]
lemma basisAlpha_mod (n j : ℕ) : basisAlpha (n%12) j = basisAlpha n j := by
  unfold basisAlpha
  simp only [spectralCoefficient_mod]
lemma basisBeta_mod (n j : ℕ) : basisBeta (n%12) j = basisBeta n j := by
  unfold basisBeta
  simp only [spectralCoefficient_mod]

def uBox (p : PointBox) (a b : CBox) (n : ℕ) : CBox :=
  (((rcast (piBounds.mul piBounds)).scale (-2) 1).mul (p.direct.powFast 7 n)).mul
    (b.add (((rcast p.t).mul a).neg))
def vBox (p : PointBox) (a : CBox) (n : ℕ) : CBox :=
  ((piI.scale 2 1).mul (p.direct.powFast 7 n)).mul a
lemma direct_power_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {n : ℕ}
    (hn : n < 128) : (p.direct.powFast 7 n).Contains
      (Complex.exp (-Complex.I*Real.pi*t*n)) := by
  have he := CBox.contains_powFast hp.2.2.2.1 7 n hn
  rw [← Complex.exp_nat_mul] at he
  convert he using 1
  congr 1
  ring
lemma uBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {a b : CBox}
    {n j : ℕ} (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j))
    (hn : n < 128) : (uBox p a b n).Contains (u n j t) := by
  have hpi := CBox.contains_scale (rcast_contains
    (RBox.contains_mul piBounds_contains piBounds_contains)) (-2) 1 (by norm_num)
  have he := CBox.contains_mul (CBox.contains_mul hpi (direct_power_contains hp hn))
    (CBox.contains_add hb (CBox.neg_contains (CBox.contains_mul (rcast_contains hp.1) ha)))
  unfold uBox
  convert he using 1
  rw [u_factored]
  push_cast
  ring
lemma vBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {a : CBox}
    {n j : ℕ} (ha : a.Contains (basisAlpha n j)) (hn : n < 128) :
    (vBox p a n).Contains (v n j t) := by
  have he := CBox.contains_mul
    (CBox.contains_mul (CBox.contains_scale piI_contains 2 1 (by norm_num))
      (direct_power_contains hp hn)) ha
  unfold vBox
  convert he using 1
  rw [v_factored]
  push_cast
  ring

lemma pointLambda_eq (t : ℝ) : pointLambda t = lambda t := by
  unfold pointLambda lambda b h
  push_cast
  rfl
lemma pointZ_eq (t : ℝ) : pointZ t = z t := by
  unfold pointZ z B h
  push_cast
  rfl

def kernel0Box (p : PointBox) (m : ℕ) : CBox := p.lam.mul (p.quarter.powFast 9 (4*m))
lemma kernel0Box_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {m : ℕ}
    (hm : m < 128) : (kernel0Box p m).Contains
      (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) := by
  have he := CBox.contains_powFast hp.2.2.2.2 9 (4*m) (by omega)
  rw [← Complex.exp_nat_mul] at he
  have hz := CBox.contains_mul hp.2.1 he
  unfold kernel0Box
  convert hz using 1
  rw [pointLambda_eq,pointZ_eq]
  congr 2
  push_cast
  ring

noncomputable def basisFunction (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then v n j t else u n j t
noncomputable def basisMoment (d e : Bool) (n j m : ℕ) (t : ℝ) : ℂ :=
  basisFunction d n j t * (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) *
    (if e then Complex.I*Real.pi*z t else 1)
def basisFunctionBox (p : PointBox) (a b : CBox) (n : ℕ) (d : Bool) : CBox :=
  if d then vBox p a n else uBox p a b n
def basisMomentBox (p : PointBox) (a b : CBox) (n m : ℕ) (d e : Bool) : CBox :=
  let k := (basisFunctionBox p a b n d).mul (kernel0Box p m)
  if e then k.mul (piI.mul p.z) else k
lemma basisFunctionBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {a b : CBox}
    {n j : ℕ} (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j))
    (hn : n < 128) (d : Bool) :
    (basisFunctionBox p a b n d).Contains (basisFunction d n j t) := by
  cases d
  · exact uBox_contains hp ha hb hn
  · exact vBox_contains hp ha hn
lemma basisMomentBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {a b : CBox}
    {n j m : ℕ} (ha : a.Contains (basisAlpha n j)) (hb : b.Contains (basisBeta n j))
    (hn : n < 128) (hm : m < 128) (d e : Bool) :
    (basisMomentBox p a b n m d e).Contains (basisMoment d e n j m t) := by
  have hk := CBox.contains_mul (basisFunctionBox_contains hp ha hb hn d)
    (kernel0Box_contains hp hm)
  cases e
  · simpa [basisMomentBox,basisMoment] using hk
  · have hh := CBox.contains_mul hk (CBox.contains_mul piI_contains hp.2.2.1)
    simpa only [basisMomentBox,basisMoment,pointZ_eq,ite_true] using hh

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerIntervals

def finSum : {N : ℕ} → (Fin N → CBox) → CBox
  | 0, _ => zeroBox
  | N+1, f => (f 0).add (finSum (fun i : Fin N => f i.succ))
lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma sum_fin_square (N : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin N, ∑ k : Fin N, f (N*i.val+k.val)) =
      ∑ v : Fin (N*N), f v.val := by
  calc
    _ = ∑ x : Fin N × Fin N, f (N*x.1.val+x.2.val) :=
      (Fintype.sum_prod_type _).symm
    _ = _ := by
      convert (finProdFinEquiv.sum_comp (fun v : Fin (N*N) => f v.val)) using 1
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      exact Nat.add_comm _ _

noncomputable def momentRuleValue (t : ℕ → ℕ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (d e : Bool) : ℂ :=
  ∑ j : Fin 6, (1/6:ℂ)*∑ v : Fin 256, (w v.val:ℂ)*
    basisMoment d e n j.val m (t j.val v.val)

def momentRuleBox (p : Fin 6 → Fin 16 → Fin 16 → PointBox)
    (w : Fin 16 → Fin 16 → RBox) (a b : Fin 6 → CBox)
    (n m : ℕ) (d e : Bool) : CBox :=
  finSum (fun j => (finSum (fun i => finSum (fun k =>
    (rcast (w i k)).mul (basisMomentBox (p j i k) (a j) (b j) n m d e)))).scale 1 6)

lemma momentRuleBox_contains
    {p : Fin 6 → Fin 16 → Fin 16 → PointBox} {t : ℕ → ℕ → ℝ}
    {w : Fin 16 → Fin 16 → RBox} {wr : ℕ → ℝ} {a b : Fin 6 → CBox}
    {n m : ℕ} (d e : Bool)
    (hp : ∀ j i k, (p j i k).Contains (t j.val (16*i.val+k.val)))
    (hw : ∀ i k, (w i k).Contains (wr (16*i.val+k.val)))
    (ha : ∀ j, (a j).Contains (basisAlpha n j.val))
    (hb : ∀ j, (b j).Contains (basisBeta n j.val))
    (hn : n < 128) (hm : m < 128) :
    (momentRuleBox p w a b n m d e).Contains (momentRuleValue t wr n m d e) := by
  unfold momentRuleBox momentRuleValue
  apply finSum_contains
  intro j
  rw [← sum_fin_square 16 (fun v => (wr v:ℂ)*basisMoment d e n j.val m (t j.val v))]
  have hh := finSum_contains (fun i => finSum_contains (fun k =>
    CBox.contains_mul (rcast_contains (hw i k))
      (basisMomentBox_contains (hp j i k) (ha j) (hb j) hn hm d e)))
  simpa only [Int.cast_one,Int.cast_ofNat] using CBox.contains_scale hh 1 6 (by norm_num)

end SharpPlanar.IntegerBasis

namespace SharpPlanar.IntegerAlpha
open IntegerIntervals IntegerBasis
def a0_0 : CBox := ⟨⟨(-2500000000000000000000000000000),(-2500000000000000000000000000000)⟩,⟨2598076211353315940260000000000,2598076211353315940330000000000⟩⟩
lemma a0_0_contains : a0_0.Contains (basisAlpha 0 0) := by
  have he : alphaBox 0 0 = a0_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 0
def b0_0 : CBox := ⟨⟨(-1000000000000000000000000000002),(-999999999999999999999999999998)⟩,⟨(-16666666669),16666666669⟩⟩
lemma b0_0_contains : b0_0.Contains (basisBeta 0 0) := by
  have he : betaBox 0 0 = b0_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 0
def a0_1 : CBox := ⟨⟨(-1500000000000000000000000000000),(-1500000000000000000000000000000)⟩,⟨866025403784438646740000000000,866025403784438646790000000000⟩⟩
lemma a0_1_contains : a0_1.Contains (basisAlpha 0 1) := by
  have he : alphaBox 0 1 = a0_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 1
def b0_1 : CBox := ⟨⟨(-833333333333333333333333333335),(-833333333333333333333333333332)⟩,⟨(-288675134594812882270000000002),(-288675134594812882239999999998)⟩⟩
lemma b0_1_contains : b0_1.Contains (basisBeta 0 1) := by
  have he : betaBox 0 1 = b0_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 1
def a0_2 : CBox := ⟨⟨(-2500000000000000000000000000000),(-2500000000000000000000000000000)⟩,⟨(-866025403784438646780000000000),(-866025403784438646750000000000)⟩⟩
lemma a0_2_contains : a0_2.Contains (basisAlpha 0 2) := by
  have he : alphaBox 0 2 = a0_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 2
def b0_2 : CBox := ⟨⟨(-1166666666666666666666666666668),(-1166666666666666666666666666666)⟩,⟨(-866025403784438646776666666668),(-866025403784438646753333333332)⟩⟩
lemma b0_2_contains : b0_2.Contains (basisBeta 0 2) := by
  have he : betaBox 0 2 = b0_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 2
def a0_3 : CBox := ⟨⟨(-500000000000000000000000000000),(-500000000000000000000000000000)⟩,⟨(-866025403784438646780000000000),(-866025403784438646750000000000)⟩⟩
lemma a0_3_contains : a0_3.Contains (basisAlpha 0 3) := by
  have he : alphaBox 0 3 = a0_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 3
def b0_3 : CBox := ⟨⟨(-166666666666666666666666666668),(-166666666666666666666666666666)⟩,⟨(-866025403784438646776666666668),(-866025403784438646753333333332)⟩⟩
lemma b0_3_contains : b0_3.Contains (basisBeta 0 3) := by
  have he : betaBox 0 3 = b0_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 3
def a0_4 : CBox := ⟨⟨0,0⟩,⟨(-1732050807568877293540000000000),(-1732050807568877293520000000000)⟩⟩
lemma a0_4_contains : a0_4.Contains (basisAlpha 0 4) := by
  have he : alphaBox 0 4 = a0_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 4
def b0_4 : CBox := ⟨⟨166666666666666666666666666666,166666666666666666666666666667⟩,⟨(-1443375672974064411283333333334),(-1443375672974064411266666666666)⟩⟩
lemma b0_4_contains : b0_4.Contains (basisBeta 0 4) := by
  have he : betaBox 0 4 = b0_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 4
def a0_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a0_5_contains : a0_5.Contains (basisAlpha 0 5) := by
  have he : alphaBox 0 5 = a0_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 0 5
def b0_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b0_5_contains : b0_5.Contains (basisBeta 0 5) := by
  have he : betaBox 0 5 = b0_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 0 5
def aRow0 : Fin 6 → CBox := ![a0_0,a0_1,a0_2,a0_3,a0_4,a0_5]
lemma aRow0_contains (j : Fin 6) : (aRow0 j).Contains (basisAlpha 0 j.val) := by
  fin_cases j
  · exact a0_0_contains
  · exact a0_1_contains
  · exact a0_2_contains
  · exact a0_3_contains
  · exact a0_4_contains
  · exact a0_5_contains
def bRow0 : Fin 6 → CBox := ![b0_0,b0_1,b0_2,b0_3,b0_4,b0_5]
lemma bRow0_contains (j : Fin 6) : (bRow0 j).Contains (basisBeta 0 j.val) := by
  fin_cases j
  · exact b0_0_contains
  · exact b0_1_contains
  · exact b0_2_contains
  · exact b0_3_contains
  · exact b0_4_contains
  · exact b0_5_contains
def a1_0 : CBox := ⟨⟨(-2500000000000000000073478665491),(-2499999999999999999933155933893)⟩,⟨866025403784438646695878312244,866025403784438646839277975147⟩⟩
lemma a1_0_contains : a1_0.Contains (basisAlpha 1 0) := by
  have he : alphaBox 1 0 = a1_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 0
def b1_0 : CBox := ⟨⟨(-511966128287415137693146900620),(-511966128287415137604977905556)⟩,⟨(-43633798654),47214926849⟩⟩
lemma b1_0_contains : b1_0.Contains (basisBeta 1 0) := by
  have he : betaBox 1 0 = b1_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 0
def a1_1 : CBox := ⟨⟨(-767949192431122706537425858341),(-767949192431122706410976860631)⟩,⟨(-133974596215561353295379180206),(-133974596215561353172527005361)⟩⟩
lemma a1_1_contains : a1_1.Contains (basisAlpha 1 1) := by
  have he : alphaBox 1 1 = a1_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 1
def b1_1 : CBox := ⟨⟨(-223290993692602255437138099428),(-223290993692602255351281393346)⟩,⟨(-166666666666666666708843380729),(-166666666666666666621419236569)⟩⟩
lemma b1_1_contains : b1_1.Contains (basisBeta 1 1) := by
  have he : betaBox 1 1 = b1_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 1
def a1_2 : CBox := ⟨⟨232050807568877293479774764070,232050807568877293578966769811⟩,⟨(-1866025403784438646813585298464),(-1866025403784438646710196150793)⟩⟩
lemma a1_2_contains : a1_2.Contains (basisAlpha 1 2) := by
  have he : alphaBox 1 2 = a1_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 2
def b1_2 : CBox := ⟨⟨110042339640731077901928774709,110042339640731077978699816801⟩,⟨(-744016935856292431214912086815),(-744016935856292431133975618380)⟩⟩
lemma b1_2_contains : b1_2.Contains (basisBeta 1 2) := by
  have he : betaBox 1 2 = b1_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 2
def a1_3 : CBox := ⟨⟨232050807568877293484086527880,232050807568877293569941772559⟩,⟨133974596215561353192996433472,133974596215561353283222117267⟩⟩
lemma a1_3_contains : a1_3.Contains (basisAlpha 1 3) := by
  have he : alphaBox 1 3 = a1_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 3
def b1_3 : CBox := ⟨⟨110042339640731077904084656614,110042339640731077974187318175⟩,⟨255983064143707568788378779153,255983064143707568862733515650⟩⟩
lemma b1_3_contains : b1_3.Contains (basisBeta 1 3) := by
  have he : betaBox 1 3 = b1_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 3
def a1_4 : CBox := ⟨⟨732050807568877293494743560103,732050807568877293558775086867⟩,⟨999999999999999999967311938286,1000000000000000000039200861018⟩⟩
lemma a1_4_contains : a1_4.Contains (basisAlpha 1 4) := by
  have he : alphaBox 1 4 = a1_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 4
def b1_4 : CBox := ⟨⟨443375672974064411244522678096,443375672974064411300076194380⟩,⟨833333333333333333304589115696,833333333333333333366719344817⟩⟩
lemma b1_4_contains : b1_4.Contains (basisBeta 1 4) := by
  have he : betaBox 1 4 = b1_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 4
def a1_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a1_5_contains : a1_5.Contains (basisAlpha 1 5) := by
  have he : alphaBox 1 5 = a1_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 1 5
def b1_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b1_5_contains : b1_5.Contains (basisBeta 1 5) := by
  have he : betaBox 1 5 = b1_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 1 5
def aRow1 : Fin 6 → CBox := ![a1_0,a1_1,a1_2,a1_3,a1_4,a1_5]
lemma aRow1_contains (j : Fin 6) : (aRow1 j).Contains (basisAlpha 1 j.val) := by
  fin_cases j
  · exact a1_0_contains
  · exact a1_1_contains
  · exact a1_2_contains
  · exact a1_3_contains
  · exact a1_4_contains
  · exact a1_5_contains
def bRow1 : Fin 6 → CBox := ![b1_0,b1_1,b1_2,b1_3,b1_4,b1_5]
lemma bRow1_contains (j : Fin 6) : (bRow1 j).Contains (basisBeta 1 j.val) := by
  fin_cases j
  · exact b1_0_contains
  · exact b1_1_contains
  · exact b1_2_contains
  · exact b1_3_contains
  · exact b1_4_contains
  · exact b1_5_contains
def a2_0 : CBox := ⟨⟨(-2000000000000000000141275204934),(-1999999999999999999869782460702)⟩,⟨(-129743478571),116486523947⟩⟩
lemma a2_0_contains : a2_0.Contains (basisAlpha 2 0) := by
  have he : alphaBox 2 0 = a2_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 0
def b2_0 : CBox := ⟨⟨(-87204526845),82781460593⟩,⟨(-84172586257),73959704406⟩⟩
lemma b2_0_contains : b2_0.Contains (basisBeta 2 0) := by
  have he : betaBox 2 0 = b2_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 0
def a2_1 : CBox := ⟨⟨(-125435175822),118800576441⟩,⟨(-119717716417),107049258927⟩⟩
lemma a2_1_contains : a2_1.Contains (basisAlpha 2 1) := by
  have he : alphaBox 2 1 = a2_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 1
def b2_1 : CBox := ⟨⟨333333333333333333248768811341,333333333333333333414211966783⟩,⟨(-82501625898),72386826902⟩⟩
lemma b2_1_contains : b2_1.Contains (basisBeta 2 1) := by
  have he : betaBox 2 1 = b2_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 1
def a2_2 : CBox := ⟨⟨1999999999999999999898600075218,2000000000000000000099188391653⟩,⟨(-96961970479),93131482739⟩⟩
lemma a2_2_contains : a2_2.Contains (basisAlpha 2 2) := by
  have he : alphaBox 2 2 = a2_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 2
def b2_2 : CBox := ⟨⟨999999999999999999923447228355,1000000000000000000074341238520⟩,⟨(-74916377252),67747568172⟩⟩
lemma b2_2_contains : b2_2.Contains (basisBeta 2 2) := by
  have he : betaBox 2 2 = b2_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 2
def a2_3 : CBox := ⟨⟨(-88236460900),86024927779⟩,⟨(-88338442857),75081488233⟩⟩
lemma a2_3_contains : a2_3.Contains (basisAlpha 2 3) := by
  have he : alphaBox 2 3 = a2_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 3
def b2_3 : CBox := ⟨⟨(-69971039704),67759506583⟩,⟨(-70604613441),58722570919⟩⟩
lemma b2_3_contains : b2_3.Contains (basisBeta 2 3) := by
  have he : betaBox 2 3 = b2_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 3
def a2_4 : CBox := ⟨⟨(-1000000000000000000066880394620),(-999999999999999999937542671626)⟩,⟨(-70273909211),52009472578⟩⟩
lemma a2_4_contains : a2_4.Contains (basisAlpha 2 4) := by
  have he : alphaBox 2 4 = a2_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 4
def b2_4 : CBox := ⟨⟨(-666666666666666666722400328850),(-666666666666666666614618893021)⟩,⟨(-58561591010),43341227149⟩⟩
lemma b2_4_contains : b2_4.Contains (basisBeta 2 4) := by
  have he : betaBox 2 4 = b2_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 4
def a2_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a2_5_contains : a2_5.Contains (basisAlpha 2 5) := by
  have he : alphaBox 2 5 = a2_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 2 5
def b2_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b2_5_contains : b2_5.Contains (basisBeta 2 5) := by
  have he : betaBox 2 5 = b2_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 2 5
def aRow2 : Fin 6 → CBox := ![a2_0,a2_1,a2_2,a2_3,a2_4,a2_5]
lemma aRow2_contains (j : Fin 6) : (aRow2 j).Contains (basisAlpha 2 j.val) := by
  fin_cases j
  · exact a2_0_contains
  · exact a2_1_contains
  · exact a2_2_contains
  · exact a2_3_contains
  · exact a2_4_contains
  · exact a2_5_contains
def bRow2 : Fin 6 → CBox := ![b2_0,b2_1,b2_2,b2_3,b2_4,b2_5]
lemma bRow2_contains (j : Fin 6) : (bRow2 j).Contains (basisBeta 2 j.val) := by
  fin_cases j
  · exact b2_0_contains
  · exact b2_1_contains
  · exact b2_2_contains
  · exact b2_3_contains
  · exact b2_4_contains
  · exact b2_5_contains
def a3_0 : CBox := ⟨⟨(-2500000000000000000101486582202),(-2499999999999999999899776324884)⟩,⟨(-866025403784438646865458496086),(-866025403784438646673967970795)⟩⟩
lemma a3_0_contains : a3_0.Contains (basisAlpha 3 0) := by
  have he : alphaBox 3 0 = a3_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 0
def b3_0 : CBox := ⟨⟨(-511966128287415137698359169417),(-511966128287415137596966210758)⟩,⟨(-49143671478),45580546819⟩⟩
lemma b3_0_contains : b3_0.Contains (basisBeta 3 0) := by
  have he : betaBox 3 0 = b3_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 0
def a3_1 : CBox := ⟨⟨(-767949192431122706553630753239),(-767949192431122706389988770571)⟩,⟨133974596215561353145648246772,133974596215561353319007066240⟩⟩
lemma a3_1_contains : a3_1.Contains (basisAlpha 3 1) := by
  have he : alphaBox 3 1 = a3_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 1
def b3_1 : CBox := ⟨⟨(-223290993692602255440383197923),(-223290993692602255345334951706)⟩,⟨166666666666666666619374118999,166666666666666666711076386324⟩⟩
lemma b3_1_contains : b3_1.Contains (basisBeta 3 1) := by
  have he : betaBox 3 1 = b3_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 1
def a3_2 : CBox := ⟨⟨232050807568877293460419172689,232050807568877293587797743707⟩,⟨1866025403784438646706073138142,1866025403784438646823295408305⟩⟩
lemma a3_2_contains : a3_2.Contains (basisAlpha 3 2) := by
  have he : alphaBox 3 2 = a3_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 2
def b3_2 : CBox := ⟨⟨110042339640731077897633444053,110042339640731077980593886386⟩,⟨744016935856292431139515749456,744016935856292431212505833679⟩⟩
lemma b3_2_contains : b3_2.Contains (basisBeta 3 2) := by
  have he : betaBox 3 2 = b3_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 2
def a3_3 : CBox := ⟨⟨232050807568877293505562439097,232050807568877293556794177625⟩,⟨(-133974596215561353256049960216),(-133974596215561353214581493329)⟩⟩
lemma a3_3_contains : a3_3.Contains (basisAlpha 3 3) := by
  have he : alphaBox 3 3 = a3_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 3
def b3_3 : CBox := ⟨⟨110042339640731077920205077257,110042339640731077965092103345⟩,⟨(-255983064143707568841545799723),(-255983064143707568806432617138)⟩⟩
lemma b3_3_contains : b3_3.Contains (basisBeta 3 3) := by
  have he : betaBox 3 3 = b3_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 3
def a3_4 : CBox := ⟨⟨732050807568877293505562439097,732050807568877293556794177625⟩,⟨(-1000000000000000000016049960216),(-999999999999999999984581493329)⟩⟩
lemma a3_4_contains : a3_4.Contains (basisAlpha 3 4) := by
  have he : alphaBox 3 4 = a3_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 4
def b3_4 : CBox := ⟨⟨443375672974064411253538410591,443375672974064411298425436678⟩,⟨(-833333333333333333348212466389),(-833333333333333333319765950472)⟩⟩
lemma b3_4_contains : b3_4.Contains (basisBeta 3 4) := by
  have he : betaBox 3 4 = b3_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 4
def a3_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a3_5_contains : a3_5.Contains (basisAlpha 3 5) := by
  have he : alphaBox 3 5 = a3_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 3 5
def b3_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b3_5_contains : b3_5.Contains (basisBeta 3 5) := by
  have he : betaBox 3 5 = b3_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 3 5
def aRow3 : Fin 6 → CBox := ![a3_0,a3_1,a3_2,a3_3,a3_4,a3_5]
lemma aRow3_contains (j : Fin 6) : (aRow3 j).Contains (basisAlpha 3 j.val) := by
  fin_cases j
  · exact a3_0_contains
  · exact a3_1_contains
  · exact a3_2_contains
  · exact a3_3_contains
  · exact a3_4_contains
  · exact a3_5_contains
def bRow3 : Fin 6 → CBox := ![b3_0,b3_1,b3_2,b3_3,b3_4,b3_5]
lemma bRow3_contains (j : Fin 6) : (bRow3 j).Contains (basisBeta 3 j.val) := by
  fin_cases j
  · exact b3_0_contains
  · exact b3_1_contains
  · exact b3_2_contains
  · exact b3_3_contains
  · exact b3_4_contains
  · exact b3_5_contains
def a4_0 : CBox := ⟨⟨(-2500000000000000000121818428037),(-2499999999999999999876652611556)⟩,⟨(-2598076211353315940405219613044),(-2598076211353315940185663132651)⟩⟩
lemma a4_0_contains : a4_0.Contains (basisAlpha 4 0) := by
  have he : alphaBox 4 0 = a4_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 0
def b4_0 : CBox := ⟨⟨(-1000000000000000000066894928682),(-999999999999999999940249324168)⟩,⟨(-59517638106),54804404662⟩⟩
lemma b4_0_contains : b4_0.Contains (basisBeta 4 0) := by
  have he : betaBox 4 0 = b4_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 0
def a4_1 : CBox := ⟨⟨(-1500000000000000000100504363592),(-1499999999999999999898985982939)⟩,⟨(-866025403784438646856588603416),(-866025403784438646673705645149)⟩⟩
lemma a4_1_contains : a4_1.Contains (basisAlpha 4 1) := by
  have he : alphaBox 4 1 = a4_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 1
def b4_1 : CBox := ⟨⟨(-833333333333333333396675917941),(-833333333333333333277304886066)⟩,⟨288675134594812882198587530166,288675134594812882306797319245⟩⟩
lemma b4_1_contains : b4_1.Contains (basisBeta 4 1) := by
  have he : betaBox 4 1 = b4_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 1
def a4_2 : CBox := ⟨⟨(-2500000000000000000063234604227),(-2499999999999999999951563554943)⟩,⟨866025403784438646710128961006,866025403784438646810738820671⟩⟩
lemma a4_2_contains : a4_2.Contains (basisAlpha 4 2) := by
  have he : alphaBox 4 2 = a4_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 2
def b4_2 : CBox := ⟨⟨(-1166666666666666666717585998152),(-1166666666666666666628164076734)⟩,⟨866025403784438646720826718307,866025403784438646801612141185⟩⟩
lemma b4_2_contains : b4_2.Contains (basisBeta 4 2) := by
  have he : betaBox 4 2 = b4_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 2
def a4_3 : CBox := ⟨⟨(-500000000000000000063234604227),(-499999999999999999951563554943)⟩,⟨866025403784438646710128961006,866025403784438646810738820671⟩⟩
lemma a4_3_contains : a4_3.Contains (basisAlpha 4 3) := by
  have he : alphaBox 4 3 = a4_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 3
def b4_3 : CBox := ⟨⟨(-166666666666666666717585998152),(-166666666666666666628164076734)⟩,⟨866025403784438646720826718307,866025403784438646801612141185⟩⟩
lemma b4_3_contains : b4_3.Contains (basisBeta 4 3) := by
  have he : betaBox 4 3 = b4_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 3
def a4_4 : CBox := ⟨⟨(-52577572004),37269759365⟩,⟨1732050807568877293484444465820,1732050807568877293566717564422⟩⟩
lemma a4_4_contains : a4_4.Contains (basisAlpha 4 4) := by
  have he : alphaBox 4 4 = a4_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 4
def b4_4 : CBox := ⟨⟨166666666666666666622852023330,166666666666666666697724799471⟩,⟨1443375672974064411237037054850,1443375672974064411305597970352⟩⟩
lemma b4_4_contains : b4_4.Contains (basisBeta 4 4) := by
  have he : betaBox 4 4 = b4_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 4
def a4_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a4_5_contains : a4_5.Contains (basisAlpha 4 5) := by
  have he : alphaBox 4 5 = a4_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 4 5
def b4_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b4_5_contains : b4_5.Contains (basisBeta 4 5) := by
  have he : betaBox 4 5 = b4_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 4 5
def aRow4 : Fin 6 → CBox := ![a4_0,a4_1,a4_2,a4_3,a4_4,a4_5]
lemma aRow4_contains (j : Fin 6) : (aRow4 j).Contains (basisAlpha 4 j.val) := by
  fin_cases j
  · exact a4_0_contains
  · exact a4_1_contains
  · exact a4_2_contains
  · exact a4_3_contains
  · exact a4_4_contains
  · exact a4_5_contains
def bRow4 : Fin 6 → CBox := ![b4_0,b4_1,b4_2,b4_3,b4_4,b4_5]
lemma bRow4_contains (j : Fin 6) : (bRow4 j).Contains (basisBeta 4 j.val) := by
  fin_cases j
  · exact b4_0_contains
  · exact b4_1_contains
  · exact b4_2_contains
  · exact b4_3_contains
  · exact b4_4_contains
  · exact b4_5_contains
def a5_0 : CBox := ⟨⟨1999999999999999999877635444654,2000000000000000000143138855047⟩,⟨(-6000000000000000000129653626530),(-5999999999999999999860633820774)⟩⟩
lemma a5_0_contains : a5_0.Contains (basisAlpha 5 0) := by
  have he : alphaBox 5 0 = a5_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 0
def b5_0 : CBox := ⟨⟨333333333333333333281679955827,333333333333333333394612940415⟩,⟨(-3000000000000000000057347709804),(-2999999999999999999942362123009)⟩⟩
lemma b5_0_contains : b5_0.Contains (basisBeta 5 0) := by
  have he : betaBox 5 0 = b5_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 0
def a5_1 : CBox := ⟨⟨1999999999999999999900418610809,2000000000000000000115053958316⟩,⟨(-4000000000000000000098166012570),(-3999999999999999999887698368482)⟩⟩
lemma a5_1_contains : a5_1.Contains (basisAlpha 5 1) := by
  have he : alphaBox 5 1 = a5_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 1
def b5_1 : CBox := ⟨⟨333333333333333333285477150187,333333333333333333389932124293⟩,⟨(-2666666666666666666718766440810),(-2666666666666666666613539547627)⟩⟩
lemma b5_1_contains : b5_1.Contains (basisBeta 5 1) := by
  have he : betaBox 5 1 = b5_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 1
def a5_2 : CBox := ⟨⟨(-37124060817),48173563696⟩,⟨(-4000000000000000000046156539992),(-3999999999999999999957972277693)⟩⟩
lemma a5_2_contains : a5_2.Contains (basisAlpha 5 2) := by
  have he : alphaBox 5 2 = a5_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 2
def b5_2 : CBox := ⟨⟨(-333333333333333333360370407021),(-333333333333333333299028007247)⟩,⟨(-2666666666666666666701429949950),(-2666666666666666666636964184031)⟩⟩
lemma b5_2_contains : b5_2.Contains (basisBeta 5 2) := by
  have he : betaBox 5 2 = b5_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 2
def a5_3 : CBox := ⟨⟨(-32812297007),39148566444⟩,⟨(-2000000000000000000039574808056),(-1999999999999999999964554009633)⟩⟩
lemma a5_3_contains : a5_3.Contains (basisAlpha 5 3) := by
  have he : alphaBox 5 3 = a5_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 3
def b5_3 : CBox := ⟨⟨(-333333333333333333358214525116),(-333333333333333333303540505873)⟩,⟨(-1666666666666666666698139083982),(-1666666666666666666640255050001)⟩⟩
lemma b5_3_contains : b5_3.Contains (basisBeta 5 3) := by
  have he : betaBox 5 3 = b5_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 3
def a5_4 : CBox := ⟨⟨(-1000000000000000000011456230727),(-999999999999999999984419032961)⟩,⟨(-2000000000000000000021510274410),(-1999999999999999999987626025288)⟩⟩
lemma a5_4_contains : a5_4.Contains (basisAlpha 5 4) := by
  have he : alphaBox 5 4 = a5_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 4
def b5_4 : CBox := ⟨⟨(-1000000000000000000010643814262),(-999999999999999999985918905477)⟩,⟨(-1666666666666666666686096061551),(-1666666666666666666655636393771)⟩⟩
lemma b5_4_contains : b5_4.Contains (basisBeta 5 4) := by
  have he : betaBox 5 4 = b5_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 4
def a5_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a5_5_contains : a5_5.Contains (basisAlpha 5 5) := by
  have he : alphaBox 5 5 = a5_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 5 5
def b5_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b5_5_contains : b5_5.Contains (basisBeta 5 5) := by
  have he : betaBox 5 5 = b5_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 5 5
def aRow5 : Fin 6 → CBox := ![a5_0,a5_1,a5_2,a5_3,a5_4,a5_5]
lemma aRow5_contains (j : Fin 6) : (aRow5 j).Contains (basisAlpha 5 j.val) := by
  fin_cases j
  · exact a5_0_contains
  · exact a5_1_contains
  · exact a5_2_contains
  · exact a5_3_contains
  · exact a5_4_contains
  · exact a5_5_contains
def bRow5 : Fin 6 → CBox := ![b5_0,b5_1,b5_2,b5_3,b5_4,b5_5]
lemma bRow5_contains (j : Fin 6) : (bRow5 j).Contains (basisBeta 5 j.val) := by
  fin_cases j
  · exact b5_0_contains
  · exact b5_1_contains
  · exact b5_2_contains
  · exact b5_3_contains
  · exact b5_4_contains
  · exact b5_5_contains
def a6_0 : CBox := ⟨⟨5499999999999999999950573124464,5500000000000000000049426875520⟩,⟨2598076211353315940219953156515,2598076211353315940388899777253⟩⟩
lemma a6_0_contains : a6_0.Contains (basisAlpha 6 0) := by
  have he : alphaBox 6 0 = a6_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 0
def b6_0 : CBox := ⟨⟨2999999999999999999972565375633,3000000000000000000021992251165⟩,⟨2309401076758503058003309911586,2309401076758503058086116555293⟩⟩
lemma b6_0_contains : b6_0.Contains (basisBeta 6 0) := by
  have he : betaBox 6 0 = b6_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 0
def a6_1 : CBox := ⟨⟨4499999999999999999964623050396,4500000000000000000027213389802⟩,⟨4330127018922193233775664814443,4330127018922193233888474885876⟩⟩
lemma a6_1_contains : a6_1.Contains (basisAlpha 6 1) := by
  have he : alphaBox 6 1 = a6_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 1
def b6_1 : CBox := ⟨⟨2833333333333333333308240363289,2833333333333333333351623336878⟩,⟨2598076211353315940262595187908,2598076211353315940336045740063⟩⟩
lemma b6_1_contains : b6_1.Contains (basisBeta 6 1) := by
  have he : betaBox 6 1 = b6_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 1
def a6_2 : CBox := ⟨⟨3499999999999999999964623050396,3500000000000000000027213389802⟩,⟨2598076211353315940255664814443,2598076211353315940348474885876⟩⟩
lemma a6_2_contains : a6_2.Contains (basisAlpha 6 2) := by
  have he : alphaBox 6 2 = a6_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 2
def b6_2 : CBox := ⟨⟨2499999999999999999974907029956,2500000000000000000018290003544⟩,⟨2020725942163690175755928521242,2020725942163690175822712406729⟩⟩
lemma b6_2_contains : b6_2.Contains (basisBeta 6 2) := by
  have he : betaBox 6 2 = b6_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 2
def a6_3 : CBox := ⟨⟨1499999999999999999977786514278,1500000000000000000014049925928⟩,⟨2598076211353315940264288342065,2598076211353315940330424891370⟩⟩
lemma a6_3_contains : a6_3.Contains (basisAlpha 6 3) := by
  have he : alphaBox 6 3 = a6_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 3
def b6_3 : CBox := ⟨⟨1499999999999999999981488761897,1500000000000000000011708271607⟩,⟨2020725942163690175760240285053,2020725942163690175813687409476⟩⟩
lemma b6_3_contains : b6_3.Contains (basisBeta 6 3) := by
  have he : betaBox 6 3 = b6_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 3
def a6_4 : CBox := ⟨⟨1999999999999999999977786514278,2000000000000000000014049925928⟩,⟨1732050807568877293504288342065,1732050807568877293560424891370⟩⟩
lemma a6_4_contains : a6_4.Contains (basisAlpha 6 4) := by
  have he : alphaBox 6 4 = a6_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 4
def b6_4 : CBox := ⟨⟨1833333333333333333314822095231,1833333333333333333345041604940⟩,⟨1443375672974064411253573618387,1443375672974064411300354076142⟩⟩
lemma b6_4_contains : b6_4.Contains (basisBeta 6 4) := by
  have he : betaBox 6 4 = b6_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 4
def a6_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a6_5_contains : a6_5.Contains (basisAlpha 6 5) := by
  have he : alphaBox 6 5 = a6_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 6 5
def b6_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b6_5_contains : b6_5.Contains (basisBeta 6 5) := by
  have he : betaBox 6 5 = b6_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 6 5
def aRow6 : Fin 6 → CBox := ![a6_0,a6_1,a6_2,a6_3,a6_4,a6_5]
lemma aRow6_contains (j : Fin 6) : (aRow6 j).Contains (basisAlpha 6 j.val) := by
  fin_cases j
  · exact a6_0_contains
  · exact a6_1_contains
  · exact a6_2_contains
  · exact a6_3_contains
  · exact a6_4_contains
  · exact a6_5_contains
def bRow6 : Fin 6 → CBox := ![b6_0,b6_1,b6_2,b6_3,b6_4,b6_5]
lemma bRow6_contains (j : Fin 6) : (bRow6 j).Contains (basisBeta 6 j.val) := by
  fin_cases j
  · exact b6_0_contains
  · exact b6_1_contains
  · exact b6_2_contains
  · exact b6_3_contains
  · exact b6_4_contains
  · exact b6_5_contains
def a7_0 : CBox := ⟨⟨(-2500000000000000000188127804075),(-2499999999999999999818506795302)⟩,⟨866025403784438646567088470640,866025403784438646939490805340⟩⟩
lemma a7_0_contains : a7_0.Contains (basisAlpha 7 0) := by
  have he : alphaBox 7 0 = a7_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 0
def b7_0 : CBox := ⟨⟨(-2821367205045918195798978576537),(-2821367205045918195573646581217)⟩,⟨(-124730856205),103138732310⟩⟩
lemma b7_0_contains : b7_0.Contains (basisBeta 7 0) := by
  have he : betaBox 7 0 = b7_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 0
def a7_1 : CBox := ⟨⟨(-4232050807568877293687926838870),(-4232050807568877293381652874355)⟩,⟨1866025403784438646599525109016,1866025403784438646901953080128⟩⟩
lemma a7_1_contains : a7_1.Contains (basisAlpha 7 1) := by
  have he : alphaBox 7 1 = a7_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 1
def b7_1 : CBox := ⟨⟨(-3110042339640731078048945082336),(-3110042339640731077834170927726)⟩,⟨166666666666666666547341916858,166666666666666666763549111441⟩⟩
lemma b7_1_contains : b7_1.Contains (basisBeta 7 1) := by
  have he : betaBox 7 1 = b7_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 1
def a7_2 : CBox := ⟨⟨(-3232050807568877293670726216459),(-3232050807568877293391709243913)⟩,⟨133974596215561353081318990758,133974596215561353364283934696⟩⟩
lemma a7_2_contains : a7_2.Contains (basisAlpha 7 2) := by
  have he : alphaBox 7 2 = a7_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 2
def b7_2 : CBox := ⟨⟨(-2776709006307397744709878208199),(-2776709006307397744504189717579)⟩,⟨(-410683602522959097958726789228),(-410683602522959097749007270370)⟩⟩
lemma b7_2_contains : b7_2.Contains (basisBeta 7 2) := by
  have he : betaBox 7 2 = b7_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 2
def a7_3 : CBox := ⟨⟨(-3232050807568877293625582950051),(-3232050807568877293422712809995)⟩,⟨(-1866025403784438646880804107600),(-1866025403784438646673592966938)⟩⟩
lemma a7_3_contains : a7_3.Contains (basisAlpha 7 3) := by
  have he : alphaBox 7 3 = a7_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 3
def b7_3 : CBox := ⟨⟨(-2776709006307397744687306574995),(-2776709006307397744519691500620)⟩,⟨(-1410683602522959097939788338407),(-1410683602522959097767945721187)⟩⟩
lemma b7_3_contains : b7_3.Contains (basisBeta 7 3) := by
  have he : betaBox 7 3 = b7_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 3
def a7_4 : CBox := ⟨⟨(-2732050807568877293614925917828),(-2732050807568877293433879495687)⟩,⟨(-1000000000000000000106488602786),(-999999999999999999917614223187)⟩⟩
lemma a7_4_contains : a7_4.Contains (basisAlpha 7 4) := by
  have he : alphaBox 7 4 = a7_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 4
def b7_4 : CBox := ⟨⟨(-2443375672974064411346868553513),(-2443375672974064411193802624415)⟩,⟨(-833333333333333333423578001864),(-833333333333333333263959892020)⟩⟩
lemma b7_4_contains : b7_4.Contains (basisBeta 7 4) := by
  have he : betaBox 7 4 = b7_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 4
def a7_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a7_5_contains : a7_5.Contains (basisAlpha 7 5) := by
  have he : alphaBox 7 5 = a7_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 7 5
def b7_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b7_5_contains : b7_5.Contains (basisBeta 7 5) := by
  have he : betaBox 7 5 = b7_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 7 5
def aRow7 : Fin 6 → CBox := ![a7_0,a7_1,a7_2,a7_3,a7_4,a7_5]
lemma aRow7_contains (j : Fin 6) : (aRow7 j).Contains (basisAlpha 7 j.val) := by
  fin_cases j
  · exact a7_0_contains
  · exact a7_1_contains
  · exact a7_2_contains
  · exact a7_3_contains
  · exact a7_4_contains
  · exact a7_5_contains
def bRow7 : Fin 6 → CBox := ![b7_0,b7_1,b7_2,b7_3,b7_4,b7_5]
lemma bRow7_contains (j : Fin 6) : (bRow7 j).Contains (basisBeta 7 j.val) := by
  fin_cases j
  · exact b7_0_contains
  · exact b7_1_contains
  · exact b7_2_contains
  · exact b7_3_contains
  · exact b7_4_contains
  · exact b7_5_contains
def a8_0 : CBox := ⟨⟨1999999999999999999892284365332,2000000000000000000114350234042⟩,⟨(-90867123064),105889569091⟩⟩
lemma a8_0_contains : a8_0.Contains (basisAlpha 8 0) := by
  have he : alphaBox 8 0 = a8_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 0
def b8_0 : CBox := ⟨⟨1999999999999999999954288696048,2000000000000000000050134370203⟩,⟨(-37247929117),46674396000⟩⟩
lemma b8_0_contains : b8_0.Contains (basisBeta 8 0) := by
  have he : betaBox 8 0 = b8_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 0
def a8_1 : CBox := ⟨⟨(-65003502108),67215035233⟩,⟨(-54738055772),59745537781⟩⟩
lemma a8_1_contains : a8_1.Contains (basisAlpha 8 1) := by
  have he : alphaBox 8 1 = a8_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 1
def b8_1 : CBox := ⟨⟨1666666666666666666628074051475,1666666666666666666708945170401⟩,⟨(-31226417901),38983724115⟩⟩
lemma b8_1_contains : b8_1.Contains (basisBeta 8 1) := by
  have he : betaBox 8 1 = b8_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 1
def a8_2 : CBox := ⟨⟨1999999999999999999959031748932,2000000000000000000047602850445⟩,⟨(-31982309834),45827761593⟩⟩
lemma a8_2_contains : a8_2.Contains (basisAlpha 8 2) := by
  have he : alphaBox 8 2 = a8_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 2
def b8_2 : CBox := ⟨⟨2333333333333333333302752468489,2333333333333333333369074442138⟩,⟨(-23641169255),34344465385⟩⟩
lemma b8_2_contains : b8_2.Contains (basisBeta 8 2) := by
  have he : betaBox 8 2 = b8_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 2
def a8_3 : CBox := ⟨⟨3999999999999999999959031748932,4000000000000000000047602850445⟩,⟨(-31982309834),45827761593⟩⟩
lemma a8_3_contains : a8_3.Contains (basisAlpha 8 3) := by
  have he : alphaBox 8 3 = a8_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 3
def b8_3 : CBox := ⟨⟨3333333333333333333302752468489,3333333333333333333369074442138⟩,⟨(-23641169255),34344465385⟩⟩
lemma b8_3_contains : b8_3.Contains (basisBeta 8 3) := by
  have he : betaBox 8 3 = b8_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 3
def a8_4 : CBox := ⟨⟨2999999999999999999980387815212,3000000000000000000024035251040⟩,⟨(-13917776188),22755745938⟩⟩
lemma a8_4_contains : a8_4.Contains (basisAlpha 8 4) := by
  have he : alphaBox 8 4 = a8_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 4
def b8_4 : CBox := ⟨⟨2666666666666666666650323179343,2666666666666666666686696042534⟩,⟨(-11598146824),18963121615⟩⟩
lemma b8_4_contains : b8_4.Contains (basisBeta 8 4) := by
  have he : betaBox 8 4 = b8_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 4
def a8_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a8_5_contains : a8_5.Contains (basisAlpha 8 5) := by
  have he : alphaBox 8 5 = a8_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 8 5
def b8_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b8_5_contains : b8_5.Contains (basisBeta 8 5) := by
  have he : betaBox 8 5 = b8_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 8 5
def aRow8 : Fin 6 → CBox := ![a8_0,a8_1,a8_2,a8_3,a8_4,a8_5]
lemma aRow8_contains (j : Fin 6) : (aRow8 j).Contains (basisAlpha 8 j.val) := by
  fin_cases j
  · exact a8_0_contains
  · exact a8_1_contains
  · exact a8_2_contains
  · exact a8_3_contains
  · exact a8_4_contains
  · exact a8_5_contains
def bRow8 : Fin 6 → CBox := ![b8_0,b8_1,b8_2,b8_3,b8_4,b8_5]
lemma bRow8_contains (j : Fin 6) : (bRow8 j).Contains (basisBeta 8 j.val) := by
  fin_cases j
  · exact b8_0_contains
  · exact b8_1_contains
  · exact b8_2_contains
  · exact b8_3_contains
  · exact b8_4_contains
  · exact b8_5_contains
def a9_0 : CBox := ⟨⟨(-2500000000000000000155691406154),(-2499999999999999999845571500932)⟩,⟨(-866025403784438646919853613556),(-866025403784438646619572853325)⟩⟩
lemma a9_0_contains : a9_0.Contains (basisAlpha 9 0) := by
  have he : alphaBox 9 0 = a9_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 0
def b9_0 : CBox := ⟨⟨(-2821367205045918195765461581390),(-2821367205045918195609863798778)⟩,⟨(-81783603407),67335732360⟩⟩
lemma b9_0_contains : b9_0.Contains (basisBeta 9 0) := by
  have he : betaBox 9 0 = b9_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 0
def a9_1 : CBox := ⟨⟨(-4232050807568877293620317413911),(-4232050807568877293433875643005)⟩,⟨(-1866025403784438646874065286900),(-1866025403784438646677606519662)⟩⟩
lemma a9_1_contains : a9_1.Contains (basisAlpha 9 1) := by
  have he : alphaBox 9 1 = a9_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 1
def b9_1 : CBox := ⟨⟨(-3110042339640731078009565916016),(-3110042339640731077874581155791)⟩,⟨(-166666666666666666740818882297),(-166666666666666666609003212030)⟩⟩
lemma b9_1_contains : b9_1.Contains (basisBeta 9 1) := by
  have he : betaBox 9 1 = b9_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 1
def a9_2 : CBox := ⟨⟨(-3232050807568877293606267487983),(-3232050807568877293456089128727)⟩,⟨(-133974596215561353313640395530),(-133974596215561353173318177597)⟩⟩
lemma a9_2_contains : a9_2.Contains (basisAlpha 9 2) := by
  have he : alphaBox 9 2 = a9_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 2
def b9_2 : CBox := ⟨⟨(-2776709006307397744671549274040),(-2776709006307397744548652317699)⟩,⟨410683602522959097779322748160,410683602522959097892426235325⟩⟩
lemma b9_2_contains : b9_2.Contains (basisBeta 9 2) := by
  have he : betaBox 9 2 = b9_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 2
def a9_3 : CBox := ⟨⟨(-3232050807568877293601955724173),(-3232050807568877293465114125979)⟩,⟨1866025403784438646692941336406,1866025403784438646820100090463⟩⟩
lemma a9_3_contains : a9_3.Contains (basisAlpha 9 3) := by
  have he : alphaBox 9 3 = a9_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 3
def b9_3 : CBox := ⟨⟨(-2776709006307397744669393392135),(-2776709006307397744553164816325)⟩,⟨1410683602522959097782613614128,1410683602522959097889135369355⟩⟩
lemma b9_3_contains : b9_3.Contains (basisBeta 9 3) := by
  have he : betaBox 9 3 = b9_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 3
def a9_4 : CBox := ⟨⟨(-2732050807568877293601955724173),(-2732050807568877293465114125979)⟩,⟨999999999999999999932941336406,1000000000000000000050100090463⟩⟩
lemma a9_4_contains : a9_4.Contains (basisAlpha 9 4) := by
  have he : alphaBox 9 4 = a9_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 4
def b9_4 : CBox := ⟨⟨(-2443375672974064411336060058801),(-2443375672974064411219831482992)⟩,⟨833333333333333333275946947462,833333333333333333375802036021⟩⟩
lemma b9_4_contains : b9_4.Contains (basisBeta 9 4) := by
  have he : betaBox 9 4 = b9_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 4
def a9_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a9_5_contains : a9_5.Contains (basisAlpha 9 5) := by
  have he : alphaBox 9 5 = a9_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 9 5
def b9_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b9_5_contains : b9_5.Contains (basisBeta 9 5) := by
  have he : betaBox 9 5 = b9_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 9 5
def aRow9 : Fin 6 → CBox := ![a9_0,a9_1,a9_2,a9_3,a9_4,a9_5]
lemma aRow9_contains (j : Fin 6) : (aRow9 j).Contains (basisAlpha 9 j.val) := by
  fin_cases j
  · exact a9_0_contains
  · exact a9_1_contains
  · exact a9_2_contains
  · exact a9_3_contains
  · exact a9_4_contains
  · exact a9_5_contains
def bRow9 : Fin 6 → CBox := ![b9_0,b9_1,b9_2,b9_3,b9_4,b9_5]
lemma bRow9_contains (j : Fin 6) : (bRow9 j).Contains (basisBeta 9 j.val) := by
  fin_cases j
  · exact b9_0_contains
  · exact b9_1_contains
  · exact b9_2_contains
  · exact b9_3_contains
  · exact b9_4_contains
  · exact b9_5_contains
def a10_0 : CBox := ⟨⟨5499999999999999999859593080110,5500000000000000000154185772113⟩,⟨(-2598076211353315940415816567902),(-2598076211353315940146786777146)⟩⟩
lemma a10_0_contains : a10_0.Contains (basisAlpha 10 0) := by
  have he : alphaBox 10 0 = a10_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 0
def b10_0 : CBox := ⟨⟨2999999999999999999953966636345,3000000000000000000055898803099⟩,⟨(-2309401076758503058078900713958),(-2309401076758503057989315326372)⟩⟩
lemma b10_0_contains : b10_0.Contains (basisBeta 10 0) := by
  have he : betaBox 10 0 = b10_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 0
def a10_1 : CBox := ⟨⟨4499999999999999999928853374972,4500000000000000000094108343981⟩,⟨(-4330127018922193233887325742290),(-4330127018922193233740579333323)⟩⟩
lemma a10_1_contains : a10_1.Contains (basisAlpha 10 1) := by
  have he : alphaBox 10 1 = a10_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 1
def b10_1 : CBox := ⟨⟨2833333333333333333298843352156,2833333333333333333379219231743⟩,⟨(-2598076211353315940324152243022),(-2598076211353315940254947419069)⟩⟩
lemma b10_1_contains : b10_1.Contains (basisBeta 10 1) := by
  have he : betaBox 10 1 = b10_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 1
def a10_2 : CBox := ⟨⟨3499999999999999999966123134337,3500000000000000000041530771977⟩,⟨(-2598076211353315940320608177868),(-2598076211353315940256134867503)⟩⟩
lemma a10_2_contains : a10_2.Contains (basisAlpha 10 2) := by
  have he : alphaBox 10 2 = a10_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 2
def b10_2 : CBox := ⟨⟨2499999999999999999977933271945,2500000000000000000028360041075⟩,⟨(-2020725942163690175801913054881),(-2020725942163690175760132597129)⟩⟩
lemma b10_2_contains : b10_2.Contains (basisBeta 10 2) := by
  have he : betaBox 10 2 = b10_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 2
def a10_3 : CBox := ⟨⟨1499999999999999999979286598219,1500000000000000000028367308103⟩,⟨(-2598076211353315940311984650246),(-2598076211353315940274184862009)⟩⟩
lemma a10_3_contains : a10_3.Contains (basisAlpha 10 3) := by
  have he : alphaBox 10 3 = a10_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 3
def b10_3 : CBox := ⟨⟨1499999999999999999984515003886,1500000000000000000021778309138⟩,⟨(-2020725942163690175797601291070),(-2020725942163690175769157594382)⟩⟩
lemma b10_3_contains : b10_3.Contains (basisBeta 10 3) := by
  have he : betaBox 10 3 = b10_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 3
def a10_4 : CBox := ⟨⟨1999999999999999999989943630442,2000000000000000000017200622411⟩,⟨(-1732050807568877293537669145432),(-1732050807568877293518206118258)⟩⟩
lemma a10_4_contains : a10_4.Contains (basisAlpha 10 4) := by
  have he : alphaBox 10 4 = a10_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 4
def b10_4 : CBox := ⟨⟨1833333333333333333324953025368,1833333333333333333347667185343⟩,⟨(-1443375672974064411281390954527),(-1443375672974064411265171765215)⟩⟩
lemma b10_4_contains : b10_4.Contains (basisBeta 10 4) := by
  have he : betaBox 10 4 = b10_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 4
def a10_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma a10_5_contains : a10_5.Contains (basisAlpha 10 5) := by
  have he : alphaBox 10 5 = a10_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 10 5
def b10_5 : CBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩
lemma b10_5_contains : b10_5.Contains (basisBeta 10 5) := by
  have he : betaBox 10 5 = b10_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 10 5
def aRow10 : Fin 6 → CBox := ![a10_0,a10_1,a10_2,a10_3,a10_4,a10_5]
lemma aRow10_contains (j : Fin 6) : (aRow10 j).Contains (basisAlpha 10 j.val) := by
  fin_cases j
  · exact a10_0_contains
  · exact a10_1_contains
  · exact a10_2_contains
  · exact a10_3_contains
  · exact a10_4_contains
  · exact a10_5_contains
def bRow10 : Fin 6 → CBox := ![b10_0,b10_1,b10_2,b10_3,b10_4,b10_5]
lemma bRow10_contains (j : Fin 6) : (bRow10 j).Contains (basisBeta 10 j.val) := by
  fin_cases j
  · exact b10_0_contains
  · exact b10_1_contains
  · exact b10_2_contains
  · exact b10_3_contains
  · exact b10_4_contains
  · exact b10_5_contains
def a11_0 : CBox := ⟨⟨1999999999999999999734706905414,2000000000000000000229508592982⟩,⟨5999999999999999999764691170066,6000000000000000000262713647619⟩⟩
lemma a11_0_contains : a11_0.Contains (basisAlpha 11 0) := by
  have he : alphaBox 11 0 = a11_0 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 0
def b11_0 : CBox := ⟨⟨333333333333333333221864948463,333333333333333333426933209970⟩,⟨2999999999999999999901084452052,3000000000000000000108051847632⟩⟩
lemma b11_0_contains : b11_0.Contains (basisBeta 11 0) := by
  have he : betaBox 11 0 = b11_0 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 0
def a11_1 : CBox := ⟨⟨1999999999999999999826012483275,2000000000000000000152931212580⟩,⟨3999999999999999999850248446211,4000000000000000000172733305229⟩⟩
lemma a11_1_contains : a11_1.Contains (basisAlpha 11 1) := by
  have he : alphaBox 11 1 = a11_1 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 1
def b11_1 : CBox := ⟨⟨333333333333333333237082544774,333333333333333333414170313236⟩,⟨2666666666666666666582010664743,2666666666666666666759721790567⟩⟩
lemma b11_1_contains : b11_1.Contains (basisBeta 11 1) := by
  have he : betaBox 11 1 = b11_1 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 1
def a11_2 : CBox := ⟨⟨(-111530188351),86050817960⟩,⟨3999999999999999999902257918789,4000000000000000000102459396018⟩⟩
lemma a11_2_contains : a11_2.Contains (basisAlpha 11 2) := by
  have he : alphaBox 11 2 = a11_2 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 2
def b11_2 : CBox := ⟨⟨(-333333333333333333408765012434),(-333333333333333333274789818304)⟩,⟨2666666666666666666599347155603,2666666666666666666736297154163⟩⟩
lemma b11_2_contains : b11_2.Contains (basisBeta 11 2) := by
  have he : betaBox 11 2 = b11_2 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 2
def a11_3 : CBox := ⟨⟨(-66386921943),55047251878⟩,⟨1999999999999999999940134820431,2000000000000000000064582494384⟩⟩
lemma a11_3_contains : a11_3.Contains (basisAlpha 11 3) := by
  have he : alphaBox 11 3 = a11_3 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 3
def b11_3 : CBox := ⟨⟨(-333333333333333333386193379230),(-333333333333333333290291601345)⟩,⟨1666666666666666666618285606424,1666666666666666666717358703346⟩⟩
lemma b11_3_contains : b11_3.Contains (basisBeta 11 3) := by
  have he : betaBox 11 3 = b11_3 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 3
def a11_4 : CBox := ⟨⟨(-1000000000000000000045030855663),(-999999999999999999968520347527)⟩,⟨1999999999999999999958199354077,2000000000000000000041510478729⟩⟩
lemma a11_4_contains : a11_4.Contains (basisAlpha 11 4) := by
  have he : alphaBox 11 4 = a11_4 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 4
def b11_4 : CBox := ⟨⟨(-1000000000000000000038622668376),(-999999999999999999972670000949)⟩,⟨1666666666666666666630328628855,1666666666666666666701977359576⟩⟩
lemma b11_4_contains : b11_4.Contains (basisBeta 11 4) := by
  have he : betaBox 11 4 = b11_4 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 4
def a11_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma a11_5_contains : a11_5.Contains (basisAlpha 11 5) := by
  have he : alphaBox 11 5 = a11_5 := by decide +kernel
  rw [← he]
  exact alphaBox_contains 11 5
def b11_5 : CBox := ⟨⟨(-1000000000000000000006581731937),(-999999999999999999993418268059)⟩,⟨(-9024997253),4311763811⟩⟩
lemma b11_5_contains : b11_5.Contains (basisBeta 11 5) := by
  have he : betaBox 11 5 = b11_5 := by decide +kernel
  rw [← he]
  exact betaBox_contains 11 5
def aRow11 : Fin 6 → CBox := ![a11_0,a11_1,a11_2,a11_3,a11_4,a11_5]
lemma aRow11_contains (j : Fin 6) : (aRow11 j).Contains (basisAlpha 11 j.val) := by
  fin_cases j
  · exact a11_0_contains
  · exact a11_1_contains
  · exact a11_2_contains
  · exact a11_3_contains
  · exact a11_4_contains
  · exact a11_5_contains
def bRow11 : Fin 6 → CBox := ![b11_0,b11_1,b11_2,b11_3,b11_4,b11_5]
lemma bRow11_contains (j : Fin 6) : (bRow11 j).Contains (basisBeta 11 j.val) := by
  fin_cases j
  · exact b11_0_contains
  · exact b11_1_contains
  · exact b11_2_contains
  · exact b11_3_contains
  · exact b11_4_contains
  · exact b11_5_contains
def aTable : Fin 12 → Fin 6 → CBox := ![aRow0,aRow1,aRow2,aRow3,aRow4,aRow5,aRow6,aRow7,aRow8,aRow9,aRow10,aRow11]
lemma aTable_contains (n : Fin 12) (j : Fin 6) : (aTable n j).Contains (basisAlpha n.val j.val) := by
  fin_cases n
  · exact aRow0_contains j
  · exact aRow1_contains j
  · exact aRow2_contains j
  · exact aRow3_contains j
  · exact aRow4_contains j
  · exact aRow5_contains j
  · exact aRow6_contains j
  · exact aRow7_contains j
  · exact aRow8_contains j
  · exact aRow9_contains j
  · exact aRow10_contains j
  · exact aRow11_contains j
def aLookup (n : ℕ) (j : Fin 6) : CBox := aTable ⟨n%12,by omega⟩ j
lemma aLookup_contains (n : ℕ) (j : Fin 6) : (aLookup n j).Contains (basisAlpha n j.val) := by
  simpa only [aLookup,basisAlpha_mod] using aTable_contains ⟨n%12,by omega⟩ j
def bTable : Fin 12 → Fin 6 → CBox := ![bRow0,bRow1,bRow2,bRow3,bRow4,bRow5,bRow6,bRow7,bRow8,bRow9,bRow10,bRow11]
lemma bTable_contains (n : Fin 12) (j : Fin 6) : (bTable n j).Contains (basisBeta n.val j.val) := by
  fin_cases n
  · exact bRow0_contains j
  · exact bRow1_contains j
  · exact bRow2_contains j
  · exact bRow3_contains j
  · exact bRow4_contains j
  · exact bRow5_contains j
  · exact bRow6_contains j
  · exact bRow7_contains j
  · exact bRow8_contains j
  · exact bRow9_contains j
  · exact bRow10_contains j
  · exact bRow11_contains j
def bLookup (n : ℕ) (j : Fin 6) : CBox := bTable ⟨n%12,by omega⟩ j
lemma bLookup_contains (n : ℕ) (j : Fin 6) : (bLookup n j).Contains (basisBeta n j.val) := by
  simpa only [bLookup,basisBeta_mod] using bTable_contains ⟨n%12,by omega⟩ j
end SharpPlanar.IntegerAlpha

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

def weightedColumnBox (p : PointBox) (w : RBox) (a b : CBox) (n : ℕ) (d : Bool) : CBox :=
  (rcast w).mul (basisFunctionBox p a b n d)
def momentKernelBox (p : PointBox) (m : ℕ) (e : Bool) : CBox :=
  if e then (kernel0Box p m).mul (piI.mul p.z) else kernel0Box p m

def cachedMomentRuleBox (c k : Fin 6 → Fin 16 → Fin 16 → CBox) : CBox :=
  finSum fun j => (finSum (fun i => finSum (fun v => (c j i v).mul (k j i v)))).scale 1 6

lemma weightedColumnBox_contains {p : PointBox} {t w : ℝ} {wb : RBox} (hp : p.Contains t)
    (hw : wb.Contains w) {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (hn : n < 128) (d : Bool) :
    (weightedColumnBox p wb a b n d).Contains ((w:ℂ)*basisFunction d n j t) :=
  CBox.contains_mul (rcast_contains hw) (basisFunctionBox_contains hp ha hb hn d)
lemma momentKernelBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {m : ℕ}
    (hm : m < 128) (e : Bool) :
    (momentKernelBox p m e).Contains (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)*
      (if e then Complex.I*Real.pi*z t else 1)) := by
  cases e
  · simpa only [momentKernelBox,Bool.false_eq_true,ite_false,mul_one] using kernel0Box_contains hp hm
  · simpa only [momentKernelBox,ite_true,pointZ_eq] using
      CBox.contains_mul (kernel0Box_contains hp hm) (CBox.contains_mul piI_contains hp.2.2.1)

lemma cachedMomentRuleBox_contains
    {c k : Fin 6 → Fin 16 → Fin 16 → CBox} {t : ℕ → ℕ → ℝ} {w : ℕ → ℝ}
    {n m : ℕ} {d e : Bool}
    (hc : ∀ j i v, (c j i v).Contains ((w (16*i.val+v.val):ℂ)*
      basisFunction d n j.val (t j.val (16*i.val+v.val))))
    (hk : ∀ j i v, (k j i v).Contains
      (lambda (t j.val (16*i.val+v.val))*Complex.exp (Complex.I*Real.pi*z (t j.val (16*i.val+v.val))*m)*
      (if e then Complex.I*Real.pi*z (t j.val (16*i.val+v.val)) else 1))) :
    (cachedMomentRuleBox c k).Contains (momentRuleValue t w n m d e) := by
  unfold cachedMomentRuleBox momentRuleValue
  apply finSum_contains
  intro j
  rw [← sum_fin_square 16 (fun v => (w v:ℂ)*basisMoment d e n j.val m (t j.val v))]
  have hh := finSum_contains (fun i => finSum_contains (fun v => CBox.contains_mul (hc j i v) (hk j i v)))
  have hs := CBox.contains_scale hh 1 6 (by norm_num)
  simpa only [Int.cast_one,Int.cast_ofNat,basisMoment,mul_assoc] using hs

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerCompact

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl
lemma complexLambda_ofReal (t : ℝ) : complexLambda t = lambda t := rfl
lemma complexZ_ofReal (t : ℝ) : complexZ t = z t := rfl
lemma complexBasisMoment_ofReal (d e : Bool) (n j m : ℕ) (t : ℝ) :
    complexBasisMoment d e n j m t = basisMoment d e n j m t := by
  unfold complexBasisMoment complexBasis basisMoment basisFunction complexTransformedFactor
  rw [complexU_ofReal,complexV_ofReal,complexLambda_ofReal,complexZ_ofReal]
  cases d <;> cases e <;> simp <;> ring


end SharpPlanar

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma exp_direct_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (-Complex.I*Real.pi*t*n)))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t))) :
    (p.mul q).Contains (Complex.exp (-Complex.I*Real.pi*t*(n+1))) := by
  have hh := CBox.contains_mul hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  congr 1
  ring
lemma exp_transformed_step {p q : CBox} {t : ℝ} {n : ℕ}
    (hp : p.Contains (Complex.exp (Complex.I*Real.pi*z t*n)))
    (hq : q.Contains (Complex.exp (Complex.I*Real.pi*z t))) :
    (p.mul q).Contains (Complex.exp (Complex.I*Real.pi*z t*(n+1))) := by
  have hh := CBox.contains_mul hp hq
  rw [← Complex.exp_add] at hh
  convert hh using 1
  congr 1
  ring

def transformedStepBox (p : PointBox) : CBox := p.quarter.powFast 3 4
lemma transformedStepBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) :
    (transformedStepBox p).Contains (Complex.exp (Complex.I*Real.pi*z t)) := by
  have hh := CBox.contains_powFast hp.2.2.2.2 3 4 (by norm_num)
  rw [← Complex.exp_nat_mul] at hh
  change (p.quarter.powFast 3 4).Contains _
  convert hh using 1
  rw [pointZ_eq]
  congr 1
  push_cast
  ring

noncomputable def waveAmplitude (d : Bool) (n j : ℕ) (t : ℝ) : ℂ :=
  if d then 2*Complex.I*Real.pi*basisAlpha n j
  else -2*(Real.pi:ℂ)^2*(basisBeta n j-(t:ℂ)*basisAlpha n j)
def waveAmplitudeBox (p : PointBox) (a b : CBox) (d : Bool) : CBox :=
  if d then (piI.scale 2 1).mul a
  else (((rcast piBounds).mul (rcast piBounds)).scale (-2) 1).mul
      (b.add ((rcast p.t).mul a).neg)
lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod,basisBeta_mod]
lemma basisFunction_wave (d : Bool) (n j : ℕ) (t : ℝ) :
    basisFunction d n j t = waveAmplitude d n j t*Complex.exp (-Complex.I*Real.pi*t*n) := by
  cases d <;> simp only [basisFunction,waveAmplitude,Bool.false_eq_true,ite_false,ite_true]
  · rw [u_factored]; ring
  · rw [v_factored]; ring
lemma waveAmplitudeBox_contains {p : PointBox} {t : ℝ} (hp : p.Contains t)
    {a b : CBox} {n j : ℕ} (ha : a.Contains (basisAlpha n j))
    (hb : b.Contains (basisBeta n j)) (d : Bool) :
    (waveAmplitudeBox p a b d).Contains (waveAmplitude d n j t) := by
  cases d
  · have hh := CBox.contains_mul
      (CBox.contains_scale (CBox.contains_mul (rcast_contains piBounds_contains)
        (rcast_contains piBounds_contains)) (-2) 1 (by norm_num))
      (CBox.contains_add hb (CBox.neg_contains (CBox.contains_mul (rcast_contains hp.1) ha)))
    convert hh using 1 <;> simp only [waveAmplitudeBox,waveAmplitude,Bool.false_eq_true,ite_false,Int.cast_neg,Int.cast_ofNat,Int.cast_one]; ring
  · have hh := CBox.contains_mul (CBox.contains_scale piI_contains 2 1 (by norm_num)) ha
    convert hh using 1 <;> simp only [waveAmplitudeBox,waveAmplitude,ite_true,Int.cast_ofNat,Int.cast_one]; ring

lemma cached_weighted_wave {p q : CBox} {t w : ℝ} {n j : ℕ} {d : Bool}
    (hp : p.Contains ((w:ℂ)*waveAmplitude d n j t))
    (hq : q.Contains (Complex.exp (-Complex.I*Real.pi*t*n))) :
    (p.mul q).Contains ((w:ℂ)*basisFunction d n j t) := by
  rw [basisFunction_wave,← mul_assoc]
  exact CBox.contains_mul hp hq

end SharpPlanar.IntegerBasis

end OAI
