import Mathlib
import OAI.Computability.MinUncut.Graphs.HonestBudgets
import OAI.Computability.MinUncut.Search.RationalBasics

namespace OAI

section
namespace MinUncut.Inner
open GaussianHermite

structure InnerData where
  s : ℕ
  m : ℕ
  k : ℕ
  n : ℕ
  H : ℕ
  A : ℕ
  γ : ℚ
  p : ℚ
  θ : ℚ
  deriving DecidableEq, Encodable

namespace InnerData

def epsilon (J m : ℕ) : ℚ := 1/(40*(rationalT J:ℚ)*(m^2+1))
def atomConstant (s m n : ℕ) : ℕ := 4^(m*n^(m-1))*(n^m+s).choose s

def Check (J : ℕ) (d : InnerData) : Prop :=
  2 ≤ d.m ∧ d.k+2 ≤ d.n ∧ 1 ≤ d.k ∧ 0 < d.H ∧ 0 < d.A ∧
  0 < d.γ ∧ 0 < d.p ∧ d.p < 1 ∧ 0 < d.θ ∧ d.θ < 1 ∧
  ((d.s:ℚ)+3)*(1+rationalSigma J^2)⁻¹ ≤ (d.s:ℚ)+2 ∧
  ((d.s:ℚ)+2)*((1+rationalSigma J^2)⁻¹)^(d.s+2) ≤ 1/16 ∧
  rationalR J*d.m < (d.m-d.s).choose 2 ∧
  ((d.s+rationalR J*d.m:ℕ):ℚ)*(d.k:ℚ)/((d.n:ℚ)-1) < (epsilon J d.m*rationalSigma J)^2 ∧
  (rationalSigma J)⁻¹^2/(d.H:ℚ) < epsilon J d.m ∧
  2*(rationalSigma J)⁻¹^2/(d.A:ℚ) < epsilon J d.m ∧
  (d.m:ℚ)/((d.k:ℚ)+1) < (epsilon J d.m/(2*(d.A:ℚ)))^(2^d.m) ∧
  (d.H:ℚ)*(d.γ+(d.H:ℚ)^2/(d.A:ℚ)) < epsilon J d.m^2 ∧
  d.θ^2+(d.m:ℚ)*d.p*(d.n^d.m:ℕ)/(rationalSigma J)^2 <
    (epsilon J d.m^2*(rationalSigma J)^2*d.γ/(atomConstant d.s d.m d.n:ℚ))^2

instance (J : ℕ) (d : InnerData) : Decidable (Check J d) := by unfold Check; infer_instance

lemma epsilon_pos {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) : 0 < (epsilon J m:ℝ) := by
  have hT : (0:ℝ) < rationalT J := by
    rw [rationalT_eq]
    exact_mod_cast sourceT_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  unfold epsilon
  push_cast
  positivity

lemma epsilon_le {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) :
    (epsilon J m:ℝ) ≤ classTarget (sourceT J) m/10 := by
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  have hc := pairClass_card_le m
  have hc' : (Fintype.card (Option (PairClass m)):ℝ) ≤ (m:ℝ)^2+1 := by exact_mod_cast hc
  have hp : (0:ℝ) < Fintype.card (Option (PairClass m)) := by positivity
  unfold epsilon classTarget
  push_cast
  rw [rationalT_eq]
  calc
    _ ≤ 1/(40*(sourceT J:ℝ)*(Fintype.card (Option (PairClass m)):ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hc' (by positivity))
    _ = _ := by ring

lemma atomConstant_cast (s m n : ℕ) : (atomConstant s m n:ℝ)=
    (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ) := by
  simp [atomConstant,Point]

def realize {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (h : d.Check J) : InnerParameters J := by
  have hm := h.1
  have hn := h.2.1
  have hk := h.2.2.1
  have hH := h.2.2.2.1
  have hA := h.2.2.2.2.1
  have hγ := h.2.2.2.2.2.1
  have hp := h.2.2.2.2.2.2.1
  have hp1 := h.2.2.2.2.2.2.2.1
  have hθ := h.2.2.2.2.2.2.2.2.1
  have hθ1 := h.2.2.2.2.2.2.2.2.2.1
  have hstep := h.2.2.2.2.2.2.2.2.2.2.1
  have hbase := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hroom := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcol := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfour := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hJr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hσ := sourceSigma_pos hJr
  have hε := epsilon_pos hJ d.m
  have hb := epsilon_le hJ d.m
  have hγr : (0:ℝ) < d.γ := by exact_mod_cast hγ
  have hAr : (0:ℝ) < d.A := by exact_mod_cast hA
  have hn0 : (1:ℝ) < d.n := by exact_mod_cast (by omega : 1 < d.n)
  refine ⟨d.s,d.m,d.k,d.n,d.H,d.A,d.γ,d.p,d.θ,hm,hn,hk,?_,?_,hH,hA,hγr,
    by exact_mod_cast hp,by exact_mod_cast hp1,by exact_mod_cast hθ,by exact_mod_cast hθ1,
    ?_,?_,?_,?_,?_,?_⟩
  · have hs' : ((d.s:ℝ)+3)*(1+(sourceSigma J)^2)⁻¹ ≤ (d.s:ℝ)+2 := by
      simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_inv,
        Rat.cast_one,Rat.cast_pow,rationalSigma_cast] using (Rat.cast_le.mpr hstep : (_:ℝ) ≤ _)
    have hb' : ((d.s:ℝ)+2)*((1+(sourceSigma J)^2)⁻¹)^(d.s+2) ≤ 1/16 := by
      simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_inv,
        Rat.cast_one,Rat.cast_pow,Rat.cast_div,rationalSigma_cast] using (Rat.cast_le.mpr hbase : (_:ℝ) ≤ _)
    intro t ht
    rw [rho_even]
    exact cutoff_tail (by positivity) hs' hb' t ht
  · simpa only [rationalR_eq] using hroom
  · have hl : ((d.s+sourceR J*d.m:ℕ):ℝ)*((d.k:ℝ)/((d.n:ℝ)-1)) <
        ((epsilon J d.m:ℝ)*sourceSigma J)^2 := by
      have hh := (Rat.cast_lt.mpr hloc : (_:ℝ) < _)
      push_cast at hh
      simpa only [rationalSigma_cast,rationalR_eq,mul_div_assoc,Nat.cast_add,Nat.cast_mul] using hh
    have hh := (Real.sqrt_lt' (show 0 < (epsilon J d.m:ℝ)*sourceSigma J by positivity)).mpr hl
    apply lt_of_lt_of_le _ hb
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_lt_iff₀ hσ).mpr hh
  · apply lt_of_lt_of_le _ hb
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_inv,Rat.cast_natCast,rationalSigma_cast]
      using (Rat.cast_lt.mpr he : (_:ℝ) < _)
  · apply lt_of_lt_of_le _ hb
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_inv,Rat.cast_natCast,
      Rat.cast_ofNat,rationalSigma_cast] using (Rat.cast_lt.mpr hc : (_:ℝ) < _)
  · have hh : (d.m:ℝ)/((d.k:ℝ)+1) < ((epsilon J d.m:ℝ)/(2*(d.A:ℝ)))^(2^d.m) := by
      simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow,
        Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_lt.mpr hcol : (_:ℝ) < _)
    have hr := (Real.rpow_inv_lt_iff_of_pos (by positivity : (0:ℝ) ≤ (d.m:ℝ)/((d.k:ℝ)+1))
      (by positivity : 0 ≤ (epsilon J d.m:ℝ)/(2*(d.A:ℝ))) (by positivity : (0:ℝ) < (2^d.m:ℕ))).mpr
      (by simpa only [Real.rpow_natCast] using hh)
    apply lt_of_lt_of_le _ hb
    simpa only [mul_comm] using (lt_div_iff₀ (show 0 < 2*(d.A:ℝ) by positivity)).mp hr
  · apply lt_of_lt_of_le ((Real.sqrt_lt' hε).mpr _) hb
    simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
      using (Rat.cast_lt.mpr hfour : (_:ℝ) < _)
  · have hC : 0 < (atomConstant d.s d.m d.n:ℝ) := by
      rw [atomConstant_cast]
      have hh : 0 < (Fintype.card (Point d.m d.n)+d.s).choose d.s := Nat.choose_pos (by omega)
      positivity
    have hh : (d.θ:ℝ)^2+(d.m:ℝ)*(d.p:ℝ)*(d.n^d.m:ℕ)/(sourceSigma J)^2 <
        ((epsilon J d.m:ℝ)^2*(sourceSigma J)^2*(d.γ:ℝ)/(atomConstant d.s d.m d.n:ℝ))^2 := by
      have hh := (Rat.cast_lt.mpr hat : (_:ℝ) < _)
      push_cast at hh
      simpa only [rationalSigma_cast,Nat.cast_pow] using hh
    apply lt_of_lt_of_le _ hb
    have h := nested_atom_lt hσ hε hγr hC hh
    simpa only [atomConstant_cast] using h
end InnerData
end MinUncut.Inner

end
section
namespace MinUncut.Inner.InnerData
open MinUncut.Inner

lemma check_exists {J : ℕ} (hJ : 1 ≤ J) : ∃ d : InnerData, d.Check J := by
  have hJr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hσ := sourceSigma_pos hJr
  obtain ⟨s,hstep,hbase⟩ := exists_finite_cutoff hσ
  obtain ⟨m,hm,_,hroom⟩ := exists_dimension (sourceR J) s
  let e : ℝ := epsilon J m
  have he : 0 < e := epsilon_pos hJ m
  obtain ⟨H,A,γ,hH,hA,hγ,_,henergy,hclip,hfourth⟩ :=
    exists_reciprocal_processing (E := (sourceSigma J)⁻¹^2) he
  have hAr : (0:ℝ) < A := by exact_mod_cast hA
  obtain ⟨k,hk,hcollision⟩ := exists_box_scale m hAr he
  obtain ⟨n,hn,hloc⟩ := exists_ambient_scale s (sourceR J*m) k hσ he
  let C : ℝ := atomConstant s m n
  have hchoose : 0 < (n^m+s).choose s := Nat.choose_pos (by omega)
  have hC : 0 < C := by dsimp [C,atomConstant]; positivity
  let L : ℝ := (m:ℝ)*(n^m:ℕ)/(sourceSigma J)^2
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by omega
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨p,θ,hp,hp1,hθ,hθ1,hQ⟩ := exists_small_rational_atoms hL
    (show 0 < (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 by positivity)
  have hloc' : (((s+sourceR J*m:ℕ):ℝ)*(k:ℝ)/((n:ℝ)-1)) < (e*sourceSigma J)^2 := by
    apply (Real.sqrt_lt' (show 0 < e*sourceSigma J by positivity)).mp
    have hx : Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1)))/sourceSigma J < e := by
      simpa only [div_eq_mul_inv,mul_comm] using hloc
    simpa only [mul_div_assoc] using (div_lt_iff₀ hσ).mp hx
  have hcol' : (m:ℝ)/((k:ℝ)+1) < (e/(2*(A:ℝ)))^(2^m) := by
    have hx : ((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < e/(2*(A:ℝ)) :=
      (lt_div_iff₀ (show 0 < 2*(A:ℝ) by positivity)).mpr (by simpa only [mul_comm] using hcollision)
    have hh := (Real.rpow_inv_lt_iff_of_pos (by positivity : (0:ℝ) ≤ (m:ℝ)/((k:ℝ)+1))
      (by positivity : (0:ℝ) ≤ e/(2*(A:ℝ))) (by positivity : (0:ℝ) < (2^m:ℕ))).mp hx
    simpa only [Real.rpow_natCast] using hh
  have hfour' := (Real.sqrt_lt' he).mp hfourth
  have hat' : (θ:ℝ)^2+(m:ℝ)*(p:ℝ)*(n^m:ℕ)/(sourceSigma J)^2 <
      (e^2*(sourceSigma J)^2*(γ:ℝ)/C)^2 := by
    convert hQ using 1
    dsimp [L]
    ring
  refine ⟨⟨s,m,k,n,H,A,γ,p,θ⟩,hm,hn,hk,hH,hA,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast hγ
  · exact_mod_cast hp
  · exact_mod_cast hp1
  · exact_mod_cast hθ
  · exact_mod_cast hθ1
  · rw [← rationalSigma_cast J] at hstep
    exact_mod_cast hstep
  · rw [← rationalSigma_cast J] at hbase
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hbase
  · simpa only [rationalR_eq] using hroom
  · rw [← rationalSigma_cast J,← rationalR_eq J] at hloc'
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    simpa only [e,Nat.cast_add,Nat.cast_mul] using hloc'
  · rw [← rationalSigma_cast J] at henergy
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact henergy
  · rw [← rationalSigma_cast J] at hclip
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hclip
  · apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hcol'
  · apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    exact hfour'
  · rw [← rationalSigma_cast J] at hat'
    apply (Rat.cast_lt (K := ℝ)).mp
    push_cast
    simpa only [e,C,Nat.cast_pow] using hat'

def search (J : ℕ) (hJ : 1 ≤ J) : InnerData := Encodable.choose (check_exists hJ)

lemma search_check (J : ℕ) (hJ : 1 ≤ J) : (search J hJ).Check J :=
  Encodable.choose_spec (check_exists hJ)

end MinUncut.Inner.InnerData

end
section
namespace MinUncut.Outer
open MinUncut.Inner

lemma listTerm_mono {M M' u θ : ℝ} (hM : 0 ≤ M) (hM' : M ≤ M') (q k : ℕ) :
    listTerm M u θ q k ≤ listTerm M' u θ q k := by
  have hsq : M^2 ≤ M'^2 := sq_le_sq₀ hM (hM.trans hM') |>.mpr hM'
  have h1 : ⌈M^2/u^2⌉₊ ≤ ⌈M'^2/u^2⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hsq (sq_nonneg u))
  have h2 : ⌈M^2/θ^2⌉₊ ≤ ⌈M'^2/θ^2⌉₊ := Nat.ceil_mono (div_le_div_of_nonneg_right hsq (sq_nonneg θ))
  unfold listTerm
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hintRate_nonnegative q) k)
  exact mul_le_mul (by exact_mod_cast h1) (by exact_mod_cast h2) (by positivity) (by positivity)

lemma remainderTerm_mono {M M' u θ : ℝ} (hM : 0 ≤ M) (hM' : M ≤ M') (hu : 0 < u) (q k t : ℕ) :
    remainderTerm M u θ q k t ≤ remainderTerm M' u θ q k t := by
  have hsq : M^2 ≤ M'^2 := sq_le_sq₀ hM (hM.trans hM') |>.mpr hM'
  unfold remainderTerm
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left hsq (sq_nonneg u))
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  gcongr

structure OuterData where
  u : ℚ
  b4 : ℚ
  v : ℚ
  k : ℕ
  t : ℕ
  deriving DecidableEq, Encodable

namespace OuterData

def amplitude (J : ℕ) (d : InnerData) : ℚ := (d.n^d.m+1)/(rationalSigma J)
def hints (d : InnerData) : ℕ := d.m*d.n^(d.m-1)-1
def rate (q : ℕ) : ℚ := 1-1/(2:ℚ)^q*(1-99999999/100000000)
def listBound (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  (⌈amplitude J d^2/o.u^2⌉₊:ℚ)*(⌈amplitude J d^2/d.θ^2⌉₊:ℚ)*rate (hints d)^o.k
def radicand (d : InnerData) (k t : ℕ) : ℚ :=
  ((2:ℚ)^(4*(hints d+3)*k)-1)*(k:ℚ)^2/(t:ℚ)

def Check (J : ℕ) (d : InnerData) (o : OuterData) : Prop :=
  0 < o.u ∧ 0 < o.b4 ∧ 0 < o.v ∧ 1 ≤ o.t ∧ o.k ≤ o.t ∧
  listBound J d o < d.p/4 ∧
  (64/(d.θ^2*rationalSigma J^2))*(J:ℚ)*o.b4 < d.p/4 ∧
  radicand d o.k o.t < o.v^2 ∧
  (256/d.θ^4)*(o.u^2*amplitude J d^2+o.v*(amplitude J d+amplitude J d^2/o.u)^4) < d.p/2

instance (J : ℕ) (d : InnerData) (o : OuterData) : Decidable (Check J d o) := by
  unfold Check; infer_instance

@[simp] lemma rate_cast (q : ℕ) : (rate q:ℝ)=hintRate q := by simp [rate,hintRate,repetitionRate]
@[simp] lemma hints_eq (d : InnerData) : hints d=Fintype.card (Row d.m d.n)-1 := by rw [hints,row_card]

lemma amplitude_nonneg {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) : 0 ≤ (amplitude J d:ℝ) := by
  have hσ := sourceSigma_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  unfold amplitude
  push_cast
  rw [rationalSigma_cast]
  positivity

lemma amplitude_ge {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) :
    Real.sqrt (d.n^d.m:ℕ)/sourceSigma J ≤ (amplitude J d:ℝ) := by
  have hσ := sourceSigma_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  have hroot : Real.sqrt (d.n^d.m:ℕ) ≤ (d.n^d.m:ℕ)+1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hN := Nat.cast_nonneg (α := ℝ) (d.n^d.m)
      nlinarith
  unfold amplitude
  push_cast
  rw [rationalSigma_cast]
  apply div_le_div_of_nonneg_right _ hσ.le
  simpa only [Nat.cast_pow] using hroot

lemma listBound_cast (J : ℕ) (d : InnerData) (o : OuterData) :
    (listBound J d o:ℝ)=listTerm (amplitude J d) o.u d.θ (hints d) o.k := by
  unfold listBound listTerm
  push_cast
  rw [rate_cast]
  rw [← ceil_rat_real (amplitude J d^2/o.u^2),← ceil_rat_real (amplitude J d^2/d.θ^2)]
  push_cast
  rfl

def realize {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : OuterParameters J (d.realize hJ hd) := by
  have hu := ho.1
  have hb := ho.2.1
  have hv := ho.2.2.1
  have ht := ho.2.2.2.1
  have hk := ho.2.2.2.2.1
  have hl := ho.2.2.2.2.2.1
  have hbud := ho.2.2.2.2.2.2.1
  have hrad := ho.2.2.2.2.2.2.2.1
  have hrem := ho.2.2.2.2.2.2.2.2
  have hu' : (0:ℝ) < o.u := by exact_mod_cast hu
  have hb' : (0:ℝ) < o.b4 := by exact_mod_cast hb
  have hv' : (0:ℝ) < o.v := by exact_mod_cast hv
  let P := d.realize hJ hd
  have hθ := P.hθ
  have hM : (0:ℝ) ≤ Real.sqrt (d.n^d.m:ℕ)/sourceSigma J := by
    have := sourceSigma_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
    positivity
  have hm := amplitude_ge hJ d
  have hL : listTerm (amplitude J d) o.u d.θ (hints d) o.k < (d.p:ℝ)/4 := by
    rw [← listBound_cast]
    exact_mod_cast hl
  have hB : (64/((d.θ:ℝ)^2*(sourceSigma J)^2))*(J:ℝ)*(o.b4:ℝ) < (d.p:ℝ)/4 := by
    have h := (Rat.cast_lt.mpr hbud : (_:ℝ) < _)
    push_cast at h
    simpa only [rationalSigma_cast] using h
  have hRad : Real.sqrt (((2:ℝ)^(4*(hints d+3)*o.k)-1)*(o.k:ℝ)^2/(o.t:ℝ)) < (o.v:ℝ) := by
    apply (Real.sqrt_lt' hv').mpr
    have h := (Rat.cast_lt.mpr hrad : (_:ℝ) < _)
    simpa only [radicand,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using h
  have hR : remainderTerm (amplitude J d) o.u d.θ (hints d) o.k o.t < (d.p:ℝ)/2 := by
    have h := (Rat.cast_lt.mpr hrem : (_:ℝ) < _)
    push_cast at h
    apply lt_of_le_of_lt _ h
    unfold remainderTerm
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right hRad.le (by positivity)
  have hL' := (listTerm_mono hM hm (hints d) o.k).trans_lt hL
  have hR' := (remainderTerm_mono hM hm hu' (hints d) o.k o.t).trans_lt hR
  refine ⟨o.u,o.b4,o.k,o.t,hu',hb',ht,hk,?_⟩
  change listTerm (Real.sqrt (d.n^d.m:ℕ)/sourceSigma J) o.u d.θ
    (Fintype.card (Row d.m d.n)-1) o.k +
    (64/((d.θ:ℝ)^2*(sourceSigma J)^2))*(J:ℝ)*o.b4 +
    remainderTerm (Real.sqrt (d.n^d.m:ℕ)/sourceSigma J) o.u d.θ
      (Fintype.card (Row d.m d.n)-1) o.k o.t < d.p
  rw [← hints_eq]
  linarith
end OuterData
end MinUncut.Outer

end
section
namespace MinUncut.Outer.OuterData
open MinUncut.Inner

lemma check_exists {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J) :
    ∃ o : OuterData, o.Check J d := by
  have hJq : (1:ℚ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0:ℚ) < J := by linarith
  have hσ : 0 < rationalSigma J := by unfold rationalSigma; positivity
  have hp : 0 < d.p := by
    have hh : (0:ℝ) < d.p := (d.realize hJ hd).hp
    exact_mod_cast hh
  have hθ : 0 < d.θ := by
    have hh : (0:ℝ) < d.θ := (d.realize hJ hd).hθ
    exact_mod_cast hh
  let M : ℚ := amplitude J d
  let C : ℚ := 256/d.θ^4
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨u,hu,hub⟩ := exists_between (show (0:ℚ) < min 1 (d.p/(8*C*(M^2+1))) by positivity)
  obtain ⟨hu1,huB⟩ := lt_min_iff.mp hub
  have hsmall : C*u^2*M^2 < d.p/8 := by
    have hb := (lt_div_iff₀ (show (0:ℚ) < 8*C*(M^2+1) by positivity)).mp huB
    have hs : u^2 ≤ u := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ C*M^2 by positivity)
    nlinarith
  let R : ℚ := (M+M^2/u)^4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨v,hv,hvB⟩ := exists_between (show (0:ℚ) < d.p/(8*C*(R+1)) by positivity)
  have hlarge : C*v*R < d.p/8 := by
    have hx := (lt_div_iff₀ (show 0 < 8*C*(R+1) by positivity)).mp hvB
    nlinarith
  obtain ⟨b,hb,hbB⟩ := exists_between (show (0:ℚ) < d.p*d.θ^2*(rationalSigma J)^2/(256*J) by positivity)
  have hbudget : (64/(d.θ^2*(rationalSigma J)^2))*(J:ℚ)*b < d.p/4 := by
    have hx := (lt_div_iff₀ (show (0:ℚ) < 256*J by positivity)).mp hbB
    have he : (64/(d.θ^2*(rationalSigma J)^2))*(J:ℚ)*b = (64*J*b)/(d.θ^2*(rationalSigma J)^2) := by ring
    rw [he]
    apply (div_lt_iff₀ (show 0 < d.θ^2*(rationalSigma J)^2 by positivity)).mpr
    nlinarith
  obtain ⟨k,hk⟩ := exists_list_scale (M:ℝ) u d.θ (hints d)
    (show (0:ℝ) < (d.p:ℝ)/4 by exact_mod_cast (show (0:ℚ) < d.p/4 by positivity))
  let B : ℚ := ((2:ℚ)^(4*(hints d+3)*k)-1)*(k:ℚ)^2
  obtain ⟨t,ht⟩ := exists_nat_gt (max (k+1:ℚ) (B/v^2))
  have htk : (k:ℚ)+1 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht0 : (0:ℚ) < t := by have := Nat.cast_nonneg (α := ℚ) k; linarith
  have hrad : B/(t:ℚ) < v^2 := by
    apply (div_lt_iff₀ ht0).mpr
    have hx := (div_lt_iff₀ (show 0 < v^2 by positivity)).mp (lt_of_le_of_lt (le_max_right _ _) ht)
    nlinarith
  let o : OuterData := ⟨u,b,v,k,t⟩
  refine ⟨o,hu,hb,hv,by exact_mod_cast (show (1:ℚ) ≤ t by have := Nat.cast_nonneg (α := ℚ) k; linarith),
    by exact_mod_cast (show (k:ℚ) ≤ t by linarith),?_,hbudget,hrad,?_⟩
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [listBound_cast]
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hk
  · change C*(u^2*M^2+v*R) < d.p/2
    nlinarith

def search (J : ℕ) (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J) : OuterData :=
  Encodable.choose (check_exists hJ d hd)

lemma search_check (J : ℕ) (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J) :
    (search J hJ d hd).Check J d := Encodable.choose_spec (check_exists hJ d hd)

end MinUncut.Outer.OuterData

end
section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian

def rationalBudgets (J : ℕ) (d : InnerData) (o : OuterData) : Test → ℚ
  | .first => 10*rationalSigma J
  | .second => 10*(rationalEta J+rationalEta J)
  | .third => (Fintype.card (Code d.m d.n):ℚ)⁻¹
  | .fourth => o.b4

lemma rationalBudgets_cast {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (j : Test) :
    (rationalBudgets J d o j:ℝ)=budgets (d.realize hJ hd) (o.realize hJ d hd ho) j := by
  cases j <;> simp only [rationalBudgets,budgets,Rat.cast_mul,Rat.cast_ofNat,
    Rat.cast_add,Rat.cast_inv,Rat.cast_natCast,rationalSigma_cast,rationalEta_cast] <;> rfl

lemma rationalBudgets_pos {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (j : Test) : 0<rationalBudgets J d o j := by
  apply (Rat.cast_pos (K := ℝ)).mp
  rw [rationalBudgets_cast hJ d hd o ho]
  exact budgets_pos (by exact_mod_cast hJ) _ _ j

def rationalWeight (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  ∑ j, (rationalBudgets J d o j)⁻¹

def tableAccuracy (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  1/(8*(1+rationalWeight J d o))

lemma rationalWeight_nonneg {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : 0≤rationalWeight J d o :=
  Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (rationalBudgets_pos hJ d hd o ho j).le)

lemma rationalWeight_cast {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) :
    (rationalWeight J d o:ℝ)=budgetWeight (d.realize hJ hd) (o.realize hJ d hd ho) := by
  simp only [rationalWeight,budgetWeight,Rat.cast_sum,Rat.cast_inv,
    rationalBudgets_cast hJ d hd o ho]

lemma tableAccuracy_pos {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : 0<tableAccuracy J d o := by
  have := rationalWeight_nonneg hJ d hd o ho
  unfold tableAccuracy
  positivity

lemma tableAccuracy_error {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : tableAccuracy J d o*rationalWeight J d o<1/2 := by
  have hw := rationalWeight_nonneg hJ d hd o ho
  unfold tableAccuracy
  rw [one_div,inv_mul_eq_div]
  apply (div_lt_iff₀ (by positivity : 0<8*(1+rationalWeight J d o))).mpr
  linarith

variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

lemma ProofFamily.finiteCost_close {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (f : ProofFamily Name I) (equations : S → Equation Name)
    (hk : o.k≤Fintype.card I) :
    |f.cost (d.realize hJ hd) (o.realize hJ d hd ho) equations-
      f.finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
        (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations|<1/2 := by
  have hh := f.finiteCost_difference hJ (d.realize hJ hd) (o.realize hJ d hd ho)
    equations hk (tableAccuracy_pos hJ d hd o ho)
  apply hh.trans_lt
  rw [← rationalWeight_cast hJ d hd o ho]
  have he := (Rat.cast_lt (K := ℝ)).mpr (tableAccuracy_error hJ d hd o ho)
  simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using he

lemma finite_honest_cost {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (equations : S → Equation Name) (s : Name → F₂)
    (hcard : Fintype.card I=o.t) (hs : (o.t:ℝ)*(1-equationFraction equations s)≤o.b4) :
    (honestProof (I := I) s).finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
      (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations < 9/2 := by
  have hk : o.k≤Fintype.card I := by rw [hcard]; exact ho.2.2.2.2.1
  have hc := (honestProof (I := I) s).finiteCost_close hJ d hd o ho equations hk
  have hb := honest_cost_le (I := I) (by exact_mod_cast hJ : (1:ℝ)≤J) (d.realize hJ hd)
    (o.realize hJ d hd ho) equations s hcard hs
  have := (abs_lt.mp hc).1
  linarith

lemma finite_unsound_cost [Fintype Name] [Nonempty I] {J : ℕ} (hJ : 1≤J)
    (d : InnerData) (hd : d.Check J) (o : OuterData) (ho : o.Check J d)
    (f : ProofFamily Name I) (equations : S → Equation Name) (hcard : Fintype.card I=o.t)
    (hs : ∀ s : Name → F₂, equationFraction equations s≤3/4) :
    (J:ℝ)-1/2 < f.finiteCost (d.realize hJ hd) (o.realize hJ d hd ho)
      (tableGrid d.m d.n (tableAccuracy J d o) (tableAccuracy_pos hJ d hd o ho)) equations := by
  have hk : o.k≤Fintype.card I := by rw [hcard]; exact ho.2.2.2.2.1
  have hc := f.finiteCost_close hJ d hd o ho equations hk
  have hb := f.cost_gt (by exact_mod_cast hJ : (1:ℝ)≤J) (d.realize hJ hd)
    (o.realize hJ d hd ho) equations hs hcard
  have := (abs_lt.mp hc).2
  linarith
end MinUncut.Outer

end
end

end OAI
