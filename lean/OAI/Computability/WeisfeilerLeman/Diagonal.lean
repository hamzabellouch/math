import OAI.Computability.WeisfeilerLeman.BoundedRun

namespace OAI

namespace WLTime.Diagonal
@[simp] theorem unary_length (n : ℕ) : (unary n).length=n+1 := by simp [unary]
@[simp] theorem entryBits_length (e : Entry) : (entryBits e).length=e.1+e.2.1+e.2.2+3 := by
  simp [entryBits]; omega
 theorem tableBits_length_upper (es : List Entry) (q g : ℕ)
    (he : ∀ e∈es,e.1<q ∧ e.2.1<g ∧ e.2.2<3) :
    (tableBits es).length ≤ (q+g+3)*es.length := by
  induction es with
  | nil => simp [tableBits]
  | cons e es ih =>
    have h := he e (by simp)
    have hs := ih (fun x hx => he x (by simp [hx]))
    change (entryBits e++tableBits es).length ≤ _
    rw [List.length_append,entryBits_length,List.length_cons]
    nlinarith
 theorem tableBits_length_lower (es : List Entry) : es.length ≤ (tableBits es).length := by
  induction es with
  | nil => simp [tableBits]
  | cons e es ih =>
    change (e::es).length ≤ (entryBits e++tableBits es).length
    rw [List.length_cons,List.length_append,entryBits_length]
    omega
 theorem designation_length (M : OneTape) :
    (designation M).length=2*(M.states+M.symbols+2+(tableBits (raw M).table).length)+1 := by
  simp only [designation,List.length_append,unary_length,description,Raw.bits,raw]
  ring
 theorem designation_bounds (M : OneTape) {m : ℕ} (hm : (designation M).length ≤ m) :
    M.states ≤ m ∧ M.symbols ≤ m ∧ M.states*M.symbols ≤ m ∧
    (tableBits (raw M).table).length ≤ m := by
  rw [designation_length] at hm
  have h := tableBits_length_lower (raw M).table
  rw [(raw_valid M).2.2.1] at h
  change M.states*M.symbols ≤ (tableBits (raw M).table).length at h
  omega
 theorem designation_upper (M : OneTape) (B : ℕ) (hq : M.states ≤ B) (hg : M.symbols ≤ B)
    (hB : 3 ≤ B) : (designation M).length ≤ 13*B^3 := by
  have he := tableBits_length_upper (raw M).table M.states M.symbols (raw_valid M).2.2.2
  rw [(raw_valid M).2.2.1] at he
  have ht : (tableBits (raw M).table).length ≤ 3*B^3 := by
    calc
      _ ≤ (M.states+M.symbols+3)*(M.states*M.symbols) := he
      _ ≤ (3*B)*(B*B) := Nat.mul_le_mul (by omega) (Nat.mul_le_mul hq hg)
      _ = 3*B^3 := by ring
  have hp : B ≤ B^3 := Nat.le_self_pow (by decide) B
  rw [designation_length]
  omega
end WLTime.Diagonal
namespace WLTime.Universal
 theorem stepBound_small (M : OneTape) {m : ℕ} (hfit : (Diagonal.designation M).length ≤ m)
    (hm : 1 ≤ m) : stepBound M ≤ 1000*m^2 := by
  obtain ⟨hq,hg,hqg,hbits⟩ := Diagonal.designation_bounds M hfit
  unfold stepBound
  calc
    _ ≤ (m+1)*(30*m+60*m+60*m+100)+50*m+100*m+100 := by gcongr
    _ ≤ 1000*m^2 := by nlinarith
 theorem timeBound_small (s : ℕ) (M : OneTape) {m : ℕ}
    (hfit : (Diagonal.designation M).length ≤ m) (hm : 2 ≤ m)
    (hs : 1 ≤ s) (hsm : 18*s ≤ m)
    (hfactor : 8*((boundedProgram s).scratch+Fintype.card Reg+1)*1200^2 ≤ m) :
    timeBound s M m ≤ m^(2*s+5) := by
  obtain ⟨hq,hg,_,_⟩ := Diagonal.designation_bounds M hfit
  have hstep := stepBound_small M hfit (by omega)
  have hpow : m ≤ m^s := Nat.le_self_pow (by omega) m
  have h1 : 65*m+3*M.states+5*M.symbols+21+(stepBound M+18*s)*m^s ≤ 1200*m^(s+2) := by
    rw [pow_add,pow_two]
    have hm2 : m ≤ m*m := by nlinarith
    have hpos : 1 ≤ m^s := one_le_pow₀ (by omega)
    nlinarith
  unfold timeBound
  calc
    _ ≤ 8*((boundedProgram s).scratch+Fintype.card Reg+1)*(1200*m^(s+2))^2 := by gcongr
    _ = (8*((boundedProgram s).scratch+Fintype.card Reg+1)*1200^2)*m^(2*s+4) := by ring
    _ ≤ m*m^(2*s+4) := Nat.mul_le_mul_right _ hfactor
    _ = m^(2*s+5) := by
      simpa only [show 2*s+5=(2*s+4)+1 by omega] using (pow_succ' m (2*s+4)).symm
end WLTime.Universal

namespace WLTime.Diagonal

theorem pointwise_contradiction (D : OneTape) (w : List Bool) (T : ℕ)
    (ht : D.toTM.halts w) (hb : D.toTM.time w ≤ T)
    (hc : D.toTM.accepts w ↔ ¬∃ t ≤ T,(D.toTM.run w t).state.val=1) : False := by
  rw [bounded_accepts_iff D w T ht hb] at hc
  exact not_iff_self hc.symm

theorem padded_designation (D : OneTape) (data : List Bool) (m : ℕ)
    (hm : (designation D).length+data.length ≤ m) :
    let w := designation D++data++List.replicate (m-((designation D).length+data.length)) false
    w.length=m ∧ designated w=some D := by
  dsimp
  constructor
  · simp only [List.length_append,List.length_replicate]
    omega
  · rw [List.append_assoc]
    exact designated_prefix D _

end WLTime.Diagonal

namespace WLTime.Numeric
open Filter
open scoped Topology
 theorem polylog_sublinear (K r : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, K*((Nat.digits 2 m).length+1)^r ≤ m := by
  have h : (fun x : ℝ => ((K : ℝ)*3^r)*(Real.logb 2 x)^r) =o[atTop] id :=
    Real.isLittleO_pow_logb_id_atTop.const_mul_left _
  have hb := tendsto_natCast_atTop_atTop.eventually (h.bound (by norm_num : (0 : ℝ)<1))
  have hall : ∀ᶠ m : ℕ in atTop, K*((Nat.digits 2 m).length+1)^r ≤ m := by
    filter_upwards [hb,eventually_ge_atTop 2] with m hm h2
    have hm0 : m ≠ 0 := by omega
    have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast h2
    have hmposR : (0 : ℝ) < m := by linarith
    have hlog : 1 ≤ Real.logb 2 (m : ℝ) := by
      rw [Real.le_logb_iff_rpow_le (by norm_num) hmposR]
      simpa using hm2R
    have hd : (((Nat.digits 2 m).length+1 : ℕ) : ℝ) ≤ 3*Real.logb 2 m := by
      rw [Nat.length_digits 2 m (by omega) hm0]
      push_cast
      have ht := Real.natLog_le_logb m 2
      norm_num at ht
      linarith
    have hl0 : 0 ≤ Real.logb 2 (m : ℝ) := by linarith
    simp only [Real.norm_eq_abs,Function.id_def] at hm
    rw [abs_of_nonneg (by positivity),abs_of_nonneg (Nat.cast_nonneg m),one_mul] at hm
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((Nat.digits 2 m).length+1 : ℕ)) hd r
    have hp' := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg K)
    rw [mul_pow] at hp'
    have hh : (K : ℝ)*(((Nat.digits 2 m).length+1 : ℕ) : ℝ)^r ≤ (m : ℝ) := by nlinarith
    exact_mod_cast hh
  exact eventually_atTop.mp hall
end WLTime.Numeric

namespace WLTime.Numeric
noncomputable def base (C m : ℕ) := 1+C*m^2*((C*m^2+1)^2+1)
 theorem base_lower (C m : ℕ) (hC : 1≤C) : m ≤ base C m := by
  have hm : m≤ m^2 := Nat.le_self_pow (by decide) m
  have hp : 1≤(C*m^2+1)^2+1 := by omega
  have hc : m^2≤C*m^2 := Nat.le_mul_of_pos_left _ (by omega)
  have ht := Nat.le_mul_of_pos_right (C*m^2) (by omega : 0<(C*m^2+1)^2+1)
  dsimp [base]; omega
 theorem base_upper (C m : ℕ) (hC : 1≤C) (hm : 1≤ m) : base C m ≤ 6*C^3*m^6 := by
  have hCm : 1≤C*m^2 := by
    have : 0<C*m^2 := by positivity
    omega
  have h1 : (C*m^2+1)^2+1≤5*(C*m^2)^2 := by nlinarith
  have h2 := Nat.mul_le_mul_left (C*m^2) h1
  have h3 : 1≤C^3*m^6 := by
    have : 0<C^3*m^6 := by positivity
    omega
  dsimp [base]
  nlinarith [show C*m^2*(5*(C*m^2)^2)=5*C^3*m^6 by ring]
noncomputable def chooseOrder (C n : ℕ) := Nat.findGreatest (fun m => base C m≤n) n
 theorem chooseOrder_bounds (C n m₀ : ℕ) (hC : 1≤C) (hn : base C m₀≤n) :
    m₀≤chooseOrder C n ∧ base C (chooseOrder C n)≤n ∧ n<base C (chooseOrder C n+1) := by
  have hb : m₀≤n := (base_lower C m₀ hC).trans hn
  have h1 := Nat.le_findGreatest (P:=fun x => base C x≤n) hb hn
  have h2 := Nat.findGreatest_spec (P:=fun x => base C x≤n) hb hn
  refine ⟨h1,h2,?_⟩
  by_cases hlt : chooseOrder C n<n
  · exact lt_of_not_ge ((Nat.findGreatest_eq_iff.mp (rfl : chooseOrder C n=chooseOrder C n)).2.2
      (by omega) (by omega))
  · have hle : chooseOrder C n≤n := Nat.findGreatest_le n
    have h := base_lower C (chooseOrder C n+1) hC
    omega
 theorem order_polynomial (C n m : ℕ) (hC : 1≤C) (hm : 384*C^3≤ m)
    (hn : n<base C (m+1)) : n≤ m^8 := by
  have hc : 1≤C^3 := one_le_pow₀ hC
  have hm1 : 1≤ m := by nlinarith
  have hu := base_upper C (m+1) hC (by omega)
  have hp : (m+1)^6≤64*m^6 := by
    calc
      _≤(2*m)^6 := Nat.pow_le_pow_left (by omega) 6
      _=64*m^6 := by ring
  have hx : n≤384*C^3*m^6 := by nlinarith
  calc
    n≤384*C^3*m^6 := hx
    _≤ m*m^6 := Nat.mul_le_mul_right _ hm
    _=m^7 := by ring
    _≤ m^8 := Nat.pow_le_pow_right (by omega) (by decide)
end WLTime.Numeric
namespace WLTime.Numeric
 theorem pow_mono (m i j : ℕ) (hm : 0 < m) (h : i ≤ j) : m^i ≤ m^j := Nat.pow_le_pow_right hm h
 theorem grow_one (m X : ℕ) (hm : 2≤ m) (hX : 1≤X) : X+1≤X*m := by nlinarith
 theorem space_arith (m X : ℕ) (hm : m≤X) (hX : 0<X) : 2*(X-1)+m+2<4*X := by omega
 theorem digits_le (n : ℕ) : (Nat.digits 2 n).length≤ n+1 := by
  apply (Nat.digits_length_le_iff (by decide) n).mpr
  exact (Nat.lt_two_pow_self (n:=n)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
 theorem digits_polynomial (n m e : ℕ) (he : 0< e) (hn : n≤ m^e) :
    (Nat.digits 2 n).length+1≤(e+1)*((Nat.digits 2 m).length+1) := by
  have hm := Nat.lt_base_pow_length_digits (m:=m) (by decide : 1< 2)
  have hp := Nat.pow_lt_pow_left hm (by omega : e≠0)
  have hn' : n< 2^((Nat.digits 2 m).length*e) := by
    rw [pow_mul] ; exact hn.trans_lt hp
  have hl := (Nat.digits_length_le_iff (by decide : 1< 2) n).mpr hn'
  nlinarith
 theorem sum_le_pow {m a b e : ℕ} (hm : 2≤ m) (ha : a≤ m^e) (hb : b≤ m^e) :
    a+b≤ m^(e+1) := by
  rw [pow_succ]
  nlinarith
 theorem input_small (n m : ℕ) (hm : 8≤ m) (hn : n≤ m^8) :
    2*(Nat.digits 2 n).length+1+2*n^2≤ m^20 := by
  have hd := digits_le n
  have hp : 1≤ m^8 := one_le_pow₀ (by omega)
  have hq : m^8≤ m^16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hn2 : n^2≤ m^16 := by simpa only [←pow_mul] using Nat.pow_le_pow_left hn 2
  have hr : 8≤ m^4 := (show 8≤ m by omega).trans (Nat.le_self_pow (by decide) m)
  rw [show 20=16+4 by decide,pow_add]
  nlinarith
 theorem scale6 (m X x : ℕ) (hm : 7≤ m) (hx : x≤X) (hX : 1≤X) : 6*x+1≤X*m := by
  nlinarith only [hm,hx,hX]
 theorem consumer_inside (m B Y W X : ℕ) (hm : 16≤ m) (hmX : m≤X) (hB : B≤X) (hY : Y≤X) (hW : W≤X) :
    m+B+5*Y+W+3≤X*m := by nlinarith only [hm,hmX,hB,hY,hW]
 theorem writer_small (C charge n m : ℕ) (hm : 128≤ m) (hC : C≤ m)
    (hf : charge≤ m) (hn : n≤ m^8) :
    17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(2*(Nat.digits 2 n).length+1)+1)+
      charge*(6*(C+n+m+2)^27+1)^8 ≤ m^2400 := by
  have hm0 : 0< m := by omega
  have hm1 : 1≤ m := by omega
  have hm2 : 2≤ m := by omega
  have hm7 : 7≤ m := by omega
  have hp (e : ℕ) (he : e≠0) : m≤ m^e := Nat.le_self_pow he m
  have hd := digits_le n
  have hQ : C+n+m+2≤ m^11 := by
    have h8 := hp 8 (by decide)
    have h3 : 4≤ m^3 := (show 4≤ m by omega).trans (hp 3 (by decide))
    rw [show 11=8+3 by decide,pow_add]
    nlinarith only [hC,hn,h8,h3,hm2]
  have hQp : (C+n+m+2)^27≤ m^(11*27) := by
    exact (Nat.pow_le_pow_left hQ 27).trans_eq (pow_mul m 11 27).symm
  have h297 : 1≤ m^(11*27) := one_le_pow₀ hm1
  have hbody : 6*(C+n+m+2)^27+1≤ m^(11*27+1) := by
    rw [pow_succ m (11*27)]
    exact scale6 m (m^(11*27)) ((C+n+m+2)^27) hm7 hQp h297
  have hbp : (6*(C+n+m+2)^27+1)^8≤ m^((11*27+1)*8) := by
    exact (Nat.pow_le_pow_left hbody 8).trans_eq (pow_mul m (11*27+1) 8).symm
  have hc : charge*(6*(C+n+m+2)^27+1)^8≤ m^((11*27+1)*8+1) := by
    calc
      _≤ m*m^((11*27+1)*8) := Nat.mul_le_mul hf hbp
      _=m^((11*27+1)*8+1) := (pow_succ' m ((11*27+1)*8)).symm
  have h8 := hp 8 (by decide)
  have h16 : (m^8)^2=m^16 := by ring
  have hn2 : (n+1)^2≤ 4*m^16 := by nlinarith only [hn,h8,hm,h16]
  have hsmall : 17*m+3+24*((Nat.digits 2 n).length+1)*(n+1)+(2*(2*(Nat.digits 2 n).length+1)+1)≤ m^20 := by
    have h4 : 256≤ m^4 := (show 256≤128^4 by decide).trans (Nat.pow_le_pow_left hm 4)
    have hn16 : n≤ m^16 := hn.trans (Nat.pow_le_pow_right hm0 (by decide))
    have hm16 := hp 16 (by decide)
    rw [show 20=16+4 by decide,pow_add]
    have hplus : (Nat.digits 2 n).length+1≤2*(n+1) := by omega
    have hprod := Nat.mul_le_mul_right (n+1) hplus
    nlinarith only [hprod,hn2,h4,hn16,hm16,hm,hd]
  have h20 : m^20≤ m^((11*27+1)*8+1) := pow_mono m 20 ((11*27+1)*8+1) hm0 (by decide)
  exact (sum_le_pow hm2 (hsmall.trans h20) hc).trans
    (pow_mono m _ _ hm0 (by decide))
 theorem consumer_small (m a B Y v factor overhead : ℕ) (hm : 16≤ m)
    (hB : B≤ m^2400) (hY : Y≤ m^20) (hv : v≤ m^(8*a))
    (hf : factor≤ m) (ho : overhead≤ m) :
    factor*(m+B+5*Y+overhead*v+3)^2≤ m^(2*(max 2400 (8*a+1))+3) := by
  have hm0 : 0< m := lt_of_lt_of_le (by decide : 0<16) hm
  let r := max 2400 (8*a+1)
  have hr : 1≤ r := (by decide : 1≤ 2400).trans (le_max_left _ _)
  have h2400 : m^2400≤ m^r := pow_mono m 2400 r hm0 (le_max_left _ _)
  have h20 : m^20≤ m^r := Nat.pow_le_pow_right hm0 ((by decide : 20≤ 2400).trans (le_max_left _ _))
  have h8 : overhead*v≤ m^r := by
    calc
      _≤ m*m^(8*a) := Nat.mul_le_mul ho hv
      _=m^(8*a+1) := by ring
      _≤ m^r := Nat.pow_le_pow_right hm0 (le_max_right _ _)
  have hmr : m≤ m^r := Nat.le_self_pow (Nat.ne_of_gt hr) m
  have hB' := hB.trans h2400
  have hY' := hY.trans h20
  have hinside : m+B+5*Y+overhead*v+3≤ m^(r+1) := by
    rw [pow_succ]
    exact consumer_inside _ _ _ _ _ hm hmr hB' hY' h8
  calc
    _≤ m*(m^(r+1))^2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hinside 2)
    _=m^(2*r+3) := by ring
end WLTime.Numeric

namespace WLTime.OneTape.Symbolic
open scoped Classical
 theorem coefficient_pos (U : OneTape) (d q : ℕ) : 0< coefficient U d q (d+q+2) := by
  unfold coefficient Compression.ConsistencyData.rectCoefficient
  apply Nat.mul_pos
  · apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0,by omega⟩,Sum.inl (.inl .dummy))⟩
  · exact Compression.ConsistencyData.tagValues_card_pos _ _
end WLTime.OneTape.Symbolic
namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 theorem worstTime_ge (A : Model) (p : InputClass) {n : ℕ} (G H : Graph n) (hp : p.contains G H) :
    A.time n (encodePair G H)≤ worstTime A p n := by
  unfold worstTime
  exact (show A.time n (encodePair G H)≤ if p.contains G H then A.time n (encodePair G H) else 0 by simp [hp]).trans
    (Finset.le_sup (f:=fun pair : Graph n × Graph n => if p.contains pair.1 pair.2 then A.time n (encodePair pair.1 pair.2) else 0)
      (Finset.mem_univ (G,H)))
 theorem promised_pair (U : OneTape) (d q : ℕ) (hr : 2≤ d+q) (w : List Bool) (pad : ℕ) (p : InputClass) :
    p.contains (pairGraph U d q hr w pad 0) (pairGraph U d q hr w pad 1) := by
  cases p with
  | unrestricted => trivial
  | diameterTwo => exact ⟨pairGraph_diameter U d q hr w pad 0,pairGraph_diameter U d q hr w pad 1⟩

 theorem designation_small (U : OneTape) (d q : ℕ) (A : TM) :
    ∃m₀,∀m≥ m₀,∀n≤ m^8,(Diagonal.designation (consumer U d q A n)).length≤ m := by
  let K := statesBound U d q A+alphabetBound U d q A+3
  obtain ⟨m₀,hm₀⟩ := Numeric.polylog_sublinear (13*(K*9)^3) 3
  refine ⟨m₀,?_⟩
  intro m hm n hn
  have hd := Numeric.digits_polynomial n m 8 (by decide) hn
  let B := K*((Nat.digits 2 n).length+1)
  have hq : (consumer U d q A n).states≤ B := by
    exact (consumer_states U d q A n).trans (Nat.mul_le_mul_right _ (by dsimp [K]; omega))
  have hg : (consumer U d q A n).symbols≤ B := by
    have h := consumer_alphabet U d q A n
    dsimp [B,K]; nlinarith
  have hB : 3≤ B := by dsimp [B,K]; nlinarith
  calc
    _≤ 13*B^3 := Diagonal.designation_upper _ B hq hg hB
    _≤ 13*(K*9*((Nat.digits 2 m).length+1))^3 := by
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      dsimp [B]
      nlinarith
    _=(13*(K*9)^3)*((Nat.digits 2 m).length+1)^3 := by ring
    _≤ m := hm₀ m hm

 theorem time_window (m s : ℕ) (hm : 2≤ m) (hs : 1≤ s) : m^(2*s+5)≤ m^(3*s+6)-1 := by
  have he : 2*s+5+1≤ 3*s+6 := by omega
  have hp := Nat.pow_le_pow_right (by omega : 0< m) he
  have hpos : 1≤ m^(2*s+5) := one_le_pow₀ (by omega)
  rw [pow_succ] at hp
  have hh : m^(2*s+5)+1≤ m^(2*s+5)*m := by
    exact Numeric.grow_one _ _ hm hpos
  exact Nat.le_sub_one_of_lt (lt_of_lt_of_le (Nat.lt_add_one _) (hh.trans hp))

 theorem space_window (m d q : ℕ) (hm : 2≤ m) (hd : 1≤ d) (hq : d+3≤ q) :
    2*(m^d-1)+m+2< m^(q+1) := by
  have hp := Nat.pow_le_pow_right (by omega : 0< m) (show d+2≤ q+1 by omega)
  have hmd := Nat.le_self_pow (by omega : d≠0) m
  rw [pow_add,pow_two] at hp
  have hm2 : 4≤ m*m := by nlinarith only [hm]
  have hx : m^d*4≤ m^(q+1) := (Nat.mul_le_mul_left (m^d) hm2).trans hp
  have ht : 0< m^d := pow_pos (by omega) _
  have hl := Numeric.space_arith m (m^d) hmd ht
  exact hl.trans_le (by simpa only [Nat.mul_comm] using hx)
end WLTime
namespace WLTime
open OneTape.Symbolic OneTape.Symbolic.FullWriter
open scoped Classical
 def conventionShift : Convention → ℕ | .joint => 1 | .separate => 2
 theorem pair_correct_convention (U : OneTape) (d q : ℕ) (hr : 2≤ d+q) (w : List Bool)
    (hm : 2≤ w.length) (pad : ℕ) (hL : 2*(w.length^d-1)+w.length+2< w.length^(q+1))
    (c : Convention) (k : ℕ) (hk : k=d+q+conventionShift c) :
    Equivalent c k (pairGraph U d q hr w pad 0) (pairGraph U d q hr w pad 1) ↔
      ¬∃t≤ w.length^d-1,(U.toTM.run w t).state.val=1 := by
  subst k
  cases c with
  | joint => exact (pairGraph_correct U d q hr w hm pad hL).1
  | separate => exact (pairGraph_correct U d q hr w hm pad hL).2

 theorem tm_pointwise (s d q k a n m : ℕ) (c : Convention) (p : InputClass) (A : TM)
    (hA : Decides (.turing A) c k p) (hk : k=d+q+conventionShift c)
    (hm : 128≤ m) (hs : 1≤ s) (hd : d=3*s+6) (hq : d+3≤ q)
    (ha : 2*max 2400 (8*a+1)+3≤ s)
    (hbase : baseOrder (Universal.machine s) d q m≤ n) (hn : n≤ m^8)
    (hfit : (Diagonal.designation (consumer (Universal.machine s) d q A n)).length≤ m)
    (hC : coefficient (Universal.machine s) d q (d+q+2)≤ m)
    (hcharge : (body (Universal.machine s) d q).charge≤ m)
    (hfactor : consumerFactor (Universal.machine s) d q A≤ m)
    (hAfac : 8*A.tapes+2≤ m)
    (hUfac : 8*((Universal.boundedProgram s).scratch+Fintype.card Universal.Reg+1)*1200^2≤ m)
    (hsm : 18*s≤ m) :
    ¬worstTime (.turing A) p n≤ n^a := by
  intro hfast
  let U := Universal.machine s
  let D := consumer U d q A n
  let z := List.replicate (m-(Diagonal.designation D).length) false
  let w := Diagonal.designation D++z
  have hlen : w.length=m := by
    dsimp [w,z]
    rw [List.length_append,List.length_replicate,Nat.add_sub_of_le hfit]
  have hr : 2≤ d+q := by omega
  let G := pairGraph U d q hr w (n-baseOrder U d q w.length) 0
  let H := pairGraph U d q hr w (n-baseOrder U d q w.length) 1
  let ys := encodePair G H
  have hgn : (listing U d q (d+q+2) w (n-baseOrder U d q w.length)).items.length=n := by
    rw [listing_length,hlen,Nat.add_sub_of_le hbase]
  have hprom : p.contains G H := promised_pair U d q hr w _ p
  have hdec := hA _ G H hprom
  change A.halts ys ∧ (A.accepts ys ↔ Equivalent c k G H) at hdec
  have htime : A.time ys≤ n^a := by
    have ht := worstTime_ge (.turing A) p G H hprom
    change A.time ys≤ worstTime (.turing A) p _ at ht
    rw [hgn] at ht
    exact ht.trans hfast
  have hprod := consumer_correct U d q A n w (by rw [hlen]; omega) hr
    (by simpa only [hlen] using hbase) ys rfl (A.time ys) (A.time_halted ys hdec.1)
  have hy : ys.length≤ m^20 := by
    have hy := input_length U d q n w hr (by simpa only [hlen] using hbase)
    exact hy.le.trans (Numeric.input_small n m (by omega) hn)
  have hb : budget U d q n w.length≤ m^2400 := by
    rw [hlen]
    simpa only [budget,encodeNat_length] using
      Numeric.writer_small (coefficient U d q (d+q+2)) (body U d q).charge n m hm hC hcharge hn
  have hv : A.time ys≤ m^(8*a) := by
    calc
      _≤ n^a := htime
      _≤(m^8)^a := Nat.pow_le_pow_left hn a
      _=m^(8*a) := (pow_mul m 8 a).symm
  have hDtime : D.toTM.time w≤ m^s := by
    have hbnd := Numeric.consumer_small m a (budget U d q n w.length) ys.length (A.time ys)
      (consumerFactor U d q A) (8*A.tapes+2) (by omega) hb hy hv hfactor hAfac
    have ht := hprod.2.1
    rw [hlen] at ht hbnd
    exact ht.trans (hbnd.trans (Nat.pow_le_pow_right (by omega) ha))
  have hU := Universal.machine_correct s D z (by change 0< w.length; rw [hlen]; omega)
  change U.toTM.halts w ∧ U.toTM.time w≤ Universal.timeBound s D w.length ∧
    (U.toTM.accepts w ↔ ¬∃t≤ w.length^s,(D.toTM.run w t).state.val=1) at hU
  have hUt : U.toTM.time w≤ w.length^d-1 := by
    apply hU.2.1.trans
    rw [hlen]
    apply (Universal.timeBound_small s D hfit (by omega) hs hsm hUfac).trans
    simpa only [hd] using time_window m s (by omega) hs
  have hwin : 2*(w.length^d-1)+w.length+2< w.length^(q+1) := by
    rw [hlen]; exact space_window m d q (by omega) (by omega) hq
  have hpair := pair_correct_convention U d q hr w (by rw [hlen]; omega) (n-baseOrder U d q w.length) hwin c k hk
  have hUb := Diagonal.bounded_accepts_iff U w (w.length^d-1) hU.1 hUt
  have hEq : Equivalent c k G H ↔ ¬U.toTM.accepts w := hpair.trans (not_congr hUb)
  have hc : D.toTM.accepts w ↔ ¬∃t≤ m^s,(D.toTM.run w t).state.val=1 := by
    have hh := hprod.2.2.trans (not_congr (hdec.2.trans hEq))
    rw [not_not] at hh
    exact hh.trans (by simpa only [hlen] using hU.2.2)
  exact Diagonal.pointwise_contradiction D w (m^s) hprod.1 hDtime hc
end WLTime

end OAI
