import OAI.Geometry.HarmonicGrowth.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace HarmonicCounterexample.Certificate

/-- The binomial polynomial, evaluated in exact rational arithmetic. -/
def binomRat (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | k+1 => binomRat x k * (x-k)/(k+1)

lemma binomRat_eq_pochhammer (x : ℚ) (k : ℕ) :
    binomRat x k = (descPochhammer ℚ k).eval x / k.factorial := by
  induction k with
  | zero => simp [binomRat]
  | succ k ih =>
    rw [binomRat,ih,descPochhammer_succ_eval,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hn : (k.factorial:ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (k:ℚ)+1 ≠ 0 := by positivity
    field_simp

lemma binomRat_nat (n k : ℕ) : binomRat n k = (n.choose k : ℚ) := by
  rw [binomRat_eq_pochhammer,Nat.cast_choose_eq_descPochhammer_div]

lemma binomRat_step (x : ℚ) (k : ℕ) :
    binomRat (x+1) (k+1) = binomRat x (k+1)+binomRat x k := by
  induction k with
  | zero => simp [binomRat]
  | succ k ih =>
    rw [binomRat,ih]
    simp only [binomRat,Nat.cast_add,Nat.cast_one]
    have h1 : (k:ℚ)+1 ≠ 0 := by positivity
    have h2 : (k:ℚ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

lemma binomRat_difference (x : ℚ) (k : ℕ) :
    binomRat (x+1) (k+1)-binomRat x (k+1) = binomRat x k := by
  rw [binomRat_step]; ring

/-- Coefficients in the exact degree-six reflected Vandermonde expansion. -/
def prefixCoefficient (l : ℚ) (j : ℕ) : ℚ :=
  (-1)^j * binomRat (l+6-j) (6-j) * ((6+j).choose 6 : ℚ)

/-- An exact antiderivative of the harmonic multiplicity kernel for s=8. -/
def countPrefix (l x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 7,prefixCoefficient l j * binomRat (x+7) (7+j)

lemma binomRat_product_six (x : ℚ) (j : ℕ) (hj : j < 7) :
    binomRat (x+6) (6+j) * ((6+j).choose 6 : ℚ) =
      binomRat (x+6) 6 * binomRat x j := by
  interval_cases j <;> norm_num [binomRat,Nat.choose] <;> ring

lemma reflected_binomial_six (l x : ℚ) :
    (∑ j ∈ Finset.range 7,(-1:ℚ)^j*binomRat (l+6-j) (6-j)*binomRat x j) =
      binomRat (l-x+6) 6 := by
  simp only [Finset.sum_range_succ,Finset.sum_range_zero]
  norm_num [binomRat]
  ring

lemma reflected_vandermonde_six (l x : ℚ) :
    (∑ j ∈ Finset.range 7,prefixCoefficient l j * binomRat (x+6) (6+j)) =
      binomRat (x+6) 6 * binomRat (l-x+6) 6 := by
  rw [← reflected_binomial_six l x,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := binomRat_product_six x j (Finset.mem_range.1 hj)
  unfold prefixCoefficient
  linear_combination (-1:ℚ)^j*binomRat (l+6-j) (6-j)*he

lemma countPrefix_difference (l x : ℚ) :
    countPrefix l x-countPrefix l (x-1) =
      binomRat (x+6) 6 * binomRat (l-x+6) 6 := by
  simp only [countPrefix,← Finset.sum_sub_distrib,← mul_sub]
  have he (j : ℕ) : binomRat (x+7) (7+j)-binomRat (x-1+7) (7+j) =
      binomRat (x+6) (6+j) := by
    rw [show x+7=(x+6)+1 by ring,show x-1+7=x+6 by ring,
      show 7+j=(6+j)+1 by omega,binomRat_difference]
  simp_rw [he]
  exact reflected_vandermonde_six l x

lemma countPrefix_neg_one (l : ℚ) : countPrefix l (-1) = 0 := by
  unfold countPrefix
  apply Finset.sum_eq_zero
  intro j _
  have hz : binomRat (6:ℚ) (7+j) = 0 := by
    rw [show (6:ℚ) = ((6:ℕ):ℚ) from rfl,binomRat_nat,
      Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  norm_num only at *
  rw [hz,mul_zero]

end HarmonicCounterexample.Certificate

end

noncomputable section
open scoped BigOperators

namespace HarmonicCounterexample.Certificate
open scoped BigOperators

lemma binomRat_mul_succ (x : ℚ) (k : ℕ) :
    ((k:ℚ)+1)*binomRat x (k+1) = (x-k)*binomRat x k := by
  rw [binomRat]
  have hk : (k:ℚ)+1 ≠ 0 := by positivity
  field_simp

lemma shifted_binom_difference (x : ℚ) (k : ℕ) :
    binomRat (x+7) (k+1)-binomRat (x-1+7) (k+1) =
      binomRat (x+6) k := by
  rw [show x+7=(x+6)+1 by ring,show x-1+7=x+6 by ring,binomRat_difference]

def chargePrimitive (l x : ℚ) (j : ℕ) : ℚ :=
  (l-2*j)^2*binomRat (x+7) (7+j)+
  4*(7+j)*(2*j+1-l)*binomRat (x+7) (8+j)+
  4*(7+j)*(8+j)*binomRat (x+7) (9+j)

lemma chargePrimitive_difference (l x : ℚ) (j : ℕ) :
    chargePrimitive l x j-chargePrimitive l (x-1) j =
      (l-2*x)^2*binomRat (x+6) (6+j) := by
  have hd0 : binomRat (x+7) (7+j)-binomRat (x-1+7) (7+j) =
      binomRat (x+6) (6+j) := by
    simpa only [show (6+j)+1=7+j by omega] using shifted_binom_difference x (6+j)
  have hd1 : binomRat (x+7) (8+j)-binomRat (x-1+7) (8+j) =
      binomRat (x+6) (7+j) := by
    simpa only [show (7+j)+1=8+j by omega] using shifted_binom_difference x (7+j)
  have hd2 : binomRat (x+7) (9+j)-binomRat (x-1+7) (9+j) =
      binomRat (x+6) (8+j) := by
    simpa only [show (8+j)+1=9+j by omega] using shifted_binom_difference x (8+j)
  have h7 : (7+(j:ℚ))*binomRat (x+6) (7+j) =
      (x-j)*binomRat (x+6) (6+j) := by
    have h := binomRat_mul_succ (x+6) (6+j)
    simpa only [Nat.cast_add,Nat.cast_ofNat,show (6+j)+1=7+j by omega,
      show (6:ℚ)+j+1=7+j by ring,show x+6-(6+j)=x-j by ring] using h
  have h8 : (8+(j:ℚ))*binomRat (x+6) (8+j) =
      (x-j-1)*binomRat (x+6) (7+j) := by
    have h := binomRat_mul_succ (x+6) (7+j)
    simpa only [Nat.cast_add,Nat.cast_ofNat,show (7+j)+1=8+j by omega,
      show (7:ℚ)+j+1=8+j by ring,show x+6-(7+j)=x-j-1 by ring] using h
  unfold chargePrimitive
  linear_combination (l-2*j)^2*hd0+4*(7+j)*(2*j+1-l)*hd1+
    4*(7+j)*(8+j)*hd2+4*(7+j)*h8+4*(x+j-l)*h7

def chargePrefix (l x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 7,prefixCoefficient l j * chargePrimitive l x j

lemma chargePrefix_difference (l x : ℚ) :
    chargePrefix l x-chargePrefix l (x-1) =
      (l-2*x)^2*(binomRat (x+6) 6 * binomRat (l-x+6) 6) := by
  simp only [chargePrefix,← Finset.sum_sub_distrib,← mul_sub,chargePrimitive_difference]
  rw [← reflected_vandermonde_six l x,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma chargePrefix_neg_one (l : ℚ) : chargePrefix l (-1) = 0 := by
  unfold chargePrefix
  apply Finset.sum_eq_zero
  intro j _
  have hz (a : ℕ) (ha : 6 < a) : binomRat (6:ℚ) a = 0 := by
    rw [show (6:ℚ) = ((6:ℕ):ℚ) from rfl,binomRat_nat,
      Nat.choose_eq_zero_of_lt ha]
    rfl
  norm_num only [chargePrimitive]
  rw [hz (7+j) (by omega),hz (8+j) (by omega),hz (9+j) (by omega)]
  ring

/-- Exact finite prefix sum, with no asymptotic approximation. -/
lemma countPrefix_sum (l : ℚ) (b : ℕ) :
    countPrefix l b = ∑ i ∈ Finset.range (b+1),binomRat (i+6) 6*binomRat (l-i+6) 6 := by
  induction b with
  | zero =>
    simpa only [Nat.cast_zero,zero_add,sub_zero,Finset.sum_range_one,
      countPrefix_neg_one,sub_zero,zero_sub] using countPrefix_difference l 0
  | succ b ih =>
    rw [Finset.sum_range_succ,← ih]
    have h := countPrefix_difference l (b+1)
    norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at *
    linear_combination h

lemma chargePrefix_sum (l : ℚ) (b : ℕ) :
    chargePrefix l b = ∑ i ∈ Finset.range (b+1),
      (l-2*i)^2*(binomRat (i+6) 6*binomRat (l-i+6) 6) := by
  induction b with
  | zero =>
    simpa only [Nat.cast_zero,zero_add,sub_zero,Finset.sum_range_one,
      countPrefix_neg_one,chargePrefix_neg_one,sub_zero,zero_sub,mul_zero]
      using chargePrefix_difference l 0
  | succ b ih =>
    rw [Finset.sum_range_succ,← ih]
    have h := chargePrefix_difference l (b+1)
    norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at *
    linear_combination h

end HarmonicCounterexample.Certificate

end

noncomputable section
open scoped BigOperators

namespace HarmonicCounterexample.Certificate

/-- Exact data for a paired, nonmiddle Hopf-charge prefix at n=16,k=50000. -/
structure GroupCertificate where
  degree : ℕ
  bound : ℕ
  count : ℕ
  charge : ℕ
  degree_ge : 49964 ≤ degree
  degree_le : degree ≤ 50212
  nonmiddle : 2*bound < degree
  count_pos : 0 < count
  count_exact : 2*((degree:ℚ)+7)/7*countPrefix degree bound = count
  charge_exact : 2*((degree:ℚ)+7)/7*chargePrefix degree bound = charge
  strict_margin : 100000*(101*(degree:ℤ)*(degree+14)*count-charge) <
    101*99853*50000*(50000+14)*count

def group49964 : GroupCertificate where
  degree := 49964
  bound := 24981
  count := 13888287758329271038915838338823697180410613333616596372
  charge := 2312165983380140931035386729675103957803496428742680763975688480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49965 : GroupCertificate where
  degree := 49965
  bound := 24982
  count := 13892994571441177796092269017932123517191879506073955040
  charge := 2312906417010261280111152954626521801816156442573287832682996960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49966 : GroupCertificate where
  degree := 49966
  bound := 24982
  count := 13896071770494687102086423519436702139721438062313388444
  charge := 2313647072928294772245763917054243932742792731473966998573586080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49967 : GroupCertificate where
  degree := 49967
  bound := 24983
  count := 13900781033137730120680257287277794719058247863368144800
  charge := 2314387951196524998716244014384592243636890470899801010356452640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49968 : GroupCertificate where
  degree := 49968
  bound := 24983
  count := 13903859833604078635254340785499194137790890762866238750
  charge := 2315129051877251755390406042599057150975703715257600836029636000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49969 : GroupCertificate where
  degree := 49969
  bound := 24984
  count := 13908571546954940924897249640562731427446734730870205200
  charge := 2315870375032791046618482541541335905983361795216708511741209360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49970 : GroupCertificate where
  degree := 49970
  bound := 24984
  count := 13911651949603385779687013731247107832526279292080255786
  charge := 2316611920725475089125613838839608909994722714323571881376065920
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49971 : GroupCertificate where
  degree := 49971
  bound := 24985
  count := 13916366114839268469651737593009655027579467553789055360
  charge := 2317353689017652315905192963888357952472528736861512558429805440
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49972 : GroupCertificate where
  degree := 49972
  bound := 24985
  count := 13919448120439405510810718762483253831710889826770356368
  charge := 2318095679971687380113067603364908483104815200670934096108430720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49973 : GroupCertificate where
  degree := 49973
  bound := 24986
  count := 13924164738738028057402378262036288033847018914235216000
  charge := 2318837893649961158962599269786761165552463541870880564304054400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49974 : GroupCertificate where
  degree := 49974
  bound := 24986
  count := 13927248348059791981178899053942454367076011985753634992
  charge := 2319580330114870757620579854646666040580720424623129660263134080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49975 : GroupCertificate where
  degree := 49975
  bound := 24987
  count := 13931967420599392375201017886926333305198819823171958656
  charge := 2320322989428829513104005737693285651185956707461575899113855360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49976 : GroupCertificate where
  degree := 49976
  bound := 24987
  count := 13935052634413056863564026686550978016070299196716635560
  charge := 2321065871654266998177709623956191452612525873481139308715915136
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49977 : GroupCertificate where
  degree := 49977
  bound := 24988
  count := 13939774162372391837859287450088099995924698850925736960
  charge := 2321808976853629025252850280144840746536997784371034890832770048
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49978 : GroupCertificate where
  degree := 49978
  bound := 24988
  count := 13942860981448569694173052523898724229519580567325811800
  charge := 2322552305089377650286260342082089241871069630056112087761416320
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49979 : GroupCertificate where
  degree := 49979
  bound := 24989
  count := 13947584966006914931238809965921132769946289147318055040
  charge := 2323295856423991176680652364863707155292954349706226465246539392
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49980 : GroupCertificate where
  degree := 49980
  bound := 24852
  count := 13726417874021952219048244989951630522553470050712939068
  charge := 2324033957528860810981114387844380437265961015149140112583523104
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49981 : GroupCertificate where
  degree := 49981
  bound := 24379
  count := 12956126738828887229229916586729234192064729359350328832
  charge := 2324286705016456593329355464680958392754645463148788183073672704
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49982 : GroupCertificate where
  degree := 49982
  bound := 23949
  count := 12259393513443249037015121593470133446856583669949901800
  charge := 2323076097470201333071766337025461524387729857868761422119579520
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49983 : GroupCertificate where
  degree := 49983
  bound := 23553
  count := 11622891934716433003258928765223038659014477864482668800
  charge := 2319853875403646389707372577004289739517107651008715656837438720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49984 : GroupCertificate where
  degree := 49984
  bound := 23185
  count := 11037494282011431051784238178747388436994169825068168270
  charge := 2314375822667633760506049745267168633549399681292748470022214656
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49985 : GroupCertificate where
  degree := 49985
  bound := 22839
  count := 10493778391983641990841054725026088588102455693245951072
  charge := 2306525299379965935105784357816935963014738726287989212755086432
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49986 : GroupCertificate where
  degree := 49986
  bound := 22513
  count := 9988502939728659520021125201916280972175318383039733762
  charge := 2296342800176767881526107355886111634509006221747960203783118560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49987 : GroupCertificate where
  degree := 49987
  bound := 22204
  count := 9516730879122593436448376230756937797811483020997313280
  charge := 2283893858421900725490829254294265008042157660705331035189412608
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49988 : GroupCertificate where
  degree := 49988
  bound := 21909
  count := 9073549487238856287131135043259815933200493834747017400
  charge := 2269235173263643431626677077665848365260771726280643967259696960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49989 : GroupCertificate where
  degree := 49989
  bound := 21627
  count := 8657094817644791133008488942713530979213744045206263296
  charge := 2252515180288924141414360302063024863386054259132059583131547136
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49990 : GroupCertificate where
  degree := 49990
  bound := 21356
  count := 8264015965385342159513035055729245603049575322094110424
  charge := 2233820603753307834666473662382527509316247267742742825145168064
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49991 : GroupCertificate where
  degree := 49991
  bound := 21096
  count := 7893893761405052970224282959991510016414674604001505280
  charge := 2213371871525289738702831863369312749807099376120342676945058560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49992 : GroupCertificate where
  degree := 49992
  bound := 20845
  count := 7543440955479375411235518675335983776048842460933630300
  charge := 2191226521249228272925468041386988256770858125638763730145740480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49993 : GroupCertificate where
  degree := 49993
  bound := 20602
  count := 7210880113658638427082298235606851955484680271619200000
  charge := 2167491529899857969943977393537288753172004996694454389097600000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49994 : GroupCertificate where
  degree := 49994
  bound := 20367
  count := 6895821317222287701282881112875254366934776482671335548
  charge := 2142365977871585767963964263790873187822892941671010898067278272
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49995 : GroupCertificate where
  degree := 49995
  bound := 20138
  count := 6595219648307290265345193806765741986882488547670263392
  charge := 2115813029616002214087348976073231605706790175891448774207004768
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49996 : GroupCertificate where
  degree := 49996
  bound := 19917
  count := 6311323133150725350891417218982793769438501477489821208
  charge := 2088259922370988788818489100772347324205964844103809496636349120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49997 : GroupCertificate where
  degree := 49997
  bound := 19701
  count := 6039883430989879431208600072494475164900054571277040480
  charge := 2059505645466042165109979082976522137873210256765960241078494560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49998 : GroupCertificate where
  degree := 49998
  bound := 19490
  count := 5780624845272482152352393154128780684995181952980277960
  charge := 2029696620603233461622167074530773081520480976397322618699302080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group49999 : GroupCertificate where
  degree := 49999
  bound := 19285
  count := 5534443166240373848107238688827008139972354881880259520
  charge := 1999137407408279810863105865332837951123458735236943785669575872
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50000 : GroupCertificate where
  degree := 50000
  bound := 19085
  count := 5299777061337566084204493477759684847076614491969069180
  charge := 1967836127810546446323488048198233503016136752079526008075570304
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50001 : GroupCertificate where
  degree := 50001
  bound := 18889
  count := 5075162362899748448471426877671028081785711599536443712
  charge := 1935769852491330644567469812292688113657880395269885571092279616
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50002 : GroupCertificate where
  degree := 50002
  bound := 18698
  count := 4861453432347706873446861909994258318800489216516292500
  charge := 1903239709149432113519868764461725787688346137627001946676736000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50003 : GroupCertificate where
  degree := 50003
  bound := 18510
  count := 4656136949699734868512349769634687954974641077455852480
  charge := 1870022045846025895608678149875271401938256142807145931386893760
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50004 : GroupCertificate where
  degree := 50004
  bound := 18327
  count := 4461134212104155656211489083826659145491482343041023472
  charge := 1836595625002294858218189200525297532987555019925136446015924352
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50005 : GroupCertificate where
  degree := 50005
  bound := 18146
  count := 4272994699986525835309178525899952015175260261421869600
  charge := 1802512274871398551851649189636831679942173764650812531093413920
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50006 : GroupCertificate where
  degree := 50006
  bound := 17970
  count := 4094606721254812954090944152952026417526723501019640340
  charge := 1768450124540703461577457742497514376397417499327287153565004960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50007 : GroupCertificate where
  degree := 50007
  bound := 17796
  count := 3922667756323273891904405585975039680535569461402907840
  charge := 1733921874214932328469373938546825238606528763318681258909330240
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50008 : GroupCertificate where
  degree := 50008
  bound := 17626
  count := 3758950642255463044542101075905297573571522914758060600
  charge := 1699420453252423455801906038917260311931583937027426990482680960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50009 : GroupCertificate where
  degree := 50009
  bound := 17458
  count := 3601305601117003990240459751090230564713892818555219840
  charge := 1664621878546019737920775926157938389448706087666316480625127296
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50010 : GroupCertificate where
  degree := 50010
  bound := 17293
  count := 3450495525594143477671886737628393646073922256296622540
  charge := 1629813822716255327329163569883588502731107859869204589792808000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50011 : GroupCertificate where
  degree := 50011
  bound := 17131
  count := 3306302766649548751547248237926909578959985020945356480
  charge := 1595076401627172419052829807401397937050384146509627445371419584
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50012 : GroupCertificate where
  degree := 50012
  bound := 16971
  count := 3167651125531719203025405478324947179459339180045507040
  charge := 1560263806340702629961770002764564455490709290506337883664812480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50013 : GroupCertificate where
  degree := 50013
  bound := 16814
  count := 3035228563164572052906088508536204433296188525400584000
  charge := 1525664044791612965829901235518133468518824033223112857054497600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50014 : GroupCertificate where
  degree := 50014
  bound := 16659
  count := 2908005424403816697163858771907763987155699624215142560
  charge := 1491118490687369312869693564138913464022105676074516804886458368
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50015 : GroupCertificate where
  degree := 50015
  bound := 16507
  count := 2786624526421286381485504256482347202140112864227087360
  charge := 1456913201576209237592585194792201509642137622740028175632368640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50016 : GroupCertificate where
  degree := 50016
  bound := 16356
  count := 2669333909241434059382171641893207610615532827528850394
  charge := 1422647266847887973797701023597750420539533762187529617345015680
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50017 : GroupCertificate where
  degree := 50017
  bound := 16208
  count := 2557546703971620182395527210622603588060679588575555600
  charge := 1388830723718630450607882297469084646004865355045106576053848080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50018 : GroupCertificate where
  degree := 50018
  bound := 16061
  count := 2449598845152997314151115255303116905312409849921326000
  charge := 1355050034387311631694063012649947844944716763057238660845772800
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50019 : GroupCertificate where
  degree := 50019
  bound := 15916
  count := 2346113343834460393259133671029354525438795102666907712
  charge := 1321581223691465578166053631632049676479660891334308736278079552
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50020 : GroupCertificate where
  degree := 50020
  bound := 15774
  count := 2247631688549459277632792769219712657403647094729110080
  charge := 1288701213170404299705283703417602697307207690955620212731944960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50021 : GroupCertificate where
  degree := 50021
  bound := 15633
  count := 2152617884262865653793281964110239775160068214618576416
  charge := 1255981496724236406305872517426251821447875278135777602145997856
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50022 : GroupCertificate where
  degree := 50022
  bound := 15493
  count := 2060989259470224817689962598739826377433825155563162000
  charge := 1223457705404736803957591263707732133212152354241921006459693600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50023 : GroupCertificate where
  degree := 50023
  bound := 15356
  count := 1973920365957182086120002017454980748178649791748198400
  charge := 1191632901631733596849243073003253154749173321722653433219092480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50024 : GroupCertificate where
  degree := 50024
  bound := 15220
  count := 1889996576191669720062668763003314435130877310942908050
  charge := 1160069062117601135299612274449066214104049915371571370814714080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50025 : GroupCertificate where
  degree := 50025
  bound := 15085
  count := 1809136897733480813812564111783813717474039931080965760
  charge := 1128795715976543324723652471388365857156806925768675379379805824
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50026 : GroupCertificate where
  degree := 50026
  bound := 14952
  count := 1731835334508169528488934642227488986876694100621771882
  charge := 1098073522395353693449353757552033392447185584869378307061208192
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50027 : GroupCertificate where
  degree := 50027
  bound := 14821
  count := 1657959710933953469066052026799370954678642706061174240
  charge := 1067925811266175348754551980143477185060649409531316582067480160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50028 : GroupCertificate where
  degree := 50028
  bound := 14691
  count := 1586839737318793518978436680640103403418864500172899600
  charge := 1038142602124730660318705118766300130062552711685567941324702560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50029 : GroupCertificate where
  degree := 50029
  bound := 14562
  count := 1518398078386729208403402843446514838646427397263854784
  charge := 1008745880431323372351127825512929206181010475599233098348855488
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50030 : GroupCertificate where
  degree := 50030
  bound := 14435
  count := 1453066571387245545175811210001335341132040520469903896
  charge := 979983754366880864492926600819658961635977049678876284739308608
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50031 : GroupCertificate where
  degree := 50031
  bound := 14309
  count := 1390229484178339180827594761582867664178795478733494976
  charge := 951644060517883014986070053917131180223288630681573327988365248
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50032 : GroupCertificate where
  degree := 50032
  bound := 14184
  count := 1329812830585531491910774129833408408336891712938797580
  charge := 923743701595370945970154337544815160059800623448970838844305504
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50033 : GroupCertificate where
  degree := 50033
  bound := 14060
  count := 1271743557606424791653424323684492215970693073062971200
  charge := 896298111123451754811541370597300999137142214995481357116792640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50034 : GroupCertificate where
  degree := 50034
  bound := 13938
  count := 1216397797584518500271755417230540361132821489013686370
  charge := 869541327186334713540054247158960431354139425129992279409046016
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50035 : GroupCertificate where
  degree := 50035
  bound := 13816
  count := 1162793942659601628704552534754191806621773356458441472
  charge := 843043569816843612554134668795231756203832364044200568032877312
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50036 : GroupCertificate where
  degree := 50036
  bound := 13696
  count := 1111745041206214363211964823684585805596309618333462380
  charge := 817253644254336970310322684252632644395899015263665321794393280
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50037 : GroupCertificate where
  degree := 50037
  bound := 13577
  count := 1062735222072018999350376836124756940455270533158006080
  charge := 791961004895077923613960626083104171324546702625161997233359168
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50038 : GroupCertificate where
  degree := 50038
  bound := 13459
  count := 1015698005706696380162737350572261297985590278930782900
  charge := 767173876907490839187973318593658047548763844034219120207264160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50039 : GroupCertificate where
  degree := 50039
  bound := 13342
  count := 970568158032245708702719039289927637794048029030134720
  charge := 742899247750851185560541167115912098070449945541558287931413440
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50040 : GroupCertificate where
  degree := 50040
  bound := 13226
  count := 927281724366899062175832743109647472668186911327935228
  charge := 719142908996520012689099200992992694110785836486627772492134720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50041 : GroupCertificate where
  degree := 50041
  bound := 13111
  count := 885776058861529424572193243717076949637810318718320128
  charge := 695909499788406838292631819604401181281197839395300001433861632
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50042 : GroupCertificate where
  degree := 50042
  bound := 12997
  count := 845989849641884284009722527356700178629940821730329250
  charge := 673202551670515515617453075708532836059467954373662321718202400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50043 : GroupCertificate where
  degree := 50043
  bound := 12884
  count := 807863139850420667901784146533955067747313832829960000
  charge := 651024534521456396327816622391066160901183376412212666024600000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50044 : GroupCertificate where
  degree := 50044
  bound := 12772
  count := 771337344781300248181672263578005394127519498874884900
  charge := 629376903348262123738779822200905286084794283615049459122794080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50045 : GroupCertificate where
  degree := 50045
  bound := 12660
  count := 736044397874367811907600614110027405413112529350655824
  charge := 608070135224130046894549498232262057931853838665774543451456720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50046 : GroupCertificate where
  degree := 50046
  bound := 12550
  count := 702560782800485783037918730312860308034611705721668460
  charge := 587486972609746972573851452676737267345698625599747692693236640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50047 : GroupCertificate where
  degree := 50047
  bound := 12441
  count := 670510375117091887730710679710605608804577513929516544
  charge := 567432988473056808821087244777842371489879442197122320631492096
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50048 : GroupCertificate where
  degree := 50048
  bound := 12332
  count := 639560161055526204363212582813195768505994782762983940
  charge := 547725645990866416061923094341205975271895302978813269212341120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50049 : GroupCertificate where
  degree := 50049
  bound := 12224
  count := 609957979775975919314935345902672667856590295208349200
  charge := 528548985674291013418416939000781384175690378313449304047865360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50050 : GroupCertificate where
  degree := 50050
  bound := 12117
  count := 581652779330174402743949086267932454748678152496232258
  charge := 509899439175565832126977362581440511236007931981543707529979968
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50051 : GroupCertificate where
  degree := 50051
  bound := 12011
  count := 554594927346969119009155225443799219497789317399418240
  charge := 491772734285974349171346548214767578158310233649980881326382976
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50052 : GroupCertificate where
  degree := 50052
  bound := 11905
  count := 528493518992394298852600357419254238348261369902228940
  charge := 473996844485322642283068937644301671714441900970070489247875616
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50053 : GroupCertificate where
  degree := 50053
  bound := 11800
  count := 503561721734594629938234339744544642961190352825527840
  charge := 456740060668903036370864856560988249812185262782856351736694560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50054 : GroupCertificate where
  degree := 50054
  bound := 11696
  count := 479753295137498904982890268118544479471817496638182040
  charge := 439996286890901543636286281816244888058202773760844147504188640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50055 : GroupCertificate where
  degree := 50055
  bound := 11593
  count := 457023400258735575182985243547507912757239113167522880
  charge := 423758888636885230967506941666149026188356941579591374535682880
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50056 : GroupCertificate where
  degree := 50056
  bound := 11490
  count := 435119115233214514842042816226399930846438953266290998
  charge := 407867196275313014026350136485208784285570645632307937813831264
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50057 : GroupCertificate where
  degree := 50057
  bound := 11389
  count := 414424922874894699900497121881597082090736220686033920
  charge := 392624077686201510513016953276572750781373037537647454140867584
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50058 : GroupCertificate where
  degree := 50058
  bound := 11287
  count := 394294029024225520748647193985335276825139649127262950
  charge := 377571066070116136194083887484085292539159250721515236744361440
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50059 : GroupCertificate where
  degree := 50059
  bound := 11187
  count := 375291604204936492743358397025274645376713135603953120
  charge := 363150179671543945543934542107491068171817813147130456874391136
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50060 : GroupCertificate where
  degree := 50060
  bound := 11087
  count := 356996981497052616508467469180052408251502203298827032
  charge := 349062486895757438677623062893519419940045536469537587084280512
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50061 : GroupCertificate where
  degree := 50061
  bound := 10988
  count := 339566272729535225654062361989381022662671914801811552
  charge := 335445613965352146751749220657091771781816180039594637185072480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50062 : GroupCertificate where
  degree := 50062
  bound := 10889
  count := 322795883311193340716649245229893415320798383614988000
  charge := 322156809294292755849270404795394003748124580492848186466011520
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50063 : GroupCertificate where
  degree := 50063
  bound := 10791
  count := 306829606252148540683695364167480503782091748132108000
  charge := 309326348457867578903262477219933501843699939618497021482792800
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50064 : GroupCertificate where
  degree := 50064
  bound := 10694
  count := 291632422067572867379311937368257067739918231036974650
  charge := 296944259930233326121905875522977205856274504768325367046163520
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50065 : GroupCertificate where
  degree := 50065
  bound := 10597
  count := 277022420919861035814591060135338227501011193104674400
  charge := 284876919267508870819063866612574796521536231924797596597292640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50066 : GroupCertificate where
  degree := 50066
  bound := 10501
  count := 263126735855110314518368411084892393269158775018426278
  charge := 273243921448292400412005187424098258239224387571861162348112128
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50067 : GroupCertificate where
  degree := 50067
  bound := 10405
  count := 249776684652197537803712381670185237747179533139712512
  charge := 261917691144591222808041329057646418739510977685039018357985792
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50068 : GroupCertificate where
  degree := 50068
  bound := 10310
  count := 237089042372701614261953621979424718682777444743260800
  charge := 251010911965681681817895204068283148726811226024546247348819200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50069 : GroupCertificate where
  degree := 50069
  bound := 10216
  count := 225033628566011309872863463879670550917459980942778592
  charge := 240512722873267241026757171937959539973642620857068052382068192
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50070 : GroupCertificate where
  degree := 50070
  bound := 10122
  count := 213460424715604106784786910897791159559765974244109400
  charge := 230304589914657450287346113106967773354675216315983571896164800
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50071 : GroupCertificate where
  degree := 50071
  bound := 10028
  count := 202356214022058887780251095343995513264152072164766912
  charge := 220384736382146594671075905668751822189447415171658450282696640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50072 : GroupCertificate where
  degree := 50072
  bound := 9936
  count := 191930486777389206186388202524797819456024477875986962
  charge := 210954168467719477530675075053169410573051035973843459387854080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50073 : GroupCertificate where
  degree := 50073
  bound := 9843
  count := 181822521794346962485862791191153141766378188831696000
  charge := 201697098836531877247190184188974723923482927137570456710710400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50074 : GroupCertificate where
  degree := 50074
  bound := 9751
  count := 172238248025394465984729347443964193858392011025177070
  charge := 192811299870640509251133859979485981013265235844125063961150880
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50075 : GroupCertificate where
  degree := 50075
  bound := 9660
  count := 163152497658393310884444786813821288364628266127430400
  charge := 184285480510153262033667619698394490273708886205279630798305024
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50076 : GroupCertificate where
  degree := 50076
  bound := 9569
  count := 154447238346155086297103689184807471137937673168337360
  charge := 176018556508503319412986326233218989974519817690732150707648640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50077 : GroupCertificate where
  degree := 50077
  bound := 9479
  count := 146201174247387517487539525629525159719187891569911520
  charge := 168094849896726641395847120525495061557614682929688342834030816
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50078 : GroupCertificate where
  degree := 50078
  bound := 9389
  count := 138305614824141268660244469288102460599657565738579800
  charge := 160418859600040001204450813320908677328891195894667116298869120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50079 : GroupCertificate where
  degree := 50079
  bound := 9300
  count := 130832372286440522962800796257243631655082284174960960
  charge := 153069239923998995394413967240616300338588043175665918296330560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50080 : GroupCertificate where
  degree := 50080
  bound := 9211
  count := 123681492132760318778203414238562952211475539832875776
  charge := 145955935307178471613856108966107211391781007110330757395488768
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50081 : GroupCertificate where
  degree := 50081
  bound := 9123
  count := 116918411728935091176487794216656936639351663335015200
  charge := 139152177574406421958327313353047869397720380020482241003111200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50082 : GroupCertificate where
  degree := 50082
  bound := 9035
  count := 110451333681718406757724239512191274351257319640094740
  charge := 132573206067949234777445172610782968206834926052909667934182784
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50083 : GroupCertificate where
  degree := 50083
  bound := 8947
  count := 104270960816444593670933581871899633808078296205140800
  charge := 126215753171456003049765648438381131941141332244292916725198400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50084 : GroupCertificate where
  degree := 50084
  bound := 8860
  count := 98433873568831319966309788844456382017474015468085120
  charge := 120145289555160554593468760394566649355959158748082550704425216
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50085 : GroupCertificate where
  degree := 50085
  bound := 8773
  count := 92859344263902518857459028462054144524053513258511680
  charge := 114284638144356347461599912308624669702686778171408586125977920
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50086 : GroupCertificate where
  degree := 50086
  bound := 8687
  count := 87598722093683220547072955175859801981424471334746112
  charge := 108694441706934791427605613853210489262805305432072738219454720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50087 : GroupCertificate where
  degree := 50087
  bound := 8601
  count := 82578150153245880310687583775111700204618503427250304
  charge := 103302421838248222926393475154634662928679759983768234488075904
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50088 : GroupCertificate where
  degree := 50088
  bound := 8516
  count := 77844166371836506184196545289615734402530618703177750
  charge := 98164645453560975978835776606784131335036730291071695455034400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50089 : GroupCertificate where
  degree := 50089
  bound := 8431
  count := 73329293635876350264328070160064511197547948561951872
  charge := 93213549490214482992114722754286154220291323953617122481605760
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50090 : GroupCertificate where
  degree := 50090
  bound := 8346
  count := 69026098134877252726868399407563030013449315995348280
  charge := 88445608152935418966489152393275313066188742140389496240398720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50091 : GroupCertificate where
  degree := 50091
  bound := 8262
  count := 64974467435503003134578069615780731274481968790522048
  charge := 83910396973832816988476559352402866104971314633291518769183552
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50092 : GroupCertificate where
  degree := 50092
  bound := 8179
  count := 61160465114083468452411691396571833928190092686275360
  charge := 79598164567927419192256657486291485045313869202128142212295584
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50093 : GroupCertificate where
  degree := 50093
  bound := 8095
  count := 57485240178759993144055939346638742176669378556880000
  charge := 75401050558695364064146494801201623304935425228998942677712000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50094 : GroupCertificate where
  degree := 50094
  bound := 8012
  count := 54030055413817938354032877867807123060013973496337152
  charge := 71415866419505973686966958867096094650122243072941065507526272
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50095 : GroupCertificate where
  degree := 50095
  bound := 7930
  count := 50782400684957178430386973565594718129214686660953088
  charge := 67633314508871387842308962981911864245880107072525876570227712
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50096 : GroupCertificate where
  degree := 50096
  bound := 7847
  count := 47656780774415544488651511936784129219798477610002170
  charge := 63957261382566522497790105651543701264348962366624736094211680
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50097 : GroupCertificate where
  degree := 50097
  bound := 7765
  count := 44722843098449281788072018435330215866047592710731936
  charge := 60473138826330005449004602657618335179591304296536119589943456
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50098 : GroupCertificate where
  degree := 50098
  bound := 7684
  count := 41969403764177333204497429926028516662945036113054150
  charge := 57172146841159013797286475807772964758654277882424896631058560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50099 : GroupCertificate where
  degree := 50099
  bound := 7603
  count := 39354335396970156105265525125760002948306000891859200
  charge := 54007390451527712661634632230739983791069807133705638344879360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50100 : GroupCertificate where
  degree := 50100
  bound := 7522
  count := 36872411491753357589914550977196355122962382564272260
  charge := 50975491503756351837641683006327129612139397523287119969288160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50101 : GroupCertificate where
  degree := 50101
  bound := 7441
  count := 34518525071735482499296223578799472548738569687144416
  charge := 48073061806679956016138268705586321313990322854936821851556320
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50102 : GroupCertificate where
  degree := 50102
  bound := 7361
  count := 32314562185375309722110772193993970759706914266613196
  charge := 45330345713647877246418023151196644966865116063744816640833312
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50103 : GroupCertificate where
  degree := 50103
  bound := 7282
  count := 30251405039483303608392533124607527216910119541838400
  charge := 42739498782003387129949449267162721535036166140704390044143040
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50104 : GroupCertificate where
  degree := 50104
  bound := 7202
  count := 28272168232923422420744514071692924792702851360094062
  charge := 40231459967542090059070799773198919772012400472204250679375392
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50105 : GroupCertificate where
  degree := 50105
  bound := 7123
  count := 26422103291063319667736810460268021050898368235564800
  charge := 37865970486117896055638491841808204986104545486226888680288000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50106 : GroupCertificate where
  degree := 50106
  bound := 7044
  count := 24671545675878893649208043473157425498663777237258890
  charge := 35607720025123254824166069821476450819088329975696077560493600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50107 : GroupCertificate where
  degree := 50107
  bound := 6966
  count := 23036829010696376900408371666429820044981666162171008
  charge := 33480301746432349049051300522799593999246837435077197000989952
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50108 : GroupCertificate where
  degree := 50108
  bound := 6888
  count := 21491301431226973636330582728661904711749023074676600
  charge := 31451373030757477454501964123784012852427531588650765600657440
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50109 : GroupCertificate where
  degree := 50109
  bound := 6810
  count := 20031236282544039334659348937534285841579120025611520
  charge := 29517956470810945006599734096140035819753130007052616547302656
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50110 : GroupCertificate where
  degree := 50110
  bound := 6733
  count := 18670211078641396009961938534904785994216101741595976
  charge := 27700194581661520023395965386112809202887472070553320738823552
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50111 : GroupCertificate where
  degree := 50111
  bound := 6655
  count := 17369306881253253036007103442921961243083671472039936
  charge := 25947813273409290137747336532907073171734809149050513629726720
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50112 : GroupCertificate where
  degree := 50112
  bound := 6578
  count := 16158617937084258602929447007850537082073549183975110
  charge := 24303055515616186303464496759989491834349583488422747225100288
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50113 : GroupCertificate where
  degree := 50113
  bound := 6502
  count := 15032149102599425397868007239271172488947269304044960
  charge := 22759891860168635630901103944167097522079637824363644321394080
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50114 : GroupCertificate where
  degree := 50114
  bound := 6426
  count := 13970689343472631344254494390708145362199642080170024
  charge := 21293714551415003766044159217284346653530925926932561232502016
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50115 : GroupCertificate where
  degree := 50115
  bound := 6350
  count := 12971333940439389846142116289404367064906776372927168
  charge := 19901910096357286184547097856520269466367195244280344948397760
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50116 : GroupCertificate where
  degree := 50116
  bound := 6274
  count := 12031264582167396687619162323130556930763022051605580
  charge := 18581895543941998127074902465962930093521766677875207825227040
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50117 : GroupCertificate where
  degree := 50117
  bound := 6199
  count := 11159040671554464433481451644236134859926951402360000
  charge := 17347186055534377513767133778332665869050176055244922249658560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50118 : GroupCertificate where
  degree := 50118
  bound := 6124
  count := 10339342649177070807541138260102896715539331207375000
  charge := 16177481220316866930304482803029665820274557807190978038200000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50119 : GroupCertificate where
  degree := 50119
  bound := 6049
  count := 9569704878408288195023590132540870890462312360079200
  charge := 15070397749563073142442745909005781084943866648364334591406560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50120 : GroupCertificate where
  degree := 50120
  bound := 5974
  count := 8847740251505330661269540208517853327833270568622570
  charge := 14023588342355600411304635053937662892215786710168218568788640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50121 : GroupCertificate where
  degree := 50121
  bound := 5900
  count := 8179888720990388600817821966937739554048905310544000
  charge := 13047591854461671904349893820640427999907094927623094080192640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50122 : GroupCertificate where
  degree := 50122
  bound := 5826
  count := 7554051128520976306015007068228349909844120652238130
  charge := 12125837744754306892355142889051471825676859412257535219712160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50123 : GroupCertificate where
  degree := 50123
  bound := 5752
  count := 6968154072211668015927539250215261703321040520250000
  charge := 11256183443933644057496416376285325794734468076136350922906000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50124 : GroupCertificate where
  degree := 50124
  bound := 5679
  count := 6427368624290990608705540347489817007168974713965800
  charge := 10447306812925600378722447334611651899665246888844242707960640
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50125 : GroupCertificate where
  degree := 50125
  bound := 5606
  count := 5921643932830747674069158672232801813875341987113632
  charge := 9685100388422152517135207423706945874555749245149271317452960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50126 : GroupCertificate where
  degree := 50126
  bound := 5533
  count := 5449188820931182513814184454578194455096594193835696
  charge := 8967624037997441586033325477290743666126797076744891879219712
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50127 : GroupCertificate where
  degree := 50127
  bound := 5460
  count := 5008276004879710446554796943841895211434173937737664
  charge := 8292978141328767718739844265550067133952825472632932464844992
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50128 : GroupCertificate where
  degree := 50128
  bound := 5388
  count := 4602686647464277288772138534608138889180325310386300
  charge := 7667737409297622070927734196644218995345731401767390914021120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50129 : GroupCertificate where
  degree := 50129
  bound := 5315
  count := 4219549331849288522253357215119312067419047988531680
  charge := 7072693968503810203561711814204890660369961922504162083008992
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50130 : GroupCertificate where
  degree := 50130
  bound := 5244
  count := 3872602746073297308611671880992423046884846080519200
  charge := 6529888136675800610969804836475541568644604774561661706931200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50131 : GroupCertificate where
  degree := 50131
  bound := 5172
  count := 3545203689972528689775871853627745097684531199411200
  charge := 6013917331177460320272466406465902637919164070674835596008960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50132 : GroupCertificate where
  degree := 50132
  bound := 5100
  count := 3241056501685922044029428770419667274037949145319504
  charge := 5531076838763354690170121661591540854148422483948799375565056
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50133 : GroupCertificate where
  degree := 50133
  bound := 5029
  count := 2962628084611538486636333753082574314566753409164800
  charge := 5085863056905481474556802025475078375086735873780282725291520
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50134 : GroupCertificate where
  degree := 50134
  bound := 4958
  count := 2704320946762043755761271416425701557431397826463840
  charge := 4669859236352191246547420028490580117686881315022069398564096
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50135 : GroupCertificate where
  degree := 50135
  bound := 4888
  count := 2468224500216413697710124159103564268592564489902592
  charge := 4286928759656781300231480242410519085189838395239587748841472
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50136 : GroupCertificate where
  degree := 50136
  bound := 4817
  count := 2246482481514200783681119390454325519413950280132202
  charge := 3924732214982632224179430009149811427528876201208677365972960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50137 : GroupCertificate where
  degree := 50137
  bound := 4747
  count := 2044317657272352489516647763663997582174116735072000
  charge := 3592187569770143750848919358893815881259099494318526665619200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50138 : GroupCertificate where
  degree := 50138
  bound := 4677
  count := 1857502768767714703191533884559634644539343092867410
  charge := 3282748412807500530729301129871985260767039075360113500280480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50139 : GroupCertificate where
  degree := 50139
  bound := 4607
  count := 1685102896174359498363107915791752549410946709178368
  charge := 2995200892358801332673893087153665942758248386275692008744960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50140 : GroupCertificate where
  degree := 50140
  bound := 4538
  count := 1528406387025427677693325138281804790138890622425152
  charge := 2732049281717286575547386983917794149894321839991433494760960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50141 : GroupCertificate where
  degree := 50141
  bound := 4469
  count := 1384029967313645374582473895798239983099459513525280
  charge := 2487937398022472183406862063907463841868110361619916199408160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50142 : GroupCertificate where
  degree := 50142
  bound := 4400
  count := 1251193745805867641134919137435630367067621677991288
  charge := 2261814210222904284052341956829424615013568215154449349821952
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50143 : GroupCertificate where
  degree := 50143
  bound := 4331
  count := 1129154096194241701154195372723643116472501558224000
  charge := 2052665338884101367820833086006625142087387378355454542275200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50144 : GroupCertificate where
  degree := 50144
  bound := 4262
  count := 1017202687455582944903442787100239897929549715806762
  charge := 1859512877613483694787886737891521975504979767626254601889152
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50145 : GroupCertificate where
  degree := 50145
  bound := 4194
  count := 916089371746607380364051591135278780495574986486560
  charge := 1683897877324859193192454842303279836262868337399302106952480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50146 : GroupCertificate where
  degree := 50146
  bound := 4126
  count := 823505475524067710334842510600394005671363196791560
  charge := 1522036282588804466911498538089792767054404869802670956348160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50147 : GroupCertificate where
  degree := 50147
  bound := 4058
  count := 738868167448691071945123781593310075265003327687360
  charge := 1373094721230658913479647967794386960980133737724185713417408
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50148 : GroupCertificate where
  degree := 50148
  bound := 3990
  count := 661624252007115031422338207289316648586187254453160
  charge := 1236273112107281794177022758766879897616052446125727150559680
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50149 : GroupCertificate where
  degree := 50149
  bound := 3922
  count := 591249262873178795568243003799323674363557865551520
  charge := 1110804288993743341773268794412090851556184645316379803673760
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50150 : GroupCertificate where
  degree := 50150
  bound := 3855
  count := 528145042788644483790314648245880927039939278436352
  charge := 997571895185047306575085001210396719152874182126156323500800
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50151 : GroupCertificate where
  degree := 50151
  bound := 3788
  count := 470777264904992009091103997091714895435212167743552
  charge := 893974649274969240527297173261267033799050790722629009507136
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50152 : GroupCertificate where
  degree := 50152
  bound := 3721
  count := 418721017938516685422732199124200456510520758522020
  charge := 799370085101479366730772529521623226171907401362822438268480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50153 : GroupCertificate where
  degree := 50153
  bound := 3654
  count := 371575093028111668441273328899744037007125185473600
  charge := 713144994265203066358452844425673151634291187621921004850240
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50154 : GroupCertificate where
  degree := 50154
  bound := 3588
  count := 329566355433312164199350127679241865741133431218850
  charge := 635832777034745589073694794002562251554618583124032871708512
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50155 : GroupCertificate where
  degree := 50155
  bound := 3521
  count := 291068236623556444268917829653175975015207455598400
  charge := 564537137163739637453735731704086512902929976048241269357120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50156 : GroupCertificate where
  degree := 50156
  bound := 3455
  count := 256906702939673352349811755762195066130820120657984
  charge := 500877678004444953842474077114831623655345730934707573869056
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50157 : GroupCertificate where
  degree := 50157
  bound := 3389
  count := 226175426131234246205692334120052177341397428619520
  charge := 443256524285601168210249948771483015177202778780764573595904
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50158 : GroupCertificate where
  degree := 50158
  bound := 3323
  count := 198591782136126565051266493414668942457179853568000
  charge := 391218538882308076897059694117609723905042018641956416819200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50159 : GroupCertificate where
  degree := 50159
  bound := 3258
  count := 174245297226011870102362372338142665117656599491840
  charge := 345007845324741437055581516216941826094941396215925582443776
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50160 : GroupCertificate where
  degree := 50160
  bound := 3192
  count := 152141201839315210592969754515341991054945459554216
  charge := 302798156874488732069582020941386738507608365314158238484256
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50161 : GroupCertificate where
  degree := 50161
  bound := 3127
  count := 132725862176224675898443122389453963760420835043616
  charge := 265498408925576602608244278897858091646310793849030402418976
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50162 : GroupCertificate where
  degree := 50162
  bound := 3062
  count := 115438392723085191988293799983867138165771026568450
  charge := 232087527395478873030402829723692563464469367400466639155200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50163 : GroupCertificate where
  degree := 50163
  bound := 2998
  count := 100309010670285964417773648150250090123231405920000
  charge := 202674202726442777549101454937011630012285926273048945248000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50164 : GroupCertificate where
  degree := 50164
  bound := 2933
  count := 86687597966648430359116381224790093570822017264000
  charge := 176035859080255369829101084410474312171708148933190311062528
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50165 : GroupCertificate where
  degree := 50165
  bound := 2868
  count := 74658820685070186135797925707496502099641637426800
  charge := 152372355715172455163037972264838183578537118817332022377200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50166 : GroupCertificate where
  degree := 50166
  bound := 2804
  count := 64221358367694386558312632218719448420383432485812
  charge := 131718727876526481036525348487670276608418841924049761486048
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50167 : GroupCertificate where
  degree := 50167
  bound := 2740
  count := 55042079870690279882540481306592618977634380450688
  charge := 113449156640854371499896184137892302494687025556233945995008
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50168 : GroupCertificate where
  degree := 50168
  bound := 2676
  count := 46995103713978722464162719888181551166050912686250
  charge := 97340342700725488989824249805021249098343920746078496090400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50169 : GroupCertificate where
  degree := 50169
  bound := 2613
  count := 40067044529335892093972185317461540790880638504960
  charge := 83391905415204324087460282094111107789421108426955854352384
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50170 : GroupCertificate where
  degree := 50170
  bound := 2549
  count := 33932298327485250866699477306304713070870996529910
  charge := 70969976858729771375948716078567587057213931489678518916320
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50171 : GroupCertificate where
  degree := 50171
  bound := 2486
  count := 28687893984721122922531633904192359359813503021184
  charge := 60290312037276718943560930590891287936741617409148216194304
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50172 : GroupCertificate where
  degree := 50172
  bound := 2422
  count := 24078449322076831468393436874871605403714486275900
  charge := 50850264722479070717373134135990441034662370524344424471520
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50173 : GroupCertificate where
  degree := 50173
  bound := 2359
  count := 20168711129753051509339265646365730873115761386400
  charge := 42797809173594072854330667138814121878720812457087214700960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50174 : GroupCertificate where
  degree := 50174
  bound := 2297
  count := 16859208860211183737148058868920622309736721086720
  charge := 35943663611167710545088410941272494120914965097029465538560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50175 : GroupCertificate where
  degree := 50175
  bound := 2234
  count := 13978938811748062726093094073498191292476117043456
  charge := 29945354084707920030193566356187540362266324415940530475264
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50176 : GroupCertificate where
  degree := 50176
  bound := 2171
  count := 11526514873038261599926157878710490686214049546080
  charge := 24809559683235734824357834474924164327888090156803034803200
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50177 : GroupCertificate where
  degree := 50177
  bound := 2109
  count := 9478923048430203024152594162269286428301422544640
  charge := 20497889564411970113875432776097928769272939180391133038336
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50178 : GroupCertificate where
  degree := 50178
  bound := 2047
  count := 7748156265965226641827544663191794953956294771200
  charge := 16833463829241798765306741793036829820786225214215992524800
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50179 : GroupCertificate where
  degree := 50179
  bound := 1985
  count := 6292965678819942591446302164293186387202953154080
  charge := 13735716621312338825715119444925729551751972129768355023264
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50180 : GroupCertificate where
  degree := 50180
  bound := 1923
  count := 5076377654351306620168510399295483625748026690660
  charge := 11131831145887458118356215055233420779579839101224865145600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50181 : GroupCertificate where
  degree := 50181
  bound := 1861
  count := 4065376059346888409358049664020214852700229415616
  charge := 8956246543802921842721250860540027213505050367398802740928
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50182 : GroupCertificate where
  degree := 50182
  bound := 1800
  count := 3242811433065198481488862730691887604662037697704
  charge := 7176678459819452461312962775771363834641899670464854982976
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50183 : GroupCertificate where
  degree := 50183
  bound := 1738
  count := 2556017671975255126432980072226874807035673025600
  charge := 5682902231614334155037361374575025194967577330337568351040
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50184 : GroupCertificate where
  degree := 50184
  bound := 1677
  count := 2004988422747410055868526979476748887084683207364
  charge := 4478027409009562031369854875083013508059879180734277582144
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50185 : GroupCertificate where
  degree := 50185
  bound := 1616
  count := 1558300021751774565946227869521984005887264969952
  charge := 3496154261571269399080259497704338023105228982043278269152
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50186 : GroupCertificate where
  degree := 50186
  bound := 1555
  count := 1199151087139276547427200695833537997949099661006
  charge := 2702552548057441771470093375613206120428123672787262059360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50187 : GroupCertificate where
  degree := 50187
  bound := 1494
  count := 912926772512954789339383063902315181792200976000
  charge := 2066774189563595386913993826217902469430698632023783449600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50188 : GroupCertificate where
  degree := 50188
  bound := 1434
  count := 690268637476250138575159051361286356594725278400
  charge := 1569627185514120498193269656862430673267128575442237839360
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50189 : GroupCertificate where
  degree := 50189
  bound := 1373
  count := 513026471647505335107254747257241142799730544000
  charge := 1171837301066735880298942030714031023687503371415848457600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50190 : GroupCertificate where
  degree := 50190
  bound := 1313
  count := 378050228134488060728769330516828967289180586312
  charge := 867342865964833659774406024322947732265294927552780412480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50191 : GroupCertificate where
  degree := 50191
  bound := 1253
  count := 274561747099499920728991998987358853590222984512
  charge := 632690608503801231403997590247648512658785122099529447488
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50192 : GroupCertificate where
  degree := 50192
  bound := 1193
  count := 196242586926013270288882515885719296997011601700
  charge := 454204018276932582318425833776584122714836881250312562560
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50193 : GroupCertificate where
  degree := 50193
  bound := 1133
  count := 137814746467200664753365616438065508935448440000
  charge := 320373119355271356491316762224457203434598516926962552000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50194 : GroupCertificate where
  degree := 50194
  bound := 1073
  count := 94911249300197459196499206481265972569140979050
  charge := 221603728536161791988631916385651169416527162796878667040
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50195 : GroupCertificate where
  degree := 50195
  bound := 1014
  count := 64391489121701807541635039394544153949956860672
  charge := 150991296633107043871839078364793392999293876615318321408
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50196 : GroupCertificate where
  degree := 50196
  bound := 954
  count := 42362551756403899156783327896654524377382409952
  charge := 99769386600984957722276989380926699860210592310093241600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50197 : GroupCertificate where
  degree := 50197
  bound := 895
  count := 27322591607518515781828830168231198094666101760
  charge := 64624031307766027613969275789537232917802000254292997120
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50198 : GroupCertificate where
  degree := 50198
  bound := 836
  count := 17097658672730769905712189051903594782112517500
  charge := 40612736913068715958243747256524478100941199106476506400
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50199 : GroupCertificate where
  degree := 50199
  bound := 777
  count := 10335071955754550154390749453705749709354262720
  charge := 24654096090763945890719542515959049766752240250182720960
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50200 : GroupCertificate where
  degree := 50200
  bound := 718
  count := 6001892743050573409986111412712687148421218180
  charge := 14378391058944875747943399356586687386871819228903860160
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50201 : GroupCertificate where
  degree := 50201
  bound := 659
  count := 3325760375102691827579493409244814023546626176
  charge := 8001216565651492472055425775405859277686888740649222272
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50202 : GroupCertificate where
  degree := 50202
  bound := 600
  count := 1743090255220200063392628143758132978668273302
  charge := 4211380628838118226025088030245850070920374786128020608
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50203 : GroupCertificate where
  degree := 50203
  bound := 542
  count := 865217824598902040451239599569664587821371520
  charge := 2099110909160029949894168725916392073478297889028132480
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50204 : GroupCertificate where
  degree := 50204
  bound := 484
  count := 396668180079108235495249086578347120232491380
  charge := 966360735153624998811873692853676013921975920991219424
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50205 : GroupCertificate where
  degree := 50205
  bound := 425
  count := 161972791564540871087213198155620799526742144
  charge := 396262823981980803194712635235910884749346375962448000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50206 : GroupCertificate where
  degree := 50206
  bound := 367
  count := 58960181977822758409849602781250989079828744
  charge := 144842292921162599525313847177945352892951352539537600
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50207 : GroupCertificate where
  degree := 50207
  bound := 309
  count := 18048574313810874319861508487226715272740480
  charge := 44521675476810265572642795094742461766017663200633984
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50208 : GroupCertificate where
  degree := 50208
  bound := 252
  count := 4445722888234317773442085061803547569068480
  charge := 11011062195841095545344948918630545404261570129111040
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50209 : GroupCertificate where
  degree := 50209
  bound := 194
  count := 740560442436115836435125497069796497380000
  charge := 1841759267728823529377222264170932044807994833892000
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50210 : GroupCertificate where
  degree := 50210
  bound := 137
  count := 69174014933041460059221260492501084368212
  charge := 172729773055986560835277047526772903310035392072512
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50211 : GroupCertificate where
  degree := 50211
  bound := 79
  count := 1702462146261089601281739014542137005952
  charge := 4268553767773120973078702906830643417445336963456
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def group50212 : GroupCertificate where
  degree := 50212
  bound := 22
  count := 497550161938969261731793597047889800
  charge := 1252522989260532076137381177860838524078258880
  degree_ge := by norm_num
  degree_le := by norm_num
  nonmiddle := by norm_num
  count_pos := by norm_num
  count_exact := by
    norm_num [countPrefix,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  charge_exact := by
    norm_num [chargePrefix,chargePrimitive,prefixCoefficient,Finset.sum_range_succ,binomRat,Nat.choose]
  strict_margin := by norm_num

def block0 : List GroupCertificate := [group49964, group49965, group49966, group49967, group49968, group49969, group49970, group49971, group49972, group49973]

lemma block0_count : (block0.map GroupCertificate.count).sum = 139062197437581973435478226938308547847283459845983412120 := by
  norm_num [block0,group49964,group49965,group49966,group49967,group49968,group49969,group49970,group49971,group49972,group49973]

def block1 : List GroupCertificate := [group49974, group49975, group49976, group49977, group49978, group49979, group49980, group49981, group49982, group49983]

lemma block1_count : (block1.map GroupCertificate.count).sum = 134189318573910639171767305502701759504224960515707671508 := by
  norm_num [block1,group49974,group49975,group49976,group49977,group49978,group49979,group49980,group49981,group49982,group49983]

def block2 : List GroupCertificate := [group49984, group49985, group49986, group49987, group49988, group49989, group49990, group49991, group49992, group49993]

lemma block2_count : (block2.map GroupCertificate.count).sum = 89679381593658382387289553249083634058495437460952893084 := by
  norm_num [block2,group49984,group49985,group49986,group49987,group49988,group49989,group49990,group49991,group49992,group49993]

def block3 : List GroupCertificate := [group49994, group49995, group49996, group49997, group49998, group49999, group50000, group50001, group50002, group50003]

lemma block3_count : (block3.map GroupCertificate.count).sum = 57049845347467795023822856089133713315760814299446655980 := by
  norm_num [block3,group49994,group49995,group49996,group49997,group49998,group49999,group50000,group50001,group50002,group50003]

def block4 : List GroupCertificate := [group50004, group50005, group50006, group50007, group50008, group50009, group50010, group50011, group50012, group50013]

lemma block4_count : (block4.map GroupCertificate.count).sum = 37071337613981218857449207138065660234803886282886791752 := by
  norm_num [block4,group50004,group50005,group50006,group50007,group50008,group50009,group50010,group50011,group50012,group50013]

def block5 : List GroupCertificate := [group50014, group50015, group50016, group50017, group50018, group50019, group50020, group50021, group50022, group50023]

lemma block5_count : (block5.map GroupCertificate.count).sum = 24152381951265346863073350156763153376899420113793916522 := by
  norm_num [block5,group50014,group50015,group50016,group50017,group50018,group50019,group50020,group50021,group50022,group50023]

def block6 : List GroupCertificate := [group50024, group50025, group50026, group50027, group50028, group50029, group50030, group50031, group50032, group50033]

lemma block6_count : (block6.map GroupCertificate.count).sum = 15639018778830337268379663493002709965843966731348741968 := by
  norm_num [block6,group50024,group50025,group50026,group50027,group50028,group50029,group50030,group50031,group50032,group50033]

def block7 : List GroupCertificate := [group50034, group50035, group50036, group50037, group50038, group50039, group50040, group50041, group50042, group50043]

lemma block7_count : (block7.map GroupCertificate.count).sum = 10006848939982029019063638662373643518269065189531058528 := by
  norm_num [block7,group50034,group50035,group50036,group50037,group50038,group50039,group50040,group50041,group50042,group50043]

def block8 : List GroupCertificate := [group50044, group50045, group50046, group50047, group50048, group50049, group50050, group50051, group50052, group50053]

lemma block8_count : (block8.map GroupCertificate.count).sum = 6298273988808880305079989225302897708298325518471466146 := by
  norm_num [block8,group50044,group50045,group50046,group50047,group50048,group50049,group50050,group50051,group50052,group50053]

def block9 : List GroupCertificate := [group50054, group50055, group50056, group50057, group50058, group50059, group50060, group50061, group50062, group50063]

lemma block9_count : (block9.map GroupCertificate.count).sum = 3882095110523435431963295481351466677385148818336980492 := by
  norm_num [block9,group50054,group50055,group50056,group50057,group50058,group50059,group50060,group50061,group50062,group50063]

def block10 : List GroupCertificate := [group50064, group50065, group50066, group50067, group50068, group50069, group50070, group50071, group50072, group50073]

lemma block10_count : (block10.map GroupCertificate.count).sum = 2333250581742853842888089876075505829903825871102386506 := by
  norm_num [block10,group50064,group50065,group50066,group50067,group50068,group50069,group50070,group50071,group50072,group50073]

def block11 : List GroupCertificate := [group50074, group50075, group50076, group50077, group50078, group50079, group50080, group50081, group50082, group50083]

lemma block11_count : (block11.map GroupCertificate.count).sum = 1360499343747770582660211644456775002345048510817523626 := by
  norm_num [block11,group50074,group50075,group50076,group50077,group50078,group50079,group50080,group50081,group50082,group50083]

def block12 : List GroupCertificate := [group50084, group50085, group50086, group50087, group50088, group50089, group50090, group50091, group50092, group50093]

lemma block12_count : (block12.map GroupCertificate.count).sum = 765289820950599513587968071473716611720439826782748526 := by
  norm_num [block12,group50084,group50085,group50086,group50087,group50088,group50089,group50090,group50091,group50092,group50093]

def block13 : List GroupCertificate := [group50094, group50095, group50096, group50097, group50098, group50099, group50100, group50101, group50102, group50103]

lemma block13_count : (block13.map GroupCertificate.count).sum = 412472722921134885790620416731902031534643753542805968 := by
  norm_num [block13,group50094,group50095,group50096,group50097,group50098,group50099,group50100,group50101,group50102,group50103]

def block14 : List GroupCertificate := [group50104, group50105, group50106, group50107, group50108, group50109, group50110, group50111, group50112, group50113]

lemma block14_count : (block14.map GroupCertificate.count).sum = 211155468923911358655854167562692838748895397797032862 := by
  norm_num [block14,group50104,group50105,group50106,group50107,group50108,group50109,group50110,group50111,group50112,group50113]

def block15 : List GroupCertificate := [group50114, group50115, group50116, group50117, group50118, group50119, group50120, group50121, group50122, group50123]

lemma block15_count : (block15.map GroupCertificate.count).sum = 101591210238447604898091861534022176318845372526171672 := by
  norm_num [block15,group50114,group50115,group50116,group50117,group50118,group50119,group50120,group50121,group50122,group50123]

def block16 : List GroupCertificate := [group50124, group50125, group50126, group50127, group50128, group50129, group50130, group50131, group50132, group50133]

lemma block16_count : (block16.map GroupCertificate.count).sum = 45250204384589483583222482425992569177348537965985476 := by
  norm_num [block16,group50124,group50125,group50126,group50127,group50128,group50129,group50130,group50131,group50132,group50133]

def block17 : List GroupCertificate := [group50134, group50135, group50136, group50137, group50138, group50139, group50140, group50141, group50142, group50143]

lemma block17_count : (block17.map GroupCertificate.count).sum = 18298735447046267322788718074238294378340792505782132 := by
  norm_num [block17,group50134,group50135,group50136,group50137,group50138,group50139,group50140,group50141,group50142,group50143]

def block18 : List GroupCertificate := [group50144, group50145, group50146, group50147, group50148, group50149, group50150, group50151, group50152, group50153]

lemma block18_count : (block18.map GroupCertificate.count).sum = 6537757635715507781283466054879403398304033736952446 := by
  norm_num [block18,group50144,group50145,group50146,group50147,group50148,group50149,group50150,group50151,group50152,group50153]

def block19 : List GroupCertificate := [group50154, group50155, group50156, group50157, group50158, group50159, group50160, group50161, group50162, group50163]

lemma block19_count : (block19.map GroupCertificate.count).sum = 1977168267898825685074881238006389874907763616240876 := by
  norm_num [block19,group50154,group50155,group50156,group50157,group50158,group50159,group50160,group50161,group50162,group50163]

def block20 : List GroupCertificate := [group50164, group50165, group50166, group50167, group50168, group50169, group50170, group50171, group50172, group50173]

lemma block20_count : (block20.map GroupCertificate.count).sum = 474539357897454154260866139394976163732927766031904 := by
  norm_num [block20,group50164,group50165,group50166,group50167,group50168,group50169,group50170,group50171,group50172,group50173]

def block21 : List GroupCertificate := [group50174, group50175, group50176, group50177, group50178, group50179, group50180, group50181, group50182, group50183]

lemma block21_count : (block21.map GroupCertificate.count).sum = 80825290356951528958042154677118032948033524975756 := by
  norm_num [block21,group50174,group50175,group50176,group50177,group50178,group50179,group50180,group50181,group50182,group50183]

def block22 : List GroupCertificate := [group50184, group50185, group50186, group50187, group50188, group50189, group50190, group50191, group50192, group50193]

lemma block22_count : (block22.map GroupCertificate.count).sum = 7865330721902373348763761869181086198919568249246 := by
  norm_num [block22,group50184,group50185,group50186,group50187,group50188,group50189,group50190,group50191,group50192,group50193]

def block23 : List GroupCertificate := [group50194, group50195, group50196, group50197, group50198, group50199, group50200, group50201, group50202, group50203]

lemma block23_count : (block23.map GroupCertificate.count).sum = 268356573612279369078258815011590492221070620832 := by
  norm_num [block23,group50194,group50195,group50196,group50197,group50198,group50199,group50200,group50201,group50202,group50203]

def block24 : List GroupCertificate := [group50204, group50205, group50206, group50207, group50208, group50209, group50210, group50211, group50212]

lemma block24_count : (block24.map GroupCertificate.count).sum = 640906888240582637410680371292619608447515192 := by
  norm_num [block24,group50204,group50205,group50206,group50207,group50208,group50209,group50210,group50211,group50212]

def superblock0 : List GroupCertificate := block0 ++ block1 ++ block2 ++ block3 ++ block4

lemma superblock0_count : (superblock0.map GroupCertificate.count).sum = 457052080566600008875807148917293314960568558404977424444 := by
  rw [superblock0]
  simp only [List.map_append,List.sum_append,block0_count,block1_count,block2_count,block3_count,block4_count]

def superblock1 : List GroupCertificate := block5 ++ block6 ++ block7 ++ block8 ++ block9

lemma superblock1_count : (superblock1.map GroupCertificate.count).sum = 59978618769410028887559937018793871246695926371482163656 := by
  rw [superblock1]
  simp only [List.map_append,List.sum_append,block5_count,block6_count,block7_count,block8_count,block9_count]

def superblock2 : List GroupCertificate := block10 ++ block11 ++ block12 ++ block13 ++ block14

lemma superblock2_count : (superblock2.map GroupCertificate.count).sum = 5082667938286270183582744176300592314252853360042497488 := by
  rw [superblock2]
  simp only [List.map_append,List.sum_append,block10_count,block11_count,block12_count,block13_count,block14_count]

def superblock3 : List GroupCertificate := block15 ++ block16 ++ block17 ++ block18 ++ block19

lemma superblock3_count : (superblock3.map GroupCertificate.count).sum = 173655075973697689270461409327138833147746500351132602 := by
  rw [superblock3]
  simp only [List.map_append,List.sum_append,block15_count,block16_count,block17_count,block18_count,block19_count]

def superblock4 : List GroupCertificate := block20 ++ block21 ++ block22 ++ block23 ++ block24

lemma superblock4_count : (superblock4.map GroupCertificate.count).sum = 563498976456808576519387725436658165991710377392930 := by
  rw [superblock4]
  simp only [List.map_append,List.sum_append,block20_count,block21_count,block22_count,block23_count,block24_count]

def selectedGroups : List GroupCertificate := superblock0 ++ superblock1 ++ superblock2 ++ superblock3 ++ superblock4

lemma selectedGroups_count : (selectedGroups.map GroupCertificate.count).sum = 522287585849246462444796810909440354012831076347230611120 := by
  rw [selectedGroups]
  simp only [List.map_append,List.sum_append,superblock0_count,superblock1_count,superblock2_count,superblock3_count,superblock4_count]

lemma low_full_count : binomRat (49963+15) 15+binomRat (49963+14) 15-17 = 46263212779662287120769028218618902818698920884331860462663 := by
  norm_num [binomRat]

lemma euclidean_count : binomRat (50000+15) 15+binomRat (50000+14) 15 = 46779709349146362239266126538609505511855492134986686636251 := by
  norm_num [binomRat]

lemma strict_surplus : binomRat (50000+15) 15+binomRat (50000+14) 15 <
    binomRat (49963+15) 15+binomRat (49963+14) 15-17 +
    ((selectedGroups.map GroupCertificate.count).sum:ℚ) := by
  rw [euclidean_count,low_full_count,selectedGroups_count]
  norm_num

end HarmonicCounterexample.Certificate

end

end OAI
